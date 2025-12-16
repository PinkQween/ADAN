#include "codegen.h"
#include <stdlib.h>
#include "liveness.h"
#include "ir.h"
#include "string.h"
#include <execinfo.h>

static void print_backtrace_info() {
	void* bt[32];
	int bt_size = backtrace(bt, 32);
	char** bt_syms = backtrace_symbols(bt, bt_size);
	fprintf(stderr, "BACKTRACE (%d):\n", bt_size);
	if (bt_syms) {
		for (int i = 0; i < bt_size; i++) fprintf(stderr, "  %s\n", bt_syms[i]);
		free(bt_syms);
	}
}



#ifdef __aarch64__
   #define ARCH_ARM64 1
#elif defined(__x86_64__) || defined(_M_X64)
   #define ARCH_X86_64 1
#else
   #define ARCH_X86_64 1  // Default to x86_64
#endif


static int last_frame_adjust = 0;
static int epilogue_emitted = 0;
/* Tracks whether we've actually emitted a function prologue in this run so
   that we avoid emitting an epilogue (pop/ret) without a matching prologue. */
static int prologue_was_emitted = 0;
/* Tracks whether the most recently emitted prologue has had any body
   instructions emitted after it (prevents emitting an epilogue for an
   empty prologue). */
static int prologue_has_body = 0;
/* Track whether any assembly text was emitted since the last prologue. This
   helps avoid flushing an epilogue immediately after a prologue when the
   actual function body appears later in the traversal. */
static int output_emitted_since_prologue = 0;


static const char* mangle_symbol(const char* name) {
   #ifdef __APPLE__
       static char mangled[256];
       snprintf(mangled, sizeof(mangled), "_%s", name);
       return mangled;
   #else
       return name;
   #endif
}


bool init_target_config(TargetConfig* cfg, int available_registers, char** register_names, int caller_saved_count, int* caller_saved_indices, int spill_slot_size) {
   cfg->available_registers = available_registers;
   cfg->register_names = register_names;
   cfg->caller_saved_indices = caller_saved_indices;
   cfg->caller_saved_count = caller_saved_count;
   cfg->spill_slot_size = spill_slot_size;


   return true;
}


void free_target_config(TargetConfig* cfg) {
   if (cfg == NULL) return;
   if (cfg->register_names != NULL) {
       for (int i = 0; i < cfg->available_registers; i++) {
           if (cfg->register_names[i] != NULL) free(cfg->register_names[i]);
       }


       free(cfg->register_names);
   }


   if (cfg->caller_saved_indices != NULL) free(cfg->caller_saved_indices);
   free(cfg);
}


const char* get_register_name(const TargetConfig* cfg, int index) {
   if (cfg == NULL) return NULL;
   if (cfg->register_names == NULL) return NULL;
   if (index < 0 || index >= cfg->available_registers) return NULL;


   return cfg->register_names[index];
}


void get_location(char* result_buffer, char* variable_name, LiveInterval* intervals, const TargetConfig* cfg) {
   if (variable_name[0] == '+' || variable_name[0] == '-') {
       if (is_digit(variable_name[1])) {
           sprintf(result_buffer, "$%s", variable_name);
           return;
       }
   } else if (is_digit(variable_name[0])) {
       sprintf(result_buffer, "$%s", variable_name);
       return;
   }


   if (variable_name[0] == '.' && variable_name[1] == 'S' && variable_name[2] == 'T' && variable_name[3] == 'R') {
       // TODO: Full ARM64 code generation requires rewriting all instruction generation
       sprintf(result_buffer, "%s(%%rip)", variable_name);
       return;
   }


   if (variable_name[0] == 'G' && variable_name[1] == '_') {
       sprintf(result_buffer, "%s(%%rip)", variable_name);
       return;
   }


   LiveInterval* current = intervals;
   while (current != NULL) {
       if (strcmp(current->variable_name, variable_name) == 0) {
           if (current->registry != -1) {
               char* register_name = cfg->register_names[current->registry];
               sprintf(result_buffer, "%%%s", register_name);
               return;
           } else {
               sprintf(result_buffer, "%d(%%rbp)", current->stack_offset);
               return;
           }
       }


       current = current->next;
   }


   strcpy(result_buffer, variable_name);
}


void generate_asm(IRInstruction* ir_head, LiveInterval* intervals, const TargetConfig* cfg, FILE* out, int stack_bytes) {
   IRInstruction* node = ir_head;
   IRInstruction* current = NULL;
   /* Reset per-run flags to ensure we don't inherit state between calls */
   epilogue_emitted = 0;
   prologue_was_emitted = 0;
   /* Reset tracking of whether we've emitted body assembly since a prologue */
   output_emitted_since_prologue = 0;

   fprintf(stderr, "DEBUG_GENASM_START: node_addr=%p &node=%p &current=%p\n", (void*)node, (void*)&node, (void*)&current);
  
   // Print first few IR nodes for debugging
   {
       IRInstruction* tmp = ir_head;
       for (int i = 0; i < 20 && tmp; i++) {
           fprintf(stderr, "IR_AT_START[%d]: addr=%p op=%d arg1=%s arg2=%s res=%s next=%p\n", i, (void*)tmp, tmp->op, tmp->arg1 ? tmp->arg1 : "(null)", tmp->arg2 ? tmp->arg2 : "(null)", tmp->result ? tmp->result : "(null)", (void*)tmp->next);
           tmp = tmp->next;
       }
   }

   char arg_locs[8][64];
   int arg_is_lea[8];
   int arg_count = 0;
  
   // TODO: Full ARM64 code generation requires rewriting all instruction generation
   const char* arg_regs[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};
  
   char loc1[64];
   char loc2[64];
   char result_loc[64];


   /* The assembler emits the "_main" label before calling generate_asm, so
      assume we're inside a function at the start and defer the prologue until
      the first non-label instruction. */
   bool in_function = true;
   bool current_function_has_body = false;
   bool prologue_pending = true;
   bool need_epilogue = false;
   int need_epilogue_last_frame_adjust = 0;
   bool prologue_emitted_local = false;


   void* _seen_nodes[8192];
int _seen_count = 0;
   node = ir_head;
   current = NULL;

   /* Prologue is pending for the externally emitted label (e.g., "_main:").
      Defer emitting the actual prologue until we see the first non-label
      instruction to ensure it's placed immediately after the label. */
   if (prologue_pending) {
       fprintf(stderr, "PROLOGUE_PENDING_AT_START: will emit when first body instruction is seen\n");
   }

   /* Track whether we've actually emitted assembly text for a function body
      since the last emitted prologue. This helps avoid flushing an epilogue
      immediately after a prologue when the actual body instructions are
      emitted later in a fragmented traversal. */
   int output_emitted_since_prologue = 0;

while (node != NULL) {
       current = node;
       fprintf(stderr, "LOOP_TOP: prologue_pending=%d current=%p op=%d\n", (int)prologue_pending, (void*)current, current ? current->op : -1);
       /* If we have a pending prologue for the most recently emitted label, emit it
          as soon as we encounter the first non-label instruction that belongs to
          that function. This prevents emitting a prologue/epilogue pair before the
          function body when traversal gets fragmented. */
       if (prologue_pending && current->op != IR_LABEL) {
           fprintf(stderr, "PROLOGUE_PENDING_CALL: current=%p op=%d\n", (void*)current, current->op);
           emit_prologue(out, cfg, stack_bytes);
           prologue_pending = false;
           prologue_emitted_local = true;
           /* We are emitting the prologue at the first non-label instruction, so
              this instruction counts as the function body — mark the prologue as
              having body immediately to prevent premature epilogue emission. */
           prologue_has_body = 1;
           current_function_has_body = true;
       }
       /* detect cycles defensively: if we've seen this node before, abort the walk */
       fprintf(stderr, "DBG: SEEN_COUNT=%d\n", _seen_count);
       int _already = 0;
       for (int _i = 0; _i < _seen_count; _i++) {
           fprintf(stderr, "DBG: SEEN[%d]=%p\n", _i, _seen_nodes[_i]);
           if (_seen_nodes[_i] == (void*)current) { _already = 1; break; }
       }
       if (_already) {
           /* determine where the match was */
           int _match_idx = -1;
           for (int _i = 0; _i < _seen_count; _i++) {
               if (_seen_nodes[_i] == (void*)current) { _match_idx = _i; break; }
           }
           /* If the match was to an earlier node (not the most recently added), treat it as a cycle and abort */
           if (_match_idx != -1 && _match_idx < (_seen_count - 1)) {
               fprintf(stderr, "ERROR: generate_asm detected IR list cycle at node %p idx=%d op=%d; aborting assembly walk\n", (void*)current, current->index, current->op);
               /* Find which previous node points to current (if any) */
               for (int _i = 0; _i < _seen_count; _i++) {
                   IRInstruction* prev = (IRInstruction*)_seen_nodes[_i];
                   if (prev->next == current) fprintf(stderr, "ERROR: previous node at %p idx=%d op=%d points to current\n", (void*)prev, prev->index, prev->op);
               }
               /* Dump seen nodes */
               for (int _i = 0; _i < _seen_count; _i++) {
                   IRInstruction* n = (IRInstruction*)_seen_nodes[_i];
                   fprintf(stderr, "SEEN[%d]=%p idx=%d op=%d next=%p\n", _i, (void*)n, n->index, n->op, (void*)n->next);
               }
               fprintf(stderr, "PRINTING BACKTRACE DUMP DUE TO CYCLE:\n");
               print_backtrace_info();
               break;
           } else {
               /* benign: matched the most recently seen node (likely the node we just added), printing backtrace and advancing */
               fprintf(stderr, "WARN: generate_asm saw repeated node equal to last seen (idx=%d), printing backtrace and advancing to next\n", _match_idx);
               print_backtrace_info();
               /* Advance explicitly to avoid spinning */
               fprintf(stderr, "ADVANCE_FROM_BENIGN: current=%p next=%p\n", (void*)current, (void*)current->next);
               /* Ensure we mark that we've emitted a body op if this node is non-label */
               if (current->op != IR_LABEL) current_function_has_body = true;
               /* Also mark as having a body if the node we're advancing to is a non-label
                  (this covers the case where we advanced over a label match and the next
                  node is the first real body instruction) */
               if (current->next != NULL && current->next->op != IR_LABEL) current_function_has_body = true;
               /* If we are advancing to a non-label node and a prologue is pending, emit the prologue now
                  so the function prologue appears immediately before the body instructions. */
               if (prologue_pending && current->next != NULL && current->next->op != IR_LABEL) {
                   fprintf(stderr, "PROLOGUE_PENDING_ADVANCE_FLUSH: emitting prologue now for advanced node=%p op=%d\n", (void*)current->next, current->next->op);
                   emit_prologue(out, cfg, stack_bytes);
                   prologue_pending = false;
                   prologue_emitted_local = true;
               }
               node = current->next;
               continue;
           }
       }

       /* TRACE: show current node for debugging traversal order */
       fprintf(stderr, "TRACE: generate_asm visiting addr=%p idx=%d op=%d\n", (void*)current, current->index, current->op);
       fprintf(stderr, "PRE_SWITCH: current=%p idx=%d op=%d\n", (void*)current, current->index, current->op);


       loc1[0] = '\0';
       loc2[0] = '\0';
       result_loc[0] = '\0';


       if (current->arg1 != NULL) get_location(loc1, current->arg1, intervals, cfg);
       if (current->arg2 != NULL) get_location(loc2, current->arg2, intervals, cfg);
       if (current->result != NULL) get_location(result_loc, current->result, intervals, cfg);


       int reset_args = 1;


       switch (current->op) {
           case IR_ADD:
               {
                   int result_is_mem = strchr(result_loc, '(') != NULL;
                   if (result_is_mem) {
                       fprintf(out, "movq %s, %%r11\n", loc1);
                       fprintf(out, "addq %s, %%r11\n", loc2);
                       fprintf(out, "movq %%r11, %s\n", result_loc);
                   } else {
                       fprintf(out, "movq %s, %s\n", loc1, result_loc);
                       fprintf(out, "addq %s, %s\n", loc2, result_loc);
                   }
               }
               break;


           case IR_SUB:
               {
                   int result_is_mem = strchr(result_loc, '(') != NULL;
                   if (result_is_mem) {
                       fprintf(out, "movq %s, %%r11\n", loc1);
                       fprintf(out, "subq %s, %%r11\n", loc2);
                       fprintf(out, "movq %%r11, %s\n", result_loc);
                   } else {
                       fprintf(out, "movq %s, %s\n", loc1, result_loc);
                       fprintf(out, "subq %s, %s\n", loc2, result_loc);
                   }
               }
               break;


       case IR_LEA: {
           // Compute effective address: result = &arg1 + arg2
           // Load base address into r11 (use leaq for label/mem), then add scaled offset
           if (loc1[0] == 'G' && loc1[1] == '_' ) {
               // label (%rip)
               fprintf(out, "leaq %s, %%r11\n", loc1);
           } else if (strchr(loc1, '(') != NULL) {
               // memory reference like -56(%rbp) - use LEA to get its address
               fprintf(out, "leaq %s, %%r11\n", loc1);
           } else {
               fprintf(out, "movq %s, %%r11\n", loc1);
           }
           fprintf(out, "addq %s, %%r11\n", loc2);
           fprintf(out, "movq %%r11, %s\n", result_loc);
           break; }


       case IR_LOAD: {
           // Load the 8-byte value pointed to by arg1 into result
           fprintf(out, "movq %s, %%r11\n", loc1);
           if (strchr(result_loc, '(') != NULL) {
               // destination is memory - avoid memory to memory movq
               fprintf(out, "movq (%%r11), %%r12\n");
               fprintf(out, "movq %%r12, %s\n", result_loc);
           } else {
               fprintf(out, "movq (%%r11), %s\n", result_loc);
           }
           break; }


       case IR_MUL: {
           int result_is_mem = strchr(result_loc, '(') != NULL;
           if (result_is_mem) {
               fprintf(out, "movq %s, %%r11\n", loc1);
               if (loc2[0] == '$') {
                   fprintf(out, "imulq %s, %%r11\n", loc2);
               } else {
                   fprintf(out, "imulq %s, %%r11\n", loc2);
               }
               fprintf(out, "movq %%r11, %s\n", result_loc);
           } else {
               fprintf(out, "movq %s, %s\n", loc1, result_loc);
               if (loc2[0] == '$') {
                   fprintf(out, "imulq %s, %s\n", loc2, result_loc);
               } else {
                   fprintf(out, "imulq %s, %s\n", loc2, result_loc);
               }
           }
           break; }


       case IR_DIV: {
           // Division uses rax and rdx: dividend in rax, quotient returned in rax
           fprintf(out, "movq %s, %%rax\n", loc1);
           fprintf(out, "cqto\n");
           if (loc2[0] == '$') {
               fprintf(out, "movq %s, %%r11\n", loc2);
               fprintf(out, "idivq %%r11\n");
           } else {
               fprintf(out, "idivq %s\n", loc2);
           }
           fprintf(out, "movq %%rax, %s\n", result_loc);
           break; }


           case IR_MOD:
               fprintf(out, "movq %s, %%rax\n", loc1);
               fprintf(out, "cqto\n");
               if (loc2[0] == '$') {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "idivq %%r11\n");
               } else {
                   fprintf(out, "idivq %s\n", loc2);
               }
               fprintf(out, "movq %%rdx, %s\n", result_loc);
               break;


           case IR_ASSIGN:
               if (current->arg1[0] == '.' && current->arg1[1] == 'S' && current->arg1[2] == 'T' && current->arg1[3] == 'R') {
                   fprintf(out, "leaq %s, %%rax\n", loc1);
                   fprintf(out, "movq %%rax, %s\n", result_loc);
               } else {
                   int src_is_mem = (strchr(loc1, '(') != NULL);
                   int dst_is_mem = (strchr(result_loc, '(') != NULL);
                   if (src_is_mem && dst_is_mem) {
                       fprintf(out, "movq %s, %%r11\n", loc1);
                       fprintf(out, "movq %%r11, %s\n", result_loc);
                   } else {
                       fprintf(out, "movq %s, %s\n", loc1, result_loc);
                   }
               }
               break;
          
           case IR_LABEL: {
               int is_block_label = (current->arg1 && current->arg1[0] == '_');
               fprintf(stderr, "DEBUG: generate_asm/IR_LABEL emit name=%s block=%d\n", current->arg1 ? current->arg1 : "(null)", is_block_label);
               fprintf(stderr, "IR_LABEL_HANDLER: name=%s is_block_label=%d in_function_before=%d\n", current->arg1 ? current->arg1 : "(null)", is_block_label, (int)in_function);
               if (!is_block_label) {
                   if (in_function) {
                       if (current_function_has_body) {
                           fprintf(stderr, "CALL_SITE(IR_LABEL): in_function=%d current=%p next=%p\n", (int)in_function, (void*)current, (void*)current->next);
                           /* Buffer the epilogue instead of emitting it inline so that function
                              body code (which may be emitted later in the traversal) remains
                              placed between prologue and epilogue in the output. */
                           /* Only buffer/flush an epilogue if we've actually emitted a prologue
                              for the function we're trying to close. This avoids emitting a
                              premature epilogue when traversal emits labels before the prologue. */
                           if (prologue_was_emitted || prologue_emitted_local) {
                               if (!need_epilogue) {
                                   need_epilogue = true;
                                   need_epilogue_last_frame_adjust = last_frame_adjust;
                                   /* mark last_frame_adjust consumed so other code doesn't double-apply it */
                                   last_frame_adjust = 0;
                               }
                               /* Flush the buffered epilogue immediately before starting the new function
                                  so the previous function is properly closed in the emitted assembly. */
                               if (need_epilogue) {
                                   fprintf(stderr, "FLUSHING_BUFFERED_EPILOGUE: frame_adjust=%d\n", need_epilogue_last_frame_adjust);
                                   last_frame_adjust = need_epilogue_last_frame_adjust;
                                   need_epilogue = false;
                                   need_epilogue_last_frame_adjust = 0;
                                   /* Only emit the buffered epilogue if we've actually emitted body
                                      assembly since the matching prologue. This avoids emitting an
                                      epilogue immediately after a prologue when the body appears
                                      later in a fragmented traversal. */
                                   if (!output_emitted_since_prologue) {
                                       fprintf(stderr, "SKIP_BUFFERED_EPILOGUE_NO_OUTPUT: skipping emit because no body assembly was emitted since prologue\n");
                                       /* Re-buffer the epilogue for later emission */
                                       need_epilogue = true;
                                       need_epilogue_last_frame_adjust = last_frame_adjust;
                                       last_frame_adjust = 0;
                                   } else {
                                       /* Use a safe emitter that checks invariants before calling */
                                       if (epilogue_emitted) {
                                           fprintf(stderr, "SAFE_EMIT_SKIP: buffered epilogue skipped because epilogue_emitted=1\n");
                                       } else if (!prologue_was_emitted) {
                                           fprintf(stderr, "SAFE_EMIT_SKIP: buffered epilogue skipped because no matching prologue (prologue_was_emitted=0)\n");
                                           /* print helpful backtrace to aid debugging why prologue wasn't emitted */
                                           print_backtrace_info();
                                       } else {
                                           emit_epilogue(out, cfg);
                                           /* Reset the sentinel */
                                           output_emitted_since_prologue = 0;
                                       }
                                   }
                               }
                           } else {
                               fprintf(stderr, "SKIP_BUFFERED_EPILOGUE_NO_PROLOGUE: skipping buffered epilogue because no prologue was emitted\n");
                           }
                       } else {
                           fprintf(stderr, "SKIP_EPILOGUE_EMPTY: in_function=%d current=%p next=%p (no body emitted)\n", (int)in_function, (void*)current, (void*)current->next);
                       }
                   }
                   #ifdef __APPLE__
                       fprintf(out, "_%s:\n", current->arg1);
                   #else
                       fprintf(out, "%s:\n", current->arg1);
                   #endif
                   /* Defer emitting the actual prologue until we see the first real body
                      instruction so we don't prematurely print a prologue followed by an
                      immediate epilogue in pathological traversal cases. */
                   prologue_pending = true;
                   prologue_emitted_local = false;
fprintf(stderr, "POST_LABEL: current=%p next=%p &current=%p\n", (void*)current, (void*)current->next, (void*)&current);
           {
               /* Avoid unsafe reads from adjacent stack memory (ASAN caught this).
                  Print pointer addresses instead of interpreting stack words beyond
                  the 'current' object's storage. */
               fprintf(stderr, "STACK_ADDRS: &current=%p &node=%p loc1=%p loc2=%p result_loc=%p\n", (void*)&current, (void*)&node, (void*)loc1, (void*)loc2, (void*)result_loc);
           }
                   current_function_has_body = false;
                   in_function = true;
               } else {
                   fprintf(out, "%s:\n", current->arg1);
               }
               break;
           }


           case IR_RETURN:
               fprintf(out, "movq %s, %%rax\n", loc1);
               break;


           case IR_JMP:
               fprintf(out, "jmp %s\n", current->arg1);
               break;


           case IR_JEQ: {
               int loc2_is_zero = (strcmp(loc2, "$0") == 0);
               if (loc2_is_zero && loc1[0] != '$') {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else if (loc1[0] == '$' && loc2[0] == '$') {
                   fprintf(out, "movq %s, %%r11\n", loc1);
                   fprintf(out, "cmpq %s, %%r11\n", loc2);
               } else if (loc1[0] == '$') {
                   fprintf(out, "cmpq %s, %s\n", loc1, loc2);
               } else if (loc2[0] == '$' || loc2[0] == '%') {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "cmpq %%r11, %s\n", loc1);
               }
               fprintf(out, "je %s\n", current->result);
               break; }


           case IR_JNE: {
               int loc1_is_imm = (loc1[0] == '$');
               int loc2_is_reg_or_imm = (loc2[0] == '$' || loc2[0] == '%');
               if (loc1_is_imm) {
                   fprintf(out, "movq %s, %%r11\n", loc1);
                   fprintf(out, "cmpq %s, %%r11\n", loc2);
               } else if (loc2_is_reg_or_imm) {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "cmpq %%r11, %s\n", loc1);
               }
               fprintf(out, "jne %s\n", current->result);
               break; }


           case IR_LT: {
               int loc1_is_imm = (loc1[0] == '$');
               int loc2_is_reg_or_imm = (loc2[0] == '$' || loc2[0] == '%');
               if (loc1_is_imm) {
                   fprintf(out, "movq %s, %%r11\n", loc1);
                   fprintf(out, "cmpq %s, %%r11\n", loc2);
               } else if (loc2_is_reg_or_imm) {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "cmpq %%r11, %s\n", loc1);
               }
               fprintf(out, "jl %s\n", current->result);
               break; }


           case IR_GT: {
               int loc1_is_imm = (loc1[0] == '$');
               int loc2_is_reg_or_imm = (loc2[0] == '$' || loc2[0] == '%');
               if (loc1_is_imm) {
                   fprintf(out, "movq %s, %%r11\n", loc1);
                   fprintf(out, "cmpq %s, %%r11\n", loc2);
               } else if (loc2_is_reg_or_imm) {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "cmpq %%r11, %s\n", loc1);
               }
               fprintf(out, "jg %s\n", current->result);
               break; }


           case IR_LTE: {
               int loc1_is_imm = (loc1[0] == '$');
               int loc2_is_reg_or_imm = (loc2[0] == '$' || loc2[0] == '%');
               if (loc1_is_imm) {
                   fprintf(out, "movq %s, %%r11\n", loc1);
                   fprintf(out, "cmpq %s, %%r11\n", loc2);
               } else if (loc2_is_reg_or_imm) {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "cmpq %%r11, %s\n", loc1);
               }
               fprintf(out, "jle %s\n", current->result);
               break; }


           case IR_GTE: {
               int loc1_is_imm = (loc1[0] == '$');
               int loc2_is_reg_or_imm = (loc2[0] == '$' || loc2[0] == '%');
               if (loc1_is_imm) {
                   fprintf(out, "movq %s, %%r11\n", loc1);
                   fprintf(out, "cmpq %s, %%r11\n", loc2);
               } else if (loc2_is_reg_or_imm) {
                   fprintf(out, "cmpq %s, %s\n", loc2, loc1);
               } else {
                   fprintf(out, "movq %s, %%r11\n", loc2);
                   fprintf(out, "cmpq %%r11, %s\n", loc1);
               }
               fprintf(out, "jge %s\n", current->result);
               break; }


           case IR_PARAM: {
               reset_args = 0;
               if (arg_count < 8) {
                   // DEBUG: show mapping
                   fprintf(stderr, "DEBUG: IR_PARAM arg=%s loc=%s\n", current->arg1 ? current->arg1 : "(null)", loc1);
                   strcpy(arg_locs[arg_count], loc1);
                   arg_is_lea[arg_count] = (current->arg1 && strncmp(current->arg1, ".STR", 4) == 0);
                   arg_count++;
               }
               break;
           }


           case IR_CALL: {
               reset_args = 0;
               int pass = arg_count;
               if (pass > 6) pass = 6;
               // DEBUG: show call and arg_count
               fprintf(stderr, "DEBUG: IR_CALL target=%s arg_count=%d\n", current->arg1 ? current->arg1 : loc1, arg_count);
               for (int i = 0; i < pass; i++) {
                   if (arg_is_lea[i]) {
                       fprintf(out, "leaq %s, %%%s\n", arg_locs[i], arg_regs[i]);
                   fprintf(stderr, "DEBUG_ASM: leaq %s -> %%%s\n", arg_locs[i], arg_regs[i]);
               } else {
                   fprintf(out, "movq %s, %%%s\n", arg_locs[i], arg_regs[i]);
                   fprintf(stderr, "DEBUG_ASM: movq %s -> %%%s\n", arg_locs[i], arg_regs[i]);
               }
           }
           arg_count = 0;
           const char* target = current->arg1 ? current->arg1 : loc1;
           #ifdef __APPLE__
               fprintf(out, "call _%s\n", target);
           #else
               fprintf(out, "call %s\n", target);
           #endif
           fprintf(out, "movq %%rax, %s\n", result_loc);
           fprintf(stderr, "DEBUG_ASM: movq %%rax -> %s\n", result_loc);
           break;
       }


       if (reset_args) arg_count = 0;
       fprintf(stderr, "POST_SWITCH: current=%p idx=%d op=%d\n", (void*)current, current->index, current->op);

       /* Mark that we've emitted something for the current function body (non-label ops) */
       if (current->op != IR_LABEL) {
           current_function_has_body = true;
           if (prologue_emitted_local) prologue_has_body = 1;
           /* Most non-label ops produce assembly; IR_PARAM is an exception, so
              avoid marking output emitted for pure parameter nodes. */
           if (current->op != IR_PARAM) output_emitted_since_prologue = 1;
       }

       fprintf(stderr, "BEFORE_ADVANCE: current=%p next=%p\n", (void*)current, (void*)current->next);
       node = node->next;
       fprintf(stderr, "AFTER_ADVANCE: node=%p\n", (void*)node);
       fprintf(stderr, "ADVANCE: next=%p\n", (void*)node);
   }


    /* If we've seen a label but never emitted its prologue (no body), clear the pending
       prologue state and skip emitting an epilogue (empty function). */
    if (prologue_pending) {
        fprintf(stderr, "SKIP_PENDING_PROLOGUE: no body was emitted for the pending label, clearing state\n");
        prologue_pending = false;
        current_function_has_body = false;
        in_function = false;
    }

    /* If we emitted a prologue earlier but no epilogue was emitted due to
       traversal quirks, force an epilogue now so the generated function has a
       proper return sequence. Only do this when we've actually emitted body
       code for the current function to avoid closing an empty/unfinished
       function prematurely. */
    if (prologue_emitted_local && !epilogue_emitted && current_function_has_body) {
        fprintf(stderr, "FORCE_EMIT_EPILOGUE_AT_END: prologue_emitted_local=%d epilogue_emitted=%d need_epilogue=%d last_frame_adjust=%d\n", (int)prologue_emitted_local, (int)epilogue_emitted, (int)need_epilogue, need_epilogue_last_frame_adjust);
        if (need_epilogue) {
            last_frame_adjust = need_epilogue_last_frame_adjust;
            need_epilogue = false;
            need_epilogue_last_frame_adjust = 0;
        }
        /* Only force the epilogue if we actually emitted assembly text for the
           function body since its prologue; otherwise skip to avoid placing the
           epilogue before the body. */
        if (!output_emitted_since_prologue) {
            fprintf(stderr, "SKIP_FORCE_EMIT_EPILOGUE_NO_OUTPUT: skipping forced emit because no body assembly emitted since prologue\n");
            /* Re-buffer if necessary */
            if (last_frame_adjust > 0) {
                need_epilogue = true;
                need_epilogue_last_frame_adjust = last_frame_adjust;
                last_frame_adjust = 0;
            }
        } else {
            emit_epilogue(out, cfg);
            output_emitted_since_prologue = 0;
        }
    } else if (prologue_emitted_local && !epilogue_emitted) {
        fprintf(stderr, "SKIP_FORCE_EPILOGUE: prologue emitted but no body seen; deferring epilogue\n");
    }

    fprintf(stderr, "FINAL_STATE: in_function=%d current_function_has_body=%d\n", (int)in_function, (int)current_function_has_body);
   if (in_function) {
       if (current_function_has_body) {
           fprintf(stderr, "CALL_SITE(END): in_function=%d\n", (int)in_function);
           /* If we ended up with no prologue emitted for this function (due to
              traversal oddities), emit it now so the epilogue will match. */
           if (!prologue_emitted_local) {
               fprintf(stderr, "MISSING_PROLOGUE_AT_END: emitting missing prologue\n");
               emit_prologue(out, cfg, stack_bytes);
               prologue_emitted_local = true;
           }
           /* If we previously buffered an epilogue, emit it now with the buffered
              frame adjust; otherwise emit the epilogue normally. */
           if (need_epilogue) {
               fprintf(stderr, "EMIT_BUFFERED_EPILOGUE: using buffered frame adjust=%d\n", need_epilogue_last_frame_adjust);
               last_frame_adjust = need_epilogue_last_frame_adjust;
               need_epilogue = false;
               need_epilogue_last_frame_adjust = 0;
               /* Only emit buffered epilogue if we've actually emitted body assembly */
               if (!output_emitted_since_prologue) {
                   fprintf(stderr, "SKIP_EMIT_BUFFERED_EPILOGUE_NO_OUTPUT: skipping buffered epilogue because no body assembly emitted since prologue\n");
                   /* Re-buffer */
                   need_epilogue = true;
                   need_epilogue_last_frame_adjust = last_frame_adjust;
                   last_frame_adjust = 0;
               } else if (epilogue_emitted) {
                   fprintf(stderr, "SAFE_EMIT_SKIP: buffered epilogue skipped because epilogue_emitted=1\n");
               } else if (!prologue_was_emitted) {
                   fprintf(stderr, "SAFE_EMIT_SKIP: buffered epilogue skipped because no matching prologue (prologue_was_emitted=0)\n");
                   print_backtrace_info();
               } else {
                   emit_epilogue(out, cfg);
                   output_emitted_since_prologue = 0;
               }
           } else {
               if (epilogue_emitted) {
                   fprintf(stderr, "SAFE_EMIT_SKIP: epilogue skipped because epilogue_emitted=1\n");
               } else if (!prologue_was_emitted) {
                   fprintf(stderr, "SAFE_EMIT_SKIP: epilogue skipped because no matching prologue (prologue_was_emitted=0)\n");
                   print_backtrace_info();
               } else {
                   if (!output_emitted_since_prologue) {
                       fprintf(stderr, "SKIP_EMIT_EPILOGUE_NO_OUTPUT: skipping emit because no body assembly emitted since prologue\n");
                       /* re-buffer nothing since this path is non-buffered, rely on final logic */
                   } else {
                       emit_epilogue(out, cfg);
                       output_emitted_since_prologue = 0;
                   }
               }
           }
       } else {
           fprintf(stderr, "SKIP_EPILOGUE_AT_END: in_function=%d (no body emitted)\n", (int)in_function);
       }
   }
   /* If we never were in a function context but we did emit body code, it's
      likely traversal emitted body instructions without the surrounding label
      or function context; as a fallback, synthesize a prologue and epilogue so
      the emitted code is a valid function. */
   if (!in_function && current_function_has_body) {
       fprintf(stderr, "MISSING_FUNCTION_CONTEXT: body emitted outside function context; deferring prologue emission until first body instruction\n");
       /* If we previously emitted an epilogue (for some other function or by mistake)
          ensure it won't prevent us from synthesizing a matching epilogue here. */
       epilogue_emitted = 0;
       /* Defer emitting the synthesized prologue until the first body instruction is
          encountered so the prologue is placed immediately before the body and we
          do not prematurely emit an epilogue. */
       prologue_pending = true; /* will cause emit_prologue() to run when a body instruction appears */
       prologue_emitted_local = false;
       /* Mark that we're now inside a synthesized function so subsequent nodes
          are treated as part of the same function instead of repeatedly
          synthesizing prologue/epilogue pairs. */
       in_function = true;

       if (need_epilogue) {
           last_frame_adjust = need_epilogue_last_frame_adjust;
           need_epilogue = false;
           need_epilogue_last_frame_adjust = 0;
       }
       /* Buffer an epilogue rather than emitting immediately so we wrap the
          entire contiguous body in a single synthesized function prologue/epilogue. */
       if (!need_epilogue) {
           need_epilogue = true;
           need_epilogue_last_frame_adjust = last_frame_adjust;
       }
       fprintf(stderr, "MISSING_FUNCTION_CONTEXT: buffered epilogue for synthesized function (last_frame_adjust=%d)\n", last_frame_adjust);
   }

   /* Safety: Ensure we emit an epilogue as a last-resort, but only when we
      have actually emitted function body code and we have a matching prologue
      — otherwise we may close an empty or unlabeled function prematurely. */
   if (!epilogue_emitted && current_function_has_body && (prologue_was_emitted || prologue_emitted_local)) {
       fprintf(stderr, "FINAL_FORCE_EMIT_EPILOGUE: epilogue_emitted=%d last_frame_adjust=%d prologue_was_emitted=%d prologue_emitted_local=%d\n", (int)epilogue_emitted, last_frame_adjust, (int)prologue_was_emitted, (int)prologue_emitted_local);
       /* Ensure the global prologue flag reflects that a prologue was (or is
          being) emitted so emit_epilogue's safety check won't skip it. */
       if (!prologue_was_emitted) {
           fprintf(stderr, "FINAL_FORCE_EMIT_EPILOGUE: prologue_was_emitted was false; forcing to true to allow epilogue\n");
           prologue_was_emitted = 1;
       }
       /* Fix-up for mismatched transient state: if we have seen body instructions
          (current_function_has_body) but our 'prologue_has_body' flag is not set
          for some reason, be conservative: do NOT force 'prologue_has_body' here.
          Forcing it may cause premature epilogue emission in fragmented traversals;
          instead rely on emit_epilogue's safety checks to avoid emitting an epilogue
          without a real body. */
       if (!prologue_has_body && current_function_has_body) {
           fprintf(stderr, "FINAL_FORCE_EMIT_EPILOGUE: prologue_has_body was false but body seen; skipping forced emit to avoid premature epilogue\n");
           /* intentional no-op: do not set prologue_has_body here */
       }
       if (epilogue_emitted) {
           fprintf(stderr, "SAFE_EMIT_SKIP: final-force epilogue skipped because epilogue_emitted=1\n");
       } else {
           if (!output_emitted_since_prologue) {
               fprintf(stderr, "SKIP_FORCE_EMIT_EPILOGUE_NO_OUTPUT: prologue emitted but no body assembly output since prologue; skipping forced emit\n");
           } else {
               emit_epilogue(out, cfg);
           }
       }
   } else if (!epilogue_emitted && current_function_has_body) {
       fprintf(stderr, "FINAL_SKIP_EMIT_NO_PROLOGUE: no epilogue emitted and body seen but no prologue was emitted; skipping\n");
   } else if (!epilogue_emitted) {
       fprintf(stderr, "FINAL_SKIP_EPILOGUE: no epilogue emitted but no body seen; skipping final emit\n");
   }
}
}


void emit_prologue(FILE* out, const TargetConfig* cfg, int stack_bytes) {
   if (out == NULL) return;
   if (stack_bytes < 0) stack_bytes = 0;

   fprintf(stderr, "EMIT_PROLOGUE: stack_bytes=%d\n", stack_bytes);
   print_backtrace_info();

   last_frame_adjust = stack_bytes;
   epilogue_emitted = 0; /* reset epilogue flag at function entry */
   prologue_was_emitted = 1;
   prologue_has_body = 0; /* no body seen yet for this newly emitted prologue */
   /* No assembly for the body has been emitted yet */
   output_emitted_since_prologue = 0;

   // TODO: Full ARM64 code generation requires rewriting all instruction generation
   fprintf(out, "\tpushq %%rbp\n");
   fprintf(out, "\tmovq %%rsp, %%rbp\n");
   if (stack_bytes > 0) {
       fprintf(out, "\tsubq $%d, %%rsp\n", stack_bytes);
   }
}


void emit_epilogue(FILE* out, const TargetConfig* cfg) {
   if (out == NULL) return;
   /* If we've already emitted an epilogue, quietly return (avoid noisy backtraces)
      — caller sites should log context when they decide to skip emitting. */
   if (epilogue_emitted) {
       fprintf(stderr, "EMIT_EPILOGUE: already emitted; skipping (epilogue_emitted=1)\n");
       return;
   }
   /* Safety: don't emit an epilogue if no matching prologue was ever emitted */
   if (!prologue_was_emitted) {
       fprintf(stderr, "EMIT_EPILOGUE_SKIPPED: no matching prologue was emitted; skipping epilogue and printing backtrace for diagnosis\n");
       print_backtrace_info();
       return;
   }

   /* Safety: don't emit an epilogue for a prologue that has never seen body code */
   if (!prologue_has_body) {
       fprintf(stderr, "EMIT_EPILOGUE_SKIPPED: prologue emitted but no body instructions seen; refusing to emit epilogue for empty prologue\n");
       print_backtrace_info();
       return;
   }

   /* Defensive: guard against invalid frame adjustments */
   if (last_frame_adjust < 0) {
       fprintf(stderr, "EMIT_EPILOGUE: suspicious last_frame_adjust=%d; forcing to 0\n", last_frame_adjust);
       last_frame_adjust = 0;
   }

   if (last_frame_adjust > 0) {
       fprintf(out, "addq $%d, %%rsp\n", last_frame_adjust);
       /* prevent double-emission of the frame adjust if called again */
       last_frame_adjust = 0;
   }
   /* Diagnostic: record that we're emitting an epilogue and capture a backtrace */
   fprintf(stderr, "EMIT_EPILOGUE_EMITTING: last_frame_adjust=%d\n", last_frame_adjust);
   print_backtrace_info();
   fprintf(out, "popq %%rbp\n");
   fprintf(out, "ret\n");
   epilogue_emitted = 1;
   /* Mark that the function has been closed so future calls won't emit epilogues */
   prologue_was_emitted = 0;
   prologue_has_body = 0;
}


void assign_stack_offsets(LiveInterval* intervals, const TargetConfig* cfg) {
   int current_stack_position = 0;
   LiveInterval* current = intervals;
  
   while (current != NULL) {
       if (current->registry == -1) {
           current_stack_position -= cfg->spill_slot_size;
           current->stack_offset = current_stack_position;
       }


       current = current->next;
   }
}


int compute_spill_frame_size(LiveInterval* intervals, const TargetConfig* cfg) {
   int total_size = 0;
   LiveInterval* current = intervals;


   while (current != NULL) {
       if (current->registry == -1) total_size += cfg->spill_slot_size;
       current = current->next;
   }


   return total_size;
}


void print_target_config(const TargetConfig* cfg, FILE* out) {
   if (out == NULL || cfg == NULL) return;


   fprintf(out, "Target Configuration:\n");
   fprintf(out, "  Available Registers: %d\n", cfg->available_registers);
   fprintf(out, "  Spill Slot Size: %d bytes\n", cfg->spill_slot_size);   
   fprintf(out, "  Register Names:\n");


   if (cfg->register_names == NULL) return;
   for (int i = 0; i < cfg->available_registers; i++) {
       if (cfg->register_names[i] != NULL) {
           fprintf(out, "  [%d] %s\n", i, cfg->register_names[i]);
       }
   }


   fprintf(out, "  Caller-Saved Registers: %d\n", cfg->caller_saved_count);
   if (cfg->caller_saved_indices != NULL && cfg->caller_saved_count > 0) {
       fprintf(out, "  Indices: ");
       for (int i = 0; i < cfg->caller_saved_count; i++) {
           fprintf(out, "%d", cfg->caller_saved_indices[i]);
           if (i < cfg->caller_saved_count - 1) fprintf(out, ", ");
       }


       fprintf(out, "\n");
   }
}