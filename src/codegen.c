#include "codegen.h"
#include <stdlib.h>
#include "liveness.h"
#include "ir.h"
#include "string.h"

#ifdef __aarch64__
	#define ARCH_ARM64 1
#elif defined(__x86_64__) || defined(_M_X64)
	#define ARCH_X86_64 1
#else
	#define ARCH_X86_64 1  // Default to x86_64
#endif

static int last_frame_adjust = 0;
static int epilogue_emitted = 0;

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
	IRInstruction* current = ir_head;
	
	char arg_locs[8][64];
	int arg_is_lea[8];
	int arg_count = 0;
	
	// TODO: Full ARM64 code generation requires rewriting all instruction generation
	const char* arg_regs[] = {"rdi", "rsi", "rdx", "rcx", "r8", "r9"};
	
	char loc1[64];
	char loc2[64];
	char result_loc[64];

	bool in_function = false;

	void* _seen_nodes[8192];
int _seen_count = 0;
while (current != NULL) {
		/* detect cycles defensively: if we've seen this node before, abort the walk */
		int _already = 0;
		for (int _i = 0; _i < _seen_count; _i++) {
			if (_seen_nodes[_i] == (void*)current) { _already = 1; break; }
		}
		if (_already) {
			fprintf(stderr, "ERROR: generate_asm detected IR list cycle at node %p; aborting assembly walk\n", (void*)current);
			break;
		}
		if (_seen_count < (int)(sizeof(_seen_nodes)/sizeof(_seen_nodes[0]))) _seen_nodes[_seen_count++] = (void*)current;

		/* TRACE: show current node for debugging traversal order */
		fprintf(stderr, "TRACE: generate_asm visiting addr=%p idx=%d op=%d\n", (void*)current, current->index, current->op);

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
				if (!is_block_label) {
					if (in_function) emit_epilogue(out, cfg);
					#ifdef __APPLE__
						fprintf(out, "_%s:\n", current->arg1);
					#else
						fprintf(out, "%s:\n", current->arg1);
					#endif
					emit_prologue(out, cfg, stack_bytes);
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

		current = current->next;
		fprintf(stderr, "ADVANCE: next=%p\n", (void*)current);
	}

	if (in_function) emit_epilogue(out, cfg);
}
}

void emit_prologue(FILE* out, const TargetConfig* cfg, int stack_bytes) {
	if (out == NULL) return;
	if (stack_bytes < 0) stack_bytes = 0;

	last_frame_adjust = stack_bytes;
	epilogue_emitted = 0; /* reset epilogue flag at function entry */

	// TODO: Full ARM64 code generation requires rewriting all instruction generation
	fprintf(out, "\tpushq %%rbp\n");
	fprintf(out, "\tmovq %%rsp, %%rbp\n");
	if (stack_bytes > 0) {
		fprintf(out, "\tsubq $%d, %%rsp\n", stack_bytes);
	}
}

void emit_epilogue(FILE* out, const TargetConfig* cfg) {
	if (out == NULL) return;
	if (epilogue_emitted) return; /* avoid emitting the same epilogue more than once */
	// TODO: Full ARM64 code generation requires rewriting all instruction generation
	if (last_frame_adjust > 0) {
		fprintf(out, "addq $%d, %%rsp\n", last_frame_adjust);
		/* prevent double-emission of the frame adjust if called again */
		last_frame_adjust = 0;
	}
	fprintf(out, "popq %%rbp\n");
	fprintf(out, "ret\n");
	epilogue_emitted = 1;
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
			fprintf(out, "	[%d] %s\n", i, cfg->register_names[i]);
		}
	}

	fprintf(out, "  Caller-Saved Registers: %d\n", cfg->caller_saved_count);
	if (cfg->caller_saved_indices != NULL && cfg->caller_saved_count > 0) {
		fprintf(out, "	Indices: ");
		for (int i = 0; i < cfg->caller_saved_count; i++) {
			fprintf(out, "%d", cfg->caller_saved_indices[i]);
			if (i < cfg->caller_saved_count - 1) fprintf(out, ", ");
		}

		fprintf(out, "\n");
	}
}
