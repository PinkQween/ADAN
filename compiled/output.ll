; ModuleID = 'adan_module'
source_filename = "adan_module"

@str = global [12 x i8] c"hoy as vaj!\00"
@fmt_str = global [5 x i8] c"%s\0A\00\00"

define double @main() {
entry:
  %sample = alloca ptr, align 8
  store ptr @str, ptr %sample, align 8
  %loadtmp = load ptr, ptr %sample, align 8
  %call_printf = call i32 (ptr, ...) @printf(ptr @fmt_str, ptr %loadtmp)
  ret double 0.000000e+00
}

declare i32 @printf(ptr, ...)
