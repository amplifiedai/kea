mod compiler;

pub use compiler::{
    CompilationContext, CompileResult, ModuleBinding, ModuleProcessResult, RunResult, compile_file,
    compile_module, compile_project, emit_diagnostics, emit_object, execute_jit,
    process_module_in_env, run_file,
};
