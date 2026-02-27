mod compiler;

pub use compiler::{
    CompilationContext, CompileResult, RunResult, compile_file, compile_module, compile_project,
    emit_diagnostics, emit_object, execute_jit, run_file,
};
