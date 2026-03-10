mod compiler;
pub mod mcp;
pub mod package;

pub use compiler::{
    CheckResult, CompilationContext, CompileResult, ModuleBinding, ModuleProcessResult, RunResult,
    TestCaseResult, TestRunOptions, TestRunResult, check_file, compile_file, compile_module,
    compile_project, emit_diagnostics, emit_object, execute_jit, process_module_in_env, run_file,
    run_test_file,
};
pub use mcp::{KeaMcpServer, serve_mcp_stdio};
pub use package::{
    DepSpec, PackageCommand, PackageManifest, ResolvedPackageGraph, dependency_namespaces,
    execute_pkg_command, find_manifest, resolve_graph_for_entry, resolve_graph_from_manifest_path,
};
