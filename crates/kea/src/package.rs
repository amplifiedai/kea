use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command as ProcessCommand;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MANIFEST_FILE_NAME: &str = "kea.toml";
const LOCK_FILE_NAME: &str = "kea.lock";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageManifest {
    pub manifest_path: PathBuf,
    pub package: PackageInfo,
    pub dependencies: BTreeMap<String, DepSpec>,
    pub dev_dependencies: BTreeMap<String, DepSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageInfo {
    pub name: String,
    pub version: String,
    pub kea: Option<String>,
    pub entry: Option<PathBuf>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DepSpec {
    Git {
        url: String,
        tag: Option<String>,
        rev: Option<String>,
        branch: Option<String>,
    },
    Path {
        path: PathBuf,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Lockfile {
    pub packages: Vec<LockedPackage>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LockedPackage {
    pub name: String,
    pub source: String,
    pub rev: String,
    pub hash: String,
}

#[derive(Debug, Clone)]
pub struct ResolvedPackageGraph {
    pub manifest: PackageManifest,
    pub package_roots: BTreeMap<String, PackageRoot>,
    pub lockfile: Lockfile,
}

#[derive(Debug, Clone)]
pub struct PackageRoot {
    pub package_name: String,
    pub namespace: String,
    pub src_root: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveMode {
    Build,
    BuildForTests,
    Update {
        only_dependency: Option<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackageCommand {
    Init,
    Add {
        name: String,
        spec: DepSpec,
    },
    Update {
        dependency: Option<String>,
    },
}

#[derive(Debug, Deserialize)]
struct ManifestToml {
    package: ManifestPackageToml,
    #[serde(default)]
    dependencies: BTreeMap<String, ManifestDependencyToml>,
    #[serde(default, rename = "dev-dependencies")]
    dev_dependencies: BTreeMap<String, ManifestDependencyToml>,
}

#[derive(Debug, Deserialize)]
struct ManifestPackageToml {
    name: String,
    version: String,
    kea: Option<String>,
    entry: Option<String>,
}

#[derive(Debug, Serialize)]
struct ManifestTomlOut {
    package: ManifestPackageTomlOut,
    #[serde(skip_serializing_if = "BTreeMap::is_empty")]
    dependencies: BTreeMap<String, ManifestDependencyTomlOut>,
    #[serde(
        skip_serializing_if = "BTreeMap::is_empty",
        rename = "dev-dependencies"
    )]
    dev_dependencies: BTreeMap<String, ManifestDependencyTomlOut>,
}

#[derive(Debug, Serialize)]
struct ManifestPackageTomlOut {
    name: String,
    version: String,
    kea: Option<String>,
    entry: Option<String>,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum ManifestDependencyToml {
    Git {
        git: String,
        tag: Option<String>,
        rev: Option<String>,
        branch: Option<String>,
    },
    Path {
        path: String,
    },
}

#[derive(Debug, Serialize)]
#[serde(untagged)]
enum ManifestDependencyTomlOut {
    Git {
        git: String,
        #[serde(skip_serializing_if = "Option::is_none")]
        tag: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        rev: Option<String>,
        #[serde(skip_serializing_if = "Option::is_none")]
        branch: Option<String>,
    },
    Path {
        path: String,
    },
}

#[derive(Debug, Default, Deserialize, Serialize)]
struct LockfileToml {
    #[serde(default, rename = "package")]
    package_entries: Vec<LockedPackage>,
}

#[derive(Debug, Clone)]
struct ResolvedDependency {
    name: String,
    source_kind: ResolvedSourceKind,
    manifest_path: PathBuf,
    src_root: PathBuf,
}

#[derive(Debug, Clone)]
enum ResolvedSourceKind {
    Git(LockedPackage),
    Path(PathBuf),
}

#[derive(Debug, Clone)]
enum ResolutionMode {
    Build,
    Update { only_dependency: Option<String> },
}

#[derive(Debug)]
struct ResolutionState {
    lock_input_by_name: BTreeMap<String, LockedPackage>,
    resolved_by_name: BTreeMap<String, ResolvedDependency>,
    lock_output_by_name: BTreeMap<String, LockedPackage>,
    visiting: Vec<String>,
    mode: ResolutionMode,
    cache_root: PathBuf,
}

impl PackageManifest {
    pub fn load(path: &Path) -> Result<Self, String> {
        let manifest_path = fs::canonicalize(path)
            .map_err(|err| format!("failed to resolve `{}`: {err}", path.display()))?;
        let raw = fs::read_to_string(&manifest_path)
            .map_err(|err| format!("failed to read `{}`: {err}", manifest_path.display()))?;
        let parsed: ManifestToml = toml::from_str(&raw)
            .map_err(|err| format!("failed to parse `{}`: {err}", manifest_path.display()))?;

        validate_package_name(&parsed.package.name, "package.name")?;
        let dependencies = parse_manifest_dependencies(parsed.dependencies, "dependency name")?;
        let dev_dependencies =
            parse_manifest_dependencies(parsed.dev_dependencies, "dev-dependency name")?;

        Ok(Self {
            manifest_path,
            package: PackageInfo {
                name: parsed.package.name,
                version: parsed.package.version,
                kea: parsed.package.kea,
                entry: parsed.package.entry.map(PathBuf::from),
            },
            dependencies,
            dev_dependencies,
        })
    }

    pub fn save(&self) -> Result<(), String> {
        let package = ManifestPackageTomlOut {
            name: self.package.name.clone(),
            version: self.package.version.clone(),
            kea: self.package.kea.clone(),
            entry: self
                .package
                .entry
                .as_ref()
                .map(|path| path.to_string_lossy().to_string()),
        };
        let dependencies = self
            .dependencies
            .iter()
            .map(|(name, dep)| {
                let out = match dep {
                    DepSpec::Git {
                        url,
                        tag,
                        rev,
                        branch,
                    } => ManifestDependencyTomlOut::Git {
                        git: url.clone(),
                        tag: tag.clone(),
                        rev: rev.clone(),
                        branch: branch.clone(),
                    },
                    DepSpec::Path { path } => ManifestDependencyTomlOut::Path {
                        path: path.to_string_lossy().to_string(),
                    },
                };
                (name.clone(), out)
            })
            .collect();
        let dev_dependencies = self
            .dev_dependencies
            .iter()
            .map(|(name, dep)| {
                let out = match dep {
                    DepSpec::Git {
                        url,
                        tag,
                        rev,
                        branch,
                    } => ManifestDependencyTomlOut::Git {
                        git: url.clone(),
                        tag: tag.clone(),
                        rev: rev.clone(),
                        branch: branch.clone(),
                    },
                    DepSpec::Path { path } => ManifestDependencyTomlOut::Path {
                        path: path.to_string_lossy().to_string(),
                    },
                };
                (name.clone(), out)
            })
            .collect();
        let rendered = toml::to_string_pretty(&ManifestTomlOut {
            package,
            dependencies,
            dev_dependencies,
        })
        .map_err(|err| format!("failed to serialize manifest: {err}"))?;
        fs::write(&self.manifest_path, rendered).map_err(|err| {
            format!(
                "failed to write manifest `{}`: {err}",
                self.manifest_path.display()
            )
        })
    }

    pub fn package_dir(&self) -> PathBuf {
        self.manifest_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf()
    }

    pub fn entry_path(&self) -> PathBuf {
        self.package_dir()
            .join(self.package.entry.clone().unwrap_or_else(|| PathBuf::from("src/main.kea")))
    }
}

fn parse_manifest_dependencies(
    deps: BTreeMap<String, ManifestDependencyToml>,
    dep_kind: &str,
) -> Result<BTreeMap<String, DepSpec>, String> {
    deps.into_iter()
        .map(|(dep_name, dep)| {
            validate_package_name(&dep_name, dep_kind)?;
            let spec = match dep {
                ManifestDependencyToml::Git {
                    git,
                    tag,
                    rev,
                    branch,
                } => {
                    let mut selector_count = 0usize;
                    if tag.is_some() {
                        selector_count += 1;
                    }
                    if rev.is_some() {
                        selector_count += 1;
                    }
                    if branch.is_some() {
                        selector_count += 1;
                    }
                    if selector_count > 1 {
                        return Err(format!(
                            "dependency `{dep_name}` can specify at most one of `tag`, `rev`, or `branch`"
                        ));
                    }
                    DepSpec::Git {
                        url: git,
                        tag,
                        rev,
                        branch,
                    }
                }
                ManifestDependencyToml::Path { path } => DepSpec::Path {
                    path: PathBuf::from(path),
                },
            };
            Ok((dep_name, spec))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()
}

impl Lockfile {
    pub fn load(path: &Path) -> Result<Self, String> {
        if !path.is_file() {
            return Ok(Self::default());
        }
        let raw = fs::read_to_string(path)
            .map_err(|err| format!("failed to read lockfile `{}`: {err}", path.display()))?;
        let parsed: LockfileToml = toml::from_str(&raw)
            .map_err(|err| format!("failed to parse lockfile `{}`: {err}", path.display()))?;
        let mut packages = parsed.package_entries;
        packages.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(Self { packages })
    }

    pub fn write(&self, path: &Path) -> Result<(), String> {
        let mut packages = self.packages.clone();
        packages.sort_by(|a, b| a.name.cmp(&b.name));
        let rendered = toml::to_string_pretty(&LockfileToml {
            package_entries: packages,
        })
        .map_err(|err| format!("failed to serialize lockfile: {err}"))?;
        fs::write(path, rendered)
            .map_err(|err| format!("failed to write lockfile `{}`: {err}", path.display()))
    }
}

pub fn find_manifest(start: &Path) -> Option<PathBuf> {
    let mut cursor = if start.is_dir() {
        Some(start.to_path_buf())
    } else {
        start.parent().map(Path::to_path_buf)
    }?;
    loop {
        let candidate = cursor.join(MANIFEST_FILE_NAME);
        if candidate.is_file() {
            return Some(candidate);
        }
        if !cursor.pop() {
            break;
        }
    }
    None
}

pub fn resolve_graph_for_entry(entry: &Path) -> Result<Option<ResolvedPackageGraph>, String> {
    resolve_graph_for_entry_with_mode(entry, ResolveMode::Build)
}

pub fn resolve_graph_for_test_entry(entry: &Path) -> Result<Option<ResolvedPackageGraph>, String> {
    resolve_graph_for_entry_with_mode(entry, ResolveMode::BuildForTests)
}

fn resolve_graph_for_entry_with_mode(
    entry: &Path,
    mode: ResolveMode,
) -> Result<Option<ResolvedPackageGraph>, String> {
    let canonical_entry = fs::canonicalize(entry)
        .map_err(|err| format!("failed to resolve `{}`: {err}", entry.display()))?;
    let Some(manifest_path) = find_manifest(&canonical_entry) else {
        return Ok(None);
    };
    let graph = resolve_graph_from_manifest_path(&manifest_path, mode)?;
    Ok(Some(graph))
}

pub fn resolve_graph_from_manifest_path(
    manifest_path: &Path,
    mode: ResolveMode,
) -> Result<ResolvedPackageGraph, String> {
    resolve_graph_from_manifest_path_with_cache_root(manifest_path, mode, kea_cache_dir())
}

fn resolve_graph_from_manifest_path_with_cache_root(
    manifest_path: &Path,
    mode: ResolveMode,
    cache_root: PathBuf,
) -> Result<ResolvedPackageGraph, String> {
    let manifest = PackageManifest::load(manifest_path)?;
    let lock_path = manifest.package_dir().join(LOCK_FILE_NAME);
    let lock = Lockfile::load(&lock_path)?;

    let (resolution_mode, include_root_dev_dependencies) = match mode {
        ResolveMode::Build => (ResolutionMode::Build, false),
        ResolveMode::BuildForTests => (ResolutionMode::Build, true),
        ResolveMode::Update { only_dependency } => (
            ResolutionMode::Update { only_dependency },
            false,
        ),
    };
    let mut state = ResolutionState {
        lock_input_by_name: lock
            .packages
            .iter()
            .cloned()
            .map(|pkg| (pkg.name.clone(), pkg))
            .collect(),
        resolved_by_name: BTreeMap::new(),
        lock_output_by_name: BTreeMap::new(),
        visiting: vec![manifest.package.name.clone()],
        mode: resolution_mode,
        cache_root,
    };

    resolve_manifest_dependencies(&manifest, &mut state, include_root_dev_dependencies)?;
    let mut lock_packages = state.lock_output_by_name.into_values().collect::<Vec<_>>();
    lock_packages.sort_by(|a, b| a.name.cmp(&b.name));
    let lockfile = Lockfile {
        packages: lock_packages,
    };
    if lockfile != lock {
        lockfile.write(&lock_path)?;
    }

    let package_roots = state
        .resolved_by_name
        .into_values()
        .map(|resolved| {
            let namespace = package_namespace(&resolved.name);
            (
                namespace.clone(),
                PackageRoot {
                    package_name: resolved.name.clone(),
                    namespace,
                    src_root: resolved.src_root,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();

    Ok(ResolvedPackageGraph {
        manifest,
        package_roots,
        lockfile,
    })
}

pub fn execute_pkg_command(command: PackageCommand) -> Result<String, String> {
    let cwd = std::env::current_dir().map_err(|err| format!("failed to read cwd: {err}"))?;
    match command {
        PackageCommand::Init => init_manifest(&cwd),
        PackageCommand::Add { name, spec } => add_dependency(&cwd, &name, spec),
        PackageCommand::Update { dependency } => update_dependencies(&cwd, dependency.as_deref()),
    }
}

fn init_manifest(cwd: &Path) -> Result<String, String> {
    let manifest_path = cwd.join(MANIFEST_FILE_NAME);
    if manifest_path.exists() {
        return Err(format!("manifest already exists at `{}`", manifest_path.display()));
    }
    let package_name = infer_package_name(cwd);
    let manifest = PackageManifest {
        manifest_path: manifest_path.clone(),
        package: PackageInfo {
            name: package_name,
            version: "0.1.0".to_string(),
            kea: Some("0.1".to_string()),
            entry: Some(PathBuf::from("src/main.kea")),
        },
        dependencies: BTreeMap::new(),
        dev_dependencies: BTreeMap::new(),
    };
    manifest.save()?;
    Ok(format!("created `{}`", manifest_path.display()))
}

fn add_dependency(cwd: &Path, name: &str, spec: DepSpec) -> Result<String, String> {
    validate_package_name(name, "dependency name")?;
    let manifest_path = find_manifest(cwd)
        .ok_or_else(|| "no `kea.toml` found in current directory or ancestors".to_string())?;
    let mut manifest = PackageManifest::load(&manifest_path)?;
    manifest.dependencies.insert(name.to_string(), spec);
    manifest.save()?;
    resolve_graph_from_manifest_path(
        &manifest_path,
        ResolveMode::Update {
            only_dependency: Some(name.to_string()),
        },
    )?;
    Ok(format!(
        "added dependency `{name}` and updated `{}`",
        manifest_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join(LOCK_FILE_NAME)
            .display()
    ))
}

fn update_dependencies(cwd: &Path, dependency: Option<&str>) -> Result<String, String> {
    let manifest_path = find_manifest(cwd)
        .ok_or_else(|| "no `kea.toml` found in current directory or ancestors".to_string())?;
    resolve_graph_from_manifest_path(
        &manifest_path,
        ResolveMode::Update {
            only_dependency: dependency.map(ToOwned::to_owned),
        },
    )?;
    Ok(format!(
        "updated `{}`",
        manifest_path
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join(LOCK_FILE_NAME)
            .display()
    ))
}

fn resolve_manifest_dependencies(
    manifest: &PackageManifest,
    state: &mut ResolutionState,
    include_dev_dependencies: bool,
) -> Result<(), String> {
    for (dep_name, spec) in manifest
        .dependencies
        .iter()
        .chain(
            include_dev_dependencies
                .then_some(manifest.dev_dependencies.iter())
                .into_iter()
                .flatten(),
        )
    {
        if state.visiting.iter().any(|seen| seen == dep_name) {
            let mut cycle = state.visiting.clone();
            cycle.push(dep_name.clone());
            return Err(format!("dependency cycle detected: {}", cycle.join(" -> ")));
        }
        let dep = resolve_dependency(dep_name, spec, manifest, state)?;

        if let Some(existing) = state.resolved_by_name.get(dep_name) {
            ensure_compatible(existing, &dep)?;
            continue;
        }

        let dep_manifest = PackageManifest::load(&dep.manifest_path)?;
        if dep_manifest.package.name != *dep_name {
            return Err(format!(
                "dependency key `{dep_name}` must match package.name `{}` in `{}`; dependency aliasing is not supported in Phase 0",
                dep_manifest.package.name,
                dep_manifest.manifest_path.display(),
            ));
        }

        state.visiting.push(dep_name.clone());
        resolve_manifest_dependencies(&dep_manifest, state, false)?;
        state.visiting.pop();

        state.resolved_by_name.insert(dep_name.clone(), dep);
    }
    Ok(())
}

fn resolve_dependency(
    dep_name: &str,
    spec: &DepSpec,
    owner_manifest: &PackageManifest,
    state: &mut ResolutionState,
) -> Result<ResolvedDependency, String> {
    match spec {
        DepSpec::Path { path } => {
            let resolved_path = owner_manifest.package_dir().join(path);
            let canonical = fs::canonicalize(&resolved_path).map_err(|err| {
                format!(
                    "failed to resolve path dependency `{dep_name}` (`{}`): {err}",
                    resolved_path.display()
                )
            })?;
            let src_root = canonical.join("src");
            if !src_root.is_dir() {
                return Err(format!(
                    "path dependency `{dep_name}` at `{}` is missing `src/`",
                    canonical.display()
                ));
            }
            Ok(ResolvedDependency {
                name: dep_name.to_string(),
                source_kind: ResolvedSourceKind::Path(canonical.clone()),
                manifest_path: canonical.join(MANIFEST_FILE_NAME),
                src_root,
            })
        }
        DepSpec::Git {
            url,
            tag,
            rev,
            branch,
        } => {
            let git_spec = DepSpec::Git {
                url: url.clone(),
                tag: tag.clone(),
                rev: rev.clone(),
                branch: branch.clone(),
            };
            let source = git_source_string(&git_spec)?;
            let refresh_this_dep = match &state.mode {
                ResolutionMode::Build => false,
                ResolutionMode::Update { only_dependency } => {
                    only_dependency.as_deref().is_none_or(|target| target == dep_name)
                }
            };
            let lock_entry = state
                .lock_input_by_name
                .get(dep_name)
                .filter(|entry| entry.source == source);
            let locked_rev = if refresh_this_dep {
                None
            } else {
                lock_entry.map(|entry| entry.rev.as_str())
            };
            let locked_hash = if refresh_this_dep {
                None
            } else {
                lock_entry.map(|entry| entry.hash.as_str())
            };
            let resolved = resolve_git_dependency(
                dep_name,
                &git_spec,
                locked_rev,
                locked_hash,
                &state.cache_root,
            )?;
            state
                .lock_output_by_name
                .insert(dep_name.to_string(), resolved.clone());
            let src_root = state
                .cache_root
                .join("git")
                .join(format!("sha256-{}", resolved.hash.trim_start_matches("sha256:")))
                .join("src");
            let manifest_path = src_root
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join(MANIFEST_FILE_NAME);
            if !src_root.is_dir() {
                return Err(format!(
                    "cached dependency `{dep_name}` is missing `src/` at `{}`",
                    src_root.display()
                ));
            }
            Ok(ResolvedDependency {
                name: dep_name.to_string(),
                source_kind: ResolvedSourceKind::Git(resolved),
                manifest_path,
                src_root,
            })
        }
    }
}

fn resolve_git_dependency(
    dep_name: &str,
    spec: &DepSpec,
    locked_rev: Option<&str>,
    locked_hash: Option<&str>,
    cache_root: &Path,
) -> Result<LockedPackage, String> {
    let DepSpec::Git {
        url,
        tag,
        rev,
        branch,
    } = spec
    else {
        return Err("internal error: expected git dependency".to_string());
    };

    let source = git_source_string(spec)?;
    let cache_dir = cache_root.join("git");
    let repo_hash = sha256_hex(url.as_bytes());
    let repos_dir = cache_dir.join("repos");
    let checkouts_dir = cache_dir.join("checkouts");
    fs::create_dir_all(&repos_dir).map_err(|err| {
        format!(
            "failed to create git cache directory `{}`: {err}",
            repos_dir.display()
        )
    })?;
    fs::create_dir_all(&checkouts_dir).map_err(|err| {
        format!(
            "failed to create git checkout cache directory `{}`: {err}",
            checkouts_dir.display()
        )
    })?;

    let repo_dir = repos_dir.join(repo_hash);
    ensure_cached_repo(url, &repo_dir, locked_rev)?;

    let resolved_rev = if let Some(pinned) = locked_rev {
        verify_git_object_exists(&repo_dir, pinned, dep_name)?;
        pinned.to_string()
    } else if let Some(explicit_rev) = rev {
        git_rev_parse(&repo_dir, explicit_rev)?
    } else if let Some(tag_name) = tag {
        git_rev_parse(&repo_dir, &format!("refs/tags/{tag_name}"))?
    } else if let Some(branch_name) = branch {
        git_branch_rev(&repo_dir, branch_name)?
    } else {
        git_default_head_rev(&repo_dir)?
    };

    let checkout_dir = checkouts_dir.join(format!("{}-{}", dep_name, resolved_rev));
    if !checkout_dir.is_dir() {
        if checkout_dir.exists() {
            fs::remove_file(&checkout_dir).map_err(|err| {
                format!(
                    "failed to remove non-directory checkout path `{}`: {err}",
                    checkout_dir.display()
                )
            })?;
        }
        clone_checkout(&repo_dir, &checkout_dir, &resolved_rev)?;
    }

    let computed_hash = hash_package_source_tree(&checkout_dir)?;
    if let Some(expected_hash) = locked_hash
        && expected_hash != computed_hash
    {
        return Err(format!(
            "hash mismatch for dependency `{dep_name}`: lockfile has `{expected_hash}`, fetched source resolved to `{computed_hash}`"
        ));
    }

    let tree_dir = cache_dir.join(format!(
        "sha256-{}",
        computed_hash.trim_start_matches("sha256:")
    ));
    if !tree_dir.is_dir() {
        copy_source_tree(&checkout_dir, &tree_dir)?;
    }

    Ok(LockedPackage {
        name: dep_name.to_string(),
        source,
        rev: resolved_rev,
        hash: computed_hash,
    })
}

fn ensure_cached_repo(url: &str, repo_dir: &Path, locked_rev: Option<&str>) -> Result<(), String> {
    if repo_dir.is_dir() {
        if fetch_repo(repo_dir).is_err() && locked_rev.is_none() {
            return Err(format!(
                "failed to refresh git dependency cache for `{}` and lockfile has no pinned revision",
                url
            ));
        }
        return Ok(());
    }
    if let Some(parent) = repo_dir.parent() {
        fs::create_dir_all(parent).map_err(|err| {
            format!(
                "failed to create git repo cache parent `{}`: {err}",
                parent.display()
            )
        })?;
    }
    run_process(
        ProcessCommand::new("git")
            .arg("clone")
            .arg("--mirror")
            .arg(url)
            .arg(repo_dir),
        "clone git dependency",
    )?;
    Ok(())
}

fn fetch_repo(repo_dir: &Path) -> Result<(), String> {
    run_process(
        ProcessCommand::new("git")
            .arg("-C")
            .arg(repo_dir)
            .arg("fetch")
            .arg("--tags")
            .arg("--prune")
            .arg("origin"),
        "fetch git dependency",
    )
}

fn git_rev_parse(repo_dir: &Path, reference: &str) -> Result<String, String> {
    run_process_capture_stdout(
        ProcessCommand::new("git")
            .arg("-C")
            .arg(repo_dir)
            .arg("rev-parse")
            .arg(format!("{reference}^{{commit}}")),
        &format!("resolve git revision `{reference}`"),
    )
}

fn git_default_head_rev(repo_dir: &Path) -> Result<String, String> {
    if let Ok(rev) = git_rev_parse(repo_dir, "refs/remotes/origin/HEAD") {
        return Ok(rev);
    }
    if let Ok(rev) = git_rev_parse(repo_dir, "HEAD") {
        return Ok(rev);
    }
    let head_ref = run_process_capture_stdout(
        ProcessCommand::new("git")
            .arg("-C")
            .arg(repo_dir)
            .arg("symbolic-ref")
            .arg("refs/remotes/origin/HEAD"),
        "resolve default branch",
    )?;
    git_rev_parse(repo_dir, &head_ref)
}

fn git_branch_rev(repo_dir: &Path, branch_name: &str) -> Result<String, String> {
    if let Ok(rev) = git_rev_parse(repo_dir, &format!("refs/remotes/origin/{branch_name}")) {
        return Ok(rev);
    }
    if let Ok(rev) = git_rev_parse(repo_dir, &format!("refs/heads/{branch_name}")) {
        return Ok(rev);
    }
    git_rev_parse(repo_dir, branch_name)
}

fn verify_git_object_exists(repo_dir: &Path, rev: &str, dep_name: &str) -> Result<(), String> {
    run_process(
        ProcessCommand::new("git")
            .arg("-C")
            .arg(repo_dir)
            .arg("cat-file")
            .arg("-e")
            .arg(format!("{rev}^{{commit}}")),
        &format!("verify locked revision for `{dep_name}`"),
    )
}

fn clone_checkout(repo_dir: &Path, checkout_dir: &Path, rev: &str) -> Result<(), String> {
    if let Some(parent) = checkout_dir.parent() {
        fs::create_dir_all(parent).map_err(|err| {
            format!(
                "failed to create git checkout cache parent `{}`: {err}",
                parent.display()
            )
        })?;
    }
    run_process(
        ProcessCommand::new("git")
            .arg("clone")
            .arg(repo_dir)
            .arg(checkout_dir),
        "create dependency checkout",
    )?;
    run_process(
        ProcessCommand::new("git")
            .arg("-C")
            .arg(checkout_dir)
            .arg("checkout")
            .arg("--detach")
            .arg(rev),
        "checkout dependency revision",
    )
}

fn run_process(cmd: &mut ProcessCommand, context: &str) -> Result<(), String> {
    let output = cmd
        .output()
        .map_err(|err| format!("failed to {context}: {err}"))?;
    if output.status.success() {
        return Ok(());
    }
    Err(format!(
        "{context} failed (status: {}): {}",
        output.status,
        String::from_utf8_lossy(&output.stderr).trim()
    ))
}

fn run_process_capture_stdout(cmd: &mut ProcessCommand, context: &str) -> Result<String, String> {
    let output = cmd
        .output()
        .map_err(|err| format!("failed to {context}: {err}"))?;
    if !output.status.success() {
        return Err(format!(
            "{context} failed (status: {}): {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let value = String::from_utf8(output.stdout)
        .map_err(|err| format!("{context} produced non-utf8 output: {err}"))?;
    Ok(value.trim().to_string())
}

fn copy_source_tree(from: &Path, to: &Path) -> Result<(), String> {
    if !from.is_dir() {
        return Err(format!("cannot copy missing source tree `{}`", from.display()));
    }
    fs::create_dir_all(to)
        .map_err(|err| format!("failed to create cache tree `{}`: {err}", to.display()))?;
    copy_tree_recursive(from, to)
}

fn copy_tree_recursive(from: &Path, to: &Path) -> Result<(), String> {
    let mut entries = fs::read_dir(from)
        .map_err(|err| format!("failed to list `{}`: {err}", from.display()))?
        .filter_map(Result::ok)
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        let name = entry.file_name();
        if ignored_source_path(&name) {
            continue;
        }
        let target = to.join(&name);
        if path.is_dir() {
            fs::create_dir_all(&target)
                .map_err(|err| format!("failed to create `{}`: {err}", target.display()))?;
            copy_tree_recursive(&path, &target)?;
            continue;
        }
        fs::copy(&path, &target).map_err(|err| {
            format!(
                "failed to copy `{}` to `{}`: {err}",
                path.display(),
                target.display()
            )
        })?;
    }
    Ok(())
}

fn hash_package_source_tree(root: &Path) -> Result<String, String> {
    let mut files = Vec::new();
    collect_kea_files(root, root, &mut files)?;
    files.sort();
    let mut hasher = Sha256::new();
    for rel_path in files {
        let full_path = root.join(&rel_path);
        let bytes = fs::read(&full_path)
            .map_err(|err| format!("failed to read `{}`: {err}", full_path.display()))?;
        hasher.update(rel_path.as_os_str().as_encoded_bytes());
        hasher.update([0u8]);
        hasher.update(bytes);
    }
    Ok(format!("sha256:{:x}", hasher.finalize()))
}

fn collect_kea_files(root: &Path, dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries = fs::read_dir(dir)
        .map_err(|err| format!("failed to list `{}`: {err}", dir.display()))?
        .filter_map(Result::ok)
        .collect::<Vec<_>>();
    entries.sort_by_key(|entry| entry.path());
    for entry in entries {
        let path = entry.path();
        let name = entry.file_name();
        if ignored_source_path(&name) {
            continue;
        }
        if path.is_dir() {
            collect_kea_files(root, &path, out)?;
            continue;
        }
        if path.extension().and_then(OsStr::to_str) != Some("kea") {
            continue;
        }
        let rel = path
            .strip_prefix(root)
            .map_err(|err| format!("failed to compute relative path: {err}"))?;
        out.push(rel.to_path_buf());
    }
    Ok(())
}

fn ignored_source_path(name: &OsStr) -> bool {
    matches!(
        name.to_str(),
        Some(".git") | Some("target") | Some("kea.lock")
    )
}

fn ensure_compatible(existing: &ResolvedDependency, candidate: &ResolvedDependency) -> Result<(), String> {
    match (&existing.source_kind, &candidate.source_kind) {
        (ResolvedSourceKind::Git(existing_git), ResolvedSourceKind::Git(candidate_git)) => {
            if existing_git.rev != candidate_git.rev {
                return Err(format!(
                    "dependency `{}` resolves to conflicting revisions (`{}` vs `{}`)",
                    existing.name, existing_git.rev, candidate_git.rev
                ));
            }
        }
        (ResolvedSourceKind::Path(existing_path), ResolvedSourceKind::Path(candidate_path)) => {
            if existing_path != candidate_path {
                return Err(format!(
                    "dependency `{}` resolves to conflicting paths (`{}` vs `{}`)",
                    existing.name,
                    existing_path.display(),
                    candidate_path.display()
                ));
            }
        }
        (ResolvedSourceKind::Git(_), ResolvedSourceKind::Path(_))
        | (ResolvedSourceKind::Path(_), ResolvedSourceKind::Git(_)) => {
            return Err(format!(
                "dependency `{}` resolves to conflicting source kinds (git vs path)",
                existing.name
            ));
        }
    }
    Ok(())
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn package_namespace(name: &str) -> String {
    name.split('-')
        .filter(|segment| !segment.is_empty())
        .map(|segment| {
            let mut chars = segment.chars();
            let mut out = String::new();
            if let Some(first) = chars.next() {
                out.push(first.to_ascii_uppercase());
                out.extend(chars);
            }
            out
        })
        .collect::<String>()
}

fn git_source_string(spec: &DepSpec) -> Result<String, String> {
    let DepSpec::Git {
        url,
        tag,
        rev: _,
        branch,
    } = spec
    else {
        return Err("internal error: expected git dependency".to_string());
    };
    let mut source = format!("git+{url}");
    if let Some(tag_name) = tag {
        source.push_str(&format!("?tag={tag_name}"));
    } else if let Some(branch_name) = branch {
        source.push_str(&format!("?branch={branch_name}"));
    }
    Ok(source)
}

fn validate_package_name(name: &str, field: &str) -> Result<(), String> {
    if name.is_empty() {
        return Err(format!("{field} must not be empty"));
    }
    if !name
        .chars()
        .all(|ch| ch.is_ascii_lowercase() || ch.is_ascii_digit() || ch == '-')
    {
        return Err(format!(
            "{field} `{name}` must contain only lowercase letters, digits, and `-`"
        ));
    }
    if name.starts_with('-') || name.ends_with('-') || name.contains("--") {
        return Err(format!(
            "{field} `{name}` must not start/end with `-` or contain consecutive dashes"
        ));
    }
    Ok(())
}

fn infer_package_name(cwd: &Path) -> String {
    let raw = cwd
        .file_name()
        .and_then(OsStr::to_str)
        .unwrap_or("app")
        .to_ascii_lowercase();
    let mut out = String::new();
    let mut prev_dash = false;
    for ch in raw.chars() {
        let normalized = if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
            prev_dash = false;
            ch
        } else {
            if prev_dash {
                continue;
            }
            prev_dash = true;
            '-'
        };
        out.push(normalized);
    }
    let trimmed = out.trim_matches('-').to_string();
    if trimmed.is_empty() {
        "app".to_string()
    } else {
        trimmed
    }
}

fn kea_cache_dir() -> PathBuf {
    let kea_home = std::env::var("KEA_HOME")
        .ok()
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var("HOME")
                .ok()
                .filter(|value| !value.is_empty())
                .map(|home| PathBuf::from(home).join(".kea"))
        })
        .unwrap_or_else(|| PathBuf::from(".kea"));
    kea_home.join("cache")
}

pub fn dependency_namespaces(graph: &ResolvedPackageGraph) -> BTreeSet<String> {
    graph.package_roots.keys().cloned().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{SystemTime, UNIX_EPOCH};

    static TEST_NONCE: AtomicU64 = AtomicU64::new(0);

    fn temp_dir(prefix: &str) -> PathBuf {
        let nonce = TEST_NONCE.fetch_add(1, Ordering::Relaxed);
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("time should move forward")
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "kea-package-tests-{prefix}-{}-{timestamp}-{nonce}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).expect("test temp dir should be created");
        dir
    }

    fn write_file(path: &Path, contents: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("parent dir should be created");
        }
        fs::write(path, contents).expect("file write should succeed");
    }

    fn run_git(repo: &Path, args: &[&str], context: &str) {
        run_process(
            ProcessCommand::new("git")
                .arg("-C")
                .arg(repo)
                .args(args),
            context,
        )
        .expect("git command should succeed");
    }

    fn git_stdout(repo: &Path, args: &[&str], context: &str) -> String {
        run_process_capture_stdout(
            ProcessCommand::new("git")
                .arg("-C")
                .arg(repo)
                .args(args),
            context,
        )
        .expect("git command should succeed")
    }

    fn init_git_package(repo: &Path, package_name: &str, module_source: &str) -> String {
        fs::create_dir_all(repo).expect("repo dir should be created");
        run_process(
            ProcessCommand::new("git").arg("init").arg(repo),
            "init git repo for package test",
        )
        .expect("git init should succeed");
        run_git(
            repo,
            &["config", "user.email", "kea-tests@example.com"],
            "set git test email",
        );
        run_git(
            repo,
            &["config", "user.name", "Kea Tests"],
            "set git test user name",
        );
        write_file(
            &repo.join(MANIFEST_FILE_NAME),
            &format!(
                "[package]\nname = \"{package_name}\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n"
            ),
        );
        write_file(&repo.join("src").join(format!("{package_name}.kea")), module_source);
        run_git(repo, &["add", "."], "stage initial package files");
        run_git(
            repo,
            &["commit", "-m", "initial package commit"],
            "commit initial package files",
        );
        git_stdout(repo, &["symbolic-ref", "--short", "HEAD"], "resolve branch")
    }

    fn commit_module_source(repo: &Path, package_name: &str, message: &str, source: &str) -> String {
        write_file(&repo.join("src").join(format!("{package_name}.kea")), source);
        run_git(repo, &["add", "."], "stage package update");
        run_git(repo, &["commit", "-m", message], "commit package update");
        git_stdout(repo, &["rev-parse", "HEAD"], "resolve head revision")
    }

    fn lock_rev(lockfile: &Lockfile, name: &str) -> String {
        lockfile
            .packages
            .iter()
            .find(|pkg| pkg.name == name)
            .unwrap_or_else(|| panic!("expected lock entry for `{name}`"))
            .rev
            .clone()
    }

    #[test]
    fn package_namespace_maps_hyphenated_name() {
        assert_eq!(package_namespace("my-utils"), "MyUtils");
        assert_eq!(package_namespace("json"), "Json");
    }

    #[test]
    fn validate_package_name_rejects_invalid_chars() {
        let err = validate_package_name("BadName", "package").expect_err("expected invalid name");
        assert!(err.contains("lowercase"));
    }

    #[test]
    fn resolve_graph_rejects_dependency_aliasing_mismatched_package_name() {
        let root = temp_dir("alias-mismatch");
        let cache_root = root.join(".kea").join("cache");
        let dep_dir = root.join("deps").join("json");
        let app_manifest = root.join(MANIFEST_FILE_NAME);

        write_file(
            &app_manifest,
            "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dependencies]\njson-utils = { path = \"deps/json\" }\n",
        );
        write_file(
            &dep_dir.join(MANIFEST_FILE_NAME),
            "[package]\nname = \"json\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n",
        );
        write_file(&dep_dir.join("src").join("json.kea"), "pub fn parse() -> Int\n  1\n");

        let err = resolve_graph_from_manifest_path_with_cache_root(
            &app_manifest,
            ResolveMode::Build,
            cache_root,
        )
        .expect_err("dependency aliasing should be rejected in phase 0");
        assert!(
            err.contains("dependency key `json-utils` must match package.name `json`"),
            "expected key/name mismatch diagnostic, got: {err}"
        );
        assert!(
            err.contains("aliasing is not supported in Phase 0"),
            "expected aliasing policy diagnostic, got: {err}"
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn branch_dependency_is_pinned_until_explicit_update() {
        let root = temp_dir("branch-pin-update");
        let cache_root = root.join(".kea").join("cache");
        let dep_repo = root.join("repos").join("json");
        let app_manifest = root.join(MANIFEST_FILE_NAME);

        let branch = init_git_package(&dep_repo, "json", "pub fn version() -> Int\n  1\n");
        let dep_url = dep_repo.to_string_lossy();
        write_file(
            &app_manifest,
            &format!(
                "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dependencies]\njson = {{ git = \"{dep_url}\", branch = \"{branch}\" }}\n"
            ),
        );

        let initial = resolve_graph_from_manifest_path_with_cache_root(
            &app_manifest,
            ResolveMode::Build,
            cache_root.clone(),
        )
        .expect("initial build resolution should succeed");
        let initial_rev = lock_rev(&initial.lockfile, "json");
        let head_rev = git_stdout(&dep_repo, &["rev-parse", "HEAD"], "resolve initial head");
        assert_eq!(
            initial_rev, head_rev,
            "first build should pin current branch revision"
        );

        let _updated_head = commit_module_source(
            &dep_repo,
            "json",
            "update json package",
            "pub fn version() -> Int\n  2\n",
        );

        let rebuilt = resolve_graph_from_manifest_path_with_cache_root(
            &app_manifest,
            ResolveMode::Build,
            cache_root.clone(),
        )
        .expect("build with existing lock should stay pinned");
        assert_eq!(
            lock_rev(&rebuilt.lockfile, "json"),
            initial_rev,
            "build mode should remain pinned to the lockfile revision"
        );

        let updated = resolve_graph_from_manifest_path_with_cache_root(
            &app_manifest,
            ResolveMode::Update {
                only_dependency: None,
            },
            cache_root,
        )
        .expect("explicit update should refresh branch dependency");
        let updated_rev = lock_rev(&updated.lockfile, "json");
        let refreshed_head = git_stdout(&dep_repo, &["rev-parse", "HEAD"], "resolve updated head");
        assert_eq!(
            updated_rev, refreshed_head,
            "update mode should advance pinned revision to branch tip"
        );
        assert_ne!(
            updated_rev, initial_rev,
            "update should advance the lockfile pin when branch head changes"
        );

        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn update_only_dependency_refreshes_target_and_keeps_other_pins() {
        let root = temp_dir("targeted-update");
        let cache_root = root.join(".kea").join("cache");
        let json_repo = root.join("repos").join("json");
        let http_repo = root.join("repos").join("http");
        let app_manifest = root.join(MANIFEST_FILE_NAME);

        let json_branch = init_git_package(&json_repo, "json", "pub fn version() -> Int\n  1\n");
        let http_branch = init_git_package(&http_repo, "http", "pub fn version() -> Int\n  1\n");
        let json_url = json_repo.to_string_lossy();
        let http_url = http_repo.to_string_lossy();
        write_file(
            &app_manifest,
            &format!(
                "[package]\nname = \"app\"\nversion = \"0.1.0\"\nkea = \"0.1\"\n\n[dependencies]\nhttp = {{ git = \"{http_url}\", branch = \"{http_branch}\" }}\njson = {{ git = \"{json_url}\", branch = \"{json_branch}\" }}\n"
            ),
        );

        let initial = resolve_graph_from_manifest_path_with_cache_root(
            &app_manifest,
            ResolveMode::Build,
            cache_root.clone(),
        )
        .expect("initial build resolution should succeed");
        let initial_json_rev = lock_rev(&initial.lockfile, "json");
        let initial_http_rev = lock_rev(&initial.lockfile, "http");

        let next_json_rev = commit_module_source(
            &json_repo,
            "json",
            "update json package",
            "pub fn version() -> Int\n  2\n",
        );
        let _next_http_rev = commit_module_source(
            &http_repo,
            "http",
            "update http package",
            "pub fn version() -> Int\n  2\n",
        );

        let updated = resolve_graph_from_manifest_path_with_cache_root(
            &app_manifest,
            ResolveMode::Update {
                only_dependency: Some("json".to_string()),
            },
            cache_root,
        )
        .expect("targeted dependency update should succeed");
        let updated_json_rev = lock_rev(&updated.lockfile, "json");
        let updated_http_rev = lock_rev(&updated.lockfile, "http");

        assert_eq!(
            updated_json_rev, next_json_rev,
            "targeted update should advance the requested dependency"
        );
        assert_ne!(
            updated_json_rev, initial_json_rev,
            "targeted dependency should no longer be pinned to old revision"
        );
        assert_eq!(
            updated_http_rev, initial_http_rev,
            "non-targeted dependency should remain pinned to its lockfile revision"
        );

        let _ = fs::remove_dir_all(root);
    }
}
