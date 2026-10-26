#!/usr/bin/env python3
"""Replay this packet against its original, prepared upstream source snapshot.

This is a verification overlay, not an installer. It never copies replacements
onto repository sources and issues no download/update/cache-fetch commands.
Prepare the pinned Lean toolchain and Lake dependencies before running it.
First reproduce the original pin; rebase and validate against newer sources
as a separate task. An existing nonempty output directory is never reused.

Examples:
  python3 validation/replay.py --repo /path/to/ProveIt
  python3 validation/replay.py --repo /path/to/ProveIt --skip-baseline-build
  python3 validation/replay.py --repo /path/to/ProveIt --with-optional --output /tmp/replay

For an already prepared external compiler/cache, --config accepts JSON with
"compiler" and "LEAN_PATH" strings. It skips Lake entirely, including baseline
builds. Relative entries are resolved relative to that JSON file. An exported
source tree without Git history is permitted only in this mode; its target
hashes are checked, but its full commit provenance is not independently proved.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


class ReplayError(Exception):
    pass


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def imports(path):
    # These frozen source headers use one ordinary `import` command per line.
    found = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)(?:\s*--.*)?$", line)
        if match:
            found.extend(match.group(1).split())
    return found


def absolute_search_path(value, base):
    result = []
    for item in value.split(os.pathsep):
        if item:
            path = Path(item).expanduser()
            result.append(str((path if path.is_absolute() else base / path).resolve()))
    return result


def check_hash(path, expected, label):
    if not path.is_file():
        raise ReplayError("Missing {}: {}".format(label, path))
    actual = sha256(path)
    if actual != expected:
        raise ReplayError("{} hash mismatch: {}\nexpected {}\nactual   {}".format(
            label, path, expected, actual))
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo", required=True, type=Path,
        help="Prepared upstream checkout at evidence/source-pin.txt; sources are read only.")
    parser.add_argument("--output", type=Path,
        help="New or empty directory for merged build objects, logs, and status.json.")
    parser.add_argument("--skip-baseline-build", action="store_true",
        help="Require already built baseline modules/dependencies instead of invoking lake build.")
    parser.add_argument("--config", type=Path,
        help="Prepared compiler/LEAN_PATH JSON; implies --skip-baseline-build and never invokes Lake.")
    parser.add_argument("--with-optional", action="store_true",
        help="Also compile every optional/*.lean probe after the two required audit files.")
    args = parser.parse_args()
    bundle = Path(__file__).resolve().parents[1]
    repo = args.repo.expanduser().resolve()
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    output = (args.output or Path.cwd() / ("lean-replay-" + stamp)).expanduser().resolve()
    if output == repo or output == bundle:
        parser.error("--output must be a separate directory, not the repository or bundle root")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        parser.error("--output must be new or empty; stale build objects cannot be reused")
    output.mkdir(parents=True, exist_ok=True)
    logs = output / "logs"
    build = output / "build"
    logs.mkdir()
    build.mkdir()
    status = {"started_utc": stamp, "status": "running", "repo": str(repo),
        "bundle": str(bundle), "output": str(output), "steps": [], "hashes": {}}

    def save():
        write_json(output / "status.json", status)

    def run(command, label, cwd, env=None):
        log = logs / (label + ".log")
        print("[replay] " + label, flush=True)
        started = time.monotonic()
        with log.open("wb") as stream:
            completed = subprocess.run(command, cwd=str(cwd), env=env,
                stdout=stream, stderr=subprocess.STDOUT, check=False)
        step = {"label": label, "command": [str(x) for x in command],
            "cwd": str(cwd), "exit_code": completed.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": str(log.relative_to(output)), "log_sha256": sha256(log)}
        status["steps"].append(step)
        save()
        if completed.returncode:
            raise ReplayError("{} failed (exit {}); see {}".format(label, completed.returncode, log))
        text = log.read_text(encoding="utf-8", errors="replace")
        if "sorryAx" in text:
            raise ReplayError("{} reported sorryAx; see {}".format(label, log))
        return text

    try:
        pin = (bundle / "evidence/source-pin.txt").read_text().strip()
        metrics_file = bundle / "evidence/source-metrics.json"
        rows = json.loads(metrics_file.read_text())
        status["source_pin"] = pin
        status["hashes"]["evidence/source-pin.txt"] = sha256(bundle / "evidence/source-pin.txt")
        status["hashes"]["evidence/source-metrics.json"] = sha256(metrics_file)
        selected = {row["module"]: row for row in rows}
        if len(selected) != 10:
            raise ReplayError("Expected the ten modules recorded by this packet")
        prefix = "Computability/DiophantineConsistency/Lean"
        source_root = repo / prefix
        overlay_root = bundle / "overlay" / prefix
        for row in rows:
            relative = Path(row["path"])
            if relative.is_absolute() or ".." in relative.parts:
                raise ReplayError("Invalid relative source path in evidence")
            baseline = repo / relative
            previous = row["before"]["sha256"]
            if previous is None:
                if baseline.exists():
                    raise ReplayError("New helper already exists in baseline: " + str(baseline))
            else:
                status["hashes"]["baseline/" + row["path"]] = check_hash(
                    baseline, previous, "baseline source")
            status["hashes"]["overlay/" + row["path"]] = check_hash(
                bundle / "overlay" / relative, row["after"]["sha256"], "overlay source")
        expected_toolchain = (bundle / "validation/lean-toolchain").read_text().strip()
        status["hashes"]["validation/lean-toolchain"] = sha256(bundle / "validation/lean-toolchain")
        if (repo / "lean-toolchain").read_text().strip() != expected_toolchain:
            raise ReplayError("The upstream lean-toolchain differs from the packet")
        upstream_manifest = bundle / "evidence/upstream-lake-manifest.json"
        status["hashes"]["baseline/lake-manifest.json"] = check_hash(
            repo / "lake-manifest.json", sha256(upstream_manifest), "upstream Lake manifest")
        manifest = json.loads(upstream_manifest.read_text())
        if (repo / ".git").exists():
            actual_pin = run(["git", "rev-parse", "HEAD"], "source-pin", repo).strip()
            if actual_pin != pin:
                raise ReplayError("Full replay requires commit {}; found {}. Rebase separately.".format(pin, actual_pin))
            run(["git", "diff", "--exit-code", "HEAD", "--", "*.lean", "lean-toolchain",
                "lake-manifest.json", "lakefile.lean", "lakefile.toml"], "tracked-source-clean", repo)
            status["pin_check"] = "Git HEAD matches; tracked Lean/build sources are unchanged"
        elif args.config:
            status["pin_check"] = "Exported sources: target hashes checked; full Git pin not independently verified"
        else:
            raise ReplayError("Default replay requires a Git checkout at the original pin; --config supports exported sources")

        # Include indirect selected dependencies through unchanged modules in the
        # same source namespace, e.g. RenameCode -> Rename -> CodeArithmetic.
        graph = {name: set() for name in selected}
        dependency_cache = {}
        def dependencies(name, visiting):
            if name in dependency_cache:
                return dependency_cache[name]
            if name in visiting:
                raise ReplayError("Import cycle through " + name)
            visiting = visiting | {name}
            path = (bundle / "overlay" / selected[name]["path"] if name in selected
                    else source_root.joinpath(*name.split(".")).with_suffix(".lean"))
            if not path.is_file():
                raise ReplayError("Missing source needed for import ordering: " + str(path))
            found = set()
            for dep in imports(path):
                if dep in selected:
                    found.add(dep)
                if dep.startswith("DiophantineConsistency."):
                    found.update(dependencies(dep, visiting))
            dependency_cache[name] = found
            return found
        for name in selected:
            graph[name] = set(dependencies(name, set()))
        order = []
        pending = list(selected)
        while pending:
            ready = next((name for name in pending if graph[name].issubset(order)), None)
            if ready is None:
                raise ReplayError("Cycle among selected overlay modules")
            order.append(ready)
            pending.remove(ready)
        status["overlay_order"] = order
        baseline_modules = [row["module"] for row in rows if row["before"]["sha256"] is not None]
        status["baseline_modules"] = baseline_modules

        if args.config:
            config_path = args.config.expanduser().resolve()
            config = json.loads(config_path.read_text())
            compiler_path = Path(config["compiler"]).expanduser()
            compiler = str((compiler_path if compiler_path.is_absolute()
                else config_path.parent / compiler_path).resolve())
            search_roots = absolute_search_path(config["LEAN_PATH"], config_path.parent)
            env = os.environ.copy()
            status["baseline_build"] = "Skipped: --config uses only the supplied prepared compiler/cache"
            status["config_sha256"] = sha256(config_path)
            if "mathlib_commit" in config:
                expected = next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
                if config["mathlib_commit"] != expected:
                    raise ReplayError("Configured Mathlib commit differs from the upstream manifest")
        else:
            lake = shutil.which("lake")
            if not lake:
                raise ReplayError("lake is not on PATH; prepare the pinned toolchain first")
            packages = repo / manifest.get("packagesDir", ".lake/packages")
            for package in manifest.get("packages", []):
                if package.get("type") == "git" and not (packages / package["name"]).is_dir():
                    raise ReplayError("Missing prepared dependency {}; this script does not download dependencies".format(package["name"]))
            if args.skip_baseline_build:
                status["baseline_build"] = "Skipped by --skip-baseline-build"
            else:
                extra = sorted({dep for row in rows for dep in imports(bundle / "overlay" / row["path"])
                    if dep.startswith("Mathlib.")})
                run([lake, "build"] + baseline_modules + extra, "baseline-build", repo)
                status["baseline_build"] = "Eight baseline modules and required direct Mathlib imports built"
            code = ("import json,os,shutil; "
                "print('REPLAY_ENV_JSON='+json.dumps({'compiler':shutil.which('lean'),"
                "'env':{k:os.environ[k] for k in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT',"
                "'PATH','LD_LIBRARY_PATH','DYLD_LIBRARY_PATH'] if k in os.environ}}))")
            output_text = run([lake, "env", sys.executable, "-c", code], "lake-environment", repo)
            payloads = [line[len("REPLAY_ENV_JSON="):] for line in output_text.splitlines()
                if line.startswith("REPLAY_ENV_JSON=")]
            if len(payloads) != 1:
                raise ReplayError("Could not read the compiler/search path from lake env")
            configured = json.loads(payloads[0])
            compiler = configured["compiler"]
            if not compiler:
                raise ReplayError("lake env could not locate lean")
            env = os.environ.copy()
            env.update(configured["env"])
            search_roots = absolute_search_path(configured["env"].get("LEAN_PATH", ""), repo)
        if not Path(compiler).is_file():
            raise ReplayError("Configured Lean compiler does not exist: " + str(compiler))
        if not search_roots:
            raise ReplayError("An explicit baseline LEAN_PATH is required")
        version = run([compiler, "--version"], "lean-version", repo, env).strip()
        expected_version = expected_toolchain.rsplit(":v", 1)[-1]
        if ("version " + expected_version + ",") not in version:
            raise ReplayError("Compiler version does not match {}: {}".format(expected_toolchain, version))
        status["compiler"] = compiler
        status["compiler_version"] = version
        status["baseline_search_roots"] = search_roots
        for module in baseline_modules:
            relative = Path(*module.split(".")).with_suffix(".olean")
            if not any((Path(root) / relative).is_file() for root in search_roots):
                raise ReplayError("Missing baseline object {}; build its dependencies first".format(module))

        # Lean selects the first existing top-level namespace directory. A bare
        # path prepend therefore hides unchanged modules. Merge that namespace
        # with read-only symlinks, omitting every selected module's old objects.
        selected_bases = [name.replace(".", "/") for name in selected]
        namespaces = sorted({name.split(".")[0] for name in selected})
        linked = 0
        for root_string in search_roots:
            root = Path(root_string)
            for namespace in namespaces:
                tree = root / namespace
                if not tree.is_dir():
                    continue
                for source in sorted(tree.rglob("*")):
                    if not source.is_file():
                        continue
                    relative = source.relative_to(root)
                    reltext = relative.as_posix()
                    if any(reltext.startswith(base + ".") for base in selected_bases):
                        continue
                    destination = build / relative
                    if destination.exists() or destination.is_symlink():
                        continue  # Earlier baseline search roots take precedence.
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.symlink_to(source.resolve())
                    linked += 1
        status["baseline_namespace_links"] = linked
        baseline_env = dict(env, LEAN_PATH=os.pathsep.join(search_roots))
        env["LEAN_PATH"] = os.pathsep.join([str(build)] + search_roots)
        status["overlay_search_path"] = env["LEAN_PATH"]
        for module in order:
            row = selected[module]
            source = bundle / "overlay" / row["path"]
            destination = build.joinpath(*module.split(".")).with_suffix(".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            if destination.exists() or destination.is_symlink():
                raise ReplayError("Refusing to overwrite a staged object or write through a link: " + str(destination))
            run([compiler, str(source), "-o", str(destination)], module, overlay_root, env)
            status["hashes"]["objects/" + module] = sha256(destination)
        checks = [bundle / "validation/AxiomAudit.lean", bundle / "validation/FirstExitChecks.lean"]
        if args.with_optional:
            checks.extend(sorted((bundle / "optional").glob("*.lean")))
        for source in checks:
            if not source.is_file():
                raise ReplayError("Missing bundled audit/probe: " + str(source))
            relative = str(source.relative_to(bundle))
            status["hashes"][relative] = sha256(source)
            run([compiler, str(source)], "check-" + source.stem, source.parent, env)
        baseline_audit = bundle / "validation/AxiomAuditBaseline.lean"
        if not baseline_audit.is_file():
            raise ReplayError("Missing bundled baseline axiom audit")
        status["hashes"][str(baseline_audit.relative_to(bundle))] = sha256(baseline_audit)
        run([compiler, str(baseline_audit)], "check-AxiomAuditBaseline", baseline_audit.parent, baseline_env)
        status["status"] = "passed"
        status["scope"] = "All ten overlay modules and requested audits; not a whole-repository rebuild"
        save()
        print("Replay passed. Receipt: " + str(output / "status.json"))
        return 0
    except (ReplayError, OSError, ValueError, KeyError) as error:
        status["status"] = "failed"
        status["error"] = str(error)
        save()
        print("Replay failed: " + str(error), file=sys.stderr)
        print("Receipt: " + str(output / "status.json"), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
