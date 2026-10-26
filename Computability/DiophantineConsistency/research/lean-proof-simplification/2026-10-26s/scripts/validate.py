#!/usr/bin/env python3
"""Compile the exact candidate import closure without changing the checkout.

Dependencies must already be built at the versions in the repository's
lake-manifest.json. No network access or repository mutation is performed.
An optional --baseline points to this review's original validation directory;
its objects are reused only when source and dependency object hashes match.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import tomllib

PIN = "23f631ea07fff8632eb8cd92286f7621bbe051c0"
BUNDLE = Path(__file__).resolve().parents[1]

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def head(path):
    return subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip()

def strip_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == "/-":
            depth += 1; out.append("  "); i += 2
        elif depth and text[i:i+2] == "-/":
            depth -= 1; out.append("  "); i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text[i:i+2] == "--":
            j = text.find("\n", i)
            if j < 0: break
            out.append("\n"); i = j+1
        else:
            out.append(text[i]); i += 1
    return "".join(out)

def imports(path):
    result = []
    for match in re.finditer(r"^\s*(?:public\s+|meta\s+)?import\s+([^\n]+)", strip_comments(path.read_text()), re.M):
        result += re.findall(r"[A-Za-z_][\w'.]*", match.group(1))
    return list(dict.fromkeys(result))

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--lean", required=True, type=Path)
    ap.add_argument("--packages", type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--baseline", type=Path)
    ap.add_argument("--plan", action="store_true")
    args = ap.parse_args()
    repo, compiler, out = args.repo.resolve(), args.lean.resolve(), args.out.resolve()
    packages = (args.packages or repo/".lake/packages").resolve()
    assert head(repo) == PIN, "Repository commit differs from the reviewed snapshot; rebase explicitly."
    cfg = tomllib.loads((repo/"lakefile.toml").read_text())
    roots = [(x["name"], Path(x.get("srcDir", "."))) for x in cfg["lean_lib"]]
    package_info = json.loads((repo/"lake-manifest.json").read_text())["packages"]
    package_paths = []
    for p in package_info:
        path = packages/p["name"]
        assert head(path) == p["rev"], "Dependency version differs: " + p["name"]
        package_paths.append(path/".lake/build/lib/lean")
    plan = json.loads((BUNDLE/"validation-plan.json").read_text())
    sources, order, active = {}, [], set()
    def resolve(name):
        for lib, root in roots:
            if name == lib or name.startswith(lib + "."):
                rel = root/(name.replace(".", "/") + ".lean")
                candidate = BUNDLE/"candidates"/rel
                source = candidate if candidate.exists() else repo/rel
                if not source.exists(): raise FileNotFoundError(source)
                source_root = (BUNDLE/"candidates" if candidate.exists() else repo)/root
                return source, source_root, rel
        return None
    def visit(name):
        if name in sources: return
        found = resolve(name)
        if found is None: return
        if name in active: raise RuntimeError("Import cycle: " + name)
        active.add(name)
        for dep in imports(found[0]): visit(dep)
        sources[name] = found; order.append(name); active.remove(name)
    for name in plan["targets"]: visit(name)
    if args.plan:
        print(json.dumps({"count":len(order), "modules":order}, indent=2)); return 0
    build, logs = out/"build", out/"logs"
    build.mkdir(parents=True, exist_ok=True); logs.mkdir(parents=True, exist_ok=True)
    records_path = out/"records.json"
    prior = {}
    if records_path.exists():
        prior = {m["module"]:m for m in json.loads(records_path.read_text())["modules"]}
    baseline = {}
    if args.baseline:
        for file in ("build_records.json", "extra_records.json"):
            p = args.baseline/file
            if p.exists():
                obj = json.loads(p.read_text())
                assert obj["repository_commit"] == PIN
                baseline.update({m["module"]:m for m in obj["modules"]})
    version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    assert "version 4.32.0," in version, "Lean toolchain differs from the repository."
    env = dict(os.environ)
    # Lean chooses the first directory containing a namespace root. A partial
    # overlay therefore cannot rely on a second root for missing sibling
    # modules. Materialize verified baseline objects as per-file symlinks in
    # our own tree, and never compile into a symlink to a baseline object.
    env["LEAN_PATH"] = ":".join(map(str, [build] + package_paths))
    effective, results = {}, []
    record = {"repository_commit":PIN, "lean_version":version,
              "package_commits":{p["name"]:p["rev"] for p in package_info},
              "validation_plan_sha256":sha(BUNDLE/"validation-plan.json"), "modules":results}
    for name in order:
        source, root, rel = sources[name]
        digest = sha(source)
        dependencies = {d:sha(effective[d]) for d in imports(source) if d in effective}
        output = build/(name.replace(".", "/") + ".olean")
        choices = [(prior.get(name), output, "same-run cache")]
        if args.baseline:
            choices.append((baseline.get(name), args.baseline/"build"/(name.replace(".", "/")+".olean"), "verified baseline"))
        reused = False
        for old, path, label in choices:
            if old and old.get("returncode") == 0 and path.exists() and old["source_sha256"] == digest and old.get("dependency_olean_sha256") == dependencies and old.get("olean_sha256") == sha(path):
                if path != output:
                    output.parent.mkdir(parents=True, exist_ok=True)
                    if output.exists() or output.is_symlink(): output.unlink()
                    output.symlink_to(path.resolve())
                effective[name] = output
                results.append({**old, "reuse":label})
                print("REUSE",name,label,flush=True); reused = True; break
        if reused: continue
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.is_symlink(): output.unlink()
        command = [str(compiler), "-R", str(root), "-o", str(output), str(source)]
        started = time.monotonic()
        run = subprocess.run(command, cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        logfile = logs/(name+".log"); logfile.write_text(run.stdout)
        item = {"module":name, "source":str(rel), "source_sha256":digest,
                "dependency_olean_sha256":dependencies, "returncode":run.returncode,
                "elapsed_seconds":time.monotonic()-started, "command":command,
                "log":str(logfile), "olean_sha256":sha(output) if run.returncode == 0 else None}
        results.append(item); records_path.write_text(json.dumps(record, indent=2)+"\n")
        print("PASS" if run.returncode == 0 else "FAIL", name, f"({item['elapsed_seconds']:.2f}s)",flush=True)
        if run.returncode:
            print(run.stdout); return run.returncode
        effective[name] = output
    records_path.write_text(json.dumps(record, indent=2)+"\n")
    print("Completed",len(results),"repository modules; no whole-repository build is claimed.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
