#!/usr/bin/env python3
"""Check the pinned GRH source and compute import reachability.

Usage: python3 check_source.py /path/to/grh-lean
Standard library and Git only. This is a check of source identity and
the theorem boundary. It does not type-check Lean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

COMMIT = "72fead102f663d5c7a407964a13dc0cf9d977207"
# Published by Andrew Sutherland at https://math.mit.edu/~drew/shortgrh/
ARCHIVE = "9138cf2f5862e64f823ed676e8d37333c0717e1a13cd8f74f6b735ab2d1ba57c"
MATHLIB = "56a005855ea17e0b0958f73ec801ae140b0a1679"
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
TARGETS = ["riemannHypothesis", "riemannZeta_eq_zero_re",
           "LFunction_ne_zero_of_half_lt_re", "LFunction_eq_zero_re",
           "LFunction_eq_zero_re_of_isPrimitive"]
IMPORT = re.compile(r"^import\s+([\w.]+)\s*$", re.MULTILINE)

def require(ok, message):
    if not ok:
        raise SystemExit(message)

def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])

def audit_edition(root, edition):
    project = root / edition
    def read(name):
        return (project / name).read_text(encoding="utf-8")
    config = json.loads(read("comparator.json"))
    require(set(config["permitted_axioms"]) == AXIOMS, "Unexpected axiom policy")
    require(config["theorem_names"] == TARGETS, "Unexpected list of targets")
    require(read("lean-toolchain").strip() == "leanprover/lean4:v4.35.0", "Wrong toolchain")
    manifest = json.loads(read("lake-manifest.json"))
    require([p["rev"] for p in manifest["packages"] if p["name"] == "mathlib"] == [MATHLIB],
            "Unexpected mathlib revision")
    require(IMPORT.findall(read("src/Statements.lean")) == ["Mathlib"], "Unexpected public import")
    declarations = re.findall(r"^theorem\s+(\w+)", read("src/Main.lean"), re.MULTILINE)
    require(declarations == TARGETS, "Unexpected declarations in Main")
    # All import commands in this pinned project's source use a single module
    # per line. Refuse an unrecognized command shape instead of omitting it.
    modules = {}
    filenames = git(root, "ls-files", "-z", f"{edition}/src/*.lean").decode().split("\0")
    for filename in filter(None, filenames):
        path = root / filename
        module = ".".join(path.relative_to(project / "src").with_suffix("").parts)
        text = path.read_text(encoding="utf-8")
        matches = IMPORT.findall(text)
        require(len(matches) == len(re.findall(r"^import\s+", text, re.MULTILINE)),
                f"Unsupported import syntax in {path}")
        modules[module] = matches
    reached = set()
    todo = ["Main"]
    while todo:
        module = todo.pop()
        if module in reached:
            continue
        reached.add(module)
        for dependency in modules[module]:
            if dependency in modules:
                todo.append(dependency)
            else:
                require(dependency.startswith("Mathlib.") or dependency == "Mathlib",
                        f"Unexpected external module {dependency}")
    return {"edition": edition, "local_source_modules": len(modules),
            "local_modules_reachable_from_Main": len(reached),
            "statements_sha256": hashlib.sha256(read("src/Statements.lean").encode()).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    args = parser.parse_args()
    require(git(args.repo, "rev-parse", "HEAD").decode().strip() == COMMIT, "Wrong commit")
    require(not git(args.repo, "status", "--porcelain", "--untracked-files=no"),
            "Tracked files differ from the pinned commit")
    digest = hashlib.sha256(git(args.repo, "archive", "HEAD")).hexdigest()
    require(digest == ARCHIVE, "Archive does not match Sutherland's source digest")
    editions = [audit_edition(args.repo, e) for e in ("grh", "grh-compact")]
    require(editions[0]["statements_sha256"] == editions[1]["statements_sha256"],
            "Public statements differ")
    print(json.dumps({"commit": COMMIT, "archive_sha256": digest, "editions": editions,
                      "public_theorems": TARGETS,
                      "check": "Source identity and import traversal. No kernel replay."},
                     indent=2))

if __name__ == "__main__":
    main()
