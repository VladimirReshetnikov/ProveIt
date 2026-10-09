#!/usr/bin/env python3
"""Preflight or apply the additive ProveIt research overlay.

Every source digest and prerequisite is checked before writes begin.
Existing byte-identical additions are accepted; conflicting files are never
overwritten. A Git checkout must be at the recorded base commit. A non-Git
source snapshot is accepted only after the same full prerequisite digest check.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys


HERE = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_path(root, relative):
    name = PurePosixPath(relative)
    if (name.is_absolute() or ".." in name.parts or not name.parts
            or str(name) != relative or "\\" in relative or ":" in relative):
        raise ValueError("invalid manifest path: " + relative)
    current = root
    for part in name.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("symbolic link in target path: " + str(current))
    return current


def preflight(repo, manifest):
    conflicts = []
    targets = {item["target"] for item in manifest["additions"]}
    for name in targets:
        parents = PurePosixPath(name).parents
        if any(str(parent) in targets for parent in parents):
            conflicts.append("overlapping addition targets: " + name)
    revision = None
    if (repo / ".git").exists():
        process = subprocess.run(
            ["git", "-C", str(repo), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=False)
        if process.returncode:
            conflicts.append("unable to read target Git revision")
        else:
            revision = process.stdout.strip()
            if revision != manifest["base_commit"]:
                conflicts.append("target Git revision differs from base_commit")
    for item in manifest["prerequisites"]:
        try:
            path = checked_path(repo, item["target"])
            if not path.is_file():
                conflicts.append("missing prerequisite: " + item["target"])
            elif digest(path) != item["sha256"]:
                conflicts.append("changed prerequisite: " + item["target"])
        except (OSError, ValueError) as error:
            conflicts.append(str(error))
    pending, identical = [], []
    destinations = set()
    for item in manifest["additions"]:
        if item["target"] in destinations:
            conflicts.append("duplicate addition target: " + item["target"])
            continue
        destinations.add(item["target"])
        try:
            source = checked_path(HERE, item["source"])
            target = checked_path(repo, item["target"])
            if not source.is_file() or digest(source) != item["sha256"]:
                conflicts.append("damaged overlay source: " + item["source"])
                continue
            if target.exists():
                if target.is_file() and digest(target) == item["sha256"]:
                    identical.append(item["target"])
                else:
                    conflicts.append("conflicting addition: " + item["target"])
            else:
                for parent in target.parents:
                    if parent == repo:
                        break
                    if parent.exists() and not parent.is_dir():
                        conflicts.append("non-directory target parent: " + str(parent))
                        break
                else:
                    conflicts.append("target escapes repository: " + item["target"])
                pending.append((source, target, item))
        except (OSError, ValueError) as error:
            conflicts.append(str(error))
    return revision, conflicts, pending, identical


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="read-only preflight (default)")
    mode.add_argument("--apply", action="store_true", help="create missing additions")
    parser.add_argument("--output", type=Path, help="optional machine-readable report")
    args = parser.parse_args()
    repo = args.repo.resolve()
    if not repo.is_dir():
        parser.error("--repo must be an existing directory")
    if args.output:
        args.output = args.output.absolute()
        resolved_report = args.output.resolve()
        if (args.output.exists() or args.output.is_symlink()
                or resolved_report.is_relative_to(repo)
                or resolved_report.is_relative_to(HERE.parent)):
            parser.error("--output must be a new file outside both the target "
                         "checkout and this artifact bundle")
    manifest = json.loads((HERE / "manifest.json").read_text())
    revision, conflicts, pending, identical = preflight(repo, manifest)
    result = dict(
        mode="apply" if args.apply else "check",
        status="CONFLICT" if conflicts else "READY",
        base_commit=manifest["base_commit"], target_revision=revision,
        prerequisites_checked=len(manifest["prerequisites"]),
        additions_total=len(manifest["additions"]),
        missing_additions=len(pending), identical_additions=len(identical),
        created=0, conflicts=conflicts,
    )
    if not conflicts and args.apply:
        try:
            for source, target, item in pending:
                target.parent.mkdir(parents=True, exist_ok=True)
                # Exclusive creation protects an unexpected concurrent writer.
                with target.open("xb") as output:
                    output.write(source.read_bytes())
                result["created"] += 1
            result["status"] = "APPLIED"
        except OSError as error:
            result["status"] = "WRITE_INTERRUPTED"
            result["conflicts"].append(str(error))
            # Earlier completed files are byte-identical and reusable. The
            # interrupted new file can be partial and needs inspection before
            # a retry; applying the whole batch is not transactional.
            # No pre-existing file is overwritten.
    serialized = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as report:
            report.write(serialized)
    sys.stdout.write(serialized)
    return 0 if result["status"] in ("READY", "APPLIED") else 2


if __name__ == "__main__":
    raise SystemExit(main())
