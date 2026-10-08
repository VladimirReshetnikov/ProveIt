#!/usr/bin/env python3
"""Assemble the reviewable source snapshot and patch against the pinned commit.

This uses a temporary Git index.  It does not change the checkout's real index,
tracked files, commits, branches, remotes, or repository configuration.  Git may
write ordinary content-addressed objects for newly staged source files.  No
network operation is performed.  Research-result JSON files stay in the main
package's results directory rather than being duplicated in the source patch.

Usage from anywhere:
  python reproduce/assemble_integration.py --repo /path/to/ProveIt
The default destination is this package's integration/ directory.  Its tree/
subdirectory must be absent or empty, preventing a stale-file mixture.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


BASELINE = "8a95834940cf77cdab1b39571ffc102ca8b6bede"
PREFIX = "Topology/UnknotRecognition/"
FAST = PREFIX + "fast/"
REFERENCE_PACKAGES = (
    PREFIX + "reports/02/unknotlab",
    PREFIX + "reports/24/reference",
    PREFIX + "reports/26/detshadow",
    PREFIX + "reports/28/src/closure_reset",
)
REFERENCE_METADATA = (
    PREFIX + "reports/02/README.md",
    PREFIX + "reports/02/pyproject.toml",
    PREFIX + "reports/24/README.md",
    PREFIX + "reports/26/LICENSE",
    PREFIX + "reports/26/README.md",
    PREFIX + "reports/26/pyproject.toml",
    PREFIX + "reports/28/LICENSE",
    PREFIX + "reports/28/README.md",
    PREFIX + "reports/28/pyproject.toml",
)


def git(repo, *arguments, env=None):
    result = subprocess.run(["git", "-C", str(repo), *arguments],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=env, check=False)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", "replace"))
    return result.stdout


def nul_paths(data):
    return [part.decode("utf-8") for part in data.split(b"\0") if part]


def source_file(path):
    """Retain maintained source, fixture, and documentation files, not results."""
    relative = Path(path)
    return ("results" not in relative.parts and "__pycache__" not in relative.parts
            and relative.suffix not in (".pyc", ".pyo"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"integration")
    args = parser.parse_args()
    repo = args.repo.resolve()
    output = args.output.resolve()
    git(repo, "cat-file", "-e", BASELINE+"^{commit}")
    root = Path(git(repo, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    if root != repo:
        parser.error("--repo must name the Git repository root")
    tree = output/"tree"
    if tree.exists() and any(tree.iterdir()):
        parser.error(str(tree)+" already contains files; use a fresh output directory")

    tracked = nul_paths(git(repo, "ls-files", "-z", "--", FAST,
                           *REFERENCE_PACKAGES, *REFERENCE_METADATA))
    changed = nul_paths(git(repo, "diff", "--name-only", "-z", BASELINE, "--", FAST))
    untracked = nul_paths(git(repo, "ls-files", "--others", "--exclude-standard", "-z", "--", FAST))
    changed = sorted(path for path in set(changed+untracked) if source_file(path))
    snapshot_paths = sorted(path for path in set(tracked+untracked)
                            if source_file(path) and (repo/path).exists())
    missing = sorted(path for path in tracked if source_file(path) and not (repo/path).exists())
    if missing:
        raise RuntimeError("Missing tracked snapshot files (expand sparse checkout):\n"
                           +"\n".join(missing))
    if not changed:
        raise RuntimeError("No source changes were found against the pinned baseline")
    for prefix in REFERENCE_PACKAGES:
        if not any(path.startswith(prefix+"/") for path in snapshot_paths):
            raise RuntimeError("Required reference package is missing: "+prefix)

    # Snapshot the actual source content first.  The temporary index contains
    # the complete baseline tree but stages only this explicit changed list.
    output.mkdir(parents=True, exist_ok=True)
    tree.mkdir(parents=True, exist_ok=True)
    manifests = []
    for relative in snapshot_paths:
        source, destination = repo/relative, tree/relative
        if source.is_symlink() or not source.is_file():
            raise RuntimeError("Only regular source files are accepted: "+relative)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        data = destination.read_bytes()
        manifests.append(dict(path=relative, bytes=len(data), sha256=sha256(data).hexdigest()))

    real_status = git(repo, "status", "--porcelain=v1", "-z")
    with tempfile.TemporaryDirectory(prefix="unknot-patch-index-") as temporary:
        env = os.environ.copy()
        env["GIT_INDEX_FILE"] = str(Path(temporary)/"index")
        git(repo, "read-tree", BASELINE, env=env)
        git(repo, "add", "--", *changed, env=env)
        patch = git(repo, "diff", "--cached", "--binary", BASELINE, "--", *changed, env=env)
        summary = git(repo, "diff", "--cached", "--stat", BASELINE, "--", *changed, env=env)
        status = git(repo, "diff", "--cached", "--name-status", "-z", BASELINE,
                     "--", *changed, env=env)
        temporary_patch = Path(temporary)/"changes.patch"
        temporary_patch.write_bytes(patch)
        git(repo, "read-tree", BASELINE, env=env)
        git(repo, "apply", "--cached", "--check", str(temporary_patch), env=env)
        git(repo, "apply", "--cached", str(temporary_patch), env=env)
        reconstructed = []
        for relative in changed:
            if (tree/relative).is_file():
                data = git(repo, "show", ":"+relative, env=env)
                if data != (tree/relative).read_bytes():
                    raise RuntimeError("Patch reconstruction differs from snapshot: "+relative)
                reconstructed.append(dict(path=relative, sha256=sha256(data).hexdigest()))
    if git(repo, "status", "--porcelain=v1", "-z") != real_status:
        raise RuntimeError("Working-tree status changed during assembly; inspect concurrent edits")
    # Detect an edit during copying/patching instead of publishing mixed states.
    for row in manifests:
        if sha256((repo/row["path"]).read_bytes()).hexdigest() != row["sha256"]:
            raise RuntimeError("Source changed during assembly: "+row["path"])

    tokens = nul_paths(status)
    if len(tokens) % 2:
        raise RuntimeError("Unexpected Git name-status structure")
    changed_rows = [dict(status=tokens[i], path=tokens[i+1]) for i in range(0, len(tokens), 2)]
    (output/"changes.patch").write_bytes(patch)
    (output/"changes.stat").write_bytes(summary)
    (output/"baseline.txt").write_text(BASELINE+"\n")
    metadata = dict(baseline=BASELINE,
                    checkout_head=git(repo, "rev-parse", "HEAD").decode().strip(),
                    patch_sha256=sha256(patch).hexdigest(),
                    patch_bytes=len(patch), changed_files=changed_rows,
                    reference_packages=list(REFERENCE_PACKAGES),
                    excluded="Historical fast/results data; current research results are supplied separately.",
                    files=manifests)
    (output/"manifest.json").write_text(json.dumps(metadata, indent=2)+"\n")
    validation = dict(baseline=BASELINE, patch_sha256=sha256(patch).hexdigest(),
                      git_apply_cached_check="passed", real_worktree_mutated=False,
                      git_apply_reconstructed_files=reconstructed)
    (output/"patch-validation.json").write_text(json.dumps(validation, indent=2)+"\n")
    (output/"README.md").write_text(
        "# Integration snapshot\n\n"
        "The `tree/` directory contains the complete maintained Python source, tests, "
        "fixtures and required earlier reference packages at assembly time. "
        "Its paths start at the repository root. Historical benchmark results are omitted; "
        "the new measurements are provided separately in this package.\n\n"
        "The exact baseline is recorded in `baseline.txt`. `changes.patch` contains "
        "all changed and added source/test files against that commit; `changes.stat` "
        "summarizes it, and `manifest.json` binds the patch and every snapshot file "
        "by SHA-256. No remote operation was performed.\n\n"
        "Apply from a clean checkout of the pinned baseline:\n\n"
        "```sh\n"
        "git apply --check /absolute/path/to/integration/changes.patch\n"
        "git apply /absolute/path/to/integration/changes.patch\n"
        "```\n\n"
        "Ordinary tests can also run directly in "
        "`tree/Topology/UnknotRecognition/fast`. The historical overlap benchmark "
        "additionally needs the pinned Git object, as explained in the main reproduction guide.\n")
    print(json.dumps(dict(snapshot_files=len(manifests), changed_files=len(changed_rows),
                          snapshot_bytes=sum(row["bytes"] for row in manifests),
                          patch_bytes=len(patch), output=str(output))))


if __name__ == "__main__":
    main()
