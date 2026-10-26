#!/usr/bin/env python3
"""Inspect, apply, or check the bundled Lean refactorings in a pinned checkout.

The default operation is read-only: verify the bundle, Git commit, source
hashes, and patch applicability, then print the targeted replay commands.
Only --apply changes source files. Both --apply and --check-existing run
targeted Lake builds, which may populate normal build and dependency caches.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shlex
import subprocess
import sys


def run(command: list[str], cwd: Path, *, capture: bool = False) -> str:
    print("+ " + shlex.join(command), flush=True)
    env = os.environ.copy()
    env["GIT_OPTIONAL_LOCKS"] = "0"
    result = subprocess.run(command, cwd=cwd, env=env, check=True,
                            text=True, capture_output=capture)
    return result.stdout if capture else ""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def targets_from_patch(path: Path) -> list[str]:
    targets: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith("+++ b/"):
            name = line[6:].split("\t", 1)[0]
            relative = PurePosixPath(name)
            if relative.is_absolute() or ".." in relative.parts or ".git" in relative.parts:
                raise ValueError(f"Unsafe patch target: {name}")
            if name not in targets:
                targets.append(name)
    if not targets:
        raise ValueError("Combined patch has no target files")
    return targets


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True,
                        help="Root of a full local ProveIt Git checkout")
    parser.add_argument("--bundle", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Extracted bundle root")
    parser.add_argument("--lake", default="lake", help="Lake executable; default: lake")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true",
                      help="Apply the combined patch, then compile targeted modules and examples")
    mode.add_argument("--check-existing", action="store_true",
                      help="Compile an already patched checkout after matching its files to the candidates")
    args = parser.parse_args()
    repo = args.repo.resolve()
    bundle = args.bundle.resolve()
    patch = bundle / "patches/combined.patch"

    try:
        run([sys.executable, str(bundle / "scripts/verify_bundle.py"),
             "--bundle", str(bundle)], cwd=bundle)
        plan = json.loads((bundle / "scripts/replay-plan.json").read_text(encoding="utf-8"))
        top = Path(run(["git", "rev-parse", "--show-toplevel"], repo, capture=True).strip()).resolve()
        if top != repo:
            raise ValueError("--repo must identify the Git checkout root")
        head = run(["git", "rev-parse", "HEAD"], repo, capture=True).strip()
        if head != plan["baseline_commit"]:
            raise ValueError(f"Wrong checkout commit: expected {plan['baseline_commit']}, found {head}")
        toolchain = (repo / "lean-toolchain").read_text(encoding="utf-8").strip()
        if toolchain != plan["lean_toolchain"]:
            raise ValueError(f"Wrong Lean toolchain pin: {toolchain}")
        targets = targets_from_patch(patch)

        if args.check_existing:
            changed = set(run(["git", "diff", "HEAD", "--name-only"], repo, capture=True).splitlines())
            if changed - set(targets):
                raise ValueError("Unrelated tracked changes are present; use an isolated checkout")
            for name in targets:
                if sha256(repo / name) != sha256(bundle / "candidate-source" / name):
                    raise ValueError(f"Checkout does not match the delivered candidate: {name}")
        else:
            tracked_changes = run(["git", "status", "--porcelain", "--untracked-files=no"],
                                  repo, capture=True)
            if tracked_changes.strip():
                raise ValueError("Tracked changes are present; use a clean isolated checkout")
            for name in targets:
                expected = plan["baseline_sha256"][name]
                if sha256(repo / name) != expected:
                    raise ValueError(f"Baseline source SHA-256 mismatch: {name}")
            run(["git", "apply", "--check", str(patch)], repo)

        modules = list(plan["modules"])
        # Explicitly build the direct imports of standalone examples as well.
        # They are outside the repository's module tree and Lake therefore
        # cannot discover them from the project targets alone.
        for name in plan["examples"]:
            source = (bundle / name).read_text(encoding="utf-8")
            imports = re.findall(r"(?m)^import\s+([A-Za-z_][A-Za-z_0-9.]*)", source)
            for module in imports:
                if module not in modules:
                    modules.append(module)
        if not modules or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*", m) for m in modules):
            raise ValueError("Invalid targeted module list in replay plan")
        build = [args.lake, "build", *["+" + module + ":olean" for module in modules]]
        examples = [[args.lake, "env", "lean", str(bundle / name)] for name in plan["examples"]]
        if not args.apply and not args.check_existing:
            print("\nRead-only checks passed. No source, build, or dependency files were changed.")
            print("To apply the combined patch and run the checks, repeat with --apply.")
            print("The targeted build will be:")
            print(shlex.join(build))
            print("Standalone examples will be checked with:")
            for command in examples:
                print(shlex.join(command))
            return 0

        if args.apply:
            run(["git", "apply", str(patch)], repo)
            for name in targets:
                if sha256(repo / name) != sha256(bundle / "candidate-source" / name):
                    raise ValueError(f"Applied patch differs from the delivered candidate: {name}")
        run(build, repo)
        for command in examples:
            output = run(command, repo, capture=True)
            print(output, end="" if output.endswith("\n") or not output else "\n")
            if "sorryAx" in output:
                raise ValueError("An example's axiom output includes sorryAx")
        print("\nTargeted module and example replay completed successfully.")
        print("This command did not build every default target in the repository.")
        return 0
    except subprocess.CalledProcessError as error:
        if error.stdout:
            print(error.stdout, file=sys.stderr)
        if error.stderr:
            print(error.stderr, file=sys.stderr)
        print(f"Replay stopped: command exited with status {error.returncode}.", file=sys.stderr)
        if args.apply:
            print("The patch may remain applied; inspect git diff before retrying. No rollback was attempted.",
                  file=sys.stderr)
        return error.returncode or 1
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Replay stopped: {error}", file=sys.stderr)
        if args.apply:
            print("Inspect git diff before retrying; no automatic rollback was attempted.", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
