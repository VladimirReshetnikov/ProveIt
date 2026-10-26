#!/usr/bin/env python3
"""Read-only applicability check for the packaged Lean patches.

This script runs only Git read operations and `git apply --check`.
It never applies patches, changes refs, installs dependencies, or uses a network.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys


PROOF_SOURCE_COMMIT = "29936089835c0c55cca81edc86b4fb0c70ce34d5"
CLOSING_AUDIT_COMMIT = "09d65a93c9df8684c1a226341d6a5120623d1cdb"
PRIMARY_PATCHES = (
    "01-coefficient-action.patch",
    "02-power-thresholds.patch",
)
OPTIONAL_PATCH = "optional-canonical-tile-index.patch"


def git_read(repository: Path, *arguments: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(repository), *arguments],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Check the two primary patches against a checkout without changing it. "
            "Run before applying any selected patch."
        )
    )
    parser.add_argument("repository", type=Path, help="Path to the ProveIt checkout")
    parser.add_argument(
        "--include-optional",
        action="store_true",
        help="Also check the optional computable quotient patch",
    )
    args = parser.parse_args()
    repository = args.repository.expanduser().resolve()
    bundle = Path(__file__).resolve().parent.parent
    names = list(PRIMARY_PATCHES)
    if args.include_optional:
        names.append(OPTIONAL_PATCH)
    patches = [bundle / "patches" / name for name in names]

    if not repository.is_dir():
        parser.error(f"Checkout directory does not exist: {repository}")
    missing = [str(path) for path in patches if not path.is_file()]
    if missing:
        parser.error("Packaged patch file(s) missing: " + ", ".join(missing))

    try:
        top = git_read(repository, "rev-parse", "--show-toplevel")
        if top.returncode:
            sys.stderr.write(top.stderr)
            return top.returncode
        repository = Path(top.stdout.strip()).resolve()
        head = git_read(repository, "rev-parse", "HEAD")
        if head.returncode:
            sys.stderr.write(head.stderr)
            return head.returncode

        print(f"Checkout: {repository}")
        print(f"Checkout commit: {head.stdout.strip()}")
        print(f"Proof-source commit: {PROOF_SOURCE_COMMIT}")
        print(f"Closing audit commit: {CLOSING_AUDIT_COMMIT}")
        if head.stdout.strip() != PROOF_SOURCE_COMMIT:
            print(
                "The checkout differs from the proof-source pin; this check only "
                "establishes whether the selected patches apply to its current files."
            )
        print("Selected patches:")
        for name in names:
            print(f"  {name}")

        result = git_read(
            repository, "apply", "--check", "--", *(str(path) for path in patches)
        )
    except FileNotFoundError:
        parser.error("Git is not installed or is not available on PATH.")
    except OSError as error:
        parser.error(str(error))

    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.stderr:
        sys.stderr.write(result.stderr)
    if result.returncode:
        print(
            "Patch applicability check failed. Review the Git diagnostics above. "
            "No patches were applied."
        )
    else:
        print("All selected patches pass git apply --check. No files were changed.")
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
