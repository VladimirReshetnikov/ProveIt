#!/usr/bin/env python3
"""Build or verify the canonical package's single exhaustive SHA-256 ledger."""

from __future__ import annotations

import argparse
import hashlib
import subprocess
from pathlib import Path, PurePosixPath


PACKAGE = Path(__file__).resolve().parents[1]
OUTPUT = PACKAGE / "SHA256SUMS"
_ROOT_QUERY = subprocess.run(
    ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
    check=True,
    stdout=subprocess.PIPE,
)
REPOSITORY = Path(_ROOT_QUERY.stdout.decode("utf-8").strip())
PACKAGE_REPOSITORY_PATH = PurePosixPath(PACKAGE.relative_to(REPOSITORY).as_posix())


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_paths(*arguments: str) -> list[str]:
    completed = subprocess.run(
        [
            "git",
            "-C",
            str(REPOSITORY),
            "ls-files",
            "-z",
            *arguments,
            "--",
            ":(top)" + PACKAGE_REPOSITORY_PATH.as_posix(),
        ],
        check=True,
        stdout=subprocess.PIPE,
    )
    return [path for path in completed.stdout.decode("utf-8").split("\0") if path]


def permanent_files() -> list[Path]:
    untracked = git_paths("--others", "--exclude-standard")
    if untracked:
        raise ValueError(
            "untracked permanent package paths must be staged or removed: "
            + ", ".join(untracked)
        )
    repository_paths = git_paths("--cached")
    files: list[Path] = []
    for raw in repository_paths:
        path = REPOSITORY / PurePosixPath(raw)
        if path.resolve() == OUTPUT.resolve() or not path.is_file():
            continue
        try:
            path.resolve().relative_to(PACKAGE.resolve())
        except ValueError as error:
            raise ValueError(f"checksum path escapes package: {raw}") from error
        files.append(path)
    if len({path.resolve() for path in files}) != len(files):
        raise ValueError("duplicate path in package checksum inventory")
    return sorted(files, key=lambda path: path.relative_to(PACKAGE).as_posix())


def ledger_bytes() -> bytes:
    rows = [
        f"{sha256(path)}  ./{path.relative_to(PACKAGE).as_posix()}\n"
        for path in permanent_files()
    ]
    return "".join(rows).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the ledger with the current permanent package inventory",
    )
    args = parser.parse_args()
    payload = ledger_bytes()
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_bytes() != payload:
            print(f"FAILED: stale or incomplete package checksum ledger: {OUTPUT}")
            return 1
        print(f"package checksum ledger: PASS ({len(payload.splitlines())} rows)")
    else:
        OUTPUT.write_bytes(payload)
        print(f"wrote: {OUTPUT}")
        print(f"rows: {len(payload.splitlines())}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
