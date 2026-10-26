#!/usr/bin/env python3
"""Verify this research bundle without modifying it or the repository.

This is an integrity and source-sanity check, not a replacement for Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


REQUIRED = {
    "report.tex",
    "report.pdf",
    "patches/combined.patch",
    "scripts/replay.py",
    "scripts/verify_bundle.py",
    "scripts/replay-plan.json",
}


def safe_relative(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if (not value or path.is_absolute() or ".." in path.parts or
            "\\" in value or "\x00" in value or path.as_posix() != value):
        raise ValueError(f"Unsafe or noncanonical bundle path: {value!r}")
    return path


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def lean_code(text: str) -> str:
    """Remove nested block comments, line comments, and ordinary strings.

    This small lexical check is scoped to the supplied examples. It is not a
    complete Lean parser and does not certify imported declarations.
    """
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated comment or string in a Lean example")
    return "".join(out)


def patch_targets(text: str) -> set[str]:
    targets: set[str] = set()
    previous: str | None = None
    for line in text.splitlines():
        if line.startswith("--- "):
            value = line[4:].split("\t", 1)[0]
            if not value.startswith("a/"):
                raise ValueError("Combined patch must modify existing files only")
            previous = safe_relative(value[2:]).as_posix()
        elif line.startswith("+++ "):
            value = line[4:].split("\t", 1)[0]
            if not value.startswith("b/"):
                raise ValueError("Combined patch must modify existing files only")
            current = safe_relative(value[2:]).as_posix()
            if current != previous:
                raise ValueError("Renames and unmatched patch headers are unsupported")
            if ".git" in PurePosixPath(current).parts:
                raise ValueError("Combined patch may not edit Git metadata")
            targets.add(current)
    if not targets:
        raise ValueError("Combined patch has no source targets")
    return targets


def verify(root: Path) -> dict:
    manifest_path = root / "MANIFEST.sha256"
    entries: dict[str, str] = {}
    for number, line in enumerate(manifest_path.read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip():
            continue
        match = re.fullmatch(r"([0-9a-fA-F]{64}) [ *](.+)", line)
        if not match:
            raise ValueError(f"Malformed manifest line {number}")
        expected, name = match.groups()
        name = safe_relative(name).as_posix()
        if name == "MANIFEST.sha256" or name in entries:
            raise ValueError(f"Duplicate or self-referential manifest entry: {name}")
        entries[name] = expected.lower()

    actual: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError(f"Unexpected symlink: {path.relative_to(root)}")
        if path.is_file():
            name = path.relative_to(root).as_posix()
            if name != "MANIFEST.sha256":
                actual.add(name)
    missing = set(entries) - actual
    extra = actual - set(entries)
    if missing or extra:
        raise ValueError(f"Manifest file-set mismatch; missing={sorted(missing)}, extra={sorted(extra)}")
    if not REQUIRED <= actual:
        raise ValueError(f"Required bundle files missing: {sorted(REQUIRED - actual)}")
    for name, expected in entries.items():
        observed = digest(root / name)
        if observed != expected:
            raise ValueError(f"SHA-256 mismatch: {name}")

    plan = json.loads((root / "scripts/replay-plan.json").read_text(encoding="utf-8"))
    if plan.get("schema_version") != 1:
        raise ValueError("Unsupported replay plan version")
    if not re.fullmatch(r"[0-9a-f]{40}", plan.get("baseline_commit", "")):
        raise ValueError("Replay plan has no full baseline commit")
    examples = plan.get("examples", [])
    if not examples or len(set(examples)) != len(examples):
        raise ValueError("Replay plan must list distinct Lean examples")
    for name in examples:
        path = safe_relative(name)
        if path.parts[0] != "lean" or path.suffix != ".lean":
            raise ValueError(f"Unexpected example path: {name}")
    actual_examples = {name for name in actual if name.startswith("lean/") and name.endswith(".lean")}
    if actual_examples != set(examples):
        raise ValueError("Replay plan does not exactly list the delivered Lean examples")
    for name in examples:
        code = lean_code((root / name).read_text(encoding="utf-8"))
        bad = re.search(r"\b(?:sorry|sorryAx|admit|axiom)\b", code)
        if bad:
            raise ValueError(f"Unwanted proof placeholder or axiom declaration in {name}: {bad.group()}")

    targets = patch_targets((root / "patches/combined.patch").read_text(encoding="utf-8"))
    baseline = plan.get("baseline_sha256", {})
    for name in targets:
        if not re.fullmatch(r"[0-9a-f]{64}", baseline.get(name, "")):
            raise ValueError(f"No baseline SHA-256 recorded for patch target: {name}")
        candidate = "candidate-source/" + name
        if candidate not in actual:
            raise ValueError(f"Full candidate source missing: {candidate}")
    candidates = {name.removeprefix("candidate-source/") for name in actual
                  if name.startswith("candidate-source/") and name.endswith(".lean")}
    if candidates != targets:
        raise ValueError("Candidate-source set differs from combined-patch target set")
    return {"files_verified": len(entries), "lean_examples_checked": len(examples),
            "patch_targets": len(targets), "baseline_commit": plan["baseline_commit"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path,
                        default=Path(__file__).resolve().parent.parent,
                        help="Extracted bundle root; defaults to this script's parent directory")
    args = parser.parse_args()
    try:
        result = verify(args.bundle.resolve())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Bundle verification failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    print("Integrity and source-sanity checks passed. Lean validation is a separate step.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
