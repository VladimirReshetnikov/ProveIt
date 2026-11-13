#!/usr/bin/env python3
"""Point-in-time direct candidate scan, with no Lean invocation."""
import hashlib
import json
import os
from pathlib import Path
import sys

if not __debug__:
    raise RuntimeError("Run without Python optimization")

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent
SEED = Path("/tmp/ipra-marked-suffix-final-build-01/lib")
PACKAGE = Path("/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib")
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ilean",
            ".olean.hash", ".olean.private.hash", ".olean.server.hash",
            ".ir.hash", ".ilean.hash")
DIRECT = (
    "DiophantineConsistency.CompactCoefficientDecoder",
    "DiophantineConsistency.ArithmeticStandardCasts",
    "Mathlib.Algebra.BigOperators.Fin",
    "DiophantineConsistency.CompactMarkedTransport",
    "DiophantineConsistency.CompactForwardCellInputs",
    "DiophantineConsistency.CompactWordCellClient",
)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    if p.is_symlink():
        target = p.resolve(strict=True)
        if not target.is_file():
            raise RuntimeError(f"symlink target is not a file: {p}")
        return {"kind": "symlink", "link_text": os.readlink(p),
                "resolved": str(target), "sha256": sha(target),
                "bytes": target.stat().st_size}
    if not p.exists():
        return None
    if not p.is_file():
        raise RuntimeError(f"non-file at candidate slot: {p}")
    return {"kind": "file", "resolved": str(p.resolve(strict=True)),
            "sha256": sha(p), "bytes": p.stat().st_size}


def main():
    for root in (SEED, PACKAGE):
        if not root.is_dir() or root.is_symlink():
            raise RuntimeError(f"provider unavailable: {root}")
    sources = [BRIDGE / "compact44-forward-cell-inputs-exploration/CompactForwardCellInputs.lean",
               HERE / "CompactWordCellClient-DRAFT.lean"]
    source_records = {str(p): record(p) for p in sources}
    if any(x is None for x in source_records.values()):
        raise RuntimeError("missing source")
    modules = {}
    for name in DIRECT:
        rel = Path(*name.split("."))
        slots = {}
        for root in (SEED, PACKAGE):
            slots[str(root)] = {s: record(root / (str(rel) + s)) for s in SUFFIXES}
        modules[name] = slots
    for name in DIRECT[:4]:
        candidates = [modules[name][str(root)][".olean"] for root in (SEED, PACKAGE)]
        present = [r for r in candidates if r is not None]
        if not present or any(r["sha256"] != present[0]["sha256"] for r in present):
            raise RuntimeError(f"missing or conflicting direct input: {name}")
    for name in DIRECT[4:]:
        for root in (SEED, PACKAGE):
            if any(modules[name][str(root)].values()):
                raise RuntimeError(f"target slot already occupied: {name} in {root}")
    print(json.dumps({"status": "READY_POINT_IN_TIME_DIRECT_SCAN_NO_LEAN",
                      "sources": source_records, "candidates": modules,
                      "scope": "Point-in-time direct slots only; no build, closure or dynamic audit."},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
