#!/usr/bin/env python3
"""Regenerate the release integrity manifest after intentional reviewed edits."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
MUTABLE_RECEIPTS = {
    "validation/VERIFICATION.json",
    "positive11/INDEPENDENT_AUDIT.json",
    "positive12/certificates/CHECKS.json",
    "positive12/certificates/CHECKS_OPTIMIZED.json",
    "integer/CHECKS.json",
    "integer/CIRCUIT_CHECKS.json",
    "integer/INTEGER23_INDEPENDENT_AUDIT.json",
    "integer/INTEGER_EXTENSIONS_INDEPENDENT_AUDIT.json",
    "integer/VERIFY_RESULTS.json",
    "exploratory/HOMOGENEOUS_CHECKS.json",
    "coefficients/recipe/INDEPENDENT_AUDIT.json",
    "coefficients/recipe/COEFFICIENT_BINDING.json",
}
SCRATCH_SUFFIXES = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".pyc"}


def main():
    entries = {}
    for path in sorted(ROOT.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(ROOT).as_posix()
        if (rel == "MANIFEST.sha256.json" or rel in MUTABLE_RECEIPTS
                or "__pycache__" in path.parts or path.suffix in SCRATCH_SUFFIXES
                or rel.startswith("coefficients/recipe/coefficients/")):
            continue
        entries[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
    result = {"algorithm": "SHA-256", "files": entries,
              "exclusions": "Self, generated runtime receipts, TeX scratch files, Python caches, and regenerated duplicate coefficient recipe outputs. Active coefficient payloads, sources, code, proofs, packets, circuits and report are hashed.",
              "boundary": "Integrity record, not a signature or a mathematical proof."}
    (ROOT / "MANIFEST.sha256.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"hashed_files": len(entries)}))


if __name__ == "__main__":
    main()
