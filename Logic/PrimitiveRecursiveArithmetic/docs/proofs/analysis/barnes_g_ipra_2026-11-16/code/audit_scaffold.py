#!/usr/bin/env python3
"""Static, non-kernel audit of the Barnes-G Lean and document scaffold.

This deliberately does *not* claim Lean compilation.  It checks that the supplied
blueprints avoid proof-bypassing tokens, contain the advertised theorem/interface
names, and that the source coverage ledger has unique IDs and valid status codes.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
from pathlib import Path
from typing import Any

FORBIDDEN_LEAN = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"(?m)^\s*axiom\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "unsafe": re.compile(r"(?m)^\s*unsafe\b"),
}
REQUIRED_LEAN_SYMBOLS = {
    "FiniteCore.lean": [
        "def fac", "def gPos", "def superfac", "def hyperfac",
        "theorem gPos_eq_superfac", "theorem gPos_telescope",
        "theorem hyperfac_cross_identity",
    ],
    "AnalyticContracts.lean": [
        "structure FastName", "structure ApartCert", "structure ProductTailCert",
        "structure TaylorTailCert", "structure FQNF",
        "producerValid", "sound",
    ],
    "ObjectLanguageTargets.lean": [
        "[] ⊢[PRAAx] phi", "Target GHyper", "Target GammaBlock",
        "Target CanonicalTail", "Target GFunctional", "pra_iff_native",
    ],
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    root = args.root.resolve()

    checks: list[dict[str, Any]] = []
    ok = True

    for name, symbols in REQUIRED_LEAN_SYMBOLS.items():
        path = root / "lean" / name
        text = path.read_text(encoding="utf-8")
        # Strip ordinary and doc comments before searching for proof bypasses;
        # explanatory prose may legitimately contain the words ``sorry`` or ``admit``.
        code_text = re.sub(r"/-.*?-/", "", text, flags=re.S)
        code_text = re.sub(r"--.*$", "", code_text, flags=re.M)
        forbidden_hits = {
            key: [m.start() for m in pattern.finditer(code_text)]
            for key, pattern in FORBIDDEN_LEAN.items()
        }
        forbidden_hits = {k: v for k, v in forbidden_hits.items() if v}
        missing = [symbol for symbol in symbols if symbol not in text]
        this_ok = not forbidden_hits and not missing
        ok &= this_ok
        checks.append({
            "kind": "lean_static",
            "file": str(path.relative_to(root)),
            "ok": this_ok,
            "forbidden_hits": forbidden_hits,
            "missing_advertised_symbols": missing,
            "sha256": sha256(path),
        })

    ledger = root / "claims" / "coverage.csv"
    with ledger.open(newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))
    ids = [r.get("id", "") for r in rows]
    statuses = [r.get("status", "") for r in rows]
    required_fields = {"id", "source_statement", "report_location", "status", "object_ipra_form"}
    ledger_ok = (
        len(rows) == 38
        and len(ids) == len(set(ids))
        and all(i for i in ids)
        and set(rows[0].keys()) == required_fields
        and all(all((r.get(field) or "").strip() for field in required_fields) for r in rows)
    )
    ok &= ledger_ok
    checks.append({
        "kind": "coverage_ledger",
        "file": str(ledger.relative_to(root)),
        "ok": ledger_ok,
        "row_count": len(rows),
        "unique_id_count": len(set(ids)),
        "distinct_status_phrases": sorted(set(statuses)),
        "sha256": sha256(ledger),
    })

    tex_files = sorted((root / "paper").rglob("*.tex"))
    tex_issues: list[dict[str, Any]] = []
    bare_frac = re.compile(r"(?<!\\)(?:t?frac|dfrac|cfrac)\b")
    for path in tex_files:
        text = path.read_text(encoding="utf-8")
        bad_controls = [
            {"offset": i, "codepoint": ord(ch)}
            for i, ch in enumerate(text)
            if ord(ch) < 32 and ch not in "\n\r\t"
        ]
        bare = [m.start() for m in bare_frac.finditer(text)]
        if bad_controls or bare:
            tex_issues.append({
                "file": str(path.relative_to(root)),
                "control_characters": bad_controls,
                "bare_fraction_tokens": bare,
            })
    tex_ok = not tex_issues
    ok &= tex_ok
    checks.append({
        "kind": "tex_static",
        "ok": tex_ok,
        "file_count": len(tex_files),
        "issues": tex_issues,
    })

    result = {
        "all_ok": ok,
        "scope_note": (
            "Static source audit only. It is not Lean kernel compilation and does not "
            "establish the analytic contracts or ProveIt object-language derivations."
        ),
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
