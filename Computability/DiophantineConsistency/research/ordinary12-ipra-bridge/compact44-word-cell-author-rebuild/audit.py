#!/usr/bin/env python3
"""Post-run author artifact check; no Lean and no transitive closure audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError("invoke python3 -I -S -B without optimization")
HERE = Path(__file__).resolve().parent
PACKET = HERE / "observations/author"
LIVE = Path("/tmp/ipra-compact-word-cell-author-01")
EXPECTED = ("CompactForwardCellInputs", "CompactWordCellClient")
NAMES = {
    "CompactForwardCellInputs." + x for x in
    ("standard_row", "selector_count", "selector_weighted", "payload_sum", "bounded_row_occupied")
} | {
    "CompactWordCellClient." + x for x in
    ("payload_definable", "word_payload_definable", "payload_row", "word_selector_definable",
     "word_payload_bit_definable", "word_occupied")
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def record(p):
    p = Path(p)
    if not os.path.lexists(p):
        return None
    need(p.is_file(), ("invalid guarded path", str(p)))
    return {"sha256": digest(p), "resolved": str(p.resolve(strict=True)),
            "link": os.readlink(p) if p.is_symlink() else None}


def check(guards):
    for p, expected in guards.items():
        need(record(p) == expected, ("guard mismatch", p))


def main():
    result_path = PACKET / "RESULT.json"
    need(digest(result_path) == "211454dc83aa90a0cb58ba5a6bf4013ac37b2018389ac1593ea9c0df6f760526",
         "result hash mismatch")
    need(result_path.read_bytes() == (LIVE / "RESULT.json").read_bytes(), "live result differs")
    result = json.loads(result_path.read_text())
    pre = json.loads((PACKET / "preflight.json").read_text())
    need(result["status"] == "PASS_AUTHOR_WORD_CELL" and
         [(s["module"], s["exit"]) for s in result["steps"]] == [(n, 0) for n in EXPECTED],
         "result schema mismatch")
    check(pre["fixed"]); check(pre["sources"]); check(result["guards"])
    found = []
    for step in result["steps"]:
        name = step["module"]
        log = PACKET / "logs" / (name + ".log")
        source = PACKET / "src/DiophantineConsistency" / (name + ".lean")
        need(digest(log) == step["log_sha256"] and log.read_bytes() == (LIVE / "logs" / log.name).read_bytes(),
             ("log mismatch", name))
        need(source.read_bytes() == (LIVE / "src/DiophantineConsistency" / source.name).read_bytes(),
             ("source snapshot mismatch", name))
        need(json.loads((PACKET / (name + ".json")).read_text()) == step, ("step mismatch", name))
        text = log.read_text()
        need(not any(x in text for x in ("error:", "warning:", "sorryAx")), ("bad diagnostic", name))
        found += re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                            text, re.M | re.S)
    need(len(found) == len(NAMES) and {name for name, _ in found} == NAMES and
         all({a.strip() for a in values.split(",") if a.strip()} <= ALLOWED for _, values in found),
         ("wrong axiom inventory", found))
    print(json.dumps({"status": "PASS_AUTHOR_WORD_CELL_ARTIFACT_CHECK", "modules": len(EXPECTED),
                      "result_sha256": digest(result_path), "named_axiom_reports": sorted(NAMES),
                      "scope": "Post-run author artifact check; not an independent Lean run or full closure audit."},
                     sort_keys=True))


if __name__ == "__main__":
    main()
