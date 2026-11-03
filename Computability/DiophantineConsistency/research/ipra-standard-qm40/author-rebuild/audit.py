#!/usr/bin/env python3
"""Post-run author artifact check; no Lean, not a transitive closure audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError("invoke python3 -I -S -B without optimization")

HERE = Path(__file__).resolve().parent
PACKET = HERE / "observations/attempt02"
LIVE = Path("/tmp/ipra-standard-qm40-author-run-02")
EXPECTED = ("IPRASuccessorInduction", "IPRAAddOneGeneral", "IPRASuccessorInductionConverse",
            "IPRAStandardTheory", "IPRAStandardQM40")
NAMES = {"DiophantineConsistency.IPRAStandardQM40." + x for x in
         ("literal_equivalence", "selected_foundation_consistency", "literal_iff_translated_consistency")}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def record(p):
    p = Path(p)
    if not os.path.lexists(p):
        return None
    need(p.is_file(), ("invalid guarded path", str(p)))
    return {"sha256": sha(p), "resolved": str(p.resolve(strict=True)),
            "link": os.readlink(p) if p.is_symlink() else None}


def check(guards):
    for p, expected in guards.items():
        need(record(p) == expected, ("guard mismatch", p))


def main():
    result_path = PACKET / "RESULT.json"
    need(sha(result_path) == "0d77e6da49ebad57c6808fa1f38aefedef7d790ae620f6cc6c61749be705339a",
         "result hash mismatch")
    need(result_path.read_bytes() == (LIVE / "RESULT.json").read_bytes(), "live result differs")
    result = json.loads(result_path.read_text())
    pre = json.loads((PACKET / "preflight.json").read_text())
    need(result["status"] == "PASS_AUTHOR_STANDARD_QM40" and
         [(s["module"], s["exit"]) for s in result["steps"]] == [(n, 0) for n in EXPECTED],
         "result schema mismatch")
    check(pre["fixed"]); check(pre["sources"]); check(result["guards"])
    for step in result["steps"]:
        name = step["module"]
        log = PACKET / "logs" / (name + ".log")
        source = PACKET / "src/DiophantineConsistency" / (name + ".lean")
        need(sha(log) == step["log_sha256"] and log.read_bytes() == (LIVE / "logs" / log.name).read_bytes(),
             ("log mismatch", name))
        live_source = LIVE / "src/DiophantineConsistency" / source.name
        need(source.read_bytes() == live_source.read_bytes(), ("source snapshot mismatch", name))
        need(json.loads((PACKET / (name + ".json")).read_text()) == step, ("step mismatch", name))
        text = log.read_text()
        need("error:" not in text and "sorryAx" not in text, ("rejected diagnostic", name))
        if "warning:" in text:
            need(name == "IPRAStandardTheory" and
                 text.replace(str(live_source), "<SOURCE>") ==
                 (HERE / "historical-IPRAStandardTheory.log").read_text().replace(
                     "/tmp/ipra-standard-current14-author-trial/src/DiophantineConsistency/IPRAStandardTheory.lean",
                     "<SOURCE>"), ("warning mismatch", name))
    final = (PACKET / "logs/IPRAStandardQM40.log").read_text()
    found = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                       final, re.M | re.S)
    need(len(found) == 3 and {name for name, _ in found} == NAMES and
         all({a.strip() for a in values.split(",") if a.strip()} <= ALLOWED for _, values in found),
         ("wrong final axiom inventory", found))
    print(json.dumps({"status": "PASS_AUTHOR_STANDARD_QM40_ARTIFACT_CHECK", "modules": len(EXPECTED),
                      "result_sha256": sha(result_path), "named_axiom_reports": sorted(NAMES),
                      "scope": "Post-run author artifact check; direct guards and source snapshots only, "
                               "not an independent Lean run or complete transitive closure."}, sort_keys=True))


if __name__ == "__main__":
    main()
