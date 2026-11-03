#!/usr/bin/env python3
"""Focused source/receipt checks of compact rank variation; never runs Lean."""
import hashlib
import json
from pathlib import Path
import re
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError("invoke python3 -I -S -B without optimization")

HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
LEAN = DC / "Lean/DiophantineConsistency"
R = DC / "research/ordinary12-ipra-bridge"
SUB = R / "compact44-conditional-rank-variation-prototype"
TEMP = Path("/tmp/ipra-compact44-symbolic-unit-join")


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def declaration(p, name):
    text = p.read_text()
    match = re.search(r"(?ms)^theorem " + re.escape(name) + r"\b.*?(?=^theorem |^end |\Z)", text)
    need(match is not None, ("missing declaration", str(p), name))
    return match.group().strip()


def main():
    old = LEAN / "ArithmeticConstructionVariation.lean"
    adapted = SUB / "ArithmeticConstructionVariationCompact44.lean"
    change = (
        ("import DiophantineConsistency.ArithmeticControllerChoice\n",
         "import DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle\n"),
        ("ArithmeticControllerData.one_lt_exp", "ArithmeticControllerDataCompact44.one_lt_exp"),
        ("ArithmeticControllerChoice.bsum_zero_fn", "ArithmeticControllerChoiceCompact44Triangle.bsum_zero_fn"),
        ("namespace DiophantineConsistency.ArithmeticConstructionVariation\n",
         "namespace DiophantineConsistency.ArithmeticConstructionVariationCompact44\n"),
        ("end DiophantineConsistency.ArithmeticConstructionVariation\n",
         "end DiophantineConsistency.ArithmeticConstructionVariationCompact44\n"),
    )
    text = old.read_text()
    for a, b in change:
        need(text.count(a) == 1, ("source substitution count", a))
        text = text.replace(a, b)
    need(text == adapted.read_text(), "adaptation contains an unreviewed edit")
    old_data = LEAN / "ArithmeticControllerData.lean"
    new_data = R / "compact44-controller-data-prototype/ArithmeticControllerDataCompact44.lean"
    old_choice = LEAN / "ArithmeticControllerChoice.lean"
    new_choice = R / "compact44-symbolic-rank-calibration-prototype/ArithmeticControllerChoiceCompact44Triangle.lean"
    for a, b, names in ((old_data, new_data, ("one_lt_exp",)),
                        (old_choice, new_choice, ("bsum_zero_fn", "calibrated"))):
        for name in names:
            need(declaration(a, name) == declaration(b, name), ("helper changed", name))
    client = SUB / "CompactRankVariation.lean"
    retry = json.loads((SUB / "observations/retry.json").read_text())
    terminal = json.loads((SUB / "observations/terminal.json").read_text())
    need([s["exit_code"] for s in terminal["stages"]] == [0, 0, 1], "initial stages changed")
    need(retry["exit_code"] == 0 and not retry["warning_present"] and not retry["sorry_present"],
         "retry receipt is not a clean compiler success")
    need(sha(client) == retry["source_sha256"] == sha(TEMP / "src/CompactRankVariationRetry.lean"),
         "client or frozen source mismatch")
    need(sha(TEMP / "lib/CompactRankVariationRetry.olean") == retry["object_sha256"],
         "retry object mismatch")
    log = SUB / "observations/CompactRankVariationRetry.log"
    need(sha(log) == retry["log_sha256"], "retry log mismatch")
    reports = re.findall(r"^'([^']+)' depends on axioms: \[([^]]*)\]$", log.read_text(), re.M)
    names = {"CompactRankVariation.rank_variation", "CompactRankVariation.calibrated_rank"}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    need(len(reports) == 2 and {n for n, _ in reports} == names and
         all({x.strip() for x in a.split(",")} <= allowed for _, a in reports), "unexpected axiom inventory")
    for stage in terminal["stages"][:2]:
        obj = TEMP / "lib" / (stage["module"] + ".olean")
        need(sha(obj) == stage["object_sha256"], ("earlier object mismatch", stage["module"]))
    print(json.dumps({"status": "PASS_COMPACT_RANK_VARIATION_SOURCE_REVIEW",
                      "reviewed_commit": "f08bb1ad13", "adaptation_sha256": sha(adapted),
                      "client_sha256": sha(client), "retry_log_sha256": sha(log),
                      "helper_declarations_unchanged": ["one_lt_exp", "bsum_zero_fn", "calibrated"],
                      "lean_launched": False,
                      "scope": "Source-level mathematical review and sampled artifact checks, "
                               "not a Lean replay or transitive/dynamic provider audit."}, sort_keys=True))


if __name__ == "__main__":
    main()
