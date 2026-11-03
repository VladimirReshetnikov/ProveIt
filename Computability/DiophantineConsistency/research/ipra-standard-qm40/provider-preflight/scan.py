#!/usr/bin/env python3
"""Compare the historical standard extension with the quartic seed, no Lean."""
import hashlib
import json
import os
from pathlib import Path
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError("invoke python3 -I -S -B without optimization")

HERE = Path(__file__).resolve().parent
DC = HERE.parents[2]
STANDARD = Path("/tmp/ipra-standard-current14-author-trial/lib")
QUARTIC = Path("/tmp/ipra-qm40-native-author-8thsscoi/lib")
PACKAGE = Path("/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib")
STATE = DC / "reviews/ipra-standard-current14-author-trial/state.json"
SOURCE = DC / "Lean"
CLIENT = HERE.parent / "draft/IPRAStandardQM40.lean"
SUFFIXES = (".olean", ".olean.private", ".olean.server", ".ir", ".ilean",
            ".olean.hash", ".olean.private.hash", ".olean.server.hash", ".ir.hash", ".ilean.hash")
PREFIX = "DiophantineConsistency."
BUILD = tuple(PREFIX + n for n in ("IPRASuccessorInduction", "IPRAAddOneGeneral",
              "IPRASuccessorInductionConverse", "IPRAStandardTheory"))


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def record(p):
    if not os.path.lexists(p):
        return None
    link = os.readlink(p) if p.is_symlink() else None
    if not p.is_file():
        need(p.is_symlink(), ("nonfile candidate", str(p)))
        return {"kind": "dangling", "link": link}
    return {"kind": "link" if link is not None else "file", "link": link,
            "resolved": str(p.resolve(strict=True)), "sha256": digest(p)}


def slots(root, name):
    stem = root / Path(*name.split("."))
    return {s: record(Path(str(stem) + s)) for s in SUFFIXES}


def main():
    need(digest(STATE) == "bd643e25b07538400b7f7cc397ff64af6ddc6d73f1e563d69fb5c6aed863da61",
         "historical state hash changed")
    state = json.loads(STATE.read_text())
    need(state["status"] == "AUTHOR_ONLY_PASS", ("historical state status", state["status"]))
    rows = {row["module"]: row for row in state["rows"]}
    need(all(n in rows for n in BUILD), "missing standard extension row")
    source_info = {}
    historical = {}
    boundary = {}
    for name in BUILD:
        row = rows[name]
        src = SOURCE / Path(*name.split(".")).with_suffix(".lean")
        need(src.is_file() and digest(src) == row["source_sha256"], ("standard source drift", name))
        old = slots(STANDARD, name)
        need(old[".olean"] is not None and old[".olean"].get("sha256") == row["object_sha256"],
             ("historical standard object unavailable or changed", name))
        source_info[name] = {"path": str(src), "sha256": digest(src)}
        historical[name] = {"object": old, "imports": row["imports"]}
        for dependency, info in row["imports"].items():
            if dependency not in BUILD:
                oldhash = boundary.setdefault(dependency, info["sha256"])
                need(oldhash == info["sha256"], ("conflicting historical import records", dependency))
    expected_boundary = {PREFIX + "IPRAAddOneDirect", PREFIX + "IPRAEqualitySymmetryGG",
                         PREFIX + "IPRAOpenDisjunctionWitness", "Init"}
    need(set(boundary) == expected_boundary, ("historical boundary changed", list(boundary)))
    compared = {}
    old_guards = state["overlay_guards"]
    for name, oldhash in sorted(boundary.items()):
        rel = Path(*name.split("."))
        current = {str(root): slots(root, name) for root in (QUARTIC, PACKAGE)}
        records = [current[str(root)][".olean"] for root in (QUARTIC, PACKAGE)]
        resolved = [r for r in records if r and r.get("sha256")]
        need(resolved and all(r["sha256"] == resolved[0]["sha256"] for r in resolved),
             ("missing or conflicting quartic boundary", name))
        oldstem = STANDARD / rel
        oldcompanions = {s: old_guards.get(str(oldstem) + s, "NOT_RECORDED") for s in SUFFIXES}
        chosen = current[str(QUARTIC)] if current[str(QUARTIC)][".olean"] else current[str(PACKAGE)]
        companion_comparison = {}
        for suffix in SUFFIXES:
            old = oldcompanions[suffix]
            now = chosen[suffix]
            if old == "NOT_RECORDED":
                result = "historical companion not recorded"
            elif old is None:
                result = "both absent" if now is None else "historical absence, current presence"
            elif now is None or not now.get("sha256"):
                result = "current missing or dangling"
            else:
                result = "matching bytes" if old["sha256"] == now["sha256"] else "different bytes"
            companion_comparison[suffix] = result
        compared[name] = {"historical_recorded_olean_sha256": oldhash,
                          "historical_recorded_companions": oldcompanions,
                          "historical_current_slots": slots(STANDARD, name),
                          "quartic_candidates": current,
                          "companion_comparison": companion_comparison,
                          "matching_olean": oldhash == resolved[0]["sha256"]}
    need(compared[PREFIX + "IPRAAddOneDirect"]["matching_olean"] is False,
         "previously observed direct input mismatch has changed; re-evaluate plan")
    need(all(compared[n]["matching_olean"] for n in expected_boundary - {PREFIX + "IPRAAddOneDirect"}),
         "another recorded direct boundary does not match; re-evaluate plan")
    for name in BUILD:
        for root in (QUARTIC, PACKAGE):
            need(all(x is None for x in slots(root, name).values()),
                 ("standard module candidate slot occupied", str(root), name))
    need(CLIENT.is_file(), "missing client source")
    print(json.dumps({"status": "PREPARATION_ONLY_HISTORICAL_BOUNDARY_MISMATCH",
                      "build_order": list(BUILD), "sources": source_info,
                      "historical_extension": historical, "boundary": compared,
                      "draft_client": {"path": str(CLIENT), "sha256": digest(CLIENT)},
                      "scope": "No Lean launched; source and direct-input comparisons at one time; "
                               "native output unobserved and transitive/package/dynamic ancestry inherited."},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
