#!/usr/bin/env python3
"""Adversarial regressions for the exact-start/halting fold-checker boundary.

Both old machines halt on blank tape in one transition. The new machines loop
on blank tape. A sound checker for same-input halting equivalence must reject
the attempted maps. These examples test actual semantic failures, not counts.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path


CASES = [
    {
        "name": "halt_as_drop", "old_start": 95, "new_start": 95,
        "drop": 254, "keep": 95, "tagoffset": None,
        "old": {(95,0):(0,1,254),(95,1):(1,1,254),
                (99,0):(0,1,254),(99,1):(1,1,254)},
        "new": {(95,0):(0,1,95),(95,1):(1,1,95),
                (99,0):(0,1,254),(99,1):(1,1,254)},
        "reason": "The halt symbol cannot be a deleted working state.",
        "new_nonhalting_proof": "At state 95 on an all-zero tape, read0 writes0, moves right, and remains in 95. This repeats at every time.",
    },
    {
        "name": "initial_tag", "old_start": 95, "new_start": 96,
        "drop": 95, "keep": 96, "tagoffset": 0,
        "old": {(95,0):(0,1,254),(95,1):(0,1,97),
                (96,0):(0,1,97),(96,1):(0,1,254),
                (97,0):(0,-1,96),(97,1):(0,-1,96)},
        "new": {(96,0):(0,1,97),(96,1):(0,1,254),
                (97,0):(0,-1,96),(97,1):(0,-1,96)},
        "reason": "The map at the initial state must not flip an input bit.",
        "new_nonhalting_proof": "The blank configuration at state96, head0 returns exactly to itself in two steps: 96/0 -> 97/head1 -> 96/head0, writing zeros.",
    },
]


def write_table(path, data, start):
    path.write_text(f"#! start {start}\n" + "".join(
        f"{q} {b} {w} {'R' if d==1 else 'L'} {z}\n"
        for (q,b),(w,d,z) in sorted(data.items())))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--checker",type=Path,required=True)
    parser.add_argument("--out",type=Path,default=Path(__file__).resolve().parent/"checker_audit/regressions")
    args=parser.parse_args()
    checker_bytes=args.checker.read_bytes()
    spec=importlib.util.spec_from_file_location("audited_fold_checker",args.checker)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    args.out.mkdir(parents=True,exist_ok=True)
    results=[]
    for case in CASES:
        for which in ("old","new"):
            filename=args.out/(case["name"]+"_"+which+".tm")
            write_table(filename,case[which],case[which+"_start"])
            assert module.table(filename)==(case[which],case[which+"_start"])
        # Actual old blank behavior, independent of the proof checker.
        assert case["old"][case["old_start"],0][2]==254
        if case["name"]=="halt_as_drop":
            assert case["new"][95,0]==(0,1,95)
        else:
            assert case["new"][96,0]==(0,1,97)
            assert case["new"][97,0]==(0,-1,96)
        try:
            answer=module.prove(case["old"],case["new"],
                                case["old_start"],case["new_start"],
                                case["keep"],case["drop"],0,case["tagoffset"],5,65,20000)
        except ValueError as ex:
            results.append({"name":case["name"],"result":"REJECTED",
                            "exception":str(ex),"reason":case["reason"],
                            "old_blank_halting_steps":1,
                            "new_nonhalting_proof":case["new_nonhalting_proof"]})
        else:
            raise AssertionError({"invalid map was not rejected":case["name"],"answer":answer})
    assert args.checker.read_bytes()==checker_bytes,"checker changed during audit"
    output={"status":"PASS", "checker_sha256":sha256(checker_bytes).hexdigest(),
            "adversarial_regressions":results,
            "scope":"two semantically invalid maps are rejected; general soundness is the separate source audit"}
    (args.out/"verification.json").write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(output,indent=2))


if __name__=="__main__":
    if not __debug__:
        raise SystemExit("Run without -O: checks use assertions.")
    main()
