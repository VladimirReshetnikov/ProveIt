#!/usr/bin/env python3
"""Replay the portable bounded search packet (Python 3.10+, g++ for --all)."""
if not __debug__:
    raise RuntimeError("Verification requires Python without -O or -OO.")

from pathlib import Path
import argparse
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import symbolic_core as c
import variant_core as v


def run(args, log=None):
    print("Running:", " ".join(map(str, args)), flush=True)
    if log is None:
        subprocess.run(list(map(str, args)), cwd=HERE, check=True)
    else:
        with (HERE / log).open("w") as out:
            subprocess.run(list(map(str, args)), cwd=HERE, stdout=out,
                           stderr=subprocess.STDOUT, check=True)


def export_contexts(folder):
    data = json.loads((folder / "all_nonloop_contexts.json").read_text())
    radius = data["radius"]
    with (folder / "nonloop_contexts.txt").open("w") as out:
        for q, contexts in sorted(data["contexts"].items(), key=lambda x: int(x[0])):
            for bits, known in contexts:
                out.write(f"{q} {(bits >> radius) & 1} {bits} {known}\n")


def check_append_zero():
    rows, _ = c.machine()
    rows[198, 0] = (0, False, 40)
    q, h, tape = 74, 0, set()
    for _ in range(76):
        w, d, q = rows[q, int(h in tape)]
        if w:
            tape.add(h)
        else:
            tape.discard(h)
        h += 1 if d else -1
    assert (q, h, sorted(tape)) == (35, 4, [-3, 1])
    assert rows[35, 0] == (1, True, 35)
    # Induction: after n further steps, state=35, head=4+n;
    # the cells strictly beyond that head remain blank. Thus no halt is reached.
    return {"steps": 76, "state": q, "head": h, "ones": sorted(tape),
            "reason": "Rejected: permanent rightward sweep over blank cells."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true",
                        help="also regenerate contexts and repeat the principal searches")
    args = parser.parse_args()
    rows, _ = c.machine()
    baseline = c.validate(rows, c.contracts())
    rotated_rows, _, rotated_contracts = v.load(HERE / "rotated196")
    rotated = c.validate(rotated_rows, rotated_contracts)
    assert baseline["ok"] and baseline["contracts"] == 4959
    assert rotated["ok"] and rotated["contracts"] == 4959
    checks = {"baseline": baseline, "rotated": rotated,
              "append_zero": check_append_zero()}
    (HERE / "portable_validation.json").write_text(json.dumps(checks, indent=2) + "\n")
    print(json.dumps(checks, indent=2), flush=True)
    if not args.all:
        return
    for source in ("full_two_row", "all_register_twofold"):
        run(["g++", "-O3", "-std=c++17", source + ".cpp", "-o", source])
    for source in ("all_nonloop_contexts", "rotated_all_nonloop_contexts"):
        run([sys.executable, source + ".py"], source + ".rerun.log")
    export_contexts(HERE)
    export_contexts(HERE / "rotated196")
    for folder, table in ((HERE, HERE / "inputs/BusyBeaver/data/pa196.tm"),
                          (HERE / "rotated196", HERE / "rotated196/candidate.dense.tm")):
        run([HERE / "full_two_row", table, folder / "nonloop_contexts.txt",
             folder / "full_two_row_candidates.rerun.txt", "196"],
            folder.relative_to(HERE) / "full_two_row.rerun.log")
    run([HERE / "all_register_twofold", HERE / "inputs/BusyBeaver/data/pa196.tm",
         HERE / "nonloop_contexts.txt", HERE / "register_selectors.txt",
         HERE / "all_register_twofold_candidates.rerun.txt"],
        "all_register_twofold.rerun.log")
    for source in ("macro_quotients", "macro_row_blends", "edge_contracts",
                   "rotated_macro_quotients", "rotated_macro_row_blends",
                   "all_nonloop_fresh_shared_helper", "all_nonloop_triple_merge_helper",
                   "rotated_all_nonloop_fresh_shared_helper",
                   "rotated_all_nonloop_triple_merge_helper"):
        run([sys.executable, source + ".py"], source + ".rerun.log")


if __name__ == "__main__":
    main()
