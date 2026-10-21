#!/usr/bin/env python3
"""Bind the compiled table definitions to the two supplied literal machines.

The mathematical equivalence is proved in M124Transfer.v.  This script checks
file identity, table generation, finite model conventions, and dense relabeling.
It is not a substitute for compiling and recursively checking the Rocq proof.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent
PINS = {
    "k215.native.tm": "9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2",
    "machine.native.tm": "8e0ccb4b631c4e4c1c02c4b52a6fe382984e67557dd1dcd949065479e38d07b9",
    "machine.tm": "fa15e120366da90e74aac43f3b808b27c0187960d373d4a95e425f8c73259e2b",
}
PATCH = {
    (110, 0): (0, "R", 124),
    (124, 0): (0, "L", 127),
    (127, 0): (0, "R", 8),
    (127, 1): (1, "R", 59),
}


def parse(path):
    start, rows = None, {}
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, d, n = line.split()
            key = int(q), int(b)
            assert key not in rows and b in ("0", "1")
            assert w in ("0", "1") and d in ("L", "R")
            rows[key] = int(w), d, int(n)
    return start, rows


def coq_table(rows):
    out = ["From Coq Require Import ZArith Bool Arith Lia.\nOpen Scope Z_scope.\n"
           "Record instr := I { out : bool; delta : Z; target : nat }.\n"
           "Definition table := nat -> bool -> option instr.\n"
           "Definition K : table := fun q b =>\n match q with\n"]
    for q in sorted({q for q, b in rows}):
        def val(v):
            w, d, n = v
            return ("Some (I " + ("true" if w else "false") + " " +
                    ("1" if d == "R" else "(-1)") + " " + str(n) + "%nat)")
        out.append(f" | {q}%nat => if b then {val(rows[q,1])} else {val(rows[q,0])}\n")
    out.append(" | _ => None\n end.\n\n")
    return "".join(out)


def check(generate=False):
    for name, digest in PINS.items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest
    start, old = parse(ROOT / "k215.native.tm")
    new_start, new = parse(ROOT / "machine.native.tm")
    dense_start, dense = parse(ROOT / "machine.tm")
    assert start == new_start == dense_start == 0
    assert len(old) == len(new) == len(dense) == 430
    states = {q for q, b in old}
    assert len(states) == 215 and states == {q for q, b in new}
    assert set(old) == set(new) == {(q, b) for q in states for b in (0, 1)}
    assert {n for w, d, n in old.values()} - states == {254}
    assert {n for w, d, n in new.values()} - states == {254}
    expected = dict(old)
    expected.update(PATCH)
    assert expected == new
    assert {k for k in old if old[k] != new[k]} == set(PATCH)

    mapping = {int(k): int(v) for k, v in
               json.loads((ROOT / "state_map.json").read_text())["native_to_dense"].items()}
    assert len(mapping) == len(set(mapping.values())) == 216
    assert mapping[0] == 0 and mapping[254] == 215
    assert dense == {(mapping[q], b): (w, d, mapping[n])
                     for (q, b), (w, d, n) in new.items()}
    assert {q for q, b in dense} == set(range(215))

    generated = coq_table(old)
    if generate:
        (ROOT / "M124Table.v").write_text(generated)
    assert (ROOT / "M124Table.v").read_text() == generated
    formal = (ROOT / "M124Facts.v").read_text()
    m_body = formal.split("Definition M : table := fun q b =>\n", 1)[1].split("end.", 1)[0]
    expected_body = ("  match q, b with\n"
                     "  | 110%nat, false => Some (I false 1 124)\n"
                     "  | 124%nat, false => Some (I false (-1) 127)\n"
                     "  | 127%nat, false => Some (I false 1 8)\n"
                     "  | 127%nat, true  => Some (I true 1 59)\n"
                     "  | _, _ => K q b\n  ")
    assert m_body == expected_body
    incoming = lambda dst: {k: v for k, v in old.items() if v[2] == dst}
    assert incoming(124) == {(104, 1): (1, "R", 124)}
    assert incoming(127) == {(110, 0): (0, "R", 127)}
    assert old[8, 0] == (0, "R", 14)
    assert old[59, 0] == (0, "R", 62)
    # A direct literal reuse of an existing selector, with no further change,
    # is impossible. This does not exclude multi-step/contextual reuse.
    direct_selectors = [q for q in states - {127}
                        if new[q, 0] == (0, "R", 8) and new[q, 1] == (1, "R", 59)]
    assert direct_selectors == []
    return {"status": "EXACT_INPUT_BINDING_PASS", "working_states": 215,
            "rows": 430, "changed_rows": 4, "native_halt": 254,
            "dense_halt": 215, "sha256": PINS,
            "coq_table_matches_literal_machine": True,
            "coq_patch_matches_literal_candidate": True,
            "dense_relabeling_matches": True,
            "single_existing_literal_selector": direct_selectors}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate-table", action="store_true")
    args = parser.parse_args()
    print(json.dumps(check(args.generate_table), indent=2))
