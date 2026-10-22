#!/usr/bin/env python3
"""Independent finite audit of the delivered fixed70 packet.

This reads the emitted JSON, rather than importing its author's construction
or verifier.  The mathematical sign/rank argument is in FIXED70_REVIEW.md.
Finite arithmetic checks do not prove the consistency equivalence.
"""
from __future__ import annotations

from collections import Counter
from hashlib import sha256
from pathlib import Path
from random import Random
import json

HERE = Path(__file__).resolve().parent
ARTIFACTS = HERE.parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical_hash(value):
    return sha256(json.dumps(value, sort_keys=True,
                             separators=(",", ":")).encode()).hexdigest()


def circuit_audit():
    receipt = json.loads((ARTIFACTS / "fixed_input.json").read_text())
    packet = next(p for p in receipt["packets"] if p["name"] == "fixed70")
    rows = packet["source"]
    expected_witnesses = {
        "Jrep", "F", "alpha", "transport_quotient", "f", "h", "i",
        "auxiliary_quotient", "s", "w", "tau_root", "eta", "zeta",
        "y_aux", "Z", "gamma",
    }
    require(set(packet["witnesses"]) == expected_witnesses,
            "wrong witness set")
    require(packet["fixed_numerals"] == ["Bm1", "Kconstant", "MC", "MF", "W0"],
            "wrong fixed numeral ports")
    known = set(packet["witnesses"] + packet["fixed_numerals"])
    dependencies, operators = {}, Counter()
    for name, op, left, right in rows:
        require(name not in known and op in {"+", "-", "*"}, "malformed SSA row")
        require(all(type(x) is int or x in known for x in (left, right)),
                "forward or undefined reference")
        dependencies[name] = {x for x in (left, right) if type(x) is str}
        operators[op] += 1
        known.add(name)
    live, queue = {packet["output"]}, [packet["output"]]
    while queue:
        for item in dependencies.get(queue.pop(), ()):
            if item not in live:
                live.add(item)
                queue.append(item)
    require(live == known, "dead gate or port")
    require(len(rows) == 70 and operators["*"] == 40, "wrong operation count")
    require(operators["+"] + operators["-"] == 30, "wrong additive count")

    # Independently written mathematical definitions of all seven factors.
    # Test signed values as well as positive ones; no compiler semantics are
    # claimed for these deliberately small, arbitrary coefficient values.
    rng = Random(70215)
    checks = 0
    for signed in (False, True):
        for _ in range(32):
            low = -7 if signed else 1
            v = {p: rng.randrange(low, 10)
                 for p in packet["witnesses"] + packet["fixed_numerals"]}
            computed = dict(v)
            for name, op, left, right in rows:
                x = left if type(left) is int else computed[left]
                y = right if type(right) is int else computed[right]
                computed[name] = x*y if op == "*" else x+y if op == "+" else x-y
            C = v["Z"] + v["W0"]
            q = C + v["F"] + v["alpha"]
            e = v["Bm1"] * v["Jrep"]
            X, Y = v["w"] * q*q, v["s"] * q*q*q
            E = X*Y
            k = v["eta"] + v["zeta"]
            c = k*Y + v["eta"]
            a = E + Y
            Delta = a*a + 4*a + 3
            D = X + a*c + v["gamma"]*(4*a+3)
            L = X*Y*Y*k
            gap = e*(q-v["F"]) + q-v["F"]-v["Z"]
            R = gap*(q*q-1) + (v["MC"]+q*v["MF"])*v["Jrep"]
            V = c*(v["auxiliary_quotient"]*v["f"]-1)-R*v["f"]**2
            Kaux = Delta**2 * v["i"]**2 * c**4
            norms = {
                "norm_first": v["tau_root"]**2 - L*(L+k),
                "norm_main": D*D-Delta*c*c,
                "norm_repunit": q-e,
                "norm_aux": Kaux*(V*V-v["y_aux"]**2)+v["y_aux"]**2,
                "norm_index": k-v["h"]*E-R,
                "norm_transport": (v["Kconstant"]+v["w"])*C
                                  + q-v["F"]-v["transport_quotient"]*e,
                "norm_strong": Delta*(v["f"]**2-Delta*v["i"]**2*c**4),
            }
            for name, value in norms.items():
                require(computed[name] == value, "factor transcription: " + name)
            product = 1
            for value in norms.values():
                product *= value
            require(computed[packet["output"]] == product-Delta,
                    "complete polynomial transcription")
            require(computed["wn2"] == X and computed["r_lhs"] == R,
                    "quadratic scale or reused repunit transcription")
            checks += 1
    return {
        "source_sha256": canonical_hash(rows),
        "instructions": len(rows), "multiplications": operators["*"],
        "additions_and_subtractions": operators["+"]+operators["-"],
        "positive_integer_witnesses": len(expected_witnesses),
        "all_rows_and_ports_live": True,
        "independent_complete_formula_fixtures": checks,
        "fixture_scope": "Signed and positive arithmetic only; not halting witnesses.",
    }


def normalization_audit():
    directory = ARTIFACTS / "compiler"
    original_bytes = (directory / "k215.tm").read_bytes()
    require(sha256(original_bytes).hexdigest()
            == "fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090",
            "K215 table pin")
    old = {}
    for line in original_bytes.decode().splitlines():
        if line and not line.startswith("#"):
            q, read, write, direction, target = line.split()
            old[int(q), int(read)] = int(target), int(write), {"L": -1, "R": 1}[direction]
    data = json.loads((directory / "normalized_machine.json").read_text())
    table = {(q, read): (target, write, move)
             for q, read, target, write, move in data["transitions"]}
    require(len(table) == 4350, "normalized table size")
    require(set(table) == {(q, a) for q in range(435) for a in range(10)},
            "normalized transition domain")
    ordinary = {(0, 0): 0, (0, 1): 3, (1, 0): 4, (1, 1): 5}
    origin = {(p, n): 6+2*p+n for p in (0, 1) for n in (0, 1)}
    step_checks = 0
    for q in range(215):
        for side in (0, 1):
            for position in (0, -1, -3):
                for p in (0, 1):
                    for n in (0, 1):
                        coding = origin if position == 0 else ordinary
                        symbol = coding[p, n]
                        virtual = -position if side == 0 else position-1
                        target, write, motion = old[q, p if side == 0 else n]
                        virtual_after = virtual+motion
                        physical_after = -virtual_after if virtual_after >= 0 else virtual_after+1
                        side_after = int(virtual_after < 0)
                        pair_after = (write, n) if side == 0 else (p, write)
                        expected = (
                            4 if target == 215 else 5+2*target+side_after,
                            coding[pair_after], physical_after-position,
                        )
                        require(table[5+2*q+side, symbol] == expected,
                                "fold simulation row")
                        step_checks += 1
    for a in range(10):
        require(table[3, a] == (3, a, 0) and table[4, a] == (4, a, 0),
                "trap/halt absorption")
    # The distinguished input, including a direct check that no head goes right.
    tape = {p: 1 for p in range(-3, 1)}
    q, head = 0, 0
    for _ in range(10):
        q, write, motion = table[q, tape.get(head, 0)]
        tape[head] = write
        head += motion
        require(head <= 0, "loader crossed the origin")
    require((q, head, tape[0]) == (5, 0, 6), "fixed-input loader endpoint")
    require(all(a == 0 for p, a in tape.items() if p != 0), "loader erasure")
    return {"source_rows": len(old), "normalized_rows": len(table),
            "independent_fold_position_and_symbol_checks": step_checks,
            "fixed_four_one_loader_steps": 10,
            "fixed_loader_endpoint_checked": True,
            "scope": "Local finite table checks; global equivalence uses the induction proof."}


def main():
    report = {"status": "PASS", "circuit": circuit_audit(),
              "normalization": normalization_audit(),
              "proof_boundary": "No proof-assistant build, giant coefficient expansion, or consistency decision."}
    path = HERE / "independent_review.json"
    path.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
