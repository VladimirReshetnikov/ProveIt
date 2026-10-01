#!/usr/bin/env python3
"""Deterministic finite tests of the compiler and certificate construction.

These tests supplement, and do not replace, the mathematical proofs.
Run from the package root: python code/verify.py --output verification/results.json
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import random
from reaction_compiler import (Instruction, Machine, Poly, compile_machine, universal_machine,
    doubling_machine, initial_polynomials, trace_certificate, trace_assignment,
    minimum_certificate, zero_residuals)


def compare_prefix(machine: Machine, counters: list[int], fuel: int, steps: int) -> int:
    net = compile_machine(machine)
    x = net.initial(counters, fuel)
    state, cs, f = machine.start, counters[:], fuel
    storage = sum(cs) + f
    checked = 0
    for _ in range(steps):
        assert net.invariant(x, storage)
        assert x[f"Q_{state}"] == 1 and x["Z"] == 2
        assert [x[f"C{j}"] for j in range(machine.registers)] == cs and x["F"] == f
        ins = machine.instructions[state]
        if ins.op == "halt":
            assert not net.choices(x)
            break
        if ins.op == "inc" and f == 0:
            assert not net.choices(x)
            break
        if ins.op == "inc":
            cs[ins.register] += 1
            f -= 1
            state = ins.positive
            length = 1
        else:
            if cs[ins.register] > 0:
                cs[ins.register] -= 1
                f += 1
                state = ins.positive
            else:
                state = ins.zero
            length = 3
        for _ in range(length):
            y, chosen = net.step(x)
            assert chosen is not None
            assert net.invariant(y, storage)
            assert sum(y.values()) == storage + 3
            x = y
            checked += 1
    return checked


def run_tests() -> dict:
    rng = random.Random(20260930)
    result: dict[str, object] = {"seed": 20260930, "status": "PASS"}
    x, z, b = (Poly.var(v) for v in ("x", "z", "b"))
    zp = zero_residuals(x, z, b)
    zero_checks = 0
    for a in range(13):
        solutions = []
        for zz in range(4):
            for bb in range(16):
                assignment = {"x": a, "z": zz, "b": bb}
                if all(p.evaluate(assignment) == 0 for p in zp):
                    solutions.append((zz, bb))
                zero_checks += 1
        assert solutions == [(int(a == 0), max(0, a - 1))]
    result["zero_gadget_assignments"] = zero_checks

    I = Instruction
    microsteps = 0
    local_cases = 0
    for register in (0, 1):
        machines = [Machine(2, {"0": I("inc", register, "H"), "H": I("halt")}, "0"),
                    Machine(2, {"0": I("dec", register, "1", "H"),
                                "1": I("inc", 1 - register, "H"), "H": I("halt")}, "0")]
        for m in machines:
            for a in range(5):
                for c in range(5):
                    for f in range(6):
                        microsteps += compare_prefix(m, [a, c], f, 5)
                        local_cases += 1
    result["exhaustive_local_cases"] = local_cases

    random_cases = 0
    for _ in range(250):
        labels = [str(i) for i in range(5)] + ["H"]
        instructions = {"H": I("halt")}
        for label in labels[:-1]:
            instructions[label] = I(rng.choice(["inc", "dec"]), rng.randrange(2),
                                    rng.choice(labels), rng.choice(labels))
        machine = Machine(2, instructions, "0")
        for _ in range(4):
            cs = [rng.randrange(5), rng.randrange(5)]
            f = rng.randrange(8)
            microsteps += compare_prefix(machine, cs, f, 80)
            random_cases += 1
    result["random_machine_input_cases"] = random_cases
    universal = universal_machine()
    netu = compile_machine(universal)
    assert len(netu.species) == 61 and len(netu.reactions) == 62
    assert sum(r.priority == 0 for r in netu.reactions) == 1
    assert netu.phase_count() == 62
    u_cases = 0
    for e in range(5):
        for a in range(5):
            for f in range(5):
                cs = [0] * 8
                cs[1], cs[2] = e, a
                microsteps += compare_prefix(universal, cs, f, 100)
                u_cases += 1
    result["universal_prefix_cases"] = u_cases
    result["checked_reaction_microsteps"] = microsteps

    toy = compile_machine(doubling_machine())
    n, fuel = Poly.var("n"), Poly.var("f")
    cert_cases = 0
    for a in range(7):
        T = 5 * a + 3
        cert = trace_certificate(toy, initial_polynomials(toy, [n, 0], fuel), T)
        for f in range(9):
            assignment = {"n": a, "f": f,
                          **trace_assignment(toy, toy.initial([a, 0], f), T)}
            value = cert.value(assignment)
            assert (value == 0) == (f >= a)
            if f >= a:
                assert assignment[f"t_x_{T}_C0"] == 0
                assert assignment[f"t_x_{T}_C1"] == 2 * a
                assert assignment[f"t_x_{T}_F"] == f - a
            cert_cases += 1
    result["doubling_threshold_certificate_cases"] = cert_cases

    cert = trace_certificate(toy, initial_polynomials(toy, [n, 0], fuel), 8)
    assignment = {"n": 1, "f": 1, **trace_assignment(toy, toy.initial([1, 0], 1), 8)}
    polynomial = cert.expanded()
    assert polynomial.degree() == 4
    for _ in range(10):
        test = {key: rng.randrange(4) for key in assignment}
        assert polynomial.evaluate(test) == cert.value(test)
    for variable in cert.witnesses:
        changed = assignment.copy()
        changed[variable] += 1
        assert cert.value(changed) > 0
    result["single_coordinate_mutations_rejected"] = len(cert.witnesses)
    result["expanded_polynomial_random_equality_tests"] = 10
    result["expanded_quartic_monomials"] = len(polynomial.terms)

    # A source program that never halts for a positive first counter.
    bad_source = Machine(1, {"0": I("dec", 0, "1", "H"),
                             "1": I("inc", 0, "1"), "H": I("halt")}, "0")
    bad = compile_machine(bad_source)
    by_name = {r.name: i for i, r in enumerate(bad.reactions)}
    forced = [by_name["enter_0"], by_name["fallback"], by_name["zero_0"]]
    initial = bad.initial([1], 0)
    bad_cert = trace_certificate(bad, {s: value for s, value in initial.items()}, 3)
    spurious = trace_assignment(bad, initial, 3, forced=forced)
    violations = bad_cert.violations(spurious)
    assert len(violations) == 1
    assert next(iter(violations)).startswith("t:priority:")
    assert bad_cert.value(spurious) == 1
    result["false_zero_branch_polynomial_value"] = 1
    result["false_zero_branch_violation"] = violations

    minimum_cases = 0
    for limit in range(4):
        T = toy.horizon(limit)
        mcert = minimum_certificate(toy, [n, 0], fuel, n + fuel, limit)
        for a in range(limit + 1):
            for f in range(limit - a + 1):
                pred = max(f - 1, 0)
                values = {"n": a, "f": f, "df": int(f == 0), "bf": pred,
                          "slack": limit - a - f,
                          **trace_assignment(toy, toy.initial([a, 0], f), T, "u"),
                          **trace_assignment(toy, toy.initial([a, 0], pred), T, "v")}
                assert (mcert.value(values) == 0) == (f == a)
                if f == a:
                    assert max(values[w] for w in mcert.witnesses) <= max(limit, 2)
                minimum_cases += 1
    result["bounded_minimum_fuel_cases"] = minimum_cases
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification/results.json"))
    args = parser.parse_args()
    results = run_tests()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
