#!/usr/bin/env python3
"""Deterministic, exact-arithmetic checks; run from any directory."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
import sys

from neural_certificates import (
    RationalNetwork, Wire, clamp_value, clamp_witness, clip, compile_trace,
    projective_example, circuit_values, compactify_circuit,
    quadratic_relations_network, quartic_synthesis_certificate,
    stack_encode, stack_top, stack_pop, stack_push, common_denominator,
)

ROOT = Path(__file__).resolve().parents[1]
COUNTS: dict[str, int] = {}


def check(condition: bool, group: str) -> None:
    if not condition:
        raise AssertionError(f"Failed: {group}")
    COUNTS[group] = COUNTS.get(group, 0) + 1


def main() -> None:
    # Given y+z=D, the linear residual determines b=U+a-y.
    # This exhausts the declared finite box, not all possible natural values.
    for D in range(1, 10):
        for U in range(-2 * D, 3 * D + 1):
            canonical = clamp_witness(D, U)
            check(clamp_value(D, U, *canonical) == 0, "scalar canonical witnesses")
            for y in range(D + 1):
                for a in range(3 * D + 3):
                    b = U + a - y
                    if b >= 0:
                        candidate = (y, D - y, a, b)
                        check((clamp_value(D, U, *candidate) == 0) == (candidate == canonical),
                              "scalar finite-box uniqueness")

    rng = random.Random(20260930)
    mutated = 0
    for _ in range(240):
        n, T, B, D = rng.randint(1, 4), rng.randint(0, 8), rng.randint(1, 5), rng.randint(1, 8)
        A = tuple(tuple(rng.randint(-5, 5) for _ in range(n)) for _ in range(n))
        b = tuple(rng.randint(-3, 3) for _ in range(n))
        net = RationalNetwork(A, b, B)
        p = tuple(rng.randint(0, D) for _ in range(n))
        cert, witness, states = compile_trace(net, p, D, T)
        check(cert.evaluate(witness) == 0, "random trace zero")
        check(len(cert.variables) == 4 * n * T, "trace variable count")
        check(cert.polynomial().degree <= 2, "trace polynomial degree")
        check(cert.polynomial().evaluate(witness) == 0, "expanded trace polynomial")
        state = states[0]
        for t in range(T):
            state = net.step(state)
            check(state == states[t + 1], "independent Fraction simulation")
            check((D * B ** (t + 1)) % common_denominator(state) == 0,
                  "denominator divisibility")
        for name in cert.variables:
            changed = dict(witness)
            changed[name] += 1
            check(cert.evaluate(changed) > 0, "single-coordinate mutation rejected")
            mutated += 1
            if witness[name]:
                changed[name] = witness[name] - 1
                check(cert.evaluate(changed) > 0, "single-coordinate mutation rejected")
                mutated += 1

    net = RationalNetwork(((6,),), (-1,), 4)
    cert, witness, states = compile_trace(net, (3,), 5, 4, halt=0, first_hit=True)
    check(cert.evaluate(witness) == 0, "worked first-hit example")
    check([s[0] for s in states] == [F(3,5), F(13,20), F(29,40), F(67,80), F(1)],
          "worked trajectory")
    check(len(cert.variables) == 20, "worked variable count")
    bad, badw, _ = compile_trace(net, (3,), 5, 3, halt=0, first_hit=True)
    check(bad.evaluate(badw) > 0, "nonaccepting horizon rejected")
    (ROOT / "examples" / "fixed_trace.json").write_text(json.dumps({
        "network": {"A": [[6]], "b": [-1], "B": 4}, "initial": "3/5", "T": 4,
        "states": [[str(x) for x in state] for state in states],
        "certificate": cert.to_json(), "witness": witness, "value": cert.evaluate(witness)
    }, indent=2) + "\n")

    for Q in range(1, 73):
        pc, pw = projective_example(Q)
        check((pc.evaluate(pw) == 0) == (Q % 12 == 0), "projective example scales")
        check(pc.polynomial().degree == 2, "projective degree")
    pc, pw = projective_example()
    (ROOT / "examples" / "projective_trace.json").write_text(json.dumps({
        "certificate": pc.to_json(), "witness": pw, "value": pc.evaluate(pw)
    }, indent=2) + "\n")

    words = 0
    for length in range(9):
        for word in product((0, 1), repeat=length):
            x = stack_encode(word)
            check(stack_pop(x) == stack_encode(word[1:]), "stack pop")
            check(stack_top(x) == (word[0] if word else 0), "stack top")
            check(clip(4*x) == (1 if word else 0), "stack nonempty")
            for bit in (0, 1):
                check(stack_push(bit, x) == stack_encode((bit,) + word), "stack push")
            words += 1

    # Circuit computes x*y - 2. x=2, y=1 is a rational zero.
    wires = [Wire("x", "input"), Wire("y", "input"), Wire("c", "const", constant=2),
             Wire("m", "mul", ("x", "y")), Wire("out", "sub", ("m", "c"))]
    values = circuit_values(wires, {"x": F(2), "y": F(1)})
    params, relations = compactify_circuit(wires, "out")
    v = F(1, 4)
    theta = {"a_" + name: (1 + v * value) / 2 for name, value in values.items()}
    theta["v"] = v
    for r in relations:
        check(r.evaluate(theta) == 0, "compactified circuit equations")
    nn = quadratic_relations_network(params, relations)
    rational_states = nn.evaluate(theta)
    check(rational_states[nn.zero_output] == 0 and rational_states[nn.positive_output] > 0,
          "four-layer synthesis acceptance")
    product_count = len({m for r in relations for m in r.terms if len(m) == 2})
    check(len(nn.nodes) == 2 * len(params) + product_count + 2 * len(relations) + 3,
          "synthesis neuron count")
    check(max(node.layer for node in nn.nodes) == 4, "synthesis depth")
    qc, qw, Q, _ = quartic_synthesis_certificate(nn, theta)
    check(qc.evaluate(qw) == 0, "quartic synthesis witness")
    check(qc.polynomial().degree == 4, "quartic synthesis degree")
    check(qc.polynomial().evaluate(qw) == 0, "expanded quartic polynomial")
    for name in qc.variables:
        changed = dict(qw)
        changed[name] += 1
        check(qc.evaluate(changed) > 0, "quartic coordinate mutation rejected")
    for trial in range(60):
        random_theta = {name: F(rng.randint(0, 16), 16) for name in params}
        outs = nn.evaluate(random_theta)
        all_zero = all(r.evaluate(random_theta) == 0 for r in relations)
        check((outs[nn.zero_output] == 0) == all_zero, "synthesis residual detectors")
        check(outs[nn.positive_output] == random_theta["v"], "positive parameter output")
    (ROOT / "examples" / "rational_synthesis.json").write_text(json.dumps({
        "circuit": [dict(name=w.name, op=w.op, inputs=w.inputs, constant=w.constant) for w in wires],
        "wire_values": {k: str(vv) for k,vv in values.items()},
        "parameters": {k: str(vv) for k,vv in theta.items()},
        "relations": [r.json_terms() for r in relations],
        "neuron_count": len(nn.nodes), "layers": 4, "common_scale": Q,
        "outputs": {"zero": str(rational_states[nn.zero_output]),
                    "positive": str(rational_states[nn.positive_output])},
        "certificate": qc.to_json(), "witness": qw, "value": qc.evaluate(qw)
    }, indent=2) + "\n")

    # Validate prime-support counting inequality for a finite family.
    for primes in ((2,), (3,), (2, 3), (2, 3, 5)):
        for n in (1, 2, 3):
            for H in range(1, 71):
                smooth = []
                for q in range(1, H + 1):
                    z = q
                    for p in primes:
                        while z % p == 0:
                            z //= p
                    if z == 1:
                        smooth.append(q)
                count = sum((q+1)**n for q in smooth)
                factor = 1
                for p in primes[1:]:
                    power, choices = 1, 0
                    while power <= H:
                        choices += 1
                        power *= p
                    factor *= choices
                bound = F(2**n * H**n * factor, 1) / (1 - F(1, primes[0]**n))
                check(count <= bound, "prime-support precision bound")

    report = ["PRECISION IS MEMORY -- EXACT-ARITHMETIC VERIFICATION",
              "Seed: 20260930", f"Python: {sys.version.split()[0]}",
              "No external Python packages; no floating point; no SMT solver.",
              "", *[f"PASS  {name}: {count}" for name, count in COUNTS.items()],
              "", f"Total assertions: {sum(COUNTS.values())}",
              f"Binary words checked: {words}", f"Random trace instances: 240",
              f"Synthesis example: {len(nn.nodes)} neurons, {len(qc.variables)} witnesses, Q={Q}",
              "", "These finite tests check implementations and examples, not the general proofs.",
              "No Lean formalization was executed or supplied."]
    text = "\n".join(report) + "\n"
    (ROOT / "verification_report.txt").write_text(text)
    print(text)


if __name__ == "__main__":
    main()
