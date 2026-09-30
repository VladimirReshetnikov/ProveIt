#!/usr/bin/env python3
"""Exact counter-machine / contraction / Diophantine compiler.

Python 3.10+, standard library only. No floating-point arithmetic is used.
Run: python verify_contraction.py --self-test --out verification
A supplied program is a JSON list of instructions; the final one must be halt.
  {"op":"inc", "counter":1, "next":0}
  {"op":"dec", "counter":2, "zero":2, "positive":0}
  {"op":"jump", "next":0}
  {"op":"halt"}
The exported polynomial is a sum of squared quadratic residuals, not a
claimed fixed-arity universal polynomial. All witness variables are natural.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import json
from math import lcm
from pathlib import Path
import random
from typing import Any

Vector = tuple[Q, Q, Q, Q]
DEMO = [dict(op="dec", counter=1, zero=2, positive=1),
        dict(op="inc", counter=2, next=0), dict(op="halt")]


def validate(program: list[dict[str, Any]]) -> None:
    if not isinstance(program, list) or len(program) < 2:
        raise ValueError("A program must have at least two instructions.")
    n = len(program) - 1
    for j, ins in enumerate(program):
        if not isinstance(ins, dict):
            raise ValueError(f"Instruction {j} must be an object.")
        op = ins.get("op")
        if op not in {"inc", "dec", "jump", "halt"}:
            raise ValueError(f"Invalid instruction {j}: {ins}")
        if (j == n) != (op == "halt"):
            raise ValueError("Only the final instruction must be halt.")
        if op in {"inc", "dec"} and (type(ins.get("counter")) is not int
                                       or ins["counter"] not in (1, 2)):
            raise ValueError("Counter must be 1 or 2.")
        keys = ("next",) if op in {"inc", "jump"} else (
            ("zero", "positive") if op == "dec" else ())
        for key in keys:
            if type(ins.get(key)) is not int or not 0 <= ins[key] <= n:
                raise ValueError(f"Invalid destination in instruction {j}.")


def constants(program: list[dict[str, Any]]) -> tuple[int, int, int, int]:
    n = len(program) - 1
    L = max(2*n + 1, 4)
    B, K = 2*L, 2*n
    return L, B, K, B*K


def step(program: list[dict[str, Any]], state: tuple[int, int, int]
         ) -> tuple[int, int, int]:
    j, c1, c2 = state
    c = [c1, c2]
    ins = program[j]
    if ins["op"] == "halt":
        return state
    if ins["op"] == "jump":
        return ins["next"], c1, c2
    i = ins["counter"] - 1
    if ins["op"] == "inc":
        c[i] += 1
        j = ins["next"]
    elif c[i] == 0:
        j = ins["zero"]
    else:
        c[i] -= 1
        j = ins["positive"]
    return j, c[0], c[1]


def encode(program: list[dict[str, Any]], state: tuple[int, int, int],
           radius: Q = Q(1)) -> Vector:
    j, a, b = state
    if not (0 <= j < len(program) and a >= 0 and b >= 0 and radius >= 0):
        raise ValueError("Invalid state or radius.")
    return (radius*Q(j, len(program)-1), radius*Q(1, 2**a),
            radius*Q(1, 2**b), radius)


def retract(y: Vector) -> Vector:
    y = tuple(Q(v) for v in y)  # Normalize integer inputs as well as Fractions.
    r = max(Q(0), y[3])
    return (min(max(Q(0), y[0]), r), min(max(Q(0), y[1]), r),
            min(max(Q(0), y[2]), r), r)


def H(program: list[dict[str, Any]], y: Vector) -> Vector:
    s, x1, x2, r = y
    if not (r >= 0 and all(0 <= v <= r for v in y[:3])):
        raise ValueError("H requires a point of the nonnegative cone.")
    n = len(program)-1
    out = [Q(0)]*3
    for j, ins in enumerate(program):
        theta = max(Q(0), r-abs(n*s-j*r))
        v = [Q(0), x1, x2]
        op = ins["op"]
        if op == "halt":
            v[0] = r
        elif op == "jump":
            v[0] = Q(ins["next"], n)*r
        elif op == "inc":
            v[0] = Q(ins["next"], n)*r
            v[ins["counter"]] /= 2
        else:
            i = ins["counter"]
            bump = max(Q(0), 2*y[i]-r)
            v[0] = (ins["positive"]*r +
                    (ins["zero"]-ins["positive"])*bump)/n
            v[i] = min(2*y[i], r)
        out = [max(out[a], min(theta, v[a])) for a in range(3)]
    return out[0], out[1], out[2], r


def F(program: list[dict[str, Any]], y: Vector) -> Vector:
    B = constants(program)[1]
    return tuple(v/B for v in H(program, retract(y)))  # type: ignore[return-value]


def ell(program: list[dict[str, Any]], y: tuple) -> Any:
    n = len(program)-1
    return 2*n*y[0]-(2*n-1)*y[3]


def norm(y: tuple) -> Any:
    return max(abs(v) for v in y)


def point_reachable(program: list[dict[str, Any]], y: Vector, z: Vector) -> bool:
    """Total exact decision procedure, including points outside the cone."""
    if y == z:
        return True
    y = F(program, y)
    if z != retract(z):
        return False
    r, s = y[3], z[3]
    if r == 0:
        return z == (0, 0, 0, 0)
    if s <= 0 or s > r:
        return False
    B = constants(program)[1]
    t = 0
    while r > s:
        r /= B
        t += 1
    if r != s:
        return False
    for _ in range(t):
        y = F(program, y)
    return y == z


def peak_prefix(program: list[dict[str, Any]], y: Vector, T: int) -> tuple[Q, Q]:
    """Return exact lower/upper bounds on the peak, on the compact cone."""
    if T < 1 or y != retract(y) or y[3] > 1:
        raise ValueError("Need T>=1 and a point of the compact cone.")
    B, radius = constants(program)[1], y[3]
    peak = Q(0)
    for _ in range(T):
        peak = max(peak, ell(program, y))
        y = F(program, y)
    return peak, max(peak, radius / B**T)


@dataclass
class Lin:
    """An integer linear form in inputs and previous positive gate wires."""
    terms: dict[int, int]

    def __add__(self, other: Lin) -> Lin:
        terms = dict(self.terms)
        for i, c in other.terms.items():
            terms[i] = terms.get(i, 0) + c
        return Lin({i: c for i, c in terms.items() if c})

    def __neg__(self) -> Lin:
        return Lin({i: -c for i, c in self.terms.items()})

    def __sub__(self, other: Lin) -> Lin:
        return self + (-other)

    def __mul__(self, k: int) -> Lin:
        if type(k) is not int:
            raise TypeError("Circuit coefficients must be integers.")
        return Lin({i: c*k for i, c in self.terms.items() if c*k})

    __rmul__ = __mul__

    def value(self, values: list[int]) -> int:
        return sum(c*values[i] for i, c in self.terms.items())


class Circuit:
    def __init__(self) -> None:
        self.gates: list[Lin] = []
        self.outputs: list[Lin] = []

    def relu(self, a: Lin) -> Lin:
        i = 4+len(self.gates)
        self.gates.append(a)
        return Lin({i: 1})

    def abs(self, a: Lin) -> Lin:
        return self.relu(a)+self.relu(-a)

    def min(self, a: Lin, b: Lin) -> Lin:
        return a-self.relu(a-b)

    def max(self, a: Lin, b: Lin) -> Lin:
        return b+self.relu(a-b)

    def evaluate(self, inputs: tuple[int, int, int, int]
                 ) -> tuple[tuple[int, ...], list[tuple[int, int]]]:
        values = list(inputs)
        witnesses = []
        for pre in self.gates:
            v = pre.value(values)
            y, z = max(v, 0), max(-v, 0)
            witnesses.append((y, z))
            values.append(y)
        return tuple(out.value(values) for out in self.outputs), witnesses

    def as_json(self) -> dict:
        return {"input_count": 4, "gates": [g.terms for g in self.gates],
                "outputs": [g.terms for g in self.outputs]}


def compile_integer(program: list[dict[str, Any]]) -> Circuit:
    """Compile S=K H, equal to D F on the cone, without rational coefficients."""
    validate(program)
    n, K = len(program)-1, constants(program)[2]
    c = Circuit()
    w = [Lin({i: 1}) for i in range(4)]
    s, x1, x2, r = w
    acc = None
    for j, ins in enumerate(program):
        theta = K*c.relu(r-c.abs(n*s-j*r))
        v = [Lin({}), K*x1, K*x2]
        op = ins["op"]
        if op == "halt":
            v[0] = K*r
        elif op == "jump":
            v[0] = 2*ins["next"]*r
        elif op == "inc":
            v[0] = 2*ins["next"]*r
            v[ins["counter"]] = n*w[ins["counter"]]
        else:
            i = ins["counter"]
            bump = c.relu(2*w[i]-r)
            v[0] = 2*ins["positive"]*r + 2*(ins["zero"]-ins["positive"])*bump
            v[i] = K*c.min(2*w[i], r)
        clipped = [c.min(theta, vi) for vi in v]
        acc = clipped if acc is None else [c.max(a, b) for a, b in zip(acc, clipped)]
    assert acc is not None
    c.outputs = acc+[K*r]
    return c


# Sparse polynomials: monomials are sorted tuples of variable indices;
# the empty tuple is the constant monomial. Integers are exact coefficients.
Poly = dict[tuple[int, ...], int]


def clean(p: Poly) -> Poly:
    return {m: c for m, c in p.items() if c}


def add_term(p: Poly, monomial: tuple[int, ...], coeff: int) -> None:
    p[monomial] = p.get(monomial, 0)+coeff


def poly_value(p: Poly, values: list[int]) -> int:
    total = 0
    for monomial, coeff in p.items():
        term = coeff
        for i in monomial:
            term *= values[i]
        total += term
    return total


def squared_sum(equations: list[Poly]) -> Poly:
    result: Poly = {}
    for eq in equations:
        for a, ca in eq.items():
            for b, cb in eq.items():
                add_term(result, tuple(sorted(a+b)), ca*cb)
    return clean(result)


def poly_json(p: Poly) -> list:
    return [[c, list(m)] for m, c in sorted(p.items(), key=lambda t: (len(t[0]), t[0]))]


def first_hit_certificate(program: list[dict[str, Any]], W0: tuple[int, ...], T: int
                          ) -> tuple[list[Poly], list[int], dict]:
    """Construct a canonical first-hit certificate; reject if the trace is not one.

    Four free input variables come first. All remaining variables are natural
    witnesses. Equations and the assignment are separately exported.
    """
    if T < 0 or len(W0) != 4 or any(type(x) is not int for x in W0):
        raise ValueError("Need a natural horizon and four integer coordinates.")
    if not (W0[3] >= 0 and all(0 <= x <= W0[3] for x in W0[:3])):
        raise ValueError("W0 must be in the integer cone.")
    c = compile_integer(program)
    values = list(W0)
    equations: list[Poly] = []
    states = [list(range(4))]
    for _ in range(T):
        inputs = states[-1]
        actual = tuple(values[i] for i in inputs)
        outputs, witnesses = c.evaluate(actual)
        wiring = list(inputs)
        for pre, (y, z) in zip(c.gates, witnesses):
            yi, zi = len(values), len(values)+1
            values.extend([y, z])
            eq: Poly = {(yi,): 1, (zi,): -1}
            for local, coeff in pre.terms.items():
                add_term(eq, (wiring[local],), -coeff)
            equations.extend([clean(eq), {(yi, zi): 1}])
            wiring.append(yi)
        indices = []
        for out, val in zip(c.outputs, outputs):
            idx = len(values)
            values.append(val)
            indices.append(idx)
            eq = {(idx,): 1}
            for local, coeff in out.terms.items():
                add_term(eq, (wiring[local],), -coeff)
            equations.append(clean(eq))
        states.append(indices)
    n = len(program)-1
    for t, ids in enumerate(states):
        sig = ell(program, tuple(values[i] for i in ids))
        slack = sig-1 if t == T else -sig
        if slack < 0:
            raise ValueError(f"The supplied trace does not first hit at T={T}.")
        idx = len(values)
        values.append(slack)
        eq = {(ids[0],): 2*n, (ids[3],): -(2*n-1),
              (idx,): -1 if t == T else 1}
        if t == T:
            eq[()] = -1
        equations.append(clean(eq))
    assert all(x >= 0 for x in values)
    assert all(poly_value(e, values) == 0 for e in equations)
    return equations, values, {"free_input_count": 4, "horizon": T,
        "gate_count_per_step": len(c.gates), "state_variable_indices": states,
        "witness_count": len(values)-4, "equation_count": len(equations)}


def run_tests() -> dict:
    counts: dict[str, Any] = {}
    local = 0
    for m in range(2, 5):
        n = m-1
        options = [dict(op="inc", counter=i, next=k)
                   for i in (1, 2) for k in range(m)]
        options += [dict(op="dec", counter=i, zero=z, positive=p)
                    for i in (1, 2) for z in range(m) for p in range(m)]
        options += [dict(op="jump", next=k) for k in range(m)]
        for j in range(n):
            for ins in options:
                program = [dict(op="jump", next=0) for _ in range(n)]+[dict(op="halt")]
                program[j] = ins
                circuit = compile_integer(program)
                L, B, K, D = constants(program)
                d = sum(i["op"] == "dec" for i in program)
                assert len(circuit.gates) == 9*m+2*d-3
                for a, b in product(range(5), repeat=2):
                    y = encode(program, (j, a, b))
                    want = encode(program, step(program, (j, a, b)), Q(1, B))
                    assert F(program, y) == want
                    den = lcm(*(v.denominator for v in y))
                    w = tuple(int(v*den) for v in y)
                    out, _ = circuit.evaluate(w)
                    assert tuple(Q(v, den*D) for v in out) == want
                    local += 1
    counts["instruction_and_integer_lift_cases"] = local
    rng = random.Random(20260930)
    ratios = []
    for _ in range(1000):
        m = rng.randrange(2, 8)
        program = []
        for _j in range(m-1):
            if rng.randrange(2):
                program.append(dict(op="inc", counter=rng.choice((1, 2)), next=rng.randrange(m)))
            else:
                program.append(dict(op="dec", counter=rng.choice((1, 2)),
                                    zero=rng.randrange(m), positive=rng.randrange(m)))
        program.append(dict(op="halt"))
        y = tuple(Q(rng.randrange(-20, 40), rng.randrange(1, 12)) for _ in range(4))
        z = tuple(Q(rng.randrange(-20, 40), rng.randrange(1, 12)) for _ in range(4))
        Fy, Fz = F(program, y), F(program, z)
        distance = norm(tuple(a-b for a, b in zip(y, z)))
        delta = norm(tuple(a-b for a, b in zip(Fy, Fz)))
        assert 2*delta <= distance
        if distance:
            ratios.append(delta/distance)
        lam = Q(rng.randrange(8), 3)
        assert F(program, tuple(lam*a for a in y)) == tuple(lam*a for a in Fy)
        cone = retract(y)
        den = lcm(*(v.denominator for v in cone))
        w = tuple(int(v*den) for v in cone)
        out, _ = compile_integer(program).evaluate(w)
        D = constants(program)[3]
        assert tuple(Q(v, den*D) for v in out) == F(program, cone)
    counts["global_lipschitz_homogeneity_random_cases"] = 1000
    counts["largest_sampled_Lipschitz_ratio"] = str(max(ratios))
    gate = 0
    for v in range(-10, 11):
        solutions = [(y, z) for y in range(12) for z in range(12)
                     if y-z == v and y*z == 0]
        assert solutions == [(max(v, 0), max(-v, 0))]
        gate += 1
    counts["exhaustive_single_gate_preactivations"] = gate
    y = encode(DEMO, (0, 3, 1))
    original, state = y, (0, 3, 1)
    for t in range(15):
        assert y == encode(DEMO, state, Q(1, 10**t))
        assert point_reachable(DEMO, original, y)
        assert not point_reachable(DEMO, original, (y[0]+y[3], y[1], y[2], y[3]))
        state, y = step(DEMO, state), F(DEMO, y)
    assert not point_reachable(DEMO, original, (Q(0),)*4)
    assert point_reachable(DEMO, (Q(1), Q(2), Q(3), Q(-1)), (Q(0),)*4)
    assert point_reachable(DEMO, original, original)
    assert peak_prefix(DEMO, original, 9) == (Q(1, 10**7), Q(1, 10**7))
    counts["trajectory_steps_checked"] = 15
    instant_eqs, instant_vals, instant_meta = first_hit_certificate(DEMO, (8, 8, 8, 8), 0)
    assert len(instant_eqs) == 1 and instant_meta["witness_count"] == 1
    assert poly_value(instant_eqs[0], instant_vals) == 0
    assert point_reachable(DEMO, (Q(0),)*4, (Q(0),)*4)
    assert F(DEMO, (0, 1, 1, 1)) == F(DEMO, tuple(map(Q, (0, 1, 1, 1))))
    counts["zero_time_and_integer_input_edge_checks"] = 4
    eqs, values, meta = first_hit_certificate(DEMO, (0, 1, 4, 8), 7)
    poly = squared_sum(eqs)
    assert poly_value(poly, values) == 0
    assert max(map(len, poly)) == 4
    for i in range(4, len(values)):
        changed = list(values)
        changed[i] += 1
        r = sum(poly_value(e, changed)**2 for e in eqs)
        assert r > 0
        # Check the independently expanded polynomial on selected mutations.
        if i % 31 == 0:
            assert poly_value(poly, changed) == r
    counts["single_witness_mutations_rejected"] = len(values)-4
    counts["demo_certificate"] = dict(meta, expanded_quartic_terms=len(poly))
    for t in range(10):
        if t != 7:
            try:
                first_hit_certificate(DEMO, (0, 1, 4, 8), t)
            except ValueError:
                pass
            else:
                raise AssertionError("Accepted an incorrect first-hit horizon.")
    counts["wrong_first_hit_horizons_rejected"] = 9
    counts["status"] = "PASS: all exact checks completed; finite tests are not a proof of universality."
    return counts


def write_json(path: Path, data: Any) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True)+"\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--program", type=Path, help="Program JSON; default is the transfer example.")
    parser.add_argument("--counter1", type=int, default=3)
    parser.add_argument("--counter2", type=int, default=1)
    parser.add_argument("--steps", type=int, default=7, help="Claimed first-hit time.")
    parser.add_argument("--out", type=Path, default=Path("verification"))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if min(args.counter1, args.counter2, args.steps) < 0:
        parser.error("Counters and horizon must be nonnegative.")
    program = json.loads(args.program.read_text()) if args.program else DEMO
    validate(program)
    args.out.mkdir(parents=True, exist_ok=True)
    if args.self_test:
        report = run_tests()
        write_json(args.out/"test_report.json", report)
        print(json.dumps(report, indent=2))
    y = encode(program, (0, args.counter1, args.counter2))
    denominator = lcm(*(v.denominator for v in y))
    w = tuple(int(v*denominator) for v in y)
    equations, values, metadata = first_hit_certificate(program, w, args.steps)
    quartic = squared_sum(equations)
    metadata.update(dict(program=program, initial_denominator=denominator,
        constants=dict(zip(("L", "B", "K", "D"), constants(program))),
        polynomial_degree=max(map(len, quartic), default=0),
        expanded_quartic_terms=len(quartic), all_variables_domain="natural numbers"))
    write_json(args.out/"example_program.json", program)
    write_json(args.out/"integer_circuit.json", compile_integer(program).as_json())
    write_json(args.out/"certificate_system.json", dict(metadata=metadata,
        equations=[poly_json(e) for e in equations]))
    write_json(args.out/"certificate_assignment.json", values)
    write_json(args.out/"expanded_quartic.json", dict(metadata=metadata,
        terms=poly_json(quartic)))
    trace = []
    state = (0, args.counter1, args.counter2)
    point = y
    for t in range(args.steps+1):
        trace.append(dict(t=t, state=list(state), point=list(map(str, point)),
                          signal=str(ell(program, point))))
        state, point = step(program, state), F(program, point)
    write_json(args.out/"example_trace.json", trace)
    print(f"Exported {len(equations)} equations and a {len(quartic)}-term quartic to {args.out}")


if __name__ == "__main__":
    main()
