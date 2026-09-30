#!/usr/bin/env python3
"""Exact finite checks for Finite Resonance Control of Nonlinear Hahn--Dulac Transseries.

These tests check polynomial recurrences and illustrative inequalities, not the
infinite-support theorems. No network access is used. Run with Python 3.10+,
SymPy, and mpmath. Output is written to build/results.json (ed. 2026-09-29; as
delivered it was written beside this program, over the recorded results.json).
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse  # ed. (2026-09-29): --output / --overwrite-recorded
import json
import platform
import random
from typing import Sequence

import sympy as sp
import mpmath as mp

L = sp.Symbol("L")
ZERO = sp.Poly(0, L, domain="EX")
ONE = sp.Poly(1, L, domain="EX")


def poly(x=0) -> sp.Poly:
    return x if isinstance(x, sp.Poly) else sp.Poly(x, L, domain="EX")


def same(a, b) -> bool:
    return sp.expand(poly(a).as_expr() - poly(b).as_expr()) == 0


@dataclass(frozen=True)
class Block:
    eigenvalue: sp.Rational
    size: int = 1

    def __post_init__(self):
        if self.size < 1:
            raise ValueError("A Jordan block must have positive size")


def solve_block(q: Sequence[sp.Poly], gamma, block: Block,
                constant: Sequence | None = None) -> list[sp.Poly]:
    """Solve (d/dL + gamma I - J)P=Q for a standard Jordan block J.

    At resonance, prescribe P(0)=constant. Otherwise take the unique
    polynomial solution, obtained by descending back substitution.
    """
    n = block.size
    if len(q) != n:
        raise ValueError("Block dimension mismatch")
    q = [poly(p) for p in q]
    c = list(constant) if constant is not None else [0] * n
    if len(c) != n:
        raise ValueError("Wrong number of resonant constants")
    a = sp.Rational(gamma) - block.eigenvalue
    out = [ZERO] * n
    for i in range(n - 1, -1, -1):
        rhs = q[i] + (out[i + 1] if i + 1 < n else ZERO)
        if a == 0:
            primitive = rhs.integrate()
            out[i] = primitive + poly(c[i] - primitive.eval(0))
        else:
            p, term, j = ZERO, rhs, 0
            while not term.is_zero:
                p += term.mul_ground((-1) ** j / a ** (j + 1))
                term = term.diff()
                j += 1
            out[i] = p
    return out


def convolution(a: dict, b: dict, cutoff) -> dict:
    out = {}
    for u, p in a.items():
        for v, q in b.items():
            if u + v <= cutoff:
                out[u + v] = out.get(u + v, ZERO) + p * q
    return {g: p for g, p in out.items() if not p.is_zero}


def rhs_coefficient(gamma, coefficients: dict, terms: list, dimension: int):
    """A term is (source_action, multiindex, vector_coefficient)."""
    out = [ZERO] * dimension
    coordinate = [
        {g: p[j] for g, p in coefficients.items() if not p[j].is_zero}
        for j in range(dimension)
    ]
    for alpha, powers, vector in terms:
        target = gamma - alpha
        if target < 0:
            continue
        acc = {sp.Rational(0): ONE}
        for j, power in enumerate(powers):
            for _ in range(power):
                acc = convolution(acc, coordinate[j], target)
                if not acc:
                    break
        p = acc.get(target, ZERO)
        if not p.is_zero:
            for j, c in enumerate(vector):
                if c != 0:
                    out[j] += p.mul_ground(c)
    return out


def solve(actions: Sequence, blocks: Sequence[Block], terms: list,
          constants: dict | None = None) -> dict:
    """Compute exact coefficients on a finite, convolution-complete prefix.

    The caller must supply every semigroup action up to the largest target
    (or a divisor-closed target set). Arbitrary missing actions are not safe.
    """
    dimension = sum(b.size for b in blocks)
    constants = constants or {}
    terms = [(sp.Rational(a), tuple(k), list(v)) for a, k, v in terms]
    for a, k, v in terms:
        if a < 0 or len(k) != dimension or len(v) != dimension:
            raise ValueError("Invalid source term")
        if a == 0 and sum(k) < 2 and any(v):
            raise ValueError("The constant and linear zero-action terms are forbidden")
    result = {}
    for gamma in sorted(set(map(sp.Rational, actions))):
        if gamma <= 0:
            raise ValueError("Actions must be positive")
        rhs = rhs_coefficient(gamma, result, terms, dimension)
        values, start = [], 0
        for bi, block in enumerate(blocks):
            q = rhs[start:start + block.size]
            c = constants.get(bi) if gamma == block.eigenvalue else None
            values += solve_block(q, gamma, block, c)
            start += block.size
        result[gamma] = values
    return result


def residual_count(solution: dict, blocks: Sequence[Block], terms: list) -> int:
    n, count = sum(b.size for b in blocks), 0
    for gamma, p in solution.items():
        rhs = rhs_coefficient(gamma, solution, terms, n)
        start = 0
        for block in blocks:
            for j in range(block.size):
                i = start + j
                lhs = p[i].diff() + p[i].mul_ground(gamma - block.eigenvalue)
                if j + 1 < block.size:
                    lhs -= p[i + 1]
                assert same(lhs, rhs[i]), (gamma, i, lhs, rhs[i])
                count += 1
            start += block.size
    return count


def degree(p: Sequence[sp.Poly]) -> int:
    return max([0] + [int(q.degree()) for q in p if not q.is_zero])


def slope(solution: dict) -> sp.Rational:
    return max([sp.Rational(0)] + [sp.Rational(degree(p)) / g for g, p in solution.items()])


def resonance_slope(solution: dict, blocks: Sequence[Block]):
    resonances = {b.eigenvalue for b in blocks if b.eigenvalue in solution}
    return max([sp.Rational(0)] + [sp.Rational(degree(solution[g])) / g for g in resonances])


def main() -> None:
    # ed. (2026-09-29): the default output is build/results.json beside verification/;
    # writing the recorded verification/results.json needs --overwrite-recorded.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "build" / "results.json")
    parser.add_argument("--overwrite-recorded", action="store_true",
                        help="allow writing the recorded verification/results.json")
    args = parser.parse_args()
    recorded = Path(__file__).resolve().with_name("results.json")
    if args.output.resolve() == recorded and not args.overwrite_recorded:
        parser.error("refusing to overwrite the recorded verification/results.json; "
                     "pass --overwrite-recorded or choose another --output")
    if not __debug__:
        raise RuntimeError("Run without -O: verification requires enabled assertions")
    rng = random.Random(20260929)
    counts = {"block_equations": 0, "system_coefficient_equations": 0,
              "random_systems": 0, "random_slope_identities": 0,
              "closed_form_coefficients": 0, "divisor_prefixes": 0,
              "numerical_tail_bounds": 0}
    records = []

    # Independent scalar/Jordan coefficient identities, including negative gaps.
    for size in range(1, 5):
        block = Block(sp.Rational(2), size)
        for a in [sp.Rational(-3), sp.Rational(-1, 3), 0, sp.Rational(1, 7), 3]:
            for d in [0, 1, 3, 6]:
                q = [poly(sum(rng.randint(-3, 3) * L ** k for k in range(d + 1)))
                     for _ in range(size)]
                constants = [rng.randint(-2, 2) for _ in range(size)]
                p = solve_block(q, 2 + a, block, constants)
                for j in range(size):
                    lhs = p[j].diff() + p[j].mul_ground(a)
                    if j + 1 < size:
                        lhs -= p[j + 1]
                    assert same(lhs, q[j])
                    if a == 0:
                        assert p[j].eval(0) == constants[j]
                    counts["block_equations"] += 1

    # An exactly soluble nonlinear equation with unbounded logarithmic degree.
    blocks = [Block(sp.Rational(1))]
    terms = [(1, (0,), [1]), (0, (2,), [1]),
             (1, (1,), [2]), (1, (2,), [1])]
    c = sp.Rational(2, 3)
    sol = solve(range(1, 17), blocks, terms, {0: [c]})
    for n, p in sol.items():
        assert same(p[0], (L + c) ** n)
        counts["closed_form_coefficients"] += 1
    counts["system_coefficient_equations"] += residual_count(sol, blocks, terms)
    assert slope(sol) == resonance_slope(sol, blocks) == 1
    records.append({"example": "geometric nonlinear feedback", "orders": 16, "slope": "1"})

    # Cancellation-sensitive algebraic log-free locus.
    a, c, d = sp.symbols("a c d")
    blocks = [Block(sp.Rational(1)), Block(sp.Rational(2))]
    terms = [(0, (2, 0), [0, 1]), (2, (0, 0), [0, a])]
    sol = solve(range(1, 7), blocks, terms, {0: [c], 1: [d]})
    assert same(sol[1][0], c)
    assert same(sol[2][1], d + (c ** 2 + a) * L)
    counts["system_coefficient_equations"] += residual_count(sol, blocks, terms)
    records.append({"example": "algebraic cancellation", "obstruction": "c**2+a"})

    # A cascade: P_j = L^(2j-1)/(2j-1)!!.
    dim = 6
    blocks = [Block(sp.Rational(j)) for j in range(1, dim + 1)]
    vec = [1] + [0] * (dim - 1)
    terms = [(1, (0,) * dim, vec)]
    for j in range(1, dim):
        powers = [0] * dim
        powers[0] += 1
        powers[j - 1] += 1
        vec = [0] * dim
        vec[j] = 1
        terms.append((0, tuple(powers), vec))
    sol = solve(range(1, dim + 2), blocks, terms)
    for j in range(1, dim + 1):
        assert same(sol[j][j - 1], L ** (2 * j - 1) / sp.factorial2(2 * j - 1))
        counts["closed_form_coefficients"] += 1
    counts["system_coefficient_equations"] += residual_count(sol, blocks, terms)
    assert slope(sol) == resonance_slope(sol, blocks) == sp.Rational(11, 6)
    records.append({"example": "six-stage cascade", "slope": "11/6"})

    # Nilpotent and nonlinear resonances interact; the sharp slope is 5/2.
    blocks = [Block(sp.Rational(1), 2), Block(sp.Rational(2))]
    terms = [(1, (0, 0, 0), [0, 1, 0]), (0, (2, 0, 0), [0, 0, 1])]
    sol = solve(range(1, 7), blocks, terms)
    assert same(sol[1][0], L ** 2 / 2)
    assert same(sol[1][1], L)
    assert same(sol[2][2], L ** 5 / 20)
    counts["system_coefficient_equations"] += residual_count(sol, blocks, terms)
    assert slope(sol) == resonance_slope(sol, blocks) == sp.Rational(5, 2)
    records.append({"example": "Jordan/nonlinear resonance", "slope": "5/2"})

    # Random coupled systems, finite rational grids, no positivity assumptions.
    for case in range(16):
        blocks = ([Block(sp.Rational(1), 2)] if case % 4 == 0
                  else [Block(sp.Rational(1)), Block(sp.Rational(2))])
        dim = 2
        terms = []
        for alpha, powers in [(1, (0, 0)), (2, (0, 0)), (3, (0, 0)),
                              (1, (1, 0)), (1, (0, 1)),
                              (0, (2, 0)), (0, (1, 1)), (0, (0, 2))]:
            terms.append((alpha, powers, [sp.Rational(rng.randint(-2, 2), 3)
                                          for _ in range(dim)]))
        constants = {bi: [sp.Rational(rng.randint(-2, 2), 2)
                          for _ in range(block.size)]
                     for bi, block in enumerate(blocks)}
        sol = solve(range(1, 9), blocks, terms, constants)
        counts["system_coefficient_equations"] += residual_count(sol, blocks, terms)
        assert slope(sol) == resonance_slope(sol, blocks)
        counts["random_systems"] += 1
        counts["random_slope_identities"] += 1
        # Perturb only above the last resonance; the certificate must not move.
        perturb = terms + [(5, (0, 0), [sp.Rational(7), sp.Rational(-11)])]
        changed = solve(range(1, 9), blocks, perturb, constants)
        for b in blocks:
            assert all(same(p, q) for p, q in zip(sol[b.eigenvalue], changed[b.eigenvalue]))
        assert resonance_slope(sol, blocks) == resonance_slope(changed, blocks)

    # Increasing finite prefixes of the accumulating semigroup below action 2.
    # Products of positive actions are >=2, and only 1+1=2.
    aa, bb, cc, kk = sp.symbols("a b c k")
    for nmax in [3, 6, 12, 24]:
        actions = sorted({sp.Rational(1), sp.Rational(2)} |
                         {sp.Rational(2) - sp.Rational(1, n) for n in range(2, nmax + 1)})
        full = set(actions) | {sp.Rational(0)}
        divisors = {g for g in full if 2 - g in full}
        assert divisors == {0, 1, 2}
        terms = [(1, (0,), [aa]), (2, (0,), [bb]), (0, (2,), [cc])]
        terms += [(2 - sp.Rational(1, n), (0,), [sp.Rational(1, n ** 3)])
                  for n in range(2, nmax + 1)]
        sol = solve(actions, [Block(sp.Rational(2))], terms, {0: [kk]})
        assert same(sol[1][0], -aa)
        assert same(sol[2][0], kk + (bb + cc * aa ** 2) * L)
        for n in range(2, nmax + 1):
            assert same(sol[2 - sp.Rational(1, n)][0], -sp.Rational(1, n ** 2))
        counts["system_coefficient_equations"] += residual_count(sol, [Block(sp.Rational(2))], terms)
        counts["divisor_prefixes"] += 1

    # High-precision illustration of the proved action-tail bound.
    mp.mp.dps = 80
    radius, T = mp.mpf("0.05"), mp.mpf(8)
    norm = radius * T / (1 - radius * T)  # Exact l1 norm for c=0.
    numerical = []
    for xstr in ["0.001", "0.005", "0.01", "0.03"]:
        x = mp.mpf(xstr)
        t = x * mp.log(x)
        q = x / radius * max(mp.mpf(1), abs(mp.log(x)) / T)
        for n in [4, 8, 12]:
            error = abs(t ** (n + 1) / (1 - t))
            bound = norm * q ** (n + 1)
            assert error <= bound
            numerical.append({"x": xstr, "last_action": n,
                              "actual_error": mp.nstr(error, 14),
                              "proved_bound": mp.nstr(bound, 14)})
            counts["numerical_tail_bounds"] += 1

    output = {"status": "all checks passed", "seed": 20260929,
              "python": platform.python_version(), "sympy": sp.__version__,
              "mpmath": mp.__version__, "counts": counts, "examples": records,
              "tail_bound_illustrations": numerical,
              "scope": "Exact finite identities plus floating-point illustrations; not a proof assistant or interval certificate."}
    path = args.output
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({"status": output["status"], "counts": counts}, indent=2))


if __name__ == "__main__":
    main()
