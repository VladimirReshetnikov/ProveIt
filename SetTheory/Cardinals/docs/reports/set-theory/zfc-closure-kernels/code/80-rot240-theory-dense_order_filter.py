#!/usr/bin/env python3
"""Exact first-order model filter for the membership structure (Q>=0, <).

This is an infinite-model decision procedure, not a finite-domain approximation.
Each quantified variable ranges over one representative from every orbit under
order automorphisms fixing the currently assigned free variables.  The proof
of the orbit lemma and the uniform Collection argument is in dense_order.tex.

The executable regressions are finite QA.  The proof that every weak-Collection
instance holds is the explicit-automorphism proof, not the test corpus.
Python 3.10+, standard library only; assertions must remain enabled.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
import json
from pathlib import Path
from typing import Iterable


# Immutable named-variable syntax.  Equality is actual equality of rationals.
Formula = tuple


def mem(x: int, y: int) -> Formula:
    return ("mem", x, y)


def eq(x: int, y: int) -> Formula:
    return ("eq", x, y)


def neg(p: Formula) -> Formula:
    return ("not", p)


def conj(*ps: Formula) -> Formula:
    if not ps:
        return ("true",)
    out = ps[0]
    for p in ps[1:]:
        out = ("and", out, p)
    return out


def disj(p: Formula, q: Formula) -> Formula:
    return ("or", p, q)


def imp(p: Formula, q: Formula) -> Formula:
    return ("imp", p, q)


def iff(p: Formula, q: Formula) -> Formula:
    return ("iff", p, q)


def all_(x: int, p: Formula) -> Formula:
    return ("all", x, p)


def ex(x: int, p: Formula) -> Formula:
    return ("ex", x, p)


def close_all(xs: Iterable[int], p: Formula) -> Formula:
    for x in reversed(tuple(xs)):
        p = all_(x, p)
    return p


@lru_cache(None)
def free(p: Formula) -> frozenset[int]:
    op = p[0]
    if op in ("mem", "eq"):
        return frozenset(p[1:])
    if op == "true":
        return frozenset()
    if op == "not":
        return free(p[1])
    if op in ("all", "ex"):
        return free(p[2]) - {p[1]}
    if op in ("and", "or", "imp", "iff"):
        return free(p[1]) | free(p[2])
    raise ValueError(f"Unknown formula constructor: {op}")


def representatives(values: Iterable[Q]) -> tuple[Q, ...]:
    """One point per orbit of Q>=0 fixing values and the definable minimum 0."""
    points = sorted({Q(0), *values})
    if points[0] < 0:
        raise ValueError("Assignments must lie in Q>=0")
    out: list[Q] = []
    for i, a in enumerate(points):
        out.append(a)
        if i + 1 < len(points):
            out.append((a + points[i + 1]) / 2)
    out.append(points[-1] + 1)
    return tuple(out)


def canonical_assignment(p: Formula, env: dict[int, Q]) -> tuple[tuple[int, Q], ...]:
    """Canonical order type, including the distinguished minimum 0.

    Replacing a tuple by its rank-preserving rational tuple is an automorphism
    reduction, not an approximation.  Positive values receive ranks 1,2,... .
    """
    variables = sorted(free(p))
    missing = set(variables) - env.keys()
    if missing:
        raise ValueError(f"Unassigned free variables: {sorted(missing)}")
    vals = {env[v] for v in variables}
    if any(v < 0 for v in vals):
        raise ValueError("Assignments must lie in Q>=0")
    positive = sorted(v for v in vals if v != 0)
    rank = {Q(0): Q(0), **{v: Q(i + 1) for i, v in enumerate(positive)}}
    return tuple((v, rank[env[v]]) for v in variables)


def truth(p: Formula, env: dict[int, Q] | None = None) -> bool:
    env = {} if env is None else env
    return _truth(p, canonical_assignment(p, env))


@lru_cache(None)
def _truth(p: Formula, assignment: tuple[tuple[int, Q], ...]) -> bool:
    env = dict(assignment)
    op = p[0]
    if op == "true":
        return True
    if op == "mem":
        return env[p[1]] < env[p[2]]
    if op == "eq":
        return env[p[1]] == env[p[2]]
    if op == "not":
        return not truth(p[1], env)
    if op == "and":
        return truth(p[1], env) and truth(p[2], env)
    if op == "or":
        return truth(p[1], env) or truth(p[2], env)
    if op == "imp":
        return not truth(p[1], env) or truth(p[2], env)
    if op == "iff":
        return truth(p[1], env) == truth(p[2], env)
    if op in ("all", "ex"):
        x, body = p[1:]
        outcomes = (truth(body, {**env, x: q}) for q in representatives(env.values()))
        return all(outcomes) if op == "all" else any(outcomes)
    raise ValueError(f"Unknown formula constructor: {op}")


def subset(x: int, y: int, z: int = 20) -> Formula:
    assert z not in (x, y)
    return all_(z, imp(mem(z, x), mem(z, y)))


def empty(x: int, z: int = 20) -> Formula:
    assert z != x
    return all_(z, neg(mem(z, x)))


def weak_collection(phi: Formula, parameters: tuple[int, ...] = ()) -> Formula:
    """Inputs x=0, y=1; B=2, C=3 must be fresh for phi.

    Uses the same guarded existential form as the original GIC first conjunct,
    modulo pure first-order equivalence.  All parameter values are quantified.
    """
    assert not (free(phi) & {2, 3})
    assert free(phi) <= {0, 1, *parameters}
    cover = all_(0, imp(mem(0, 2), imp(ex(1, phi), ex(1, conj(phi, mem(1, 3))))))
    return close_all(parameters, all_(2, ex(3, cover)))


def global_image_collection(phi: Formula, parameters: tuple[int, ...] = ()) -> Formula:
    assert not (free(phi) & {2, 3})
    assert free(phi) <= {0, 1, *parameters}
    cover = all_(0, imp(mem(0, 2), imp(ex(1, phi), ex(1, conj(phi, mem(1, 3))))))
    support = all_(1, imp(mem(1, 3), ex(0, phi)))
    return close_all(parameters, all_(2, ex(3, conj(cover, support))))


def separation(psi: Formula, parameters: tuple[int, ...] = ()) -> Formula:
    # Free separated element 0; bounding and output sets 2,3 are fresh.
    assert free(psi) <= {0, *parameters}
    return close_all(parameters, all_(2, ex(3, all_(0, iff(mem(0, 3), conj(mem(0, 2), psi))))))


def axioms() -> dict[str, Formula]:
    # Names p=0,V=1,x=2,W=3,z=4,t=5.
    cp = all_(0, ex(1, conj(mem(0, 1), all_(2, imp(mem(2, 1), conj(
        subset(2, 1, 5),
        ex(3, conj(mem(3, 1), all_(4, imp(subset(4, 2, 5), mem(4, 3))))),
    ))))))
    ext = close_all((0, 1), imp(all_(2, iff(mem(2, 0), mem(2, 1))), eq(0, 1)))
    union = all_(0, ex(1, all_(2, iff(mem(2, 1), ex(3, conj(mem(3, 0), mem(2, 3)))))))
    foundation = all_(0, imp(ex(1, mem(1, 0)), ex(1, conj(mem(1, 0), all_(2, neg(conj(mem(2, 1), mem(2, 0))))))))
    pairing = close_all((0, 1), ex(2, all_(3, iff(mem(3, 2), disj(eq(3, 0), eq(3, 1))))))
    power = all_(0, ex(1, all_(2, iff(mem(2, 1), subset(2, 0, 3)))))
    # Ordinary ZF-style Infinity, using exact empty and exact successor.
    successor = all_(4, iff(mem(4, 3), disj(mem(4, 2), eq(4, 2))))
    infinity = ex(0, conj(ex(1, conj(mem(1, 0), empty(1, 4))), all_(2, imp(mem(2, 0), ex(3, conj(mem(3, 0), successor))))))
    return {
        "CP": cp,
        "Extensionality": ext,
        "Empty": ex(0, empty(0, 1)),
        "Union": union,
        "Foundation": foundation,
        "Irreflexivity": all_(0, neg(mem(0, 0))),
        "Transitive_membership": close_all((0, 1, 2), imp(conj(mem(0, 1), mem(1, 2)), mem(0, 2))),
        "Pairing": pairing,
        "Power_Set": power,
        "Infinity": infinity,
        "Separation_empty_objects": separation(empty(0, 1)),
        "GIC_empty_outputs": global_image_collection(empty(1, 4)),
        "WeakCollection_empty_outputs": weak_collection(empty(1, 4)),
    }


def shrink_automorphism(t: Q, m: Q, old_witness: Q) -> Q:
    """Automorphism fixing [0,m], sending old_witness>m to m+1/2."""
    assert m >= 0 and old_witness > m and t >= 0
    return t if t <= m else m + (t - m) / (2 * (old_witness - m))


def inverse_shrink(t: Q, m: Q, old_witness: Q) -> Q:
    assert m >= 0 and old_witness > m and t >= 0
    return t if t <= m else m + 2 * (old_witness - m) * (t - m)


def run() -> dict:
    if not __debug__:
        raise RuntimeError("Run with assertions enabled (do not use python -O).")
    expected_true = {"CP", "Extensionality", "Empty", "Union", "Foundation", "Irreflexivity", "Transitive_membership", "WeakCollection_empty_outputs"}
    results = {name: truth(phi) for name, phi in axioms().items()}
    assert {name for name, value in results.items() if value} == expected_true

    # Full first-order LC instances, including parameters, alternate quantifiers,
    # nonfunctional fibers, and equality.  The uniform theorem is in the paper.
    samples = {
        "true": (("true",), ()),
        "false": (neg(("true",)), ()),
        "identity": (eq(0, 1), ()),
        "increasing": (mem(0, 1), ()),
        "decreasing": (mem(1, 0), ()),
        "above_parameter": (mem(4, 1), (4,)),
        "between_two_parameters": (conj(mem(4, 1), mem(1, 5)), (4, 5)),
        "input_output_parameter_interleaving": (conj(mem(0, 1), mem(1, 4)), (4,)),
        "empty_outputs": (empty(1, 6), ()),
        "no_common_strict_lower_bound": (all_(6, neg(conj(mem(6, 0), mem(6, 1)))), ()),
        "dense_interval": (ex(6, conj(mem(0, 6), mem(6, 1))), ()),
        "quantifier_alternation": (all_(6, imp(mem(6, 0), ex(7, conj(mem(6, 7), mem(7, 1))))), ()),
        "parameterized_quantifier_alternation": (all_(6, imp(conj(mem(4, 6), mem(6, 0)), ex(7, conj(mem(6, 7), mem(7, 1))))), (4,)),
    }
    lc_results = {name: truth(weak_collection(phi, params)) for name, (phi, params) in samples.items()}
    assert all(lc_results.values())

    # Regression for genuine surjectivity, not merely an order embedding.
    grid = tuple(sorted({Q(a, b) for a in range(13) for b in range(1, 6)}))
    auto_cases = 0
    for m in (Q(0), Q(1, 3), Q(2), Q(7, 2)):
        for old_witness in (m + Q(1, 7), m + 1, m + 19):
            assert shrink_automorphism(old_witness, m, old_witness) == m + Q(1, 2)
            transformed = [shrink_automorphism(t, m, old_witness) for t in grid]
            assert all(a < b for a, b in zip(transformed, transformed[1:]))
            for t in grid:
                assert inverse_shrink(shrink_automorphism(t, m, old_witness), m, old_witness) == t
                assert shrink_automorphism(inverse_shrink(t, m, old_witness), m, old_witness) == t
                if t <= m:
                    assert shrink_automorphism(t, m, old_witness) == t
                auto_cases += 1

    return {
        "status": "PASS",
        "model": "domain=nonnegative rationals; membership=strict rational order; equality=identity",
        "semantics": "Exact infinite-model evaluation by finite automorphism orbits; no finite-domain cutoff",
        "axiom_results": results,
        "weak_collection_sample_results": lc_results,
        "automorphism_point_regressions": auto_cases,
        "formula_cache": _truth.cache_info()._asdict(),
        "scope": "Every weak-Collection instance is covered by the ordinary uniform automorphism proof; the sample corpus does not prove that theorem. No binary TM or state saving is claimed.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--formula", type=Path, help="Optional JSON formula to evaluate exactly; nested lists use the constructors documented in this file")
    args = parser.parse_args()
    if args.formula:
        def freeze(x):
            return tuple(map(freeze, x)) if isinstance(x, list) else x
        phi = freeze(json.loads(args.formula.read_text()))
        result = {"formula": phi, "truth_in_nonnegative_rational_membership": truth(phi)}
    else:
        result = run()
    data = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(data)
    print(data, end="")


if __name__ == "__main__":
    main()
