#!/usr/bin/env python3
"""Reproduce the pure-subset seeded-BIC reduction's finite and syntax checks.

Standard library only; run `python kernel_reduction.py --out results.json`.
This is not a proof assistant or a Turing-machine verifier.

Attribution: ProveIt b07d1a27bbe2814f2fd84cc55feef71c4de5b2db,
SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/article.tex.
The node basis and expansion policy match 02-seeded-formulas.py. The
switching relation and constant-class lemma are inherited; their use to
delete the membership arm is the new reduction. The factored spelling was
already present in 01-bic-bic.py.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import random
from typing import Any

F = tuple[Any, ...]


def atom(kind: str, x: str, y: str) -> F:
    return (kind, x, y)


def mem(x: str, y: str) -> F:
    return atom("in", x, y)


def eq(x: str, y: str) -> F:
    return atom("eq", x, y)


def hole(x: str, y: str) -> F:
    return atom("hole", x, y)


BOT: F = ("bot",)


def imp(p: F, q: F) -> F:
    return ("imp", p, q)


def all_(x: str, p: F) -> F:
    return ("all", x, p)


def alls(xs: list[str], p: F) -> F:
    for x in reversed(xs):
        p = all_(x, p)
    return p


def neg(p: F) -> F:
    return imp(p, BOT)


def ex(x: str, p: F) -> F:
    return neg(all_(x, neg(p)))


def and_(p: F, q: F) -> F:
    return neg(imp(p, neg(q)))


def or_(p: F, q: F) -> F:
    return imp(neg(p), q)


def iff(p: F, q: F) -> F:
    return and_(imp(p, q), imp(q, p))


def sub(x: str, y: str, z: str = "z") -> F:
    return all_(z, imp(mem(z, x), mem(z, y)))


def counts(f: F) -> Counter[str]:
    result: Counter[str] = Counter()
    def walk(p: F) -> None:
        result[p[0]] += 1
        if p[0] == "imp":
            walk(p[1]); walk(p[2])
        elif p[0] == "all":
            walk(p[2])
    walk(f)
    return result


def templates() -> dict[str, F]:
    profile = all_("z", iff(mem("z", "x"), mem("z", "y")))
    ext = alls(["x", "y"], imp(profile, eq("x", "y")))
    ec = alls(["x", "y"], imp(profile,
        all_("w", iff(mem("x", "w"), mem("y", "w")))))
    cp = all_("p", ex("V", and_(mem("p", "V"),
        all_("x", imp(mem("x", "V"), and_(sub("x", "V"),
        ex("W", and_(mem("W", "V"), all_("z",
        imp(sub("z", "x", "u"), mem("z", "W")))))))))))
    support = all_("y", imp(mem("y", "C"), ex("x", hole("x", "y"))))
    gic = all_("B", ex("C", and_(all_("x", imp(mem("x", "B"),
        all_("y", imp(hole("x", "y"), ex("v", and_(
        hole("x", "v"), mem("v", "C"))))))), support)))
    result = {"Ext": ext, "EC": ec, "CP": cp, "GIC": gic}
    for kernel in ("mixed", "subset"):
        bound = sub("y", "b")
        if kernel == "mixed":
            bound = or_(mem("y", "b"), bound)
        premise = all_("x", ex("b", all_("y", imp(hole("x", "y"), bound))))
        for seed in ("point", "subset"):
            seed_test = eq("x", "a") if seed == "point" else sub("x", "a")
            active = or_(seed_test, mem("x", "C"))
            for spelling in ("source02", "factored"):
                if spelling == "source02":
                    closed = alls(["x", "y"], imp(and_(active, hole("x", "y")), mem("y", "C")))
                else:
                    closed = all_("x", imp(active, all_("y", imp(hole("x", "y"), mem("y", "C")))))
                result[f"{kernel}_{seed}_{spelling}"] = imp(premise,
                    all_("a", ex("C", and_(closed, support))))
    return result


def metric_audit(ts: dict[str, F]) -> dict[str, Any]:
    details = {k: dict(counts(v)) for k, v in ts.items()}
    nodes = {k: sum(v.values()) for k, v in details.items()}
    totals: dict[str, int] = {"RCC": nodes["CP"] + nodes["GIC"]}
    for kernel in ("mixed", "subset"):
        for spelling in ("source02", "factored"):
            for name, control, seed in (("point", "Ext", "point"),
                ("subset", "Ext", "subset"), ("equality_free_subset", "EC", "subset")):
                totals[f"{kernel}_{name}_{spelling}"] = nodes[control] + nodes[f"{kernel}_{seed}_{spelling}"]
    expected = {
        "RCC": 80,
        "mixed_point_source02": 69, "mixed_subset_source02": 72,
        "mixed_equality_free_subset_source02": 83,
        "subset_point_source02": 65, "subset_subset_source02": 68,
        "subset_equality_free_subset_source02": 79,
        "mixed_point_factored": 65, "mixed_subset_factored": 68,
        "mixed_equality_free_subset_factored": 79,
        "subset_point_factored": 61, "subset_subset_factored": 64,
        "subset_equality_free_subset_factored": 75,
    }
    assert totals == expected, (totals, expected)
    return {"basis": ["in", "eq", "bot", "imp", "all"],
        "hole_policy": "One atom for each occurrence; arbitrary matrix payload excluded.",
        "excluded": ["variable payloads", "arbitrary parameter closure", "logical proof engine", "TM backend"],
        "theory_nodes": totals, "template_nodes": nodes, "constructors": details}


def evaluate(f: F, n: int, membership: int, relation: int,
             env: dict[str, int] | None = None) -> bool:
    env = {} if env is None else env
    op = f[0]
    if op == "bot":
        return False
    if op == "in" or op == "hole":
        bits = membership if op == "in" else relation
        return bool(bits & (1 << (env[f[1]] * n + env[f[2]])))
    if op == "eq":
        return env[f[1]] == env[f[2]]
    if op == "imp":
        return not evaluate(f[1], n, membership, relation, env) or evaluate(f[2], n, membership, relation, env)
    if op == "all":
        return all(evaluate(f[2], n, membership, relation, dict(env, **{f[1]: x})) for x in range(n))
    raise ValueError(f"unknown operator {op}")


def formula_audit(ts: dict[str, F]) -> dict[str, int]:
    comparisons = 0
    for n in (1, 2):
        for membership in range(1 << (n*n)):
            for relation in range(1 << (n*n)):
                for kernel in ("mixed", "subset"):
                    for seed in ("point", "subset"):
                        p = ts[f"{kernel}_{seed}_source02"]
                        q = ts[f"{kernel}_{seed}_factored"]
                        assert evaluate(p, n, membership, relation) == evaluate(q, n, membership, relation)
                        comparisons += 1
    rng = random.Random(20261016)
    for _ in range(128):
        n = 3
        membership, relation = rng.randrange(1 << 9), rng.randrange(1 << 9)
        for kernel in ("mixed", "subset"):
            for seed in ("point", "subset"):
                p, q = (ts[f"{kernel}_{seed}_{s}"] for s in ("source02", "factored"))
                assert evaluate(p, n, membership, relation) == evaluate(q, n, membership, relation)
                comparisons += 1
    return {"factoring_semantics_comparisons": comparisons, "random_seed": 20261016}


def members(x: int) -> list[int]:
    return [i for i in range(x.bit_length()) if x & (1 << i)]


def subsets(x: int) -> list[int]:
    result, y = [0], x
    while y:
        result.append(y)
        y = (y-1) & x
    return result


def switch_outputs(x: int) -> list[int]:
    if x and not x & (x-1):
        return [x.bit_length()-1]
    return subsets(x)


def positive_hull(seed_inputs: list[int]) -> set[int]:
    output: set[int] = set()
    todo: list[int] = []
    for x in seed_inputs:
        for y in switch_outputs(x):
            if y not in output:
                output.add(y); todo.append(y)
    while todo:
        x = todo.pop()
        for y in switch_outputs(x):
            if y not in output:
                output.add(y); todo.append(y)
    return output


def hull_audit(limit: int) -> dict[str, int]:
    local_outputs = container_members = mixed_outputs = sep_outputs = union_outputs = 0
    for b in range(limit):
        local_bound = b.bit_length()-1 if b and not b & (b-1) else b
        for y in switch_outputs(b):
            assert y & ~local_bound == 0
            local_outputs += 1
        singleton_b = 1 << b
        point_container = positive_hull([singleton_b])
        subset_container = positive_hull(subsets(singleton_b))
        for container in (point_container, subset_container):
            assert b in container
            mask = sum(1 << x for x in container)
            for x in container:
                assert set(members(x)) <= container
                assert set(switch_outputs(x)) <= container
                container_members += 1
            for y in set(members(b)) | set(subsets(b)):
                assert y & ~mask == 0
                mixed_outputs += 1
            for y in members(b):
                assert y & ~mask == 0
                sep_outputs += 1
            union_b = 0
            for x in members(b):
                union_b |= x
            for y in members(union_b):
                assert y & ~mask == 0
                union_outputs += 1
    assert set(subsets(2)) == {0, 2} and 1 not in set(subsets(2))
    return {"HF_bounds_checked": limit, "seed_types": 2,
        "local_fiber_output_checks": local_outputs,
        "container_members_checked": container_members,
        "mixed_bound_output_checks": mixed_outputs,
        "separation_output_checks": sep_outputs, "union_output_checks": union_outputs}


def collision_audit() -> dict[str, Any]:
    # Directly transcribe the three-slot generated wrapper, then identify i=j.
    # A closed true matrix ensures the failure is independent of matrix binding.
    i, j, c = "v", "v", "c"
    true_matrix = imp(BOT, BOT)
    premise = all_(i, ex(c, all_(j, imp(true_matrix,
        all_(i, imp(mem(i, j), mem(i, c)))))))
    cases = {}
    for seed in ("point", "subset"):
        seed_test = eq(i, j) if seed == "point" else sub(i, j, c)
        closed = all_(i, imp(or_(seed_test, mem(i, c)),
            all_(j, imp(true_matrix, mem(j, c)))))
        support = all_(j, imp(mem(j, c), ex(i, true_matrix)))
        conclusion = all_(j, ex(c, and_(closed, support)))
        assert evaluate(premise, 1, 0, 0)
        assert not evaluate(conclusion, 1, 0, 0)
        assert not evaluate(imp(premise, conclusion), 1, 0, 0)
        cases[seed] = {"premise": True, "conclusion": False, "instance": False}
    return {"model": "one object with empty membership (satisfies IR)", "collided_slots": "i=j", "cases": cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path("kernel_reduction_results.json"))
    parser.add_argument("--hf-limit", type=int, default=4096)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError("Run without -O: assertions implement the regression checks.")
    if args.hf_limit < 1:
        parser.error("--hf-limit must be positive")
    ts = templates()
    result = {"status": "passed", "scope": "Syntax and finite regression evidence only; no infinite-schema proof certificate or TM certification.",
        "metrics": metric_audit(ts), "formula_regressions": formula_audit(ts),
        "switching_hulls": hull_audit(args.hf_limit), "collision": collision_audit()}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "metrics": result["metrics"]["theory_nodes"],
        "formula_regressions": result["formula_regressions"], "switching_hulls": result["switching_hulls"],
        "collision": result["collision"]}, indent=2))


if __name__ == "__main__":
    main()
