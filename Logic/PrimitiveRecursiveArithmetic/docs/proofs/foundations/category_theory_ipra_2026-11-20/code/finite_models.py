#!/usr/bin/env python3
"""Exact finite examples for Category Theory in iPRA.

This is an executable model and exhaustive bounded validation, not an iPRA
proof checker. Only Python's standard library is used. Maps [n] -> [m] are
tuples of n digits below m; their optional integer codes use base m+1.
Exponentials use increasing-code ranks of valid tables, so all empty cases
are included without a division-by-zero convention.
"""

from __future__ import annotations

import argparse
import json
from functools import lru_cache
from itertools import product
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def table_code(codomain: int, values: tuple[int, ...]) -> int:
    require(codomain >= 0, "negative cardinality")
    require(all(0 <= value < codomain for value in values), "invalid digit")
    base = codomain + 1
    return sum(value * base**i for i, value in enumerate(values))


def decode_table(domain: int, codomain: int, code: int) -> tuple[int, ...] | None:
    base = codomain + 1
    if not (domain >= 0 and codomain >= 0 and 0 <= code < base**domain):
        return None
    values = tuple((code // base**i) % base for i in range(domain))
    return values if all(value < codomain for value in values) else None


@lru_cache(maxsize=None)
def maps(domain: int, codomain: int) -> tuple[tuple[int, ...], ...]:
    require(domain >= 0 and codomain >= 0, "negative cardinality")
    return tuple(sorted(product(range(codomain), repeat=domain),
                        key=lambda values: table_code(codomain, values)))


def identity(n: int) -> tuple[int, ...]:
    return tuple(range(n))


def compose(g: tuple[int, ...], f: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(g[x] for x in f)


def product_pair(m: int, f: tuple[int, ...], g: tuple[int, ...]) -> tuple[int, ...]:
    require(len(f) == len(g), "incompatible domains")
    return tuple(m * x + y for x, y in zip(f, g))


def product_projections(n: int, m: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
    # The comprehension is empty when m=0, so neither operation divides by zero.
    return (tuple(q // m for q in range(n * m)),
            tuple(q % m for q in range(n * m)))


def evaluation(n: int, m: int) -> tuple[int, ...]:
    tables = maps(n, m)
    # Product encoding (rank, i) is n*rank+i, as in the report.
    return tuple(tables[rank][i] for rank in range(len(tables)) for i in range(n))


def curry(z: int, n: int, m: int, h: tuple[int, ...]) -> tuple[int, ...]:
    require(len(h) == z * n, "wrong uncurried domain")
    ranks = {table: i for i, table in enumerate(maps(n, m))}
    return tuple(ranks[tuple(h[n * t + i] for i in range(n))] for t in range(z))


def uncurry(z: int, n: int, m: int, u: tuple[int, ...]) -> tuple[int, ...]:
    require(len(u) == z, "wrong curried domain")
    tables = maps(n, m)
    return tuple(tables[u[t]][i] for t in range(z) for i in range(n))


def finite_limit(sizes: tuple[int, ...], edges: tuple[tuple[int, int, tuple[int, ...]], ...]):
    """Limit of a diagram presented by finitely many generating arrows."""
    tuples = tuple(xs for xs in product(*(range(n) for n in sizes))
                   if all(f[xs[i]] == xs[j] for i, j, f in edges))
    projections = tuple(tuple(xs[i] for xs in tuples) for i in range(len(sizes)))
    return tuples, projections


def finite_colimit(sizes: tuple[int, ...], edges: tuple[tuple[int, int, tuple[int, ...]], ...]):
    """Colimit by bounded Boolean transitive closure and least representatives."""
    offsets = [0]
    for n in sizes:
        offsets.append(offsets[-1] + n)
    total = offsets[-1]
    relation = [[i == j for j in range(total)] for i in range(total)]
    for i, j, f in edges:
        require(len(f) == sizes[i], "wrong edge domain")
        require(all(0 <= y < sizes[j] for y in f), "wrong edge codomain")
        for x, y in enumerate(f):
            a, b = offsets[i] + x, offsets[j] + y
            relation[a][b] = relation[b][a] = True
    # Separate matrices implement the literal primitive-recursive recurrence.
    for k in range(total):
        relation = [[relation[i][j] or (relation[i][k] and relation[k][j])
                     for j in range(total)] for i in range(total)]
    least = [next(j for j in range(total) if relation[i][j]) for i in range(total)]
    representatives = tuple(sorted(set(least)))
    rank = {r: j for j, r in enumerate(representatives)}
    injections = tuple(tuple(rank[least[offsets[i] + x]] for x in range(n))
                       for i, n in enumerate(sizes))
    return representatives, injections, relation


def test_table_codes(bound: int) -> dict:
    valid_count = invalid_count = 0
    for n, m in product(range(bound + 1), repeat=2):
        tables = maps(n, m)
        require(len(tables) == m**n, "table count, including 0^0")
        for code in range((m + 1)**n):
            table = decode_table(n, m, code)
            if table is None:
                invalid_count += 1
            else:
                require(table_code(m, table) == code, "code/decode round trip")
                require(table in tables, "missing valid table")
                valid_count += 1
        for table in tables:
            require(decode_table(n, m, table_code(m, table)) == table,
                    "decode/code round trip")
    return {"cardinality_bound": bound, "valid_codes": valid_count,
            "invalid_codes_rejected": invalid_count, "zero_power_zero": 0**0}


def test_products_and_exponentials(bound: int) -> dict:
    product_pairs = product_uniqueness = beta = eta = empty_cases = 0
    for n, m, z in product(range(bound + 1), repeat=3):
        p, q = product_projections(n, m)
        for f, g in product(maps(z, n), maps(z, m)):
            pair = product_pair(m, f, g)
            require(compose(p, pair) == f and compose(q, pair) == g, "product beta")
            product_pairs += 1
        for h in maps(z, n * m):
            require(product_pair(m, compose(p, h), compose(q, h)) == h, "product eta")
            product_uniqueness += 1
        exp_size = m**n
        require(len(maps(n, m)) == exp_size, "exponential rank cardinality")
        ev = evaluation(n, m)
        require(len(ev) == exp_size * n and all(v < m for v in ev), "evaluation typing")
        for h in maps(z * n, m):
            u = curry(z, n, m, h)
            require(all(rank < exp_size for rank in u), "curry typing")
            require(uncurry(z, n, m, u) == h, "exponential beta")
            # Evaluation is independently composed with u times the identity.
            paired = tuple(n * u[t] + i for t in range(z) for i in range(n))
            require(compose(ev, paired) == h, "evaluation/curry formula")
            beta += 1
        for u in maps(z, exp_size):
            require(curry(z, n, m, uncurry(z, n, m, u)) == u, "exponential eta")
            eta += 1
        if 0 in (n, m, z):
            empty_cases += 1
    return {"cardinality_bound": bound, "product_beta_cases": product_pairs,
            "product_eta_cases": product_uniqueness, "exponential_beta_cases": beta,
            "exponential_eta_cases": eta, "parameter_triples_with_zero": empty_cases}


DIAGRAMS = (
    ("empty", (), ()),
    ("empty_object", (0,), ()),
    ("empty_factor", (0, 2), ()),
    ("pullback", (2, 3, 2), ((0, 2, (0, 1)), (1, 2, (0, 1, 0)))),
    ("empty_equalizer", (2, 2), ((0, 1, (0, 1)), (0, 1, (1, 0)))),
    ("transitive_coequalizer", (3, 3), ((0, 1, (0, 1, 2)), (0, 1, (1, 2, 2)))),
    ("loop_swap", (2,), ((0, 0, (1, 0)),)),
    ("zero_to_nonzero", (0, 3), ((0, 1, ()),)),
)


def test_limits_colimits(bound: int) -> list[dict]:
    summaries = []
    for name, sizes, edges in DIAGRAMS:
        limit, projections = finite_limit(sizes, edges)
        colimit, injections, relation = finite_colimit(sizes, edges)
        rank = {xs: i for i, xs in enumerate(limit)}
        cone_count = cocone_count = 0
        for z in range(bound + 1):
            cones = tuple(qs for qs in product(*(maps(z, n) for n in sizes))
                          if all(compose(f, qs[i]) == qs[j] for i, j, f in edges))
            for qs in cones:
                mediator = tuple(rank[tuple(q[t] for q in qs)] for t in range(z))
                require(all(compose(p, mediator) == q for p, q in zip(projections, qs)),
                        f"limit factorization: {name}")
                cone_count += 1
            cone_images = tuple(tuple(compose(p, h) for p in projections)
                                for h in maps(z, len(limit)))
            require(len(set(cone_images)) == len(cone_images), f"limit uniqueness: {name}")
            require(set(cone_images) == set(cones), f"limit universal property: {name}")
            cocones = tuple(qs for qs in product(*(maps(n, z) for n in sizes))
                            if all(compose(qs[j], f) == qs[i] for i, j, f in edges))
            images = tuple(tuple(compose(h, injection) for injection in injections)
                           for h in maps(len(colimit), z))
            require(len(set(images)) == len(images), f"colimit uniqueness: {name}")
            require(set(images) == set(cocones), f"colimit universal property: {name}")
            cocone_count += len(cocones)
        total = sum(sizes)
        require(all(relation[i][i] for i in range(total)), "closure reflexive")
        require(all(relation[i][j] == relation[j][i] for i in range(total) for j in range(total)),
                "closure symmetric")
        require(all(not(relation[i][j] and relation[j][k]) or relation[i][k]
                    for i in range(total) for j in range(total) for k in range(total)),
                "closure transitive")
        summaries.append({"diagram": name, "limit_cardinality": len(limit),
                          "colimit_cardinality": len(colimit),
                          "cones_checked": cone_count, "cocones_checked": cocone_count})
    require(summaries[4]["limit_cardinality"] == 0, "empty equalizer not tested")
    require(summaries[5]["colimit_cardinality"] == 1, "transitive quotient not tested")
    return summaries


def test_yoneda_monoids() -> list[dict]:
    examples = (
        ("cyclic_group_order_two", 0, 4,
         lambda g, f: (g + f) % 2, lambda f, x: x ^ f),
        ("two_element_zero_monoid", 1, 3,
         lambda g, f: g * f, lambda f, x: x if f else 0),
    )
    summaries = []
    for name, unit, size, mul, act in examples:
        require(all(act(unit, x) == x for x in range(size)), "presheaf unit")
        require(all(act(mul(g, f), x) == act(f, act(g, x))
                    for f, g, x in product(range(2), range(2), range(size))), "presheaf comp")
        natural = tuple(alpha for alpha in maps(2, size)
                        if all(alpha[mul(g, f)] == act(f, alpha[g])
                               for f, g in product(range(2), repeat=2)))
        canonical = tuple(tuple(act(f, x) for f in range(2)) for x in range(size))
        require(set(natural) == set(canonical), "Yoneda surjectivity and completeness")
        require(len(set(canonical)) == size, "Yoneda injectivity")
        for alpha in natural:
            require(tuple(act(f, alpha[unit]) for f in range(2)) == alpha,
                    "Yoneda natural-transformation round trip")
        for x in range(size):
            require(tuple(act(f, x) for f in range(2))[unit] == x, "Yoneda element round trip")
        summaries.append({"monoid": name, "presheaf_cardinality": size,
                          "candidate_transformations": size**2,
                          "natural_transformations": len(natural)})
    return summaries


def inverse_image(f: tuple[int, ...], subset: int) -> int:
    return sum(1 << i for i, value in enumerate(f) if subset & (1 << value))


def test_yoneda_powerset() -> dict:
    # Full category of finite sets of cardinalities 0,1,2; h_2 to powerset.
    representable = [maps(n, 2) for n in range(3)]
    indices = [{f: i for i, f in enumerate(fs)} for fs in representable]
    candidates = product(*(maps(len(representable[n]), 2**n) for n in range(3)))
    natural = []
    count = 0
    for alpha in candidates:
        count += 1
        is_natural = all(
            alpha[a][indices[a][compose(g, f)]] == inverse_image(f, alpha[b][indices[b][g]])
            for a, b in product(range(3), repeat=2)
            for f in maps(a, b) for g in representable[b]
        )
        if is_natural:
            natural.append(alpha)
    canonical = tuple(tuple(tuple(inverse_image(f, subset) for f in representable[n])
                            for n in range(3)) for subset in range(4))
    require(set(natural) == set(canonical), "powerset Yoneda completeness")
    for alpha in natural:
        element = alpha[2][indices[2][identity(2)]]
        require(alpha == canonical[element], "powerset Yoneda round trip")
    return {"object_cardinalities": [0, 1, 2], "representing_cardinality": 2,
            "candidate_transformations": count, "natural_transformations": len(natural)}


def kleisli_comp(g: tuple[int, ...], f: tuple[int, ...]) -> tuple[int, ...]:
    # None=0 and Some(x)=x+1.
    return tuple(0 if value == 0 else g[value - 1] for value in f)


def test_option_kleisli(bound: int) -> dict:
    units = associativity = 0
    for n, m in product(range(bound + 1), repeat=2):
        for f in maps(n, m + 1):
            require(kleisli_comp(tuple(x + 1 for x in range(m)), f) == f, "Kleisli left unit")
            require(kleisli_comp(f, tuple(x + 1 for x in range(n))) == f, "Kleisli right unit")
            units += 1
    for n, m, k, ell in product(range(bound + 1), repeat=4):
        for f, g, h in product(maps(n, m + 1), maps(m, k + 1), maps(k, ell + 1)):
            require(kleisli_comp(h, kleisli_comp(g, f)) == kleisli_comp(kleisli_comp(h, g), f),
                    "Kleisli associativity")
            associativity += 1
    return {"cardinality_bound": bound, "unit_cases": units, "associativity_cases": associativity}


def run_all() -> dict:
    result = {
        "status": "all bounded exact checks passed",
        "scope": "finite examples; not formal proofs or an iPRA proof checker",
        "encoding": "base m+1 valid tables; exponential points are valid-table ranks",
        "table_codes": test_table_codes(3),
        "products_and_exponentials": test_products_and_exponentials(3),
        "limits_and_colimits": test_limits_colimits(3),
        "yoneda_monoids": test_yoneda_monoids(),
        "yoneda_powerset": test_yoneda_powerset(),
        "option_kleisli": test_option_kleisli(2),
    }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="write the exact verification summary")
    args = parser.parse_args()
    result = run_all()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.json is not None:
        args.json.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
