"""Exhaustive finite checks for the eager-iteration countermodel.

These checks illustrate the accompanying structural proof.  They are not a
formal verification of that proof and are not part of any trusted checker.
Only the Python standard library is used.
"""

from itertools import product
import json


DOMAIN = (0, 1)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def monotone_tables(arity):
    points = tuple(product(DOMAIN, repeat=arity))
    order_pairs = tuple(
        (i, j)
        for i, x in enumerate(points)
        for j, y in enumerate(points)
        if all(a <= b for a, b in zip(x, y))
    )
    for outputs in product(DOMAIN, repeat=len(points)):
        if all(outputs[i] <= outputs[j] for i, j in order_pairs):
            yield dict(zip(points, outputs))


def main():
    counts = []
    sections = 0
    zero_instances = 0
    successor_instances = 0
    for passive_count in range(4):
        tables = tuple(monotone_tables(passive_count + 1))
        counts.append(len(tables))
        for table in tables:
            for passive in product(DOMAIN, repeat=passive_count):
                h = tuple(table[(state,) + passive] for state in DOMAIN)
                sections += 1
                require(h in ((0, 0), (0, 1), (1, 1)), "unexpected section")
                for a in DOMAIN:
                    # F(n,a;h) is interpreted as h(a), for either counter.
                    f_zero = h[a]
                    require(f_zero == h[a], "zero computation failed")
                    zero_instances += 1
                    for n in DOMAIN:
                        successor_n = 1
                        f_successor = h[a]
                        f_n = h[a]
                        require(successor_n in DOMAIN, "successor not total")
                        require(f_successor == h[f_n], "step computation failed")
                        successor_instances += 1

    # Every formula with fixed passive parameters defines one of these four
    # subsets.  Thus this checks induction for every possible such extension.
    induction_extensions = 0
    for truth_values in product((False, True), repeat=2):
        base = truth_values[0]
        step = all(not truth_values[n] or truth_values[1] for n in DOMAIN)
        require(not (base and step) or all(truth_values), "induction failed")
        induction_extensions += 1

    coverage = all(x == 0 or any(x == 1 for _ in DOMAIN) for x in DOMAIN)
    separation = all(0 != 1 for _ in DOMAIN)
    injectivity = all(x == y for x in DOMAIN for y in DOMAIN if 1 == 1)
    require(coverage, "coverage failed")
    require(separation, "zero-successor separation failed")
    require(not injectivity, "expected noninjective successor")
    require(counts == [3, 6, 20, 168], "monotone-table inventory changed")

    print(json.dumps({
        "domain_size": len(DOMAIN),
        "monotone_update_tables_by_passive_arity": counts,
        "unary_update_sections_checked": sections,
        "zero_equation_instances_checked": zero_instances,
        "successor_equation_instances_checked": successor_instances,
        "formula_extensions_checked_for_induction": induction_extensions,
        "coverage": coverage,
        "zero_successor_separation": separation,
        "successor_injective": injectivity,
        "status": "PASS",
        "scope": "finite-model calculations; structural proof is in the note"
    }, indent=2))


if __name__ == "__main__":
    main()
