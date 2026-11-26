#!/usr/bin/env python3
"""Finite exact sanity checks for the source audit's module bridges.

This does NOT compute Galois cohomology or verify the GRH proof.
It checks (i) the sharp one-level saturation criterion on all finite
abelian p-module types in an explicit range, with optional divisible
summands, and (ii) scalar-extension identities by enumerating cocycles
on small cyclic groups, including oddness at p=2.
Only the Python standard library is required.
"""
from __future__ import annotations

from itertools import combinations_with_replacement, product
import argparse
import json
from pathlib import Path


def truncated_length(exponents: tuple[int, ...], divisible_rank: int, level: int) -> int:
    return sum(min(a, level) for a in exponents) + divisible_rank * level


def check_saturation() -> dict:
    cases = 0
    certificate_cases = 0
    nonvacuous = 0
    for rank in range(6):
        for exponents in combinations_with_replacement(range(1, 9), rank):
            for divisible_rank in range(3):
                for level in range(1, 13):
                    small = truncated_length(exponents, divisible_rank, level)
                    if small < level:
                        assert divisible_rank == 0
                        assert all(a < level for a in exponents)
                        assert small == sum(exponents)
                        nonvacuous += 1
                    cases += 1
                for bound in range(13):
                    all_level_bound = divisible_rank == 0 and sum(exponents) <= bound
                    one_level_bound = truncated_length(exponents, divisible_rank, bound + 1) <= bound
                    assert all_level_bound == one_level_bound
                    certificate_cases += 1
    for level in range(1, 13):
        assert truncated_length((), 1, level) == level
    return {
        "module_types": "direct sums of at most 5 cyclic factors p^a, 1<=a<=8; 0,1,2 copies of Qp/Zp",
        "saturation_checks": cases,
        "nonvacuous_saturation_checks": nonvacuous,
        "certificate_equivalence_checks": certificate_cases,
        "sharpness_model": "M=Qp/Zp has length M[p^N]=N at every level; M has infinite length",
    }


def add(x: tuple[int, ...], y: tuple[int, ...], q: int) -> tuple[int, ...]:
    return tuple((a + b) % q for a, b in zip(x, y))


def scale(a: int, x: tuple[int, ...], q: int) -> tuple[int, ...]:
    return tuple((a * b) % q for b in x)


def solutions(n: int, q: int, a: int, degree: int, odd: bool, local_zero: tuple[int, ...]):
    """All cocycles C_n -> (Z/q)^degree, with scalar action a^g.

    Every cocycle is determined by its value on the generator. We
    enumerate that value, then independently check all cocycle equations
    and all prescribed local and oddness equations.
    """
    assert pow(a, n, q) == 1
    zero = (0,) * degree
    answer = []
    for generator_value in product(range(q), repeat=degree):
        vals = [zero]
        for g in range(n):
            vals.append(add(vals[-1], scale(pow(a, g, q), generator_value, q), q))
        if vals[n] != zero:
            continue
        vals = vals[:n]
        if any(vals[g] != zero for g in local_zero):
            continue
        if odd and any(vals[(-g) % n] != scale(-1, vals[g], q) for g in range(n)):
            continue
        assert all(
            vals[(g + h) % n] == add(vals[g], scale(pow(a, g, q), vals[h], q), q)
            for g in range(n) for h in range(n)
        )
        answer.append(tuple(vals))
    return answer


def integer_log(p: int, value: int) -> int:
    result = 0
    while value > 1:
        assert value % p == 0
        value //= p
        result += 1
    return result


def check_coefficient_extension() -> list[dict]:
    rows = []
    configs = [
        (2, 4, -1, True, (0,)),
        (2, 4, 1, True, (0,)),
        (3, 3, 1, True, (0,)),
        (3, 4, -1, True, (0,)),
        (2, 4, -1, False, (0, 2)),
    ]
    for p, n, a, odd, local_zero in configs:
        for level in range(1, 4):
            q = p**level
            base = solutions(n, q, a % q, 1, odd, local_zero)
            base_as_scalars = {tuple(x[0] for x in f) for f in base}
            base_length = integer_log(p, len(base))
            for degree in (2, 3):
                extended = solutions(n, q, a % q, degree, odd, local_zero)
                assert len(extended) == len(base)**degree
                # Surjectivity/injectivity of the actual coordinate map.
                coordinates = set()
                for f in extended:
                    coord = tuple(tuple(f[g][k] for g in range(n)) for k in range(degree))
                    assert all(c in base_as_scalars for c in coord)
                    coordinates.add(coord)
                assert len(coordinates) == len(base)**degree
                assert integer_log(p, len(extended)) == degree * base_length
                rows.append({
                    "prime": p, "group": f"C{n}", "action_on_generator": a,
                    "odd_under_inversion": odd, "zero_on_elements": list(local_zero),
                    "torsion_level": level, "coefficient_degree": degree,
                    "base_module_cardinality": len(base),
                    "extended_module_cardinality": len(extended),
                    "base_length": base_length,
                    "normalized_length_after_extension": base_length,
                })
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1] / "data" / "module_bridge_checks.json")
    args = parser.parse_args()
    result = {
        "status": "all exact checks passed",
        "scope": "finite module and finite cyclic-cocycle models; not arithmetic Galois cohomology",
        "saturation": check_saturation(),
        "coefficient_extension": check_coefficient_extension(),
        "coefficient_note": (
            "A finite free Z_p-basis identifies O/p^nu with (Z/p^nu)^degree "
            "for all equations here. Raw O-length scales by ramification index, "
            "not by the whole coefficient degree; normalized length is unchanged."
        ),
    }
    output = args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    print(json.dumps(result["saturation"], indent=2))
    print(f"coefficient-extension models: {len(result['coefficient_extension'])}")
    print(f"output: {output}")


if __name__ == "__main__":
    main()

