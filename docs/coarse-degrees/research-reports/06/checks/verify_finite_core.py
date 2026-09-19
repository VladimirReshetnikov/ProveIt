#!/usr/bin/env python3
"""Exhaustive finite checks for the sparse minimal-pair construction.

These tests certify finite combinatorial invariants only. They do NOT simulate
0'', decide divergence of an arbitrary oracle program, or formalize the infinite
construction. Run with ordinary Python 3.9+; no third-party packages are needed.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from pathlib import Path
from typing import Callable, Dict, List, Optional, Sequence, Tuple

Bits = Tuple[int, ...]
Budget = Callable[[int], int]


def require(condition: bool, message: str) -> None:
    """Unlike an assert statement, this check remains active under python -O."""
    if not condition:
        raise AssertionError(message)


def bits_of(value: int, width: int) -> Bits:
    return tuple((value >> i) & 1 for i in range(width))


def words(width: int) -> List[Bits]:
    return [bits_of(value, width) for value in range(1 << width)]


def hamming(left: Bits, right: Bits) -> int:
    require(len(left) == len(right), "Unequal lengths in Hamming distance")
    return sum(a != b for a, b in zip(left, right))


def hypercube_path(left: Bits, right: Bits) -> List[Bits]:
    require(len(left) == len(right), "Unequal cube dimensions")
    current = list(left)
    result = [left]
    for i, (a, b) in enumerate(zip(left, right)):
        if a != b:
            current[i] = b
            result.append(tuple(current))
    return result


def log_budget(n: int) -> int:
    require(n >= 0, "Negative prefix length")
    return (n + 1).bit_length() - 1  # floor(log_2(n+1)), exactly


def variation(frontier: Sequence[Bits]) -> frozenset[int]:
    require(bool(frontier), "Empty frontier")
    length = len(frontier[0])
    require(all(len(word) == length for word in frontier), "Unequal frontier lengths")
    first = frontier[0]
    return frozenset(i for i in range(length)
                     if any(word[i] != first[i] for word in frontier[1:]))


def budget_holds(frontier: Sequence[Bits], budget: Budget) -> bool:
    var = variation(frontier)
    used = 0
    for n in range(len(frontier[0]) + 1):
        if n and n - 1 in var:
            used += 1
        if used > budget(n):
            return False
    return True


def common_extend(frontier: Sequence[Bits], suffix: Bits) -> List[Bits]:
    return [word + suffix for word in frontier]


def buffer(frontier: Sequence[Bits], budget: Budget) -> List[Bits]:
    require(budget_holds(frontier, budget), "Invalid starting frontier")
    used = len(variation(frontier))
    old_length = len(frontier[0])
    length = old_length
    while budget(length) < used + 1:
        length += 1
        if length - old_length > 1_000_000:
            raise RuntimeError("Finite test guard: buffer search exceeded one million")
    result = common_extend(frontier, (0,) * (length - old_length))
    require(budget_holds(result, budget), "Buffer violated invariant")
    require(budget(length) >= used + 1, "Buffer failed to reserve one bit")
    return result


def admissible(length: int, used: int, u: Bits, v: Bits, budget: Budget) -> bool:
    require(len(u) == len(v), "Unequal suffix lengths")
    count = used
    if count > budget(length):
        return False
    for k, (a, b) in enumerate(zip(u, v), start=1):
        count += a != b
        if count > budget(length + k):
            return False
    return True


def lift(frontier: Sequence[Bits], i: int, j: int, u: Bits, v: Bits) -> List[Bits]:
    require(i != j and 0 <= i < len(frontier) and 0 <= j < len(frontier),
            "Invalid selected leaves")
    require(len(u) == len(v), "Unequal lift suffixes")
    return [word + (v if index == j else u) for index, word in enumerate(frontier)]


def test_hypercube() -> Dict[str, int]:
    pairs = 0
    edges = 0
    for dimension in range(9):
        cube = words(dimension)
        for u in cube:
            for v in cube:
                path = hypercube_path(u, v)
                require(path[0] == u and path[-1] == v, "Incorrect path endpoints")
                require(len(path) == hamming(u, v) + 1, "Non-shortest cube path")
                for a, b in zip(path, path[1:]):
                    require(hamming(a, b) == 1, "Non-edge in cube path")
                    require(hamming(a + (0, 1, 1), b + (0, 1, 1)) == 1,
                            "Common suffix changed Hamming distance")
                    edges += 1
                pairs += 1
    return {"dimensions_inclusive": 8, "ordered_pairs": pairs, "edges_checked": edges}


def split_witness(f: Sequence[Optional[int]], g: Sequence[Optional[int]],
                  dimension: int) -> Optional[Tuple[int, int]]:
    for u in range(1 << dimension):
        # The diagonal and every oriented one-bit edge are checked.
        adjacent = [u] + [u ^ (1 << bit) for bit in range(dimension)]
        for v in adjacent:
            if f[u] is not None and g[v] is not None and f[u] != g[v]:
                return u, v
    return None


def test_total_lookup() -> Dict[str, object]:
    total = 0
    counts: Dict[str, int] = {}
    for dimension in range(4):
        size = 1 << dimension
        tables = list(itertools.product((0, 1), repeat=size))
        no_split = 0
        for f in tables:
            for g in tables:
                witness = split_witness(f, g, dimension)
                if witness is None:
                    no_split += 1
                    require(len(set(f + g)) == 1, "No-split tables were nonconstant")
                else:
                    u, v = witness
                    require((u ^ v) == 0 or ((u ^ v) & ((u ^ v) - 1)) == 0,
                            "Witness was not adjacent")
                    require(f[u] != g[v], "False split witness")
                total += 1
        require(no_split == 2, "Wrong number of no-split Boolean pairs")
        counts[str(dimension)] = no_split
    return {"lookup_pairs": total, "no_split_pairs_by_dimension": counts}


def test_partial_lookup() -> Dict[str, int]:
    total = 0
    split = 0
    divergence = 0
    constant = 0
    for dimension in range(3):
        size = 1 << dimension
        tables = list(itertools.product((None, 0, 1), repeat=size))
        for f in tables:
            for g in tables:
                witness = split_witness(f, g, dimension)
                if witness is not None:
                    split += 1
                elif None in f or None in g:
                    # In this finite model a None value is stipulated to be
                    # divergence on the entire corresponding cylinder.
                    divergence += 1
                else:
                    require(len(set(f + g)) == 1, "Partial-model trilemma failed")
                    constant += 1
                total += 1
    return {"lookup_pairs": total, "split": split,
            "divergent_cylinder": divergence, "constant": constant}


def base_frontier() -> List[Bits]:
    zero = (0,) * 16
    result = [zero]
    for position in (7, 11, 15):
        word = list(zero)
        word[position] = 1
        result.append(tuple(word))
    return result


def test_budget_lifting() -> Dict[str, int]:
    frontier = base_frontier()
    require(budget_holds(frontier, log_budget), "Invalid test frontier")
    length = len(frontier[0])
    used = len(variation(frontier))
    require(used == 3 and log_budget(length) == 4, "Wrong one-bit reserve")
    tested = accepted = rejected = one_bit_pairs = 0
    for width in range(6):
        suffixes = words(width)
        for i in range(len(frontier)):
            for j in range(len(frontier)):
                if i == j:
                    continue
                for u in suffixes:
                    for v in suffixes:
                        okay = admissible(length, used, u, v, log_budget)
                        if hamming(u, v) <= 1:
                            require(okay, "A one-bit suffix pair was rejected")
                            one_bit_pairs += 1
                        extended = lift(frontier, i, j, u, v)
                        expected = variation(frontier) | frozenset(
                            length + k for k in range(width) if u[k] != v[k])
                        require(variation(extended) == expected, "Lift variation mismatch")
                        require(budget_holds(extended, log_budget) == okay,
                                "Admissibility did not match global budget")
                        if okay:
                            accepted += 1
                        else:
                            rejected += 1
                        tested += 1
    # Regression: charging only the selected pair's OLD disagreement is wrong.
    u, v = (0, 0, 0), (1, 1, 1)
    wrong_used = hamming(frontier[0], frontier[1])
    require(admissible(length, wrong_used, u, v, log_budget),
            "Regression failed to exhibit the incorrect heuristic")
    require(not admissible(length, used, u, v, log_budget),
            "Regression failed to reject the over-budget lift")
    require(not budget_holds(lift(frontier, 0, 1, u, v), log_budget),
            "Over-budget lift unexpectedly valid")
    return {"suffix_lifts": tested, "accepted": accepted, "rejected": rejected,
            "diagonal_or_one_bit_pairs": one_bit_pairs,
            "global_vs_pair_budget_regressions": 1}


def test_finite_fusion() -> Dict[str, object]:
    rng = random.Random(20260918)
    frontier: List[Bits] = [()]
    levels = []
    previous_var: frozenset[int] = frozenset()
    for stage in range(6):
        frontier = buffer(frontier, log_budget)
        frontier = [word + (bit,) for word in frontier for bit in (0, 1)]
        require(budget_holds(frontier, log_budget), "Simultaneous split overran budget")
        # A common extension, then a one-bit pair extension; no oracle claims.
        suffix = tuple(rng.randrange(2) for _ in range(3))
        frontier = common_extend(frontier, suffix)
        frontier = buffer(frontier, log_budget)
        i, j = rng.sample(range(len(frontier)), 2)
        u = tuple(rng.randrange(2) for _ in range(3))
        v_list = list(u)
        v_list[rng.randrange(3)] ^= 1
        v = tuple(v_list)
        frontier = lift(frontier, i, j, u, v)
        require(budget_holds(frontier, log_budget), "Pair extension overran budget")
        current_var = variation(frontier)
        require(previous_var <= current_var, "Variation disappeared")
        require(len(current_var) == 2 * (stage + 1), "Wrong variation increment")
        require(len(set(frontier)) == len(frontier), "Leaf incompatibility lost")
        previous_var = current_var
        levels.append({"stage": stage, "leaves": len(frontier),
                       "length": len(frontier[0]), "variation": len(current_var)})
    return {"seed": 20260918, "levels": levels,
            "note": "Finite structural simulation, not a simulation of the oracle construction."}


def test_sparse_coding() -> Dict[str, int]:
    rng = random.Random(150501707)
    cases = 0
    for length in range(1, 513):
        f = tuple(rng.randrange(4) for _ in range(length))
        d = tuple(value if rng.randrange(8) else rng.randrange(4) for value in f)
        b = tuple(rng.randrange(2) for _ in range(length.bit_length()))
        y = list(d)
        sparse = set()
        k = 0
        while (1 << k) < length:
            position = 1 << k
            y[position] = b[k]
            sparse.add(position)
            require(y[position] == b[k], "Sparse decoder failed")
            k += 1
        old_errors = {i for i in range(length) if d[i] != f[i]}
        new_errors = {i for i in range(length) if y[i] != f[i]}
        require(new_errors <= old_errors | sparse, "Sparse coding error inclusion failed")
        cases += 1
    return {"prefix_cases": cases}


def test_majority() -> Dict[str, int]:
    cases = 0
    for width in (1, 2, 4, 8):
        for word in words(width):
            for true_bit in (0, 1):
                errors = sum(bit != true_bit for bit in word)
                decoded = int(sum(word) > width / 2)  # ties to zero
                if errors * 2 < width:
                    require(decoded == true_bit, "Strict-majority decoder failed")
                if decoded != true_bit:
                    require(errors * 2 >= width, "Wrong bit without enough errors")
                cases += 1
    return {"block_cases": cases}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("results.json"))
    args = parser.parse_args()
    tests = {
        "hypercube_paths": test_hypercube,
        "total_lookup_connectivity": test_total_lookup,
        "partial_lookup_trilemma": test_partial_lookup,
        "budget_lifting": test_budget_lifting,
        "finite_fusion": test_finite_fusion,
        "sparse_coding": test_sparse_coding,
        "majority_decoding": test_majority,
    }
    results: Dict[str, object] = {
        "status": "PASS", "scope": "Finite invariants only; no infinite proof certificate.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "tests": {},
    }
    for name, test in tests.items():
        outcome = test()
        results["tests"][name] = outcome  # type: ignore[index]
        print("PASS", name, json.dumps(outcome, sort_keys=True))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("ALL FINITE CHECKS PASSED")


if __name__ == "__main__":
    main()
