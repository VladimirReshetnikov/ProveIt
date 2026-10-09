"""Independent bounded audit of support algebra and cancellation replay.

This is a research audit, not production code.  Synthetic matrices exercise
the stated finite-row algebraic contract; they do not claim to be triangulations.
The matrix oracle is dense rational elimination, independent of producer
Bareiss elimination and checker modular elimination.  Only the cancellation
checks use the supplied normal-surface fixtures.
"""

from copy import deepcopy
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import random
import sys
import time

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.normal_support import compile_support, decode_support
from fastunknot.normal_support_verify import verify_support, _unit_minor
from fastunknot.normal_packed_components import normal_packed_component_census
from fastunknot.normal_packed_verify import verify_normal_packed_certificate
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.weighted_orbit_verify import _InvalidWeightedProof
from normal_orbit_research.fixtures import layered_torus


def rational_rank(equations, columns):
    """Small dense Fraction oracle; no implementation helper is used."""
    matrix = [[Fraction(row.get(j, 0)) for j in columns] for row in equations]
    rank = 0
    for j in range(len(columns)):
        chosen = next((i for i in range(rank, len(matrix)) if matrix[i][j]), None)
        if chosen is None:
            continue
        matrix[rank], matrix[chosen] = matrix[chosen], matrix[rank]
        pivot = matrix[rank][j]
        matrix[rank] = [value / pivot for value in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            if matrix[i][j]:
                coefficient = matrix[i][j]
                matrix[i] = [a - coefficient * b
                             for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def contract_rows(source):
    """All balanced signed rows of squared norm at most four."""
    result = []
    for width in range(2, min(4, len(source)) + 1):
        for indices in combinations(range(len(source)), width):
            for tail in product((-1, 1), repeat=width - 1):
                values = (1, *tail)
                if sum(source[i] * value for i, value in zip(indices, values)) == 0:
                    result.append(dict(zip(indices, values)))
    return result


def algebra_audit():
    rng = random.Random(20261009)
    cases, bases, nonunit_denominators, empty_cases = 0, 0, 0, 0
    for trial in range(40):
        size = 5 + trial % 4
        source = [rng.randrange(1, 17) for _ in range(size)]
        if trial % 7 == 0:
            source[0] = 0
        if trial == 0:
            source = [0] * size
        rows = contract_rows(source)
        rng.shuffle(rows)
        rows = rows[:rng.randrange(min(14, len(rows)) + 1)]
        prepared, analysed = {"matching": rows}, {"rows": [source]}
        proof = compile_support(prepared, analysed)
        assert verify_support(prepared, analysed, proof)
        support = [i for i, value in enumerate(source) if value]
        rank = rational_rank(rows, support)
        assert proof["rank"] == rank
        assert proof["nullity"] == len(support) - rank
        cost = sum(source[j].bit_length() for j in proof["selected"])
        optimum = None
        for pivots in combinations(support, rank):
            if rational_rank(rows, pivots) == rank:
                retained = set(support).difference(pivots)
                candidate = sum(source[j].bit_length() for j in retained)
                optimum = candidate if optimum is None else min(optimum, candidate)
                bases += 1
        assert cost == optimum
        projected = [source[j] for j in proof["selected"]]
        assert decode_support(analysed, proof, projected) == source
        # Every certified rational column must reproduce its free coordinate
        # exactly and annihilate every original (not merely pivot) equation.
        for column, j in enumerate(proof["selected"]):
            values = {i: Fraction(row[column], proof["denominator"])
                      for i, row in zip(support, proof["numerators"])}
            assert values[j] == 1
            assert all(sum(coefficient * values.get(i, 0)
                           for i, coefficient in row.items()) == 0 for row in rows)
        nonunit_denominators += proof["denominator"] > 1
        empty_cases += not support
        cases += 1
    assert nonunit_denominators > 0, "The audit must exercise actual division."
    return dict(cases=cases, independent_bases_checked=bases,
                nonunit_denominators=nonunit_denominators,
                empty_support_cases=empty_cases)


def modular_audit():
    prepared = {"matching": [{0: 1, 1: -1}]}
    analysed = {"rows": [[7, 7]]}
    proof = compile_support(prepared, analysed)
    composite = deepcopy(proof)
    composite["modulus"] = 4
    assert verify_support(prepared, analysed, composite)
    assert not _unit_minor([{0: 2}], [0], [0], 4, lambda: None)
    # An invertible matrix over Z/6 need not admit the checker's restricted
    # unit-entry pivot strategy. Rejection is permitted: this is a sufficient
    # witness, while the producer supplies a suitable prime modulus.
    assert not _unit_minor([{0: 2, 1: 3}, {0: 3, 1: 2}], [0, 1], [0, 1],
                           6, lambda: None)
    # Scaling a denominator and its numerator does not change the decoder;
    # certificates prove a rational map, not reduced-fraction uniqueness.
    scaled = deepcopy(proof)
    scaled["denominator"] *= 2
    scaled["numerators"] = [[2 * value for value in row]
                            for row in scaled["numerators"]]
    assert verify_support(prepared, analysed, scaled)
    broken = deepcopy(scaled)
    broken["numerators"][0][0] += 1
    assert not verify_support(prepared, analysed, broken)
    for field in ("rank", "nullity", "denominator", "modulus"):
        bad = deepcopy(proof)
        bad[field] = True
        assert not verify_support(prepared, analysed, bad)
    return dict(composite_unit_witness_accepted=True,
                nonunit_pivot_rejected=True,
                incomplete_composite_strategy_rejects_safely=True,
                valid_unreduced_decoder_accepted=True,
                malformed_decoder_rejected=True,
                boolean_integer_mutations_rejected=4)


def cancellation_audit():
    raw, rows = layered_torus(2)
    certificate = normal_packed_component_census(raw, rows,
                                                record_certificate=True)["certificate"]
    cases = (("_prepare", NormalOrbitError),
             ("full_vector_signature", ValueError),
             ("full_vector_signature", NormalOrbitError),
             ("_initial_weights", _InvalidWeightedProof))
    accepted = []
    for target, exception_type in cases:
        marker = exception_type("targeted cooperative cancellation")
        reached = [False]

        def check():
            frame = sys._getframe(1)
            while frame:
                if frame.f_code.co_name == target:
                    reached[0] = True
                    raise marker
                frame = frame.f_back

        try:
            verify_normal_packed_certificate(raw, rows, certificate, check=check)
        except BaseException as exc:
            assert exc is marker, (target, type(exc))
        else:
            raise AssertionError((target, "callback exception swallowed"))
        assert reached[0]
        accepted.append({"location": target, "exception": exception_type.__name__})
    # The same certificate cannot be rebound to new source magnitudes.
    twice = [[2 * value for value in row] for row in rows]
    assert not verify_normal_packed_certificate(raw, twice, certificate)
    return dict(exact_callback_objects_propagated=accepted,
                altered_source_rejected=True)


if __name__ == "__main__":
    start = time.monotonic()
    report = dict(algebra=algebra_audit(), modular=modular_audit(),
                  cancellation=cancellation_audit())
    report["wall_seconds"] = round(time.monotonic() - start, 6)
    report["status"] = "PASS"
    print(json.dumps(report, indent=2, sort_keys=True))
