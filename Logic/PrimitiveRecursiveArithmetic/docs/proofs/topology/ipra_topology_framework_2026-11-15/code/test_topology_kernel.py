#!/usr/bin/env python3
from __future__ import annotations

from itertools import product
import json
from pathlib import Path
import tempfile
import unittest

from topology_kernel import (
    Carrier,
    FinitePreorder,
    ObservationTower,
    SimplicialComplex,
    betti_numbers_mod2,
    boundary_matrix,
    chain_map_matrix,
    cycle_complex,
    cycle_refinement,
    mat_mul_mod2,
    rank_mod2,
    validate_json_certificate,
    verify_prism_identity,
)


class SimplicialKernelTests(unittest.TestCase):
    def test_interval_betti(self) -> None:
        interval = SimplicialComplex.from_facets(2, [(0, 1)])
        self.assertEqual(betti_numbers_mod2(interval), (1, 0))

    def test_circle_betti(self) -> None:
        self.assertEqual(betti_numbers_mod2(cycle_complex(7)), (1, 1))

    def test_two_components(self) -> None:
        two_points = SimplicialComplex.from_facets(2, [(0,), (1,)])
        self.assertEqual(betti_numbers_mod2(two_points), (2,))

    def test_boundary_squared_zero(self) -> None:
        triangle = SimplicialComplex.from_facets(3, [(0, 1, 2)])
        d2 = boundary_matrix(triangle, 2)
        d1 = boundary_matrix(triangle, 1)
        self.assertEqual(mat_mul_mod2(d1, d2), [[0], [0], [0]])

    def test_mod2_rank(self) -> None:
        self.assertEqual(rank_mod2([[1, 0, 1], [0, 1, 1], [1, 1, 0]]), 2)

    def test_carrier_selections_and_prism(self) -> None:
        carrier = cycle_refinement(8, 4)
        f = carrier.selection("min")
        g = carrier.selection("max")
        carrier.validate_selection(f)
        carrier.validate_selection(g)
        self.assertTrue(carrier.selections_are_contiguous(f, g))
        self.assertTrue(verify_prism_identity(carrier, f, g))

    def test_chain_map_commutes_with_boundary(self) -> None:
        carrier = cycle_refinement(8, 4)
        f = carrier.selection("min")
        f1 = chain_map_matrix(carrier.source, carrier.target, f, 1)
        f0 = chain_map_matrix(carrier.source, carrier.target, f, 0)
        ds = boundary_matrix(carrier.source, 1)
        dt = boundary_matrix(carrier.target, 1)
        self.assertEqual(mat_mul_mod2(dt, f1), mat_mul_mod2(f0, ds))

    def test_carrier_composition(self) -> None:
        r8_4 = cycle_refinement(8, 4)
        r16_8 = cycle_refinement(16, 8)
        composed = r16_8.compose(r8_4)
        composed.validate()
        self.assertEqual(composed.source.n_vertices, 16)
        self.assertEqual(composed.target.n_vertices, 4)
        self.assertTrue(verify_prism_identity(composed, composed.selection("min"), composed.selection("max")))

    def test_observation_tower(self) -> None:
        c4 = cycle_complex(4)
        c8 = cycle_complex(8)
        c16 = cycle_complex(16)
        tower = ObservationTower.make(
            [c4, c8, c16],
            [cycle_refinement(8, 4), cycle_refinement(16, 8)],
        )
        direct = tower.refinement(2, 0)
        direct.validate()
        self.assertEqual(direct, cycle_refinement(16, 8).compose(cycle_refinement(8, 4)))

    def test_invalid_carrier_rejected(self) -> None:
        source = SimplicialComplex.from_facets(2, [(0, 1)])
        target = SimplicialComplex.from_facets(2, [(0,), (1,)])
        with self.assertRaises(ValueError):
            Carrier.make(source, target, [{0}, {1}])


class FiniteTopologyTests(unittest.TestCase):
    def test_sierpinski_opens(self) -> None:
        p = FinitePreorder.make([[1, 1], [0, 1]])
        self.assertEqual(set(p.opens()), {frozenset(), frozenset({1}), frozenset({0, 1})})

    def test_discrete_opens(self) -> None:
        p = FinitePreorder.make([[1, 0], [0, 1]])
        self.assertEqual(len(p.opens()), 4)

    def test_monotone_iff_continuous_exhaustive(self) -> None:
        preorders = [
            FinitePreorder.make([[1, 0], [0, 1]]),
            FinitePreorder.make([[1, 1], [0, 1]]),
            FinitePreorder.make([[1, 1], [1, 1]]),
        ]
        for source in preorders:
            for target in preorders:
                for mapping in product(range(target.size), repeat=source.size):
                    self.assertEqual(
                        source.monotone_to(target, mapping),
                        source.continuous_to(target, mapping),
                    )

    def test_nontransitive_relation_rejected(self) -> None:
        with self.assertRaises(ValueError):
            FinitePreorder.make(
                [
                    [1, 1, 0],
                    [0, 1, 1],
                    [0, 0, 1],
                ]
            )


class CertificateTests(unittest.TestCase):
    def test_json_certificate(self) -> None:
        data = {
            "source_complex": {
                "n_vertices": 8,
                "facets": [[i, (i + 1) % 8] for i in range(8)],
            },
            "target_complex": {
                "n_vertices": 4,
                "facets": [[i, (i + 1) % 4] for i in range(4)],
            },
            "carrier_images": {
                str(j): ([j // 2] if j % 2 == 0 else [j // 2, (j // 2 + 1) % 4])
                for j in range(8)
            },
            "expected": {
                "source_betti_mod2": [1, 1],
                "target_betti_mod2": [1, 1],
                "contiguous": True,
                "prism_identity_mod2": True,
            },
        }
        report = validate_json_certificate(data)
        self.assertTrue(report["valid"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
