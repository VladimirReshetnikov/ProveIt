#!/usr/bin/env python3
"""Finite exact checks of extraction, geometric witnesses, and rejection paths.

These tests support the executable artifacts; the unbounded theorem is proved
in the manuscript, not inferred from a finite test suite.
"""

from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import unittest

from make_examples import build
from minkowski import InvalidCertificate, determinant, extract, parse_and_check, verify_witness


def reversed_one_dimensional_case():
    return {
        "schema": "minkowski-ipra-boxes-v1", "dimension": 1,
        "basis": [["-1/2"]],
        "slabs": [{"normal": ["1"], "bound": "3/4"}],
        "boxes": [{"lower": ["0"], "upper": ["3/4"]},
                  {"lower": ["-3/4"], "upper": ["0"]}],
    }


class ExactChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.examples = build()

    def test_examples_against_independent_membership(self):
        for name, data in self.examples.items():
            with self.subTest(name=name):
                witness = extract(data)
                self.assertTrue(verify_witness(data, witness))
                z = witness["integer_coefficients"]
                basis = [[Q(x) for x in row] for row in data["basis"]]
                point = [sum((a * b for a, b in zip(row, z)), Q(0)) for row in basis]
                self.assertTrue(any(point))
                self.assertEqual(point, list(map(Q, witness["lattice_point"])))
                for slab in data["slabs"]:
                    self.assertLessEqual(abs(sum((Q(a) * x for a, x in zip(slab["normal"], point)), Q(0))),
                                         Q(slab["bound"]))
                self.assertLessEqual(witness["cells_examined"], witness["number_of_colors"] + 1)

    def test_exact_diamond_volume(self):
        model = parse_and_check(self.examples["diamond"])
        self.assertEqual(model["volume"], Q(33, 32))
        self.assertEqual(model["cell_count"], 264)
        self.assertEqual(model["m"], 16)

    def test_negative_orientation_and_fractional_basis(self):
        data = deepcopy(self.examples["square"])
        data["basis"] = [["0", "1/2"], ["-2", "0"]]
        data["slabs"] = [{"normal": ["1", "0"], "bound": "3/4"},
                         {"normal": ["0", "1"], "bound": "3"}]
        self.assertTrue(verify_witness(data, extract(data)))
        self.assertEqual(determinant([[Q(0), Q(1)], [Q(1), Q(0)]]), -1)

    def test_negative_quotient_with_reversed_boxes(self):
        # Listing the positive box first forces a collision whose later
        # coordinate is negative and whose divisible difference is negative.
        data = reversed_one_dimensional_case()
        witness = extract(data)
        self.assertEqual(witness["earlier_cell"], [1])
        self.assertEqual(witness["later_cell"], [-3])
        self.assertEqual(witness["integer_coefficients"], [-1])
        self.assertEqual(witness["lattice_point"], ["1/2"])
        self.assertEqual(witness["lattice_covolume"], "1/2")
        self.assertTrue(verify_witness(data, witness))

    def test_touching_box_faces_are_allowed(self):
        data = deepcopy(self.examples["square"])
        data["boxes"] = [{"lower": ["-3/4", "-3/4"], "upper": ["0", "3/4"]},
                         {"lower": ["0", "-3/4"], "upper": ["3/4", "3/4"]}]
        self.assertTrue(verify_witness(data, extract(data)))

    def test_invalid_geometric_and_arithmetic_inputs(self):
        bad = []
        data = deepcopy(self.examples["square"])
        data["boxes"].append(deepcopy(data["boxes"][0]))
        bad.append(data)
        data = deepcopy(self.examples["square"])
        data["boxes"][0]["lower"] = ["-1/2", "-1/2"]
        data["boxes"][0]["upper"] = ["1/2", "1/2"]
        bad.append(data)  # The strict volume inequality is essential.
        data = deepcopy(self.examples["square"])
        data["slabs"][0]["bound"] = "1"
        bad.append(data)
        data = deepcopy(self.examples["square"])
        data["basis"] = [["1", "0"], ["1", "0"]]
        bad.append(data)
        data = deepcopy(self.examples["square"])
        data["boxes"][0]["lower"][0] = -0.75
        bad.append(data)
        data = deepcopy(self.examples["square"])
        data["dimension"] = 0
        bad.append(data)
        for i, data in enumerate(bad):
            with self.subTest(corruption=i), self.assertRaises(InvalidCertificate):
                extract(data)

    def test_corrupt_witnesses_rejected(self):
        data = self.examples["square"]
        original = extract(data)
        changes = {"integer_coefficients": [0, 0], "lattice_point": ["99", "99"],
                   "residues": [0, 0], "later_index": 1000, "earlier_cell": [99, 99],
                   "normalized_inner_volume": "1", "nonzero_coordinate": 0,
                   "cells_examined": 0, "number_of_colors": 17, "total_cells": 0,
                   "lattice_covolume": "2"}
        for key, value in changes.items():
            with self.subTest(field=key), self.assertRaises(InvalidCertificate):
                verify_witness(data, {**original, key: value})

    def test_noninteger_witness_metadata_rejected(self):
        # Numerically equal floats, and booleans equal to 0 or 1, must not
        # be accepted as integer fields in the exact certificate schema.
        data = reversed_one_dimensional_case()
        original = extract(data)
        fields = ("dimension", "modulus", "number_of_colors", "total_cells",
                  "cells_examined", "earlier_index", "later_index", "earlier_box",
                  "later_box", "nonzero_coordinate")
        for key in fields:
            for value in (float(original[key]), bool(original[key])):
                with self.subTest(field=key, value=value), self.assertRaises(InvalidCertificate):
                    verify_witness(data, {**original, key: value})

    def test_tiny_residue_collision_space(self):
        # Exhaust all color lists of length M+1 for M=1,2,3. This checks
        # a distinct finite combinatorial component independently of boxes.
        for m in range(1, 4):
            for colors in product(range(m), repeat=m + 1):
                pairs = [(i, j) for j in range(m + 1) for i in range(j)
                         if colors[i] == colors[j]]
                self.assertTrue(pairs)


if __name__ == "__main__":
    unittest.main(verbosity=2)
