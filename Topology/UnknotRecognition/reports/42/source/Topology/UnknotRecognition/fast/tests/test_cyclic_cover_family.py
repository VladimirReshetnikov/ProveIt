"""Independent sheet-orbit checks for affine surface-assembly families."""

from copy import deepcopy
from itertools import product
import json
import random
import unittest

from fastunknot.cyclic_cover_family import (
    compile_family, component_count_at, optimize_cover_family,
    realize_family, verify_cover_family_certificate,
)
from fastunknot.surface_cover import canonical_schema, classify_cover
from fastunknot.integer_codec import json_safe


def expression(constant=0, coefficients=()):
    return {"constant": constant, "coefficients": list(coefficients)}


def annulus_family(modulus=12):
    return {"sheets": modulus, "variables": 1,
            "pieces": [{"surface": {"orientable": True, "genus": 0,
                                      "boundary_components": 2},
                        "monodromy": [expression(6, [0])]}],
            "seams": [{"left": [0, 0], "right": [0, 1], "direction": -1,
                       "shift": expression(0, [1])}],
            "constraints": {"matrix": [[2]], "rhs": [8]}}


def literal_components(raw, parameters):
    """Direct DSU on piece x sheet, without a spanning tree or holonomies."""
    modulus = raw["sheets"]
    def value(expr):
        return (expr["constant"] + sum(a * b for a, b in
                                       zip(expr["coefficients"], parameters))) % modulus
    for row, rhs in zip(raw["constraints"]["matrix"], raw["constraints"]["rhs"]):
        if sum(a * b for a, b in zip(row, parameters)) % modulus != rhs % modulus:
            return None
    parent = list(range(modulus * len(raw["pieces"])))
    def root(index):
        while parent[index] != index:
            parent[index] = parent[parent[index]]
            index = parent[index]
        return index
    def join(a, b):
        parent[root(a)] = root(b)
    boundaries = []
    for index, piece in enumerate(raw["pieces"]):
        surface = piece["surface"]
        _, _, words, _ = canonical_schema(surface["orientable"], surface["genus"],
                                          surface["boundary_components"])
        maps = [value(expr) for expr in piece["monodromy"]]
        boundaries.append([sum((1 if letter > 0 else -1) * maps[abs(letter) - 1]
                               for letter in word) % modulus for word in words])
        for shift in maps:
            for sheet in range(modulus):
                join(index * modulus + sheet, index * modulus + (sheet + shift) % modulus)
    for seam in raw["seams"]:
        u, ub = seam["left"]
        v, vb = seam["right"]
        if (boundaries[u][ub] - seam["direction"] * boundaries[v][vb]) % modulus:
            return None
        shift = value(seam["shift"])
        for sheet in range(modulus):
            join(u * modulus + sheet, v * modulus + (sheet + shift) % modulus)
    return len({root(index) for index in range(len(parent))})


class CyclicCoverFamilyTests(unittest.TestCase):
    def test_nontrivial_constrained_annulus_assembly(self):
        raw = annulus_family()
        result = optimize_cover_family(raw)
        optimization = result["optimization"]
        self.assertTrue(optimization["feasible"])
        self.assertEqual(optimization["solution_count"], 2)
        self.assertEqual(optimization["minimum_components"], 2)
        self.assertFalse(optimization["connected_member_exists"])
        self.assertTrue(verify_cover_family_certificate(raw, result))
        self.assertEqual(literal_components(raw, optimization["parameters"]), 2)

    def test_gluing_connects_disconnected_local_covers(self):
        raw = annulus_family()
        raw["constraints"] = {"matrix": [], "rhs": []}
        raw["pieces"][0]["monodromy"] = [expression(0, [0])]
        result = optimize_cover_family(raw)
        self.assertEqual(result["optimization"]["minimum_components"], 1)
        concrete = realize_family(raw, result["optimization"]["parameters"])
        local = classify_cover({**concrete["pieces"][0], "sheets": raw["sheets"]})
        self.assertEqual(local["component_count"], raw["sheets"])
        self.assertEqual(literal_components(raw, result["optimization"]["parameters"]), 1)

    def test_empty_generator_and_one_sheet_cases(self):
        raw = {"sheets": 7, "variables": 0,
               "pieces": [{"surface": {"orientable": True, "genus": 0,
                                         "boundary_components": 1}, "monodromy": []}],
               "seams": [], "constraints": {"matrix": [], "rhs": []}}
        result = optimize_cover_family(raw)
        self.assertEqual(result["optimization"]["minimum_components"], 7)
        self.assertTrue(verify_cover_family_certificate(raw, result))
        raw["sheets"] = 1
        self.assertEqual(optimize_cover_family(raw)["optimization"]["minimum_components"], 1)

    def test_boundary_direction_produces_congruence(self):
        raw = annulus_family(8)
        raw["pieces"][0]["monodromy"] = [expression(0, [1])]
        raw["seams"][0]["direction"] = 1
        raw["seams"][0]["shift"] = expression(0, [0])
        raw["constraints"] = {"matrix": [], "rhs": []}
        result = optimize_cover_family(raw)
        self.assertEqual(result["optimization"]["solution_count"], 2)
        self.assertEqual(result["optimization"]["minimum_components"], 4)
        for z in range(8):
            expected = literal_components(raw, [z])
            if expected is None:
                with self.assertRaises(ValueError):
                    realize_family(raw, [z])
            else:
                self.assertEqual(component_count_at(raw, [z]), expected)

    def test_infeasible_seam(self):
        raw = annulus_family(7)
        raw["pieces"][0]["monodromy"] = [expression(1, [0])]
        raw["seams"][0]["direction"] = 1
        result = optimize_cover_family(raw)
        self.assertFalse(result["optimization"]["feasible"])
        self.assertTrue(verify_cover_family_certificate(raw, result))
        mutation = deepcopy(result)
        mutation["optimization"]["obstruction"]["multipliers"] = [0] * len(
            mutation["optimization"]["obstruction"]["multipliers"])
        self.assertFalse(verify_cover_family_certificate(raw, mutation))

    def test_random_literal_families(self):
        rng = random.Random(20261008)
        feasible = infeasible = comparisons = 0
        for trial in range(120):
            modulus = rng.randrange(2, 9)
            variables = trial % 3
            piece_count = 1 + trial % 4
            edges = [(i, i + 1) for i in range(piece_count - 1)]
            if trial % 2:
                edges.append((piece_count - 1, 0))
            degrees = [0] * piece_count
            for u, v in edges:
                degrees[u] += 1
                degrees[v] += 1
            def random_expression():
                return expression(rng.randrange(modulus),
                                  [rng.randrange(modulus) for _ in range(variables)])
            pieces = []
            for degree in degrees:
                boundaries = max(1, degree + 1)
                pieces.append({"surface": {"orientable": True, "genus": trial % 2,
                                            "boundary_components": boundaries},
                               "monodromy": [random_expression() for _ in
                                              range(2 * (trial % 2) + boundaries - 1)]})
            ports = [0] * piece_count
            seams = []
            for u, v in edges:
                left = [u, ports[u]]
                ports[u] += 1
                right = [v, ports[v]]
                ports[v] += 1
                seams.append({"left": left, "right": right,
                              "direction": rng.choice([-1, 1]), "shift": random_expression()})
            raw = {"sheets": modulus, "variables": variables, "pieces": pieces,
                   "seams": seams, "constraints": {"matrix": [], "rhs": []}}
            values = []
            for parameters in product(range(modulus), repeat=variables):
                expected = literal_components(raw, parameters)
                if expected is not None:
                    values.append(expected)
                    comparisons += 1
                    self.assertEqual(component_count_at(raw, parameters), expected)
            result = optimize_cover_family(raw)
            if values:
                feasible += 1
                self.assertEqual(result["optimization"]["solution_count"], len(values))
                self.assertEqual(result["optimization"]["minimum_components"], min(values))
                self.assertTrue(verify_cover_family_certificate(raw, result))
            else:
                infeasible += 1
                self.assertFalse(result["optimization"]["feasible"])
                self.assertTrue(verify_cover_family_certificate(raw, result))
        self.assertGreater(feasible, 20)
        self.assertGreater(infeasible, 20)
        self.assertGreater(comparisons, 300)

    def test_hex_transport_large_modulus(self):
        raw = annulus_family()
        raw["sheets"] = hex(2 ** 20000)
        raw["constraints"] = {"matrix": [], "rhs": []}
        result = optimize_cover_family(raw)
        self.assertEqual(result["optimization"]["minimum_components"], 1)
        self.assertTrue(verify_cover_family_certificate(raw, result))

    def test_large_witness_json_round_trip(self):
        raw = annulus_family(6 ** 4096)
        raw["constraints"] = {"matrix": [], "rhs": []}
        raw["pieces"][0]["monodromy"] = [expression(0, [0])]
        raw["seams"][0]["shift"] = expression(2, [1])
        result = optimize_cover_family(raw)
        serialized = json.loads(json.dumps(json_safe(result)))
        witness = serialized["optimization"]["parameters"][0]
        self.assertIsInstance(witness, str)
        self.assertTrue(verify_cover_family_certificate(raw, serialized))
        # Producer metadata and the unverified count are deliberately ignored.
        serialized["compilation"] = {"message": "0xnot-an-integer"}
        serialized["optimization"]["solution_count"] = "not checked by this certificate"
        self.assertTrue(verify_cover_family_certificate(raw, serialized))
        serialized["optimization"]["parameters"][0] = hex(int(witness, 16) + 1)
        self.assertFalse(verify_cover_family_certificate(raw, serialized))

    def test_large_minimum_json_round_trip(self):
        modulus = 2 ** 20000
        raw = {"sheets": hex(modulus), "variables": 0,
               "pieces": [{"surface": {"orientable": True, "genus": 0,
                                         "boundary_components": 1}, "monodromy": []}],
               "seams": [], "constraints": {"matrix": [], "rhs": []}}
        serialized = json.loads(json.dumps(json_safe(optimize_cover_family(raw))))
        self.assertEqual(serialized["optimization"]["minimum_components"], hex(modulus))
        self.assertTrue(verify_cover_family_certificate(raw, serialized))
        serialized["optimization"]["minimum_components"] = hex(modulus // 2)
        self.assertFalse(verify_cover_family_certificate(raw, serialized))

    def test_large_dual_json_round_trip(self):
        raw = annulus_family(2 ** 20000)
        raw["constraints"] = {"matrix": [[1]], "rhs": [2]}
        raw["pieces"][0]["monodromy"] = [expression(0, [0])]
        serialized = json.loads(json.dumps(json_safe(optimize_cover_family(raw))))
        dual_rows = serialized["optimization"]["dual_rows"]
        position = next((i, j) for i, row in enumerate(dual_rows)
                        for j, value in enumerate(row) if isinstance(value, str))
        self.assertTrue(verify_cover_family_certificate(raw, serialized))
        i, j = position
        dual_rows[i][j] = hex(int(dual_rows[i][j], 16) + 1)
        self.assertFalse(verify_cover_family_certificate(raw, serialized))

    def test_large_infeasibility_json_round_trip(self):
        raw = annulus_family(2 ** 20000)
        raw["constraints"] = {"matrix": [[2]], "rhs": [1]}
        raw["pieces"][0]["monodromy"] = [expression(0, [0])]
        serialized = json.loads(json.dumps(json_safe(optimize_cover_family(raw))))
        obstruction = serialized["optimization"]["obstruction"]
        self.assertIsInstance(obstruction["residue"], str)
        self.assertTrue(any(isinstance(value, str) for value in obstruction["multipliers"]))
        self.assertTrue(verify_cover_family_certificate(raw, serialized))
        obstruction["residue"] = "0x0"
        self.assertFalse(verify_cover_family_certificate(raw, serialized))

    def test_reversed_tree_edge_cycle_holonomy(self):
        # Root 0 reaches 1 against edge orientation: t_1=-2.  The other
        # root edge gives t_2=z, so the remaining edge voltage is 1-z.
        pieces = [{"surface": {"orientable": True, "genus": 0,
                               "boundary_components": 2},
                   "monodromy": [expression(0, [0])]} for _ in range(3)]
        raw = {"sheets": 12, "variables": 1, "pieces": pieces,
               "constraints": {"matrix": [], "rhs": []},
               "seams": [
                   {"left": [1, 0], "right": [0, 0], "direction": -1,
                    "shift": expression(2, [0])},
                   {"left": [1, 1], "right": [2, 0], "direction": 1,
                    "shift": expression(3, [0])},
                   {"left": [0, 1], "right": [2, 1], "direction": -1,
                    "shift": expression(0, [1])},
               ]}
        from math import gcd
        for parameter in range(12):
            expected = gcd(12, 1 - parameter)
            self.assertEqual(literal_components(raw, [parameter]), expected)
            self.assertEqual(component_count_at(raw, [parameter]), expected)
        reversed_seam = deepcopy(raw)
        seam = reversed_seam["seams"][0]
        seam["left"], seam["right"] = seam["right"], seam["left"]
        seam["shift"] = expression(-2, [0])
        for parameter in range(12):
            self.assertEqual(component_count_at(reversed_seam, [parameter]),
                             gcd(12, 1 - parameter))

    def test_nonorientable_peripheral_squares(self):
        pieces = [{"surface": {"orientable": False, "genus": 1,
                               "boundary_components": 1},
                   "monodromy": [expression(0, [1])]},
                  {"surface": {"orientable": False, "genus": 1,
                               "boundary_components": 1},
                   "monodromy": [expression(2, [0])]}]
        raw = {"sheets": 10, "variables": 1, "pieces": pieces,
               "constraints": {"matrix": [], "rhs": []},
               "seams": [{"left": [1, 0], "right": [0, 0], "direction": 1,
                          "shift": expression(3, [1])}]}
        for direction, expected_values in ((1, {2, 7}), (-1, {3, 8})):
            raw["seams"][0]["direction"] = direction
            feasible_values = set()
            for parameter in range(10):
                expected = literal_components(raw, [parameter])
                if expected is not None:
                    feasible_values.add(parameter)
                    self.assertEqual(component_count_at(raw, [parameter]), expected)
            self.assertEqual(feasible_values, expected_values)
            result = optimize_cover_family(raw)
            self.assertEqual(result["optimization"]["solution_count"], 2)
            self.assertEqual(result["optimization"]["minimum_components"], 1)
            self.assertTrue(verify_cover_family_certificate(raw, result))

    def test_certificate_field_types_and_invalid_callback(self):
        raw = annulus_family()
        result = optimize_cover_family(raw)
        for mutate in (
            lambda value: value.update(optimization=None),
            lambda value: value["optimization"].update(feasible=1),
            lambda value: value["optimization"].update(minimum_components=True),
            lambda value: value["optimization"].update(parameters=["12"]),
            lambda value: value["optimization"].update(holonomies=["0xinvalid"]),
            lambda value: value["optimization"].update(dual_rows=None),
            lambda value: value["optimization"].update(connected_member_exists="false"),
        ):
            mutation = deepcopy(result)
            mutate(mutation)
            self.assertFalse(verify_cover_family_certificate(raw, mutation))
        with self.assertRaisesRegex(ValueError, "callable"):
            verify_cover_family_certificate(raw, result, check=3)

    def test_mutated_witness_rejected(self):
        raw = annulus_family()
        result = optimize_cover_family(raw)
        mutation = deepcopy(result)
        mutation["optimization"]["minimum_components"] = 1
        self.assertFalse(verify_cover_family_certificate(raw, mutation))
        mutation = deepcopy(result)
        mutation["optimization"]["parameters"] = [3]
        self.assertFalse(verify_cover_family_certificate(raw, mutation))
        mutation = deepcopy(result)
        mutation["compilation"] = {"untrusted": "deliberately ignored"}
        self.assertTrue(verify_cover_family_certificate(raw, mutation))

    def test_same_connectivity_different_genus(self):
        def pants(shift):
            return {"sheets": 5, "surface": {"orientable": True, "genus": 0,
                                             "boundary_components": 3},
                    "monodromy": [{"sign": 1, "shift": 1}, {"sign": 1, "shift": shift}]}
        a, b = classify_cover(pants(1)), classify_cover(pants(4))
        self.assertEqual((a["component_count"], b["component_count"]), (1, 1))
        self.assertEqual((a["families"][0]["genus"], b["families"][0]["genus"]), (2, 0))

    def test_invalid_schema_rejected(self):
        for mutate in (
            lambda raw: raw.update(variables=True),
            lambda raw: raw.update(sheets=0),
            lambda raw: raw["seams"][0].update(direction=0),
            lambda raw: raw["seams"][0].update(right=[0, 0]),
            lambda raw: raw["pieces"][0]["monodromy"][0].update(coefficients=[]),
        ):
            raw = annulus_family()
            mutate(raw)
            with self.assertRaises(ValueError):
                compile_family(raw)

    def test_disconnected_base_not_optimized_componentwise(self):
        raw = annulus_family()
        raw["pieces"].append(deepcopy(raw["pieces"][0]))
        with self.assertRaisesRegex(ValueError, "connected"):
            compile_family(raw)

    def test_cancellation_propagates(self):
        class Cancelled(Exception):
            pass
        def check():
            raise Cancelled()
        with self.assertRaises(Cancelled):
            optimize_cover_family(annulus_family(), check=check)


if __name__ == "__main__":
    unittest.main()
