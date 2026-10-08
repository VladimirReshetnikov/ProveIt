"""Independent finite-sheet and certificate tests for regular cover gluings."""

from copy import deepcopy
from itertools import product
import random
import unittest

from fastunknot.regular_cover_gluing import (
    RegularCoverAssembly, compare_assemblies, verify_certificate,
    transport_witness, verify_transport, phase_orbit_count, canonicalize_assembly,
)
from regular_cover_research.oracle import (
    ExpandedGroup, element, make_assembly, brute_phase_orbits,
)


class RegularCoverGluingTests(unittest.TestCase):
    def compare_expanded(self, source, target, marks=()):
        raw_marks = list(marks)
        group = ExpandedGroup(source["group"]["kind"], source["group"]["modulus"])
        expected = group.all_gauges(source, target, marks)
        certificate = compare_assemblies(source, target, raw_marks)
        self.assertTrue(verify_certificate(source, target, raw_marks, certificate))
        self.assertEqual(certificate["isomorphism_count"], len(expected))
        self.assertEqual(certificate["equivalent"], bool(expected))
        actual = set()
        if expected:
            choices = []
            for component in certificate["components"]:
                roots = []
                for branch in component["branches"]:
                    if "obstruction" not in branch:
                        roots.extend(element(branch["parity"], t)
                                     for t in range(branch["residue"], group.modulus,
                                                    branch["modulus"]))
                choices.append(roots)
            for roots in product(*choices):
                gauges = transport_witness(source, target, certificate, list(roots))
                self.assertTrue(verify_transport(source, target, raw_marks, gauges))
                actual.add(tuple(group.encode(x) for x in gauges))
        self.assertEqual(actual, expected)
        if not marks:
            normal_source = canonicalize_assembly(source)
            normal_target = canonicalize_assembly(target)
            self.assertEqual(normal_source["key"] == normal_target["key"], bool(expected))
            normalized = deepcopy(source)
            for edge, phase in zip(normalized["edges"], normal_source["phases"]):
                edge["phase"] = phase
            self.assertTrue(verify_transport(source, normalized, [], normal_source["gauges"]))
        return certificate

    def test_all_single_edge_phase_pairs(self):
        for kind in ("cyclic", "dihedral"):
            for modulus in range(1, 5):
                group = ExpandedGroup(kind, modulus)
                for a, b in product(range(group.size), repeat=2):
                    source = make_assembly(kind, modulus, 2, [(0, 1)], [group.decode(a)])
                    target = make_assembly(kind, modulus, 2, [(0, 1)], [group.decode(b)])
                    self.compare_expanded(source, target)

    def test_random_cycles_loops_parallel_edges_and_marks(self):
        rng = random.Random(8675309)
        graphs = [(2, [(0, 1), (0, 1)]), (2, [(0, 0), (0, 1), (1, 1)]),
                  (3, [(0, 1), (1, 2), (2, 0)]), (3, [(1, 0)])]
        for kind in ("cyclic", "dihedral"):
            for modulus in range(1, 6):
                group = ExpandedGroup(kind, modulus)
                for _ in range(24):
                    vertices, graph = rng.choice(graphs)
                    source = make_assembly(kind, modulus, vertices, graph,
                                           [group.decode(rng.randrange(group.size)) for _ in graph],
                                           extras=(2, 3))
                    if rng.randrange(2):
                        target = group.change_gauges(
                            source, [rng.randrange(group.size) for _ in range(vertices)])
                    else:
                        target = deepcopy(source)
                        for edge in target["edges"]:
                            edge["phase"] = group.decode(rng.randrange(group.size))
                    marks = []
                    for _ in range(rng.randrange(4)):
                        vertex = rng.randrange(vertices)
                        mark = {"kind": rng.choice(("point", "boundary")), "block": vertex,
                                "source": group.decode(rng.randrange(group.size)),
                                "target": group.decode(rng.randrange(group.size))}
                        if mark["kind"] == "boundary":
                            mark["boundary"] = rng.randrange(
                                source["blocks"][vertex]["surface"]["boundary_components"])
                        marks.append(mark)
                    self.compare_expanded(source, target, marks)

    def test_every_boundary_lift_pair(self):
        for kind in ("cyclic", "dihedral"):
            for modulus in range(1, 8):
                group = ExpandedGroup(kind, modulus)
                source = make_assembly(kind, modulus, 1, [], extras=(2, 3))
                count = source["blocks"][0]["surface"]["boundary_components"]
                for boundary in range(count):
                    for x, y in product(range(group.size), repeat=2):
                        mark = {"kind": "boundary", "block": 0, "boundary": boundary,
                                "source": group.decode(x), "target": group.decode(y)}
                        self.compare_expanded(source, source, [mark])

    def test_mixed_modulus_crt_and_obstruction_pair(self):
        source = make_assembly("cyclic", 12, 1, [], extras=(4, 6))
        marks = [
            {"kind": "boundary", "block": 0, "boundary": 0,
             "source": element(), "target": element(0, 1)},
            {"kind": "boundary", "block": 0, "boundary": 1,
             "source": element(), "target": element(0, 3)},
        ]
        certificate = self.compare_expanded(source, source, marks)
        self.assertEqual(certificate["components"][0]["branches"][0]["residue"], 9)
        marks[1]["target"] = element(0, 2)
        certificate = self.compare_expanded(source, source, marks)
        self.assertEqual(certificate["components"][0]["branches"][0]["obstruction"]["kind"], "pair")

    def test_reflection_congruence_gcd_obstruction(self):
        source = make_assembly("dihedral", 6, 1, [(0, 0)], [element(1, 0)])
        target = deepcopy(source)
        target["edges"][0]["phase"] = element(1, 1)
        certificate = self.compare_expanded(source, target)
        self.assertFalse(certificate["equivalent"])
        self.assertTrue(all(b["obstruction"]["kind"] == "unary"
                            for b in certificate["components"][0]["branches"]))

    def test_disconnected_roots_are_independent(self):
        source = make_assembly("dihedral", 5, 3, [])
        certificate = self.compare_expanded(source, source)
        self.assertEqual(certificate["isomorphism_count"], 10 ** 3)

    def test_phase_orbit_count_cyclic(self):
        graph = [(0, 1), (0, 1), (1, 0)]
        for modulus in range(1, 6):
            self.assertEqual(brute_phase_orbits("cyclic", modulus, 2, graph), modulus ** 2)
            self.assertEqual(phase_orbit_count("cyclic", modulus, 2), modulus ** 2)

    def test_phase_orbit_count_dihedral(self):
        graph = [(0, 0), (0, 0)]
        for modulus in range(1, 7):
            if modulus % 2:
                expected = ((2 * modulus) ** 2 + (modulus - 1) * modulus ** 2
                            + modulus * 2 ** 2) // (2 * modulus)
            else:
                expected = (2 * (2 * modulus) ** 2 + (modulus - 2) * modulus ** 2
                            + modulus * 4 ** 2) // (2 * modulus)
            self.assertEqual(brute_phase_orbits("dihedral", modulus, 1, graph), expected)
            self.assertEqual(phase_orbit_count("dihedral", modulus, 2), expected)

    def test_canonical_keys_exhaustive_phase_orbits(self):
        for kind in ("cyclic", "dihedral"):
            for modulus in range(1, 7):
                group = ExpandedGroup(kind, modulus)
                keys = set()
                for a, b in product(range(group.size), repeat=2):
                    source = make_assembly(kind, modulus, 1, [(0, 0), (0, 0)],
                                           [group.decode(a), group.decode(b)])
                    result = canonicalize_assembly(source)
                    keys.add(result["key"])
                    for gauge in range(group.size):
                        changed = group.change_gauges(source, [gauge])
                        self.assertEqual(canonicalize_assembly(changed)["key"], result["key"])
                self.assertEqual(len(keys), brute_phase_orbits(
                    kind, modulus, 1, [(0, 0), (0, 0)]))

    def test_nontrivial_boundary_preimage_gluings(self):
        for modulus in range(1, 7):
            annulus = {"surface": {"orientable": True, "genus": 0,
                                   "boundary_components": 2},
                       "monodromy": [element(0, 1)]}
            cyclic = {"group": {"kind": "cyclic", "modulus": modulus},
                      "blocks": [deepcopy(annulus), deepcopy(annulus)],
                      "edges": [{"source": {"block": 0, "boundary": 0},
                                 "target": {"block": 1, "boundary": 1},
                                 "phase": element(0, 1)}]}
            self.compare_expanded(cyclic, cyclic)
            topology = RegularCoverAssembly(cyclic).topology()[0]
            self.assertEqual((topology["genus"], topology["boundary_components"]), (0, 2))

            pants = {"surface": {"orientable": True, "genus": 0,
                                 "boundary_components": 3},
                     "monodromy": [element(0, 1), element(1, 0)]}
            dihedral = {"group": {"kind": "dihedral", "modulus": modulus},
                        "blocks": [deepcopy(pants), deepcopy(pants)],
                        "edges": [{"source": {"block": 0, "boundary": 1},
                                   "target": {"block": 1, "boundary": 1},
                                   "phase": element(1, 2)}]}
            self.compare_expanded(dihedral, dihedral)
            topology = RegularCoverAssembly(dihedral).topology()[0]
            self.assertEqual((topology["genus"], topology["boundary_components"]),
                             (modulus - 1, 2 * modulus + 4))
            dihedral["blocks"][1]["monodromy"][0] = element(0, -1)
            dihedral["edges"][0]["source"]["boundary"] = 0
            dihedral["edges"][0]["target"]["boundary"] = 0
            self.compare_expanded(dihedral, dihedral)
            topology = RegularCoverAssembly(dihedral).topology()[0]
            self.assertEqual((topology["genus"], topology["boundary_components"]),
                             (1, 4 * modulus))

    def test_large_binary_modulus_no_sheet_expansion(self):
        modulus = (1 << 24000) + 27
        source = make_assembly("dihedral", modulus, 3,
                               [(0, 1), (1, 2), (2, 0), (1, 1)],
                               [element(1, 17), element(0, modulus - 5),
                                element(1, 8), element(1, 93)])
        prepared = RegularCoverAssembly(source)
        group = prepared.group
        gauges = [(1, modulus - 1), (0, 1 << 23000), (1, 919)]
        target = deepcopy(source)
        for edge in target["edges"]:
            u, v = edge["source"]["block"], edge["target"]["block"]
            phase = group.parse(edge["phase"])
            new = group.multiply(group.inverse(gauges[u]), group.multiply(phase, gauges[v]))
            edge["phase"] = element(*new)
        mark = {"kind": "point", "block": 2, "source": element(),
                "target": element(*gauges[2])}
        certificate = compare_assemblies(source, target, [mark])
        self.assertTrue(certificate["equivalent"])
        self.assertEqual(certificate["isomorphism_count"], 1)
        self.assertTrue(verify_certificate(source, target, [mark], certificate))
        witness = transport_witness(source, target, certificate)
        self.assertTrue(verify_transport(source, target, [mark], witness))
        self.assertEqual(prepared.topology()[0]["genus"], 2 * modulus * 4 - 3 + 1)

    def test_invalid_inputs_and_base_binding(self):
        valid = make_assembly("dihedral", 5, 2, [(0, 1)])
        examples = []
        bad = deepcopy(valid)
        bad["group"]["modulus"] = 0
        examples.append(bad)
        bad = deepcopy(valid)
        bad["group"]["modulus"] = True
        examples.append(bad)
        bad = deepcopy(valid)
        bad["blocks"][0]["monodromy"][-1] = element()
        examples.append(bad)
        bad = deepcopy(valid)
        bad["edges"].append(deepcopy(bad["edges"][0]))
        examples.append(bad)
        bad = deepcopy(valid)
        bad["edges"][0]["target"]["boundary"] = 1  # nontrivial T monodromy
        examples.append(bad)
        bad = deepcopy(valid)
        bad["blocks"][0]["surface"]["orientable"] = False
        examples.append(bad)
        for raw in examples:
            with self.assertRaises(ValueError):
                RegularCoverAssembly(raw)
        different = make_assembly("dihedral", 7, 2, [(0, 1)])
        with self.assertRaises(ValueError):
            compare_assemblies(valid, different)

    def test_certificates_are_checked_and_direct_witness_is_checked(self):
        source = make_assembly("dihedral", 5, 2, [(0, 1)], [element(1, 3)])
        target = make_assembly("dihedral", 5, 2, [(0, 1)], [element(0, 1)])
        certificate = compare_assemblies(source, target)
        self.assertTrue(verify_certificate(source, target, [], certificate))
        mutations = []
        bad = deepcopy(certificate)
        bad["isomorphism_count"] += 1
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad["components"][0]["branches"][0]["modulus"] = 5
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad["components"][0]["branches"][0] = {"parity": 0, "obstruction": {
            "kind": "unary", "constraint": -1}}
        mutations.append(bad)
        bad = deepcopy(certificate)
        bad["source_paths"][1] = element()
        mutations.append(bad)
        for changed in mutations:
            self.assertFalse(verify_certificate(source, target, [], changed))
        witness = transport_witness(source, target, certificate)
        self.assertTrue(verify_transport(source, target, [], witness))
        witness[0]["shift"] += 1
        self.assertFalse(verify_transport(source, target, [], witness))

    def test_signed_hex_input_and_cancel(self):
        source = make_assembly("cyclic", 12, 1, [])
        source["group"]["modulus"] = "0xc"
        source["blocks"][0]["monodromy"][0]["shift"] = "-0xb"
        self.assertEqual(RegularCoverAssembly(source).group.modulus, 12)

        class Cancelled(RuntimeError):
            pass

        def cancel():
            raise Cancelled("requested cancellation")

        with self.assertRaises(Cancelled):
            compare_assemblies(source, source, check=cancel)
        certificate = compare_assemblies(source, source)
        with self.assertRaises(Cancelled):
            verify_certificate(source, source, [], certificate, check=cancel)


if __name__ == "__main__":
    unittest.main()
