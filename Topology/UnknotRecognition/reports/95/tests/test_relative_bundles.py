"""Geometric incidence compilation: native smoke and adversarial finite replay.

The synthetic helpers encode explicit standard relative topological models;
they are not claimed to be complete native normal-cut source certificates.
The enclosing native test uses a real triangulation and normal coordinates.
"""

from copy import deepcopy
import json
from pathlib import Path
import unittest

from relative_bundles import compile_relative_bundles, census_after_complete_cancellation
from relative_bundles_verify import replay_relative_bundle_compilation


def standard_relative_model(core_ranks, bases):
    """Solid-torus/ball cores and disjoint vertical annulus attachments.

    Each base record is (chi, boundary_count, orientable, [(core, winding),...]).
    The attached annulus slope on a solid torus is (winding,1); zero winding
    is a nullhomotopic annulus in a ball region.  Repeated annuli on one core
    are parallel in these tests.  Port-chart metadata represents the relevant
    local rectangles; all unused native polygon data are intentionally absent.
    """
    zero = [dict(id=i) for i in range(len(core_ranks))]
    one, core_edge = [], {}
    for core, rank in enumerate(core_ranks):
        if rank not in (0, 1):
            raise ValueError("test model permits balls and solid tori")
        if rank:
            h = len(one)
            core_edge[core] = h
            one.append(dict(id=h, ends=[core, core], tetrahedron=100 + h,
                            face=0, target_tetrahedron=100 + h, target_face=1))
    geometry = dict(core=dict(handles0=zero, handles1=one, handles2=[], handles3=[]),
                    ports=[], polygons=[])
    profiles, interfaces = [], []
    for chi, boundary, orientable, circles in bases:
        owned = []
        for core, winding in circles:
            word = []
            for crossing in range(max(1, winding)):
                p = len(geometry["ports"])
                if winding:
                    h = core_edge[core]
                    polygon = len(geometry["polygons"])
                    geometry["polygons"].append(dict(
                        kind="edge_cap", edges=[dict(kind="face_sector")],
                        vertices=[dict(tetrahedron=100 + h, face=0),
                                  dict(tetrahedron=100 + h, face=1)]))
                    port = dict(id=p, core_dimension=1, core_handle=h,
                                polygon=polygon, edge=0)
                else:
                    port = dict(id=p, core_dimension=0, core_handle=core)
                geometry["ports"].append(port)
                owned.append(p)
                word.append(p + 1)
            interfaces.append(dict(kind="circle", word=word))
        profiles.append(dict(euler_characteristic=chi, boundary_components=boundary,
                             orientable=orientable, product=orientable,
                             multiplicity=1, core_ports=owned))
    summary = dict(base_profiles=profiles,
                   core_euler_characteristic=len(zero) - len(one),
                   bundle_euler_characteristic=sum(p["euler_characteristic"] for p in profiles),
                   attachment_euler_characteristic=0)
    return geometry, summary, dict(attachment_components=interfaces)


class RelativeBundlesTests(unittest.TestCase):
    def compile_and_replay(self, model):
        answer = compile_relative_bundles(*model)
        self.assertEqual(answer["status"], "READY")
        checked = replay_relative_bundle_compilation(*model, answer["certificate"])
        self.assertIsNotNone(checked)
        self.assertEqual(checked["counts"], answer["counts"])
        return answer

    def test_saturated_annulus_joins_two_core_components(self):
        model = standard_relative_model((1, 1), [(0, 2, True, [(0, 1), (1, 3)])])
        answer = self.compile_and_replay(model)
        self.assertEqual(answer["counts"], {0: {0: 1, 1: 2}})
        component = answer["joined_components"][0]
        self.assertEqual(component["core_components"], [0, 1])
        self.assertEqual(component["private_one_handles"], 0)
        self.assertEqual(component["genus_if_complete"], 1)

    def test_two_saturated_annuli_connect_three_cores(self):
        model = standard_relative_model((1, 1, 1), [
            (0, 2, True, [(0, 1), (1, 1)]),
            (0, 2, True, [(1, 1), (2, 1)]),
        ])
        answer = self.compile_and_replay(model)
        self.assertEqual(answer["counts"], {0: {0: 1, 1: 1}, 1: {1: 1, 2: 1}})
        self.assertEqual(answer["joined_components"][0]["private_one_handles"], 0)
        self.assertEqual(answer["joined_components"][0]["genus_if_complete"], 1)

    def test_saturated_mobius_and_torus_private_families(self):
        for chi, orientable, private, genus in [(0, False, 1, 1), (-1, True, 2, 2)]:
            model = standard_relative_model((1,), [(chi, 1, orientable, [(0, 1)])])
            answer = self.compile_and_replay(model)
            self.assertEqual(answer["counts"], {0: {0: 1}})
            self.assertEqual(answer["joined_components"][0]["private_one_handles"], private)
            self.assertEqual(census_after_complete_cancellation(answer)["histogram"],
                             [dict(genus=genus, multiplicity=1)])

    def test_binary_base_genus_never_expands_private_columns(self):
        genus = 1 << 4096
        model = standard_relative_model((1,), [(1 - 2 * genus, 1, True, [(0, 1)])])
        answer = self.compile_and_replay(model)
        self.assertEqual(answer["counts"], {0: {0: 1}})
        self.assertEqual(answer["stats"]["active_entries"], 1)
        self.assertEqual(answer["joined_components"][0]["private_one_handles"], 2 * genus)
        self.assertEqual(answer["joined_components"][0]["genus_if_complete"], 2 * genus)

    def test_unsaturated_annulus_is_only_a_collar(self):
        model = standard_relative_model((1,), [(0, 2, True, [(0, 3)])])
        answer = self.compile_and_replay(model)
        self.assertEqual(answer["counts"], {})
        self.assertEqual(answer["joined_components"][0]["private_one_handles"], 0)
        self.assertEqual(census_after_complete_cancellation(answer)["histogram"],
                         [dict(genus=1, multiplicity=1)])

    def test_saturated_disk_agrees_with_absorption_incidence(self):
        answer = self.compile_and_replay(
            standard_relative_model((1,), [(1, 1, True, [(0, 1)])]))
        self.assertEqual(answer["counts"], {0: {0: 1}})
        self.assertEqual(answer["joined_components"][0]["private_one_handles"], 0)
        self.assertEqual(census_after_complete_cancellation(answer)["histogram"],
                         [dict(genus=0, multiplicity=1)])

    def test_empty_active_row_never_claims_a_ball(self):
        answer = self.compile_and_replay(
            standard_relative_model((0,), [(0, 1, False, [(0, 0)])]))
        self.assertEqual(answer["status"], "READY")
        self.assertEqual(answer["counts"], {0: {}})
        self.assertNotIn("census", answer)
        self.assertEqual(answer["joined_components"][0]["genus_if_complete"], 0)
        # The actual group is Z/2.  The conditional arithmetic value cannot
        # replace the missing (and impossible in this model) unit cancellation.

    def test_all_large_core_crossings_remain_a_raw_obstruction(self):
        answer = self.compile_and_replay(
            standard_relative_model((1, 1), [(0, 2, True, [(0, 2), (1, 3)])]))
        self.assertEqual(answer["counts"], {0: {0: 2, 1: 2}})
        self.assertEqual(answer["joined_components"][0]["genus_if_complete"], 1)

    def test_unattached_profiles_keep_binary_multiplicity(self):
        model = standard_relative_model((1,), [(0, 2, True, [])])
        model[1]["base_profiles"][0]["multiplicity"] = 1 << 4096
        answer = self.compile_and_replay(model)
        self.assertEqual(answer["isolated_bundles"],
                         [dict(base_profile=0, genus=1, multiplicity=1 << 4096)])

    def test_hostile_compilation_records_are_rejected(self):
        model = standard_relative_model((1, 1), [(0, 2, True, [(0, 1), (1, 3)])])
        answer = self.compile_and_replay(model)
        changes = [
            lambda p: p["rows"][0]["counts"].pop(),
            lambda p: p["rows"][0]["counts"][0].__setitem__(1, True),
            lambda p: p["bases"][0].update(saturated=False),
            lambda p: p["bases"][0].update(relative_one_handles=2),
            lambda p: p["joined_components"][0].update(private_one_handles=1),
            lambda p: p["joined_components"][0].update(genus_if_complete=False),
            lambda p: p["attachments"][0]["crossings"][0].update(sign=-1),
            lambda p: p["attachments"][0].update(core_component=1),
            lambda p: p.update(source_euler_characteristic=True),
            lambda p: p.update(forest=[0]),
            lambda p: p.update(schema="disk-bundle-absorption-v1"),
        ]
        for change in changes:
            proof = deepcopy(answer["certificate"])
            change(proof)
            self.assertIsNone(replay_relative_bundle_compilation(*model, proof))

    def test_profile_and_port_contracts_are_checked(self):
        model = standard_relative_model((1,), [(0, 1, False, [(0, 1)])])
        proof = self.compile_and_replay(model)["certificate"]
        for field, value in [("boundary_components", True), ("multiplicity", 2),
                             ("orientable", True), ("euler_characteristic", 1)]:
            bad = deepcopy(model)
            bad[1]["base_profiles"][0][field] = value
            with self.assertRaises(ValueError):
                compile_relative_bundles(*bad)
            self.assertIsNone(replay_relative_bundle_compilation(*bad, proof))
        bad = deepcopy(model)
        bad[2]["attachment_components"][0]["word"] *= 2
        with self.assertRaises(ValueError):
            compile_relative_bundles(*bad)
        self.assertIsNone(replay_relative_bundle_compilation(*bad, proof))

    def test_callback_exceptions_propagate_after_initial_checks(self):
        model = standard_relative_model((1,), [(-1, 1, True, [(0, 1)])])
        answer = self.compile_and_replay(model)

        class Cancel:
            def __init__(self, exception):
                self.calls = 0
                self.exception = exception

            def __call__(self):
                self.calls += 1
                if self.calls == 4:
                    raise self.exception("requested cancellation")

        for exception in (ValueError, TypeError, RuntimeError):
            with self.assertRaisesRegex(exception, "requested cancellation"):
                compile_relative_bundles(*model, check=Cancel(exception))
            with self.assertRaisesRegex(exception, "requested cancellation"):
                replay_relative_bundle_compilation(*model, answer["certificate"],
                                                   check=Cancel(exception))

    def test_native_normal_cut_and_independent_source_replay(self):
        from fastunknot.normal_parallelity import normal_cut_parallelity
        from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
        from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
        from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
        from normal_orbit_research.fixtures import layered_torus

        triangulation, coordinates = layered_torus(2)
        source = normal_cut_parallelity(triangulation, coordinates, record_certificate=True)
        boundary = normal_parallelity_boundary_words(triangulation, coordinates,
                                                     record_certificate=True)
        self.assertTrue(verify_normal_cut_parallelity(triangulation, coordinates,
                                                     source["certificate"]))
        self.assertTrue(verify_parallelity_boundary_words(triangulation, coordinates,
                                                          boundary["certificate"]))
        self.compile_and_replay((source["geometry"], source["summary"], boundary["skeleton"]))


if __name__ == "__main__":
    unittest.main()
