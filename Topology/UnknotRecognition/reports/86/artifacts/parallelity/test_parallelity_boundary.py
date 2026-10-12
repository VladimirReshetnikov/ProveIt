"""Source fixtures, literal boundary walks, hostile proofs, and binary stress."""

from contextlib import ExitStack
from copy import deepcopy
import itertools
import json
from pathlib import Path
import random
import unittest
from unittest.mock import patch

import fastunknot
from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
from normal_orbit_research.fixtures import layered_torus
from tests.test_normal_surface_orbits import relabel

from parallelity_boundary import parallelity_boundary_interface, disc_replacement_plan
from parallelity_boundary_reference import literal_boundary_interface
from parallelity_boundary_verify import verify_parallelity_boundary_interface


ROOT = Path(fastunknot.__file__).resolve().parents[2]


def disc_geometry(degree, selected):
    labels = {edge: port for port, edge in enumerate(selected)}
    polygon = dict(id=0, start=0, stop=1, rank_start=1, rank_stop=2,
                   vertices=[{} for _ in range(degree)],
                   corner_starts=list(range(degree)))
    free, ports = [], [None]*len(selected)
    for side in range(degree):
        record = dict(polygon=0, edge=side, rank_start=1, rank_stop=2,
                      original_boundary=side not in labels)
        if side in labels:
            port = labels[side]
            record['port'] = port
            ports[port] = dict(id=port, polygon=0, edge=side, rank=1)
        free.append(record)
    return dict(corner_points=degree, polygon_points=1, polygons=[polygon],
                free_edges=free, ports=ports, gluings=[])


def band_geometry(twisted):
    geometry = disc_geometry(4, [0, 2])
    geometry['free_edges'] = [edge for edge in geometry['free_edges']
                              if edge['edge'] in (0, 2)]
    geometry['gluings'] = [dict(left=0, right=0, left_edge=1, right_edge=3,
                                rank_start=1, rank_stop=2, left_map=[1, -1],
                                right_map=[1, -1], ends_reverse=not twisted,
                                fibre_flip=twisted)]
    return geometry


def disc_profile(ports, multiplicity=1):
    return dict(euler_characteristic=1, boundary_components=1, orientable=True,
                product=True, genus=0, crosscaps=None, handles=[1, 0, 0],
                original_boundary_edges=0, core_ports=ports, multiplicity=multiplicity)


class ParallelityBoundaryTests(unittest.TestCase):
    def checked_geometry(self, geometry):
        result = parallelity_boundary_interface(geometry, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        self.assertEqual(result['interface'], literal_boundary_interface(geometry))
        self.assertTrue(verify_parallelity_boundary_interface(geometry, result['certificate']))
        return result

    def checked_source(self, raw, coordinates):
        source = normal_cut_parallelity(raw, coordinates, record_certificate=True)
        self.assertEqual(source['status'], 'COMPLETE')
        self.assertTrue(verify_normal_cut_parallelity(raw, coordinates, source['certificate']))
        result = self.checked_geometry(source['geometry'])
        interface = result['interface']
        self.assertEqual(interface['attachment_euler_characteristic'],
                         source['summary']['attachment_euler_characteristic'])
        self.assertEqual(interface['core_attachment_vertices'],
                         source['summary']['core_attachment_vertices'])
        plan = disc_replacement_plan(interface, source['summary']['base_profiles'])
        self.assertLessEqual(plan['relative_one_handles']+plan['relative_two_handles'],
                             interface['port_count'])
        return source, result, plan

    def test_every_boundary_marking_of_small_discs(self):
        for degree in range(1, 7):
            for selected_count in range(degree+1):
                for selected in itertools.combinations(range(degree), selected_count):
                    with self.subTest(degree=degree, selected=selected):
                        result = self.checked_geometry(disc_geometry(degree, selected))
                        plan = disc_replacement_plan(result['interface'],
                                                     [disc_profile(list(range(len(selected))))])
                        if not selected:
                            self.assertEqual(plan['isolated_balls'], 1)
                        elif len(selected) == degree:
                            self.assertEqual(plan['relative_two_handles'], 1)
                        else:
                            chosen = set(selected)
                            runs = sum(side in chosen and (side-1) % degree not in chosen
                                       for side in range(degree))
                            self.assertEqual(plan['relative_one_handles'], runs-1)
                            self.assertEqual(plan['relative_two_handles'], 0)

    def test_distinct_endpoint_flags_with_coincident_addresses(self):
        result = self.checked_geometry(disc_geometry(1, [0]))
        self.assertEqual(result['interface']['endpoint_vertices'], [[0, 1]])
        self.assertEqual(result['interface']['gaps'][0]['ends'], [0, 1])
        self.assertTrue(result['interface']['gaps'][0]['zero_length'])

    def test_annulus_and_mobius_boundary_fibre_transport(self):
        annulus = self.checked_geometry(band_geometry(False))['interface']
        mobius = self.checked_geometry(band_geometry(True))['interface']
        self.assertEqual(annulus['marked_boundary_components'], 2)
        self.assertEqual(mobius['marked_boundary_components'], 1)
        self.assertTrue(all(gap['fibre_flip'] for gap in mobius['gaps']))
        self.assertFalse(mobius['boundary_cycles'][0]['fibre_holonomy'])

    def test_partial_disc_attachment_can_add_two_one_handles(self):
        result = self.checked_geometry(disc_geometry(8, [0, 2, 3, 6]))
        plan = disc_replacement_plan(result['interface'], [disc_profile([0, 1, 2, 3])])
        self.assertEqual(plan['relative_one_handles'], 2)
        self.assertEqual(plan['records'][0]['attaching_intervals'], 3)
        self.assertEqual(plan['records'][0]['relative_euler_characteristic'], -2)

    def test_layered_meridians_and_one_sided_sources(self):
        for tetrahedra in (1, 2, 4, 8):
            raw, meridian = layered_torus(tetrahedra)
            for multiple in (0, 1, 2, 5):
                self.checked_source(raw, [[multiple*x for x in row] for row in meridian])
        raw, _ = layered_torus(1)
        for multiple in range(1, 10):
            self.checked_source(raw, [[0, 0, 0, 0, 0, multiple, 0]])

    def test_source_partial_discs_are_collars(self):
        raw, meridian = layered_torus(2)
        _, result, plan = self.checked_source(raw, [[3*x for x in row] for row in meridian])
        self.assertEqual(result['interface']['port_count'], 2)
        self.assertEqual(plan['relative_one_handles'], 0)
        self.assertEqual(plan['relative_two_handles'], 0)
        self.assertEqual(plan['isolated_balls'], 2)
        attached = [row for row in plan['records'] if row['core_ports']]
        self.assertEqual(len(attached), 2)
        self.assertTrue(all(row['attaching_intervals'] == 1 for row in attached))

    def test_two_handle_only_base_full_attachment(self):
        bank = json.loads((ROOT/'synthesis/data/parallelity-audit.json').read_text())
        case = next(row for row in bank['source_proofs']
                    if row['id'] == 'pilot/fibonacci_lst_02/0')
        source, result, plan = self.checked_source(case['triangulation'], case['coordinates'])
        self.assertEqual(result['interface']['port_count'], 8)
        self.assertEqual(len(source['summary']['base_profiles']), 1)
        self.assertEqual(source['summary']['base_profiles'][0]['handles'], [0, 0, 1])
        self.assertTrue(result['interface']['boundary_cycles'][0]['full_core_circle'])
        self.assertEqual(plan['relative_two_handles'], 1)

    def test_rich_source_fixtures(self):
        bank = json.loads((ROOT/'synthesis/data/cut-complement-audit.json').read_text())
        prefixes = ('interior_1_2/', 'finite_trefoil/', 'finite_figureEight/',
                    'solid_torus_sum_rp3/', 'solid_torus_sum_s2xs1/')
        checked = 0
        for case in bank['source_proofs']:
            if case['id'].startswith(prefixes):
                self.checked_source(case['triangulation'], case['coordinates'])
                checked += 1
        self.assertGreater(checked, 10)

    def test_source_relabellings(self):
        randomizer = random.Random(26101219)
        for tetrahedra in (1, 2, 4):
            raw, meridian = layered_torus(tetrahedra)
            vector = [[3*x for x in row] for row in meridian]
            for _ in range(4):
                changed, rows = relabel(raw, vector, randomizer)
                self.checked_source(changed, rows)

    def test_large_binary_multiplicity_exact_json_and_independent_replay(self):
        raw, meridian = layered_torus(4)
        multiple = 1 << 8192
        source = normal_cut_parallelity(raw, [[multiple*x for x in row] for row in meridian])
        geometry = source['geometry']
        result = parallelity_boundary_interface(geometry, record_certificate=True)
        self.assertEqual(result['status'], 'COMPLETE')
        with self.assertRaises(ValueError):
            literal_boundary_interface(geometry)
        proof = json.loads(json.dumps(json_safe(result['certificate'])))
        disabled = ('parallelity_boundary.parallelity_boundary_interface',
                    'parallelity_boundary._queries', 'parallelity_boundary._groups',
                    'parallelity_boundary._assemble')
        with ExitStack() as stack:
            for name in disabled:
                stack.enter_context(patch(name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_parallelity_boundary_interface(geometry, proof))
        plan = disc_replacement_plan(result['interface'], source['summary']['base_profiles'])
        self.assertEqual(plan['isolated_balls'], multiple-1)
        self.assertLess(result['interface']['port_count'], 20)

    def test_shared_caps_hostile_proofs_and_cancellation(self):
        raw, rows = layered_torus(2)
        geometry = normal_cut_parallelity(raw, rows)['geometry']
        result = parallelity_boundary_interface(geometry, record_certificate=True)
        cycles = sum(stat['orbit_cycles'] for stat in result['stats'].values())
        self.assertGreater(cycles, 0)
        for cap in (0, cycles-1):
            partial = parallelity_boundary_interface(geometry, max_cycles=cap,
                                                     record_certificate=True)
            self.assertEqual(partial['status'], 'INCONCLUSIVE')
            self.assertNotIn('interface', partial)
            self.assertNotIn('certificate', partial)
        exact = parallelity_boundary_interface(geometry, max_cycles=cycles)
        self.assertEqual(exact['interface'], result['interface'])
        proof = result['certificate']
        operations = sum(len(p['orbit_proof']['operations'])
                         for p in proof['orbit_proofs'].values())
        self.assertFalse(verify_parallelity_boundary_interface(
            geometry, proof, max_operations=operations-1))
        self.assertTrue(verify_parallelity_boundary_interface(
            geometry, proof, max_operations=operations))
        bad = []
        forged = deepcopy(proof)
        forged['interface']['gaps'][0]['zero_length'] ^= True
        bad.append(forged)
        forged = deepcopy(proof)
        forged['interface']['boundary_cycles'][0]['ports'][0]['entry_end'] ^= 1
        bad.append(forged)
        forged = deepcopy(proof)
        forged['interface']['gaps'][0]['fibre_flip'] ^= True
        bad.append(forged)
        forged = deepcopy(proof)
        forged['geometry_sha256'] = '0'*64
        bad.append(forged)
        forged = deepcopy(proof)
        forged['orbit_proofs']['gaps']['histogram'][0]['weight'][0] += 1
        bad.append(forged)
        for forged in bad:
            self.assertFalse(verify_parallelity_boundary_interface(geometry, forged))
        def cancel():
            raise ValueError('cancelled')
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            parallelity_boundary_interface(geometry, check=cancel)
        with self.assertRaisesRegex(ValueError, 'cancelled'):
            verify_parallelity_boundary_interface(geometry, proof, check=cancel)


if __name__ == '__main__':
    unittest.main()
