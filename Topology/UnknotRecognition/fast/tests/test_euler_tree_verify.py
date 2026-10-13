"""Independent relaxed-cone duals and exact implicit preorder coverage."""
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
import unittest
from unittest.mock import patch

from fastunknot.normal_euler_tree_verify import (
    verify_euler_relaxation_certificate, verify_euler_branch_tree,
)
from fastunknot.normal_euler_verify import verify_sector_euler_certificate
from fastunknot.normal_surface_geometry import NormalOrbitError
from normal_orbit_research.fixtures import layered_torus


def base(source, mask, schema='normal-euler-relaxation-v1'):
    return dict(schema=schema, status='NO_POSITIVE_EULER',
        source_sha256=sha256(json.dumps(source, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        allowed_types=[list(pair) for pair in mask])


def one_tet_leaf(source, mask=((0, 0), (0, 1)), kind='envelope'):
    proof = base(source, mask)
    proof['proof_kind'] = kind
    if kind == 'envelope':
        proof['multipliers'] = []
    else:
        proof['duals'] = [dict(anchors=[a], multipliers=[]) for a in (0, 1, 2)]
    return proof


def two_tet_leaf():
    source, _ = layered_torus(2)
    proof = base(source, [(0, 0), (0, 1), (1, 0), (1, 1)])
    # A genuine relaxed cone with seven nonpositive anchor objectives. Its
    # componentwise envelope is positive, so a zero envelope dual is false.
    proof.update(proof_kind='anchors', duals=[dict(anchors=[a], multipliers=[[int(a == 2), 1]])
                                            for a in (0, 1, 2, 3, 4, 5, 6)])
    return source, proof


def one_tet_tree():
    source, _ = layered_torus(1)
    proof = base(source, [(0, 0), (0, 1)], 'normal-euler-branch-tree-v1')
    proof['nodes'] = [dict(kind='split', tetrahedron=0),
                     dict(kind='negative', certificate=one_tet_leaf(source, [(0, 0)])),
                     dict(kind='negative', certificate=one_tet_leaf(source, [(0, 1)]))]
    return source, proof


def two_tet_tree():
    source, _ = layered_torus(2)
    proof = base(source, [(0, 0), (0, 1), (1, 0), (1, 1)], 'normal-euler-branch-tree-v1')
    proof['nodes'] = [dict(kind='split', tetrahedron=0)]
    frozen = {
        (0, 0): [(0, 0, 1), (1, 0, 1), (2, 0, 1), (3, 0, 1), (6, 1, 1)],
        (0, 1): [(0, 0, 1), (1, 0, 1), (2, 0, 1)],
        (1, 0): [(0, 0, 1), (1, 0, 1), (6, -1, 2)],
        (1, 1): [(0, 0, 1), (2, 1, 1), (3, 1, 1)],
    }
    for first in (0, 1):
        proof['nodes'].append(dict(kind='split', tetrahedron=1))
        for second in (0, 1):
            leaf = base(source, [(0, first), (1, second)])
            leaf.update(proof_kind='anchors', duals=[dict(anchors=[a], multipliers=[[num, den]])
                        for a, num, den in frozen[first, second]])
            proof['nodes'].append(dict(kind='negative', certificate=leaf))
    return source, proof


def source_model_tree():
    source, _ = layered_torus(2)
    proof = base(source, [(0, 0), (1, 0), (1, 1), (1, 2)],
                 'normal-euler-branch-tree-v1')
    proof['nodes'] = [dict(kind='split', tetrahedron=1)]
    for q in range(3):
        leaf = base(source, [(0, 0), (1, q)], 'normal-euler-relaxation-v2')
        leaf.update(proof_kind='envelope', multipliers=[[int(q == 2), 1]])
        proof['nodes'].append(dict(kind='negative', certificate=leaf))
    return source, proof


class EulerRelaxationVerifierTests(unittest.TestCase):
    def test_source_model_versions_have_distinct_exact_dual_conventions(self):
        source, _ = layered_torus(2)
        old = base(source, [(0, 0), (1, 0)])
        old.update(proof_kind='envelope', multipliers=[[1, 1]])
        new = base(source, [(0, 0), (1, 0)], 'normal-euler-relaxation-v2')
        new.update(proof_kind='envelope', multipliers=[[0, 1]])
        self.assertTrue(verify_euler_relaxation_certificate(source, old))
        self.assertTrue(verify_euler_relaxation_certificate(source, new))
        old['schema'] = 'normal-euler-relaxation-v2'
        new['schema'] = 'normal-euler-relaxation-v1'
        self.assertFalse(verify_euler_relaxation_certificate(source, old))
        self.assertFalse(verify_euler_relaxation_certificate(source, new))

    def test_source_dual_reuse_checks_every_allowed_column_and_only_those_columns(self):
        source, _ = layered_torus(2)
        proof = base(source, [(0, 0), (1, 0), (1, 1)], 'normal-euler-relaxation-v2')
        proof.update(proof_kind='envelope', multipliers=[[0, 1]])
        self.assertTrue(verify_euler_relaxation_certificate(source, proof))
        for mask in ([(0, 0)], [(1, 0)], [(1, 1)], [(0, 0), (1, 1)], []):
            child = deepcopy(proof); child['allowed_types'] = [list(p) for p in mask]
            self.assertTrue(verify_euler_relaxation_certificate(source, child))
        # Column (1,2) is global column 5, not column 0 of a compacted list.
        # The zero dual fails its envelope inequality even when it is the
        # only allowed type. A valid nonzero full-source dual succeeds.
        bad = deepcopy(proof); bad['allowed_types'] = [[1, 2]]
        self.assertFalse(verify_euler_relaxation_certificate(source, bad))
        bad['multipliers'] = [[1, 1]]
        self.assertTrue(verify_euler_relaxation_certificate(source, bad))
        bad = deepcopy(proof); bad['allowed_types'].append([1, 2])
        self.assertFalse(verify_euler_relaxation_certificate(source, bad))

    def test_source_model_requires_full_row_dimensions_and_all_source_anchors(self):
        source, _ = layered_torus(2)
        proof = base(source, [(0, 0), (1, 2)], 'normal-euler-relaxation-v2')
        proof.update(proof_kind='anchors', duals=[
            dict(anchors=[a], multipliers=[[int(a in (2, 6)), 1]]) for a in range(7)])
        self.assertTrue(verify_euler_relaxation_certificate(source, proof))
        for index in range(7):
            bad = deepcopy(proof); bad['duals'].pop(index)
            self.assertFalse(verify_euler_relaxation_certificate(source, bad))
        empty = deepcopy(proof); empty['allowed_types'] = []
        self.assertTrue(verify_euler_relaxation_certificate(source, empty))
        empty['duals'] = [dict(anchors=[], multipliers=[[0, 1]])]
        self.assertFalse(verify_euler_relaxation_certificate(source, empty))
        source3, _ = layered_torus(3)
        full_rows = base(source3, [(0, 0), (1, 1)], 'normal-euler-relaxation-v2')
        full_rows.update(proof_kind='envelope', multipliers=[[0, 1]]*3)
        self.assertTrue(verify_euler_relaxation_certificate(source3, full_rows))
        for values in ([], [[0, 1]], [[0, 1]]*2, [[0, 1]]*4):
            bad = deepcopy(full_rows); bad['multipliers'] = values
            self.assertFalse(verify_euler_relaxation_certificate(source3, bad))
        self.assertFalse(verify_euler_relaxation_certificate(source, full_rows))
        # Even a rewritten digest cannot conceal source row-count changes.
        forged = deepcopy(full_rows)
        forged['source_sha256'] = base(source, [])['source_sha256']
        self.assertFalse(verify_euler_relaxation_certificate(source, forged))

    def test_genuine_multiple_type_masks_and_both_dual_kinds(self):
        source, _ = layered_torus(1)
        for kind in ('anchors', 'envelope'):
            proof = one_tet_leaf(source, kind=kind)
            self.assertTrue(verify_euler_relaxation_certificate(source, proof))
            original = deepcopy(proof)
            self.assertTrue(verify_euler_relaxation_certificate(source, proof))
            self.assertEqual(proof, original)
            # The older compatible-sector parser must remain strict.
            proof['schema'] = 'normal-sector-euler-lp-v1'
            self.assertFalse(verify_sector_euler_certificate(source, proof))
        source, proof = two_tet_leaf()
        self.assertTrue(verify_euler_relaxation_certificate(source, proof))

    def test_every_anchor_is_required_and_envelope_is_a_separate_inequality(self):
        source, proof = two_tet_leaf()
        for index in range(len(proof['duals'])):
            bad = deepcopy(proof); bad['duals'].pop(index)
            self.assertFalse(verify_euler_relaxation_certificate(source, bad))
        for mutation in ('repeat', 'order', 'false_dual', 'bool_anchor', 'extra'):
            bad = deepcopy(proof)
            if mutation == 'repeat': bad['duals'][1] = deepcopy(bad['duals'][0])
            elif mutation == 'order': bad['duals'].reverse()
            elif mutation == 'false_dual': bad['duals'][2]['multipliers'] = [[0, 1]]
            elif mutation == 'bool_anchor': bad['duals'][0]['anchors'] = [False]
            else: bad['duals'][0]['extra'] = 0
            self.assertFalse(verify_euler_relaxation_certificate(source, bad))
        bad = deepcopy(proof)
        bad.pop('duals'); bad.update(proof_kind='envelope', multipliers=[[0, 1]])
        self.assertFalse(verify_euler_relaxation_certificate(source, bad))

    def test_empty_mask_requires_a_complete_empty_anchor_or_envelope(self):
        source, _ = layered_torus(1)
        proof = base(source, [])
        proof.update(proof_kind='anchors', duals=[dict(anchors=[], multipliers=[])])
        self.assertTrue(verify_euler_relaxation_certificate(source, proof))
        proof['duals'] = []
        self.assertFalse(verify_euler_relaxation_certificate(source, proof))
        proof.pop('duals'); proof.update(proof_kind='envelope', multipliers=[])
        self.assertTrue(verify_euler_relaxation_certificate(source, proof))

    def test_positive_sector_and_positive_packets_cannot_be_relaxation_negatives(self):
        source, _ = layered_torus(1)
        for mask in (((0, 2),), ((0, 0), (0, 1), (0, 2))):
            proof = one_tet_leaf(source, mask)
            self.assertFalse(verify_euler_relaxation_certificate(source, proof))
        proof = one_tet_leaf(source)
        proof['status'] = 'POSITIVE_EULER'
        self.assertFalse(verify_euler_relaxation_certificate(source, proof))
        proof['coordinates'] = [[1, 1, 0, 0, 0, 0, 1]]
        self.assertFalse(verify_euler_relaxation_certificate(source, proof))

    def test_exact_numeric_transport_and_hostile_rational_duals(self):
        source, original = two_tet_leaf()
        proof = deepcopy(original)
        for record in proof['duals']:
            record['multipliers'] = [[hex(2*a), hex(2*b)] for a, b in record['multipliers']]
        self.assertTrue(verify_euler_relaxation_certificate(source, proof))
        for value in (None, [1], (1, 1), [1, 0], [1, -1], [True, 1],
                      [1, True], [1.0, 1], ['1', 1], [1, '1']):
            bad = deepcopy(original); bad['duals'][2]['multipliers'][0] = value
            self.assertFalse(verify_euler_relaxation_certificate(source, bad))

    def test_strict_leaf_schema_masks_and_source_binding(self):
        source, _ = layered_torus(1)
        proof = one_tet_leaf(source)
        foreign, _ = layered_torus(2)
        self.assertFalse(verify_euler_relaxation_certificate(foreign, proof))
        for key in proof:
            bad = deepcopy(proof); del bad[key]
            self.assertFalse(verify_euler_relaxation_certificate(source, bad))
        for field, value in (('schema', 'normal-sector-euler-lp-v1'), ('status', 'UNKNOT'),
                             ('source_sha256', '0'*64), ('extra', 0), ('proof_kind', None),
                             ('allowed_types', None), ('allowed_types', [[0, False]]),
                             ('allowed_types', [[True, 0]]), ('allowed_types', [(0, 0)]),
                             ('allowed_types', [[0, 1], [0, 0]]),
                             ('allowed_types', [[0, 0], [0, 0]]),
                             ('allowed_types', [[1, 0]]), ('allowed_types', [[0, 3]]),
                             ('allowed_types', [[-1, 0]]), ('allowed_types', [['0x0', 0]])):
            bad = deepcopy(proof); bad[field] = value
            self.assertFalse(verify_euler_relaxation_certificate(source, bad), (field, value))
        for value in (None, [], {}, True, 1):
            self.assertFalse(verify_euler_relaxation_certificate(source, value))
            self.assertFalse(verify_euler_relaxation_certificate(value, proof))


class EulerBranchTreeVerifierTests(unittest.TestCase):
    def test_cached_dual_products_never_cache_mask_or_objective_acceptance(self):
        from fastunknot import normal_euler_tree_verify as verifier
        source, proof = source_model_tree()
        with patch.object(verifier, '_dual_image', wraps=verifier._dual_image) as image:
            with patch.object(verifier, '_euler_objective', wraps=verifier._euler_objective) as objective:
                self.assertTrue(verify_euler_branch_tree(source, proof))
                self.assertEqual(image.call_count, 2)  # dual zero is shared by two children
                self.assertEqual(objective.call_count, 1)
        bad = deepcopy(proof)
        bad['nodes'][3]['certificate']['multipliers'] = [[0, 1]]
        with patch.object(verifier, '_dual_image', wraps=verifier._dual_image) as image:
            self.assertFalse(verify_euler_branch_tree(source, bad))
            self.assertEqual(image.call_count, 1)  # third child's cache hit still fails
        leaf = base(source, [(0, 1), (1, 0)], 'normal-euler-relaxation-v2')
        leaf.update(proof_kind='anchors', duals=[dict(anchors=[a],
            multipliers=[[int(a == 2), 1]]) for a in range(7)])
        self.assertTrue(verify_euler_relaxation_certificate(source, leaf))
        leaf['duals'][2]['multipliers'] = [[0, 1]]
        with patch.object(verifier, '_dual_image', wraps=verifier._dual_image) as image:
            self.assertFalse(verify_euler_relaxation_certificate(source, leaf))
            self.assertEqual(image.call_count, 1)  # same dual, different objective

    def test_cache_keys_use_parsed_rationals_but_every_payload_is_validated(self):
        from fastunknot import normal_euler_tree_verify as verifier
        source, proof = source_model_tree()
        proof['nodes'][2]['certificate']['multipliers'] = [['0x0', '0x2']]
        with patch.object(verifier, '_dual_image', wraps=verifier._dual_image) as image:
            self.assertTrue(verify_euler_branch_tree(source, proof))
            self.assertEqual(image.call_count, 2)
        for payload in ([[False, 1]], [[0.0, 1]], [[0, True]], [[0, 0]], [], [[0, 1], [0, 1]]):
            bad = deepcopy(proof)
            bad['nodes'][2]['certificate']['multipliers'] = payload
            self.assertFalse(verify_euler_branch_tree(source, bad))
        for field, value in (('extra', 0), ('source_sha256', '0'*64),
                             ('allowed_types', [[0, 0], [1, True]])):
            bad = deepcopy(proof); bad['nodes'][2]['certificate'][field] = value
            self.assertFalse(verify_euler_branch_tree(source, bad))

    def test_replay_caches_are_isolated_between_calls_and_labelled_sources(self):
        from fastunknot import normal_euler_tree_verify as verifier
        source, _ = layered_torus(2)
        renamed = dict(tetrahedra=deepcopy(list(reversed(source['tetrahedra']))))
        for row in renamed['tetrahedra']:
            for face in row:
                if face is not None:
                    face['tetrahedron'] = 1-face['tetrahedron']
        self.assertNotEqual(source, renamed)
        with patch.object(verifier, '_dual_image', wraps=verifier._dual_image) as image:
            with patch.object(verifier, '_euler_objective', wraps=verifier._euler_objective) as objective:
                for triangulation in (source, renamed, source):
                    # The same exact dual on empty masks still requires an
                    # independent source model and fresh arithmetic each call.
                    leaf = base(triangulation, [], 'normal-euler-relaxation-v2')
                    leaf.update(proof_kind='envelope', multipliers=[[1, 1]])
                    self.assertTrue(verify_euler_relaxation_certificate(triangulation, leaf))
                self.assertEqual(image.call_count, 3)
                self.assertEqual(objective.call_count, 3)

    def test_dual_cache_eviction_retains_at_most_256_exact_products(self):
        from fastunknot import normal_euler_tree_verify as verifier
        source, _ = layered_torus(2)
        prepared = verifier._prepare(source, lambda: None)
        state = {}
        leaf = base(source, [], 'normal-euler-relaxation-v2')
        leaf.update(proof_kind='envelope', multipliers=[[0, 1]])
        def replay(value):
            leaf['multipliers'] = [[value, 1]]
            return verifier._leaf(prepared, leaf['source_sha256'], leaf, lambda: None, source_model=state)
        with patch.object(verifier, '_dual_image', wraps=verifier._dual_image) as image:
            for value in range(300):
                self.assertTrue(replay(value))
                self.assertLessEqual(len(state['dual_images']), 256)
            self.assertEqual(len(state['dual_images']), 256)
            self.assertEqual(image.call_count, 300)
            self.assertTrue(replay(299))
            self.assertEqual(image.call_count, 300)
            self.assertTrue(replay(0))
            self.assertEqual(image.call_count, 301)
            self.assertEqual(len(state['dual_images']), 256)
            # An evicted-and-rebuilt zero product must still fail at column 5.
            leaf['allowed_types'] = [[1, 2]]
            self.assertFalse(replay(0))
            self.assertEqual(image.call_count, 301)

    def test_objective_cache_is_bounded_and_does_not_expand_anchor_products(self):
        from fractions import Fraction
        from fastunknot import normal_euler_tree_verify as verifier
        # Abstract arithmetic cache control, not a synthetic accepted source:
        # 300 distinct anchor objectives can be visited without retaining all.
        state = {'model': (((0,),), (0,), (tuple(range(300)),),
                           {a: (0,) for a in range(300)}, (1,))}
        with patch.object(verifier, '_euler_objective', wraps=verifier._euler_objective) as objective:
            for anchor in range(300):
                self.assertTrue(verifier._source_dominates(state, (Fraction(0),),
                                                           (anchor,), (0,), lambda: None))
                self.assertLessEqual(len(state['objectives']), 256)
            self.assertEqual(len(state['objectives']), 256)
            self.assertEqual(objective.call_count, 300)
            self.assertTrue(verifier._source_dominates(state, (Fraction(0),), (299,), (0,), lambda: None))
            self.assertEqual(objective.call_count, 300)
            self.assertTrue(verifier._source_dominates(state, (Fraction(0),), (0,), (0,), lambda: None))
            self.assertEqual(objective.call_count, 301)
            self.assertEqual(len(state['objectives']), 256)
            self.assertEqual(len(state['dual_images']), 1)

    def test_cached_and_uncached_replay_agree_on_valid_and_hostile_trees(self):
        from fastunknot import normal_euler_tree_verify as verifier
        cases = [one_tet_tree(), two_tet_tree(), source_model_tree()]
        source, mixed = source_model_tree()
        mixed['nodes'][1]['certificate'].update(schema='normal-euler-relaxation-v1', multipliers=[[1, 1]])
        cases.append((source, mixed))
        for source, proof in cases:
            mutations = [proof]
            for index, node in enumerate(proof['nodes']):
                bad = deepcopy(proof); bad['nodes'].pop(index); mutations.append(bad)
                if node['kind'] == 'negative':
                    for field, value in (('allowed_types', []), ('source_sha256', 'f'*64), ('extra', 0)):
                        bad = deepcopy(proof); bad['nodes'][index]['certificate'][field] = value
                        mutations.append(bad)
            for packet in mutations:
                cached = verify_euler_branch_tree(source, packet)
                with patch.object(verifier, '_REPLAY_CACHE_LIMIT', 0):
                    self.assertEqual(cached, verify_euler_branch_tree(source, packet))

    def test_frozen_source_model_tree_reuses_duals_across_different_children(self):
        source, _ = layered_torus(2)
        proof = base(source, [(0, 1), (1, 0), (1, 1), (1, 2)],
                     'normal-euler-branch-tree-v1')
        proof['nodes'] = [dict(kind='split', tetrahedron=1)]
        # Frozen from a real shared-cache search: the first child requires all
        # seven anchor objectives, while the next two reuse the same envelope
        # dual. Replay relies on each inequality, never cache provenance.
        for q in range(3):
            leaf = base(source, [(0, 1), (1, q)], 'normal-euler-relaxation-v2')
            if q == 0:
                leaf.update(proof_kind='anchors', duals=[dict(anchors=[a],
                    multipliers=[[int(a == 2), 1]]) for a in range(7)])
            else:
                leaf.update(proof_kind='envelope', multipliers=[[1, 1]])
            proof['nodes'].append(dict(kind='negative', certificate=leaf))
        self.assertTrue(verify_euler_branch_tree(source, proof))
        for index in (2, 3):
            bad = deepcopy(proof)
            bad['nodes'][index]['certificate']['multipliers'] = [[0, 1]]
            self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(proof)
        first = bad['nodes'][1]['certificate']
        del first['duals']
        first.update(proof_kind='envelope', multipliers=[[1, 1]])
        self.assertFalse(verify_euler_branch_tree(source, bad))

    def test_source_model_is_built_once_per_tree_and_may_mix_with_v1_leaves(self):
        from fastunknot.normal_euler_verify import _reference_model
        source, proof = source_model_tree()
        with patch('fastunknot.normal_euler_tree_verify._reference_model', wraps=_reference_model) as model:
            self.assertTrue(verify_euler_branch_tree(source, proof))
            self.assertEqual(model.call_count, 1)
            self.assertEqual(model.call_args.args[1], tuple((t, q) for t in range(2) for q in range(3)))
        mixed = deepcopy(proof)
        mixed['nodes'][1]['certificate'].update(schema='normal-euler-relaxation-v1', multipliers=[[1, 1]])
        with patch('fastunknot.normal_euler_tree_verify._reference_model', wraps=_reference_model) as model:
            self.assertTrue(verify_euler_branch_tree(source, mixed))
            self.assertEqual(model.call_count, 2)
        for index in (1, 2, 3):
            omitted = deepcopy(proof)
            omitted['nodes'][index]['certificate']['allowed_types'] = [[0, 0]]
            self.assertFalse(verify_euler_branch_tree(source, omitted))

    def test_genuine_three_child_negative_tree_on_an_incompatible_positive_relaxation(self):
        source, _ = layered_torus(2)
        proof = base(source, [(0, 0), (1, 0), (1, 1), (1, 2)],
                     'normal-euler-branch-tree-v1')
        proof['nodes'] = [dict(kind='split', tetrahedron=1)]
        for q in range(3):
            leaf = base(source, [(0, 0), (1, q)])
            leaf.update(proof_kind='envelope', multipliers=[[int(q == 0), 1]])
            self.assertTrue(verify_euler_relaxation_certificate(source, leaf))
            proof['nodes'].append(dict(kind='negative', certificate=leaf))
        self.assertTrue(verify_euler_branch_tree(source, proof))
        for index in (1, 2, 3):
            bad = deepcopy(proof); bad['nodes'].pop(index)
            self.assertFalse(verify_euler_branch_tree(source, bad))
        # A dual for one compatible child cannot be silently extended to the
        # parent relaxation, whose incompatible positive points prompted the split.
        bad_leaf = deepcopy(proof['nodes'][1]['certificate'])
        bad_leaf['allowed_types'] = proof['allowed_types']
        self.assertFalse(verify_euler_relaxation_certificate(source, bad_leaf))

    def test_genuine_single_leaf_and_two_level_preorder_trees(self):
        for source, leaf in (two_tet_leaf(),):
            proof = base(source, leaf['allowed_types'], 'normal-euler-branch-tree-v1')
            proof['nodes'] = [dict(kind='negative', certificate=leaf)]
            self.assertTrue(verify_euler_branch_tree(source, proof))
        for source, proof in (one_tet_tree(), two_tet_tree()):
            original = deepcopy((source, proof))
            self.assertTrue(verify_euler_branch_tree(source, proof))
            self.assertEqual((source, proof), original)

    def test_missing_extra_reordered_or_repeated_children_rejected(self):
        source, original = two_tet_tree()
        for index in range(len(original['nodes'])):
            bad = deepcopy(original); bad['nodes'].pop(index)
            self.assertFalse(verify_euler_branch_tree(source, bad))
        for mutation in ('extra', 'order', 'duplicate_leaf', 'duplicate_subtree'):
            bad = deepcopy(original)
            nodes = bad['nodes']
            if mutation == 'extra': nodes.append(deepcopy(nodes[-1]))
            elif mutation == 'order': nodes[2], nodes[3] = nodes[3], nodes[2]
            elif mutation == 'duplicate_leaf': nodes[3] = deepcopy(nodes[2])
            else: nodes[4:7] = deepcopy(nodes[1:4])
            self.assertFalse(verify_euler_branch_tree(source, bad), mutation)

    def test_leaf_context_cannot_drop_change_add_or_import_types(self):
        source, original = two_tet_tree()
        for mask in ([], [[0, 0]], [[0, 0], [1, 1]],
                     [[0, 0], [0, 1], [1, 0]], [[0, False], [1, 0]]):
            bad = deepcopy(original)
            bad['nodes'][2]['certificate']['allowed_types'] = mask
            self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(original); bad['nodes'][2]['certificate']['source_sha256'] = 'f'*64
        self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(original); bad['nodes'][2]['certificate']['status'] = 'POSITIVE_EULER'
        self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(original)
        bad['nodes'][2]['certificate']['schema'] = 'normal-sector-euler-lp-v1'
        self.assertFalse(verify_euler_branch_tree(source, bad))

    def test_split_requires_ambiguous_existing_tetrahedron_and_exact_node_shape(self):
        source, original = one_tet_tree()
        for node in ({'kind': 'split', 'tetrahedron': True},
                     {'kind': 'split', 'tetrahedron': -1},
                     {'kind': 'split', 'tetrahedron': 1},
                     {'kind': 'split', 'tetrahedron': '0x0'},
                     {'kind': 'split', 'tetrahedron': 0, 'children': 2},
                     {'kind': 'leaf', 'certificate': original['nodes'][1]['certificate']},
                     {'kind': 'positive', 'certificate': original['nodes'][1]['certificate']},
                     {'kind': 'negative', 'certificate': original['nodes'][1]['certificate'], 'extra': 0},
                     None, [], {}):
            bad = deepcopy(original); bad['nodes'][0] = node
            self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(original); bad['allowed_types'] = [[0, 0]]
        self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(original); bad['allowed_types'] = []
        self.assertFalse(verify_euler_branch_tree(source, bad))
        bad = deepcopy(original)
        bad['nodes'][1] = dict(kind='split', tetrahedron=0)
        self.assertFalse(verify_euler_branch_tree(source, bad))

    def test_three_way_coverage_cannot_omit_a_positive_third_choice(self):
        source, proof = one_tet_tree()
        proof['allowed_types'].append([0, 2])
        self.assertFalse(verify_euler_branch_tree(source, proof))
        proof['nodes'].append(dict(kind='negative', certificate=one_tet_leaf(source, [(0, 2)])))
        self.assertFalse(verify_euler_branch_tree(source, proof))

    def test_strict_tree_header_and_empty_node_sequence(self):
        source, original = one_tet_tree()
        for key in original:
            bad = deepcopy(original); del bad[key]
            self.assertFalse(verify_euler_branch_tree(source, bad))
        for field, value in (('nodes', []), ('nodes', ()), ('nodes', None),
                             ('schema', 'wrong'), ('status', 'POSITIVE_EULER'),
                             ('source_sha256', 'f'*64), ('extra', 1),
                             ('allowed_types', [[0, 1], [0, 0]])):
            bad = deepcopy(original); bad[field] = value
            self.assertFalse(verify_euler_branch_tree(source, bad))

    def test_deep_incomplete_preorder_uses_an_iterative_stack(self):
        # Structural stress only: source preparation is stubbed. No leaf is
        # reached and no certificate is accepted on this artificial source.
        count = 1100
        source = dict(tetrahedra=[[None]*4 for _ in range(count)])
        proof = base(source, [(t, q) for t in range(count) for q in (0, 1)],
                     'normal-euler-branch-tree-v1')
        proof['nodes'] = [dict(kind='split', tetrahedron=t) for t in range(count)]
        with patch('fastunknot.normal_euler_tree_verify._prepare', return_value=source):
            self.assertFalse(verify_euler_branch_tree(source, proof))

    def test_replay_disables_every_existing_producer_and_solver(self):
        source, proof = two_tet_tree()
        leaf_source, leaf = two_tet_leaf()
        with ExitStack() as stack:
            for name in ('normal_euler.decide_sector_euler', 'normal_euler._euler_model',
                         'normal_euler.build_sector_kernel', 'normal_euler.solve_nonnegative_kernel',
                         'normal_sector.build_sector_kernel', 'normal_sector.sector_rays',
                         'normal_euler_tree.search_euler_tree',
                         'exact_lp.solve_nonnegative_kernel'):
                stack.enter_context(patch('fastunknot.'+name, side_effect=AssertionError('producer used')))
            self.assertTrue(verify_euler_branch_tree(source, proof))
            self.assertTrue(verify_euler_relaxation_certificate(leaf_source, leaf))
            source2, tree2 = source_model_tree()
            self.assertTrue(verify_euler_branch_tree(source2, tree2))

    def test_every_callback_exception_propagates_unchanged(self):
        class Stop(BaseException):
            pass
        class Callback:
            def __init__(self, limit, error):
                self.calls, self.limit, self.error = 0, limit, error
            def __bool__(self):
                return False
            def __call__(self):
                self.calls += 1
                if self.calls == self.limit:
                    raise self.error
        source, tree = two_tet_tree()
        leaf_source, leaf = two_tet_leaf()
        source2, tree2 = source_model_tree()
        for verify, triangulation, proof in ((verify_euler_branch_tree, source, tree),
                    (verify_euler_relaxation_certificate, leaf_source, leaf),
                    (verify_euler_branch_tree, source2, tree2),
                    (verify_euler_relaxation_certificate, source2, tree2['nodes'][3]['certificate'])):
            counter = Callback(None, None)
            self.assertTrue(verify(triangulation, proof, check=counter))
            for location in range(1, counter.calls+1):
                for error in (NormalOrbitError('cancel'), ValueError('cancel'), Stop('cancel')):
                    with self.assertRaises(type(error)) as raised:
                        verify(triangulation, proof, check=Callback(location, error))
                    self.assertIs(raised.exception, error)
            for kind in (TypeError, KeyError, IndexError, AttributeError, OverflowError, KeyboardInterrupt):
                error = kind('cancel')
                with self.assertRaises(kind) as raised:
                    verify(triangulation, proof, check=Callback(counter.calls//2, error))
                self.assertIs(raised.exception, error)


if __name__ == '__main__':
    unittest.main()
