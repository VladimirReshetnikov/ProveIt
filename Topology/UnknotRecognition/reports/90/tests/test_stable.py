"""Independent tests for exact through-component reblocking and source addresses."""

import copy
import json
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'code'), str(ROOT / 'experiments')]

from pattern_kernel.core import Block, Tile, certify_cubic_graph, expand, validate_chain
from pattern_kernel.signatures import power, tile_table
from routed_patterns.core import build_kernel as old_build_kernel
from routed_patterns.stable import (
    UnsupportedTile, build_kernel, reblock_chain, solve, through_components)
from routed_patterns.stable_verify import reconstruct, verify_result, verify_source_witness
from routed_patterns.verify import verify_source_witness as aligned_source_witness
from routing_families import star_triangle, routed_beads
from routing_oracle import graph_table


def sharp_tile(d):
    """Cubic-seam realization of the sharp d-step partition stabilization family."""
    if d < 2:
        raise ValueError('sharp family starts at d=2')
    w = d + 1
    edges = [(0, w), (w, w + 2), (w + 2, 1)]
    next_vertex = 2 * w
    for j in range(2, d + 1):
        target = j + 1 if j < d else 1
        a, b, c = next_vertex, next_vertex + 1, next_vertex + 2
        next_vertex += 3
        edges.extend([(j, a), (w + target, b), (w + target, c),
                      (a, b), (a, c), (b, c)])
    return Tile(next_vertex, tuple(edges), tuple(range(w)), tuple(range(w, 2*w)))


def mismatched_path():
    return Tile(6, ((0, 1), (1, 3), (3, 5), (2, 4)), (0, 1, 2), (3, 4, 5))


class StableTests(unittest.TestCase):
    def test_partition_mismatch_now_supported(self):
        tile = mismatched_path()
        with self.assertRaises(ValueError):
            old_build_kernel((Block(tile, 100),))
        adapted, plans, _ = reblock_chain((Block(tile, 100),))
        self.assertEqual(plans[0]['period'], 2)
        self.assertEqual(plans[0]['ranks'], [2, 1])
        independently, _ = reconstruct((Block(tile, 100),), plans)
        self.assertEqual(adapted, independently)

    def test_full_open_signatures(self):
        tile = mismatched_path()
        for n in (1, 2, 3, 4, 7, 8, 17, 101):
            kernel, _, _ = build_kernel((Block(tile, n),), close=False)
            self.assertEqual(graph_table(kernel), power(tile_table(tile), n))

    def test_general_threshold_open_signatures(self):
        tile = mismatched_path()
        for threshold in (0, 1, 2, 4, 5):
            kernel, _, _ = build_kernel((Block(tile, 29),), threshold, close=False)
            self.assertEqual(graph_table(kernel, threshold),
                             power(tile_table(tile, threshold), 29, threshold))

    def test_sharp_stabilization_family(self):
        for d in range(2, 9):
            tile = sharp_tile(d)
            validate_chain((Block(tile, 2),))
            adapted, plans, _ = reblock_chain((Block(tile, (1 << 1024) + 17),))
            self.assertEqual(plans[0]['period'], d)
            self.assertEqual(plans[0]['ranks'], list(range(d, 0, -1)))
            self.assertEqual(len(through_components(adapted[0].tile)), 1)
            self.assertEqual(reconstruct((Block(tile, (1 << 1024) + 17),), plans)[0], adapted)

    def test_zero_quotient_and_exact_tail(self):
        tile = sharp_tile(4)
        for n in (1, 2, 3):
            adapted, plans, _ = reblock_chain((Block(tile, n),))
            self.assertEqual(plans[0]['quotient'], '0x0')
            self.assertEqual(len(adapted), 1)
            self.assertEqual(adapted[0].copies, 1)
            self.assertEqual(len(adapted[0].tile.edges), n * len(tile.edges))
            original, _ = expand((Block(tile, n),))
            bracketed, _ = expand(adapted)
            self.assertEqual(original, bracketed)

    def test_small_cubic_verdicts_match_expansion(self):
        for d in (2, 3):
            for n in (1, 2, 3, 4, 7, 11):
                chain = (Block(sharp_tile(d), n),)
                proof = solve(chain)
                graph, _ = expand(chain)
                self.assertEqual(proof['verdict'], certify_cubic_graph(graph)['verdict'])
                self.assertTrue(verify_result(chain, proof))

    def test_huge_exponent_and_tail_source_address(self):
        n = (1 << 4096) + 1
        chain = (Block(sharp_tile(2), n),)
        proof = solve(chain)
        self.assertTrue(verify_result(chain, proof))
        self.assertEqual(proof['reblocking'][0]['period'], 2)
        self.assertEqual(len(proof['nested']['kernel']['edges']), 81)
        source = verify_source_witness(chain, proof)
        self.assertEqual(source['cost'], 3)
        self.assertIn(n - 1, [int(e['copy'], 16) for e in source['crossings']])
        self.assertTrue(all(0 <= int(e['copy'], 16) < n
                            for e in source['crossings'] + source['anchors']))
        self.assertTrue(verify_result(chain, json.loads(json.dumps(proof))))

    def test_original_edge_occurrences_match_exact_rebracketing(self):
        first, second = sharp_tile(2), routed_beads([1, 2, 0])
        for exponents in ((1, 3), (3, 2), (10, 9), (17, 5)):
            chain = (Block(first, exponents[0]), Block(second, exponents[1]))
            proof = solve(chain)
            self.assertTrue(verify_result(chain, proof))
            adapted, _, _ = reblock_chain(chain)
            original, _ = expand(chain)
            bracketed, _ = expand(adapted)
            self.assertEqual(original, bracketed)
            if proof['verdict'] != 'LOW_CYCLIC_CUT':
                continue
            before = aligned_source_witness(adapted, proof['nested']['source_witness'])
            after = verify_source_witness(chain, proof)
            for aa, bb in zip(before['crossings'] + before['anchors'],
                              after['crossings'] + after['anchors']):
                old_index = sum(b.copies * len(b.tile.edges) for b in chain[:bb['block']])
                old_index += int(bb['copy'], 16) * len(chain[bb['block']].tile.edges) + bb['edge']
                new_index = sum(b.copies * len(b.tile.edges) for b in adapted[:aa['block']])
                new_index += int(aa['copy'], 16) * len(adapted[aa['block']].tile.edges) + aa['edge']
                self.assertEqual(old_index, new_index)
                self.assertEqual(original.edges[old_index], bracketed.edges[new_index])

    def test_shuffled_vertex_labels_preserve_exact_composition(self):
        rng = random.Random(26101244)
        tile = sharp_tile(3)
        for _ in range(12):
            labels = list(range(tile.n))
            rng.shuffle(labels)
            changed = Tile(tile.n, tuple((labels[a], labels[b]) for a, b in tile.edges),
                           tuple(labels[v] for v in tile.left), tuple(labels[v] for v in tile.right))
            chain = (Block(changed, 8),)
            adapted, plans, _ = reblock_chain(chain)
            self.assertEqual(adapted, reconstruct(chain, plans)[0])
            self.assertEqual(expand(chain)[0], expand(adapted)[0])

    def test_non_through_large_unsupported_small_literal(self):
        # One private cubic K4 component, plus a routed bead of width one.
        bead = routed_beads([0])
        edges = bead.edges + tuple((5 + a, 5 + b)
                                  for a in range(4) for b in range(a + 1, 4))
        tile = Tile(9, edges, bead.left, bead.right)
        for copies in (1, 3, 4):
            chain = (Block(tile, copies),)
            proof = solve(chain)
            self.assertTrue(verify_result(chain, proof))
            self.assertEqual(proof['reblocking'][0]['kind'], 'literal')
        with self.assertRaises(UnsupportedTile):
            solve((Block(tile, 5),))

    def test_independent_checker_with_producers_disabled(self):
        chain = (Block(sharp_tile(2), (1 << 257) + 1),)
        proof = solve(chain)
        with patch('routed_patterns.stable.reblock_chain', side_effect=AssertionError), \
             patch('routed_patterns.stable._power_tile', side_effect=AssertionError), \
             patch('routed_patterns.stable._map_source_addresses', side_effect=AssertionError), \
             patch('routed_patterns.core.components', side_effect=AssertionError):
            self.assertTrue(verify_result(chain, proof))

    def test_metadata_and_source_address_mutations(self):
        chain = (Block(sharp_tile(2), (1 << 257) + 1),)
        proof = solve(chain)
        variants = []
        for field, value in (('period', 1), ('period', 1 << 300), ('components', True),
                             ('quotient', '0x0'), ('remainder', 0), ('ranks', [2, 2]),
                             ('adapted_blocks', [1, 0])):
            bad = copy.deepcopy(proof)
            bad['reblocking'][0][field] = value
            variants.append(bad)
        for field in ('source_sha256', 'adapted_sha256'):
            bad = copy.deepcopy(proof)
            bad[field] = 'wrong'
            variants.append(bad)
        for field, value in (('copy', '0x0'), ('edge', True), ('block', 9)):
            bad = copy.deepcopy(proof)
            bad['original_source_addresses']['crossings'][-1][field] = value
            variants.append(bad)
        bad = copy.deepcopy(proof)
        bad['original_source_addresses']['anchors'].reverse()
        variants.append(bad)
        bad = copy.deepcopy(proof)
        bad['nested']['kernel']['edges'][0] = [0, 0]
        variants.append(bad)
        for bad in variants:
            self.assertFalse(verify_result(chain, bad))
        self.assertFalse(verify_result((Block(sharp_tile(2), (1 << 257) + 3),), proof))

    def test_aligned_positive_wrapper(self):
        chain = (Block(star_triangle(), 1),)
        proof = solve(chain)
        self.assertEqual(proof['reblocking'][0]['period'], 1)
        self.assertNotIn('original_source_addresses', proof)
        self.assertTrue(verify_result(chain, proof))
        proof['nested']['graph_proof']['four_flows'].pop()
        self.assertFalse(verify_result(chain, proof))


if __name__ == '__main__':
    unittest.main()
