"""Independent finite optimization, binary heights and primal/dual forgeries."""
from copy import deepcopy
from itertools import product, permutations
import json
import random
import unittest
from unittest.mock import patch

from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_span_verify import verify_cocycle_span
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cocycle import CocycleLimit


class CocycleSpanTests(unittest.TestCase):
    def test_exhaustive_integral_potentials(self):
        rng = random.Random(261009460)
        for _ in range(120):
            n = rng.randrange(1, 6)
            vertices = [[rng.randrange(3) for _ in range(4)] for _ in range(n)]
            heights = [[rng.randrange(-3, 4) for _ in range(4)] for _ in range(n)]
            labels = sorted({v for row in vertices for v in row})
            best = min(sum(max(h+f[v] for v, h in zip(vs, hs))
                           - min(h+f[v] for v, h in zip(vs, hs))
                           for vs, hs in zip(vertices, heights))
                       for tail in product(range(-12, 13), repeat=len(labels)-1)
                       for f in [dict(zip(labels, (0,)+tail))])
            answer = minimize_cocycle_span(vertices, heights)
            self.assertEqual(answer['stats']['disc_count'], best)
            self.assertTrue(verify_cocycle_span(vertices, heights, answer['certificate']))

    def test_exhaustive_dual_matchings(self):
        rng = random.Random(261009461)
        for _ in range(40):
            n = 5
            vertices = [[rng.randrange(5) for _ in range(4)] for _ in range(n)]
            heights = [[rng.randrange(-100, 101) for _ in range(4)] for _ in range(n)]
            weights = {}
            for t in range(n):
                for s in range(n):
                    choices = [heights[s][j]-heights[t][i] for i in range(4) for j in range(4)
                               if vertices[t][i] == vertices[s][j]]
                    if choices: weights[t, s] = max(choices)
            best = max(sum(weights[t, s] for t, s in enumerate(order))
                       for order in permutations(range(n))
                       if all((t, s) in weights for t, s in enumerate(order)))
            self.assertEqual(minimize_cocycle_span(vertices, heights)['stats']['disc_count'], best)

    def test_binary_scaling_and_independent_coordinate_reconstruction(self):
        vertices = [[0, 1, 0, 2], [2, 1, 3, 0], [3, 0, 1, 2]]
        heights = [[0, 2, 7, 4], [1, -3, 0, 2], [4, 1, 8, 0]]
        small = minimize_cocycle_span(vertices, heights)
        scale = 1 << 20000
        large = [[scale*h for h in row] for row in heights]
        result = minimize_cocycle_span(vertices, large)
        self.assertEqual(result['stats']['disc_count'], scale*small['stats']['disc_count'])
        for key in ('work', 'augmentations', 'relaxations', 'heap_pops', 'network_arcs', 'network_nodes'):
            self.assertEqual(result['stats'][key], small['stats'][key])
        proof = json.loads(json.dumps(json_safe(result['certificate'])))
        with patch('fastunknot.cocycle_span.minimize_cocycle_span', side_effect=AssertionError), \
             patch('fastunknot.normal_cocycle.local_coordinates', side_effect=AssertionError):
            self.assertTrue(verify_cocycle_span(vertices, large, proof))
        for row in list(permutations((0, 1, 4, 11))) + [(0, 0, 0, 0), (0, 0, 1, 1), (0, 2, 2, 4)]:
            answer = minimize_cocycle_span([[0, 0, 0, 0]], [list(row)])
            self.assertTrue(verify_cocycle_span([[0]*4], [list(row)], answer['certificate']))
            self.assertEqual(sum(answer['coordinates'][0]), max(row)-min(row))

    def test_disconnected_incidence_parallel_arcs_and_unreachable_residual_nodes(self):
        vertices = [[i//2]*4 for i in range(12)]
        heights = [[i, -i, i+7, 2*i] for i in range(12)]
        result = minimize_cocycle_span(vertices, heights)
        self.assertEqual(result['stats']['disc_count'], sum(max(row)-min(row) for row in heights))
        self.assertTrue(verify_cocycle_span(vertices, heights, result['certificate']))

    def test_mutated_witnesses_and_exact_schemas(self):
        vertices = [[0, 1, 0, 1], [0, 1, 2, 2], [2, 0, 1, 2]]
        heights = [[0, 2, 5, -1], [3, 1, -2, 4], [0, 1, 7, 5]]
        proof = minimize_cocycle_span(vertices, heights)['certificate']
        for field in proof:
            bad = deepcopy(proof); del bad[field]
            self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        for bad in (None, [], dict(proof, extra=True)):
            self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        bad = deepcopy(proof); bad['matching'][1] = bad['matching'][0]
        self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        for value in (True, -1, 3, '0'):
            bad = deepcopy(proof); bad['matching'][0][0] = value
            self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        bad = deepcopy(proof); bad['coordinates'][0][0] += 1
        self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        bad = deepcopy(proof); bad['disc_count'] += 1
        self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        bad = deepcopy(proof); bad['potential'][0] = True
        self.assertFalse(verify_cocycle_span(vertices, heights, bad))
        # A per-tetrahedron integer height shift does not change this query.
        shifted = [[h+17*(i+1) for h in row] for i, row in enumerate(heights)]
        self.assertTrue(verify_cocycle_span(vertices, shifted, proof))

    def test_caps_invalid_inputs_and_cancellation(self):
        vertices, heights = [[0, 1, 2, 3]], [[0, 2, -1, 4]]
        before = deepcopy((vertices, heights))
        for cap in (0, 1, 10):
            with self.assertRaises(CocycleLimit): minimize_cocycle_span(vertices, heights, max_work=cap)
        for value in (-1, True, 0.5):
            with self.assertRaises(ValueError): minimize_cocycle_span(vertices, heights, max_work=value)
        for vs, hs in (([], []), ([[True, 0, 1, 2]], heights), (vertices, [[0, 1, False, 2]])):
            with self.assertRaises(ValueError): minimize_cocycle_span(vs, hs)
        class Stop:
            def __bool__(self): return False
            def __call__(self): raise RuntimeError('cancelled')
        proof = minimize_cocycle_span(vertices, heights)['certificate']
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            minimize_cocycle_span(vertices, heights, check=Stop())
        with self.assertRaisesRegex(RuntimeError, 'cancelled'):
            verify_cocycle_span(vertices, heights, proof, check=Stop())
        self.assertEqual((vertices, heights), before)


if __name__ == '__main__':
    unittest.main()
