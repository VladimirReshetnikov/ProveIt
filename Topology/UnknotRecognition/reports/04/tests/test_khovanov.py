from itertools import product
import json
from pathlib import Path
import random
import unittest

from unknot import Diagram, DiagramError, Limits, recognize
from unknot.khovanov import Budget, Complex, Resolution, Saddle
from unknot.linear import apply_matrix


def result(m, word, **kwargs):
    return recognize(Diagram.from_braid(m, word), verify_d2=True, **kwargs)


def inverse(word):
    return [-g for g in reversed(word)]


class KhovanovTests(unittest.TestCase):
    def test_known_alternating_knots(self):
        for strands, word, rank in [(1, [], 1), (2, [1], 1), (2, [-1], 1),
                                    (2, [1]*3, 3), (2, [-1]*3, 3),
                                    (3, [1, -2]*2, 5), (2, [1]*5, 5),
                                    (2, [1]*7, 7), (2, [1]*9, 9)]:
            with self.subTest(word=word):
                r = result(strands, word)
                self.assertEqual(r.reduced_rank, rank)
                self.assertEqual(r.status, 'UNKNOT' if rank == 1 else 'KNOTTED')
                self.assertEqual(r.states_built, 1 << len(word))
                self.assertEqual(r.generators_built - 2*sum(r.differential_ranks), rank)

    def test_external_pd_fixtures(self):
        root = Path(__file__).resolve().parents[1]
        for path in (root / 'examples').glob('atlas_*.json'):
            data = json.loads(path.read_text())
            d = Diagram.from_json(data)
            r = recognize(d, verify_d2=True)
            self.assertEqual(r.reduced_rank, data['expected_rank'])
        # Independently represented determinant-one example, not an invariant shortcut.
        self.assertEqual(result(3, [1, 2]*5).reduced_rank, 7)

    def test_connected_sum(self):
        for word in [[1]*3 + [2]*3, [1]*3 + [-2]*3]:
            self.assertEqual(result(3, word).reduced_rank, 9)

    def test_braid_cancellation(self):
        for m, word in [(2, [1]*3), (3, [1, -2]*2), (3, [1, 2])]:
            rank = result(m, word).reduced_rank
            for pos in range(len(word) + 1):
                for g in range(1, m):
                    for sign in [-1, 1]:
                        changed = word[:pos] + [sign*g, -sign*g] + word[pos:]
                        self.assertEqual(result(m, changed).reduced_rank, rank)

    def test_markov_stabilization(self):
        for m, word in [(1, []), (2, [1]*3), (3, [1, -2]*2), (3, [1]*3+[-2]*3)]:
            old = result(m, word).reduced_rank
            for sign in [-1, 1]:
                self.assertEqual(result(m+1, word+[sign*m]).reduced_rank, old)

    def test_braid_relation(self):
        # The common suffix makes both permutation closures one-component.
        for suffix in [[1], [-1], [2], [-2], [1, 1, 1]]:
            self.assertEqual(result(3, [1, 2, 1] + suffix).reduced_rank,
                             result(3, [2, 1, 2] + suffix).reduced_rank)
            self.assertEqual(result(3, [-1, -2, -1] + suffix).reduced_rank,
                             result(3, [-2, -1, -2] + suffix).reduced_rank)

    def test_braid_conjugation(self):
        word = [1, -2]*2
        conjugator = [2, -1]
        self.assertEqual(result(3, conjugator + word + inverse(conjugator)).reduced_rank, 5)

    def test_commuting_distant_generators(self):
        a = [1, 3, 2, 1, 2]
        b = [3, 1, 2, 1, 2]
        self.assertEqual(result(4, a).reduced_rank, result(4, b).reduced_rank)

    def test_basepoint_all_edges_and_mirror(self):
        for m, word in [(2, [1]*3), (3, [1, -2]*2), (3, [1, 2]*4)]:
            d = Diagram.from_braid(m, word)
            rank = recognize(d).reduced_rank
            for edge in range(d.edges):
                marked = Diagram.from_pd(d.pd, edge)
                self.assertEqual(recognize(marked, verify_d2=True).reduced_rank, rank)
                self.assertEqual(recognize(marked.mirror(), verify_d2=True).reduced_rank, rank)

    def test_reorder_and_relabel(self):
        random_ = random.Random(427)
        d = Diagram.from_braid(3, [1, -2]*2)
        for _ in range(20):
            rows = list(d.pd)
            random_.shuffle(rows)
            labels = list(range(d.edges))
            random_.shuffle(labels)
            rows = [tuple(labels[a]+100 for a in c) for c in rows]
            self.assertEqual(recognize(Diagram.from_pd(rows), verify_d2=True).reduced_rank, 5)

    def test_exhaustive_three_braid_short_words(self):
        count = 0
        for length in (2, 4):
            for word in product([-2, -1, 1, 2], repeat=length):
                try:
                    d = Diagram.from_braid(3, word)
                except DiagramError:
                    continue
                r = recognize(d, verify_d2=True)
                self.assertIn(r.status, ('UNKNOT', 'KNOTTED'))
                self.assertEqual(r.reduced_rank, recognize(d.mirror()).reduced_rank)
                count += 1
        self.assertEqual(count, 168)

    def test_random_six_crossing_three_braids(self):
        random_ = random.Random(173)
        count = 0
        for _ in range(100):
            word = [random_.choice([-2, -1, 1, 2]) for _ in range(6)]
            try:
                d = Diagram.from_braid(3, word)
            except DiagramError:
                continue
            r = recognize(d, verify_d2=True)
            self.assertEqual(r.reduced_rank, recognize(d.mirror()).reduced_rank)
            count += 1
        self.assertGreater(count, 50)

    def test_d_squared_zero_dense(self):
        d = Diagram.from_braid(3, [1, -2]*2)
        c = Complex.build(d, Budget(Limits()))
        matrices = [list(c.columns(i)) for i in range(d.crossings)]
        for left, right in zip(matrices, matrices[1:]):
            for column in left:
                self.assertEqual(apply_matrix(right, column), 0)

    def test_compact_label_roundtrip(self):
        for k in range(1, 7):
            for p in range(k):
                r = Resolution(0, 0, tuple((i,) for i in range(k)), tuple(range(k)),
                               p, 1 << (k-1), 0)
                for compact in range(r.dimension):
                    full = r.full_labels(compact)
                    self.assertEqual((full >> p) & 1, 1)
                    self.assertEqual(r.compact_labels(full), compact)

    def test_merge_and_split_tables_on_unmarked_circles(self):
        # Circle zero carries the basepoint throughout; the other circles saddle.
        split_source = Resolution(0, 0, ((0,), (1, 2)), (0, 1, 1), 0, 2, 0)
        split_target = Resolution(1, 1, ((0,), (1,), (2,)), (0, 1, 2), 0, 4, 0)
        split = Saddle.between(split_source, split_target)
        self.assertEqual(set(split.images(0b001)), {0b01, 0b10})
        self.assertEqual(split.images(0b011), (0b11,))
        merge_source = Resolution(0, 0, ((0,), (1,), (2,)), (0, 1, 2), 0, 4, 0)
        merge_target = Resolution(1, 1, ((0,), (1, 2)), (0, 1, 1), 0, 2, 0)
        merge = Saddle.between(merge_source, merge_target)
        self.assertEqual(merge.images(0b001), (0,))
        self.assertEqual(merge.images(0b011), (1,))
        self.assertEqual(merge.images(0b101), (1,))
        self.assertEqual(merge.images(0b111), ())

    def test_limits_are_unknown_not_verdict(self):
        d = Diagram.from_braid(2, [1]*3)
        for limits in [Limits(max_states=7), Limits(max_generators=0), Limits(seconds=0)]:
            r = recognize(d, limits, verify_d2=True)
            self.assertEqual(r.status, 'UNKNOWN')
            self.assertIsNone(r.reduced_rank)
            self.assertFalse(r.verified_d2)
        self.assertEqual(recognize(d, Limits(max_states=8, max_generators=15)).status, 'KNOTTED')
        self.assertEqual(recognize(Diagram.from_pd([]), Limits(max_states=0)).status, 'UNKNOWN')

    def test_invalid_limits(self):
        for kwargs in [{'max_states': -1}, {'max_states': True}, {'seconds': -1},
                       {'seconds': float('nan')}, {'seconds': float('inf')},
                       {'max_generators': 1.0}, {'seconds': True}, {'seconds': 10**1000}]:
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                Limits(**kwargs)

    def test_machine_readable_complexity_disclaimer(self):
        data = result(2, [1]).to_json()
        self.assertFalse(data['quasipolynomial_guarantee'])
        self.assertIn('NOT', data['worst_case_bound'])


if __name__ == '__main__':
    unittest.main()
