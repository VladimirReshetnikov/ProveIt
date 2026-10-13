"""Literal order quotients, reflected arrows, exact traces and hostile gaps."""

from bisect import bisect_right
from copy import deepcopy
from itertools import product
import random
import unittest
from unittest.mock import patch
from contextlib import ExitStack
import json

from fastunknot.integer_codec import json_safe
from fastunknot.interval_orbits import IntervalPairing, _contract, count_orbits
from fastunknot.interval_orbit_verify import _contract_pairings, verify_orbit_certificate
from fastunknot.weighted_orbits import weighted_orbit_histogram
from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
from fastunknot.weighted_transversal import weighted_orbit_transversal
from fastunknot.weighted_transversal_verify import verify_weighted_orbit_transversal


def naive_rows(rows, gaps):
    def shift(point):
        return point - sum(hi - lo + 1 for lo, hi in gaps if hi < point)
    return [[shift(a), shift(b), shift(c), shift(d), sign]
            for a, b, c, d, sign in rows]


def literal_gaps(n, retained):
    result = []
    point = 0
    while point < n:
        if point in retained:
            point += 1
            continue
        lo = point
        while point < n and point not in retained:
            point += 1
        result.append([lo, point - 1])
    return result


class GapPrefixReplayTests(unittest.TestCase):
    def test_all_tiny_complements_and_inverse_order_maps(self):
        for n in range(10):
            for bits in product((False, True), repeat=n):
                kept = [i for i, bit in enumerate(bits) if bit]
                gaps = literal_gaps(n, set(kept))
                rows = [[point] * 4 + [1] for point in kept]
                actual, removed = _contract_pairings(rows, gaps)
                self.assertEqual(actual, naive_rows(rows, gaps))
                self.assertEqual(actual, [[rank] * 4 + [1] for rank in range(len(kept))])
                self.assertEqual(removed, n - len(kept))
                anchors, prefix = [], [0]
                for lo, hi in gaps:
                    anchors.append(lo - prefix[-1])
                    prefix.append(prefix[-1] + hi - lo + 1)
                restored = [rank + prefix[bisect_right(anchors, rank)]
                            for rank in range(len(kept))]
                self.assertEqual(restored, kept)
                pairs = [IntervalPairing(*row[:4]) for row in rows]
                size, mapped, count, produced_gaps = _contract(n, pairs)
                self.assertEqual((size, count, produced_gaps), (len(kept), removed, gaps))
                self.assertEqual([[p.a, p.b, p.c, p.d, 1] for p in mapped], actual)
                if not gaps:
                    self.assertIs(mapped, pairs)

    def test_arbitrary_signed_pairings_match_literal_oracle(self):
        rng = random.Random(20261012)
        for _ in range(700):
            n = rng.randrange(1, 65)
            pairs = []
            for _ in range(rng.randrange(1, 17)):
                width = rng.randrange(1, n + 1)
                a, c = (rng.randrange(n - width + 1) for _ in range(2))
                pairs.append(IntervalPairing(a, a + width - 1,
                                            c, c + width - 1, bool(rng.randrange(2))))
            retained = {x for p in pairs for lo, hi in ((p.a, p.b), (p.c, p.d))
                        for x in range(lo, hi + 1)}
            gaps = literal_gaps(n, retained)
            rows = [[p.a, p.b, p.c, p.d, -1 if p.reverse else 1] for p in pairs]
            expected = naive_rows(rows, gaps)
            actual, removed = _contract_pairings(rows, gaps)
            self.assertEqual(actual, expected)
            size, mapped, amount, produced = _contract(n, pairs)
            self.assertEqual((size, amount, produced), (n - removed, removed, gaps))
            self.assertEqual([[p.a, p.b, p.c, p.d, -1 if p.reverse else 1]
                              for p in mapped], actual)

    def test_enormous_gaps_do_not_expand_points(self):
        scale = 1 << 16384
        gaps = [[0, scale - 1], [scale + 3, 3 * scale - 1]]
        rows = [[scale, scale + 2, 3 * scale, 3 * scale + 2, -1]]
        self.assertEqual(_contract_pairings(rows, gaps),
                         ([[0, 2, 3, 5, -1]], 3 * scale - 3))

    def test_bad_gaps_still_fail_before_prefix_transport(self):
        n = 12
        pairs = [IntervalPairing(2, 3, 8, 9, True)]
        proof = count_orbits(n, pairs, record_certificate=True).certificate
        self.assertTrue(verify_orbit_certificate(n, pairs, proof))
        index = next(i for i, event in enumerate(proof['operations']) if event['op'] == 'contract')
        malformed = ([[0, 0]], [[0, 2], [4, 7], [10, 11]],
                     [[4, 7], [0, 1], [10, 11]], [[0, 1], [1, 7], [10, 11]])
        for gaps in malformed:
            bad = deepcopy(proof)
            bad['operations'][index]['gaps'] = gaps
            with patch('fastunknot.interval_orbit_verify._contract_pairings',
                       side_effect=AssertionError('unauthenticated gaps remapped')):
                self.assertFalse(verify_orbit_certificate(n, pairs, bad))

    def test_weighted_and_selector_checkers_keep_independent_code(self):
        n = 36
        pairs = [IntervalPairing(2, 5, 12, 15, True),
                 IntervalPairing(12, 15, 28, 31)]
        weights = [(0, 7, (2, -1)), (10, 19, (-3, 2)), (27, 36, (1, 4))]
        weighted = weighted_orbit_histogram(n, pairs, weights, dimension=2,
                                           record_certificate=True)
        selector = weighted_orbit_transversal(n, pairs, weights, dimension=2,
                                             record_certificate=True)
        with patch('fastunknot.weighted_orbits._contract_rows',
                   side_effect=AssertionError('producer row mapper used')):
            self.assertTrue(verify_weighted_orbit_certificate(
                n, pairs, weights, weighted['certificate'], dimension=2))
            self.assertTrue(verify_weighted_orbit_transversal(
                n, pairs, weights, selector['certificate'], dimension=2))

    def test_callbacks_run_inside_long_prefix_and_endpoint_scans(self):
        class Cancel(Exception):
            pass
        checks = 0
        def stop():
            nonlocal checks
            checks += 1
            if checks == 3:
                raise Cancel()
        with self.assertRaises(Cancel):
            _contract_pairings([[8, 8, 8, 8, 1]], [[0, 1], [3, 4], [6, 7]], stop)

    def test_nested_weighted_proofs_authenticate_gaps_before_mapping(self):
        pairs = [IntervalPairing(2, 3, 8, 9, True)]
        weights = [(0, 12, (3, -7))]
        weighted = weighted_orbit_histogram(12, pairs, weights, record_certificate=True)
        tagged = weighted_orbit_transversal(12, pairs, weights, record_certificate=True)
        for result, verify, nested in (
                (weighted, verify_weighted_orbit_certificate, False),
                (tagged, verify_weighted_orbit_transversal, True)):
            for gaps in ([[0, 0]], [[0, 2], [4, 7], [10, 11]],
                         [[4, 7], [0, 1], [10, 11]], [[0, 1], [1, 7]],
                         [[False, 1], [4, 7], [10, 11]], [[-1, 1]]):
                bad = deepcopy(result['certificate'])
                trace = (bad['weighted_certificate'] if nested else bad)['orbit_proof']
                event = next(e for e in trace['operations'] if e['op'] == 'contract')
                event['gaps'] = gaps
                with ExitStack() as stack:
                    for module in ('interval_orbit_verify', 'weighted_orbit_verify',
                                   'weighted_transversal_verify'):
                        stack.enter_context(patch('fastunknot.' + module + '._contract_pairings',
                            side_effect=AssertionError('unauthenticated gaps remapped')))
                    self.assertFalse(verify(12, pairs, weights, bad, dimension=2))

    def test_large_binary_weighted_gaps_and_original_representatives(self):
        scale = 1 << 16384
        value = [1 << 511, -(1 << 997)]
        pairs = [IntervalPairing(scale, scale + 2, 3 * scale, 3 * scale + 2, True)]
        weights = [(0, 4 * scale, value)]
        answer = weighted_orbit_transversal(4 * scale, pairs, weights,
                                            record_certificate=True)
        self.assertEqual(answer['status'], 'COMPLETE')
        self.assertEqual(answer['representative_runs'], [
            dict(start=0, stop=scale, weight=value),
            dict(start=scale, stop=scale + 3, weight=[2 * v for v in value]),
            dict(start=scale + 3, stop=3 * scale, weight=value),
            dict(start=3 * scale + 3, stop=4 * scale, weight=value)])
        proof = json.loads(json.dumps(json_safe(answer['certificate'])))
        self.assertTrue(verify_weighted_orbit_transversal(4 * scale, pairs, weights,
                                                         proof, dimension=2))
        self.assertTrue(verify_weighted_orbit_certificate(4 * scale, pairs, weights,
                              proof['weighted_certificate'], dimension=2))


if __name__ == '__main__':
    unittest.main()
