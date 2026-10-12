from copy import deepcopy
import json
import random
import unittest
from unittest.mock import patch

from unsaturated_bundles import census, make_certificate, verify_certificate
from unsaturated_bundles.finite import encode


def model(cores=(0,), chi=0, boundary=2, orientable=True, attached=((0, 'circle'),)):
    return dict(cores=[dict(id=i, genus=g) for i, g in enumerate(cores)],
                bases=[dict(id=0, chi=chi, boundary=boundary,
                            orientable=orientable, multiplicity=1)],
                attachments=[dict(id=i, base=0, core=c, kind=k)
                             for i, (c, k) in enumerate(attached)])


class FiniteTests(unittest.TestCase):
    def test_annular_collar_preserves_core(self):
        for g in (0, 1, 7, 1 << 16384):
            source = model(cores=(g,))
            result = make_certificate(source)
            self.assertEqual(result['census']['histogram'], [dict(genus=g, multiplicity=1)])
            self.assertEqual(result['census']['reductions'][0]['one_handles'], 0)
            self.assertTrue(verify_certificate(source, result['certificate']))

    def test_two_pants_annuli_same_or_different_cores(self):
        joined = model(cores=(0, 0), chi=-1, boundary=3,
                       attached=((0, 'circle'), (1, 'circle')))
        self.assertTrue(census(joined)['census']['one_ball'])
        loop = model(chi=-1, boundary=3,
                     attached=((0, 'circle'), (0, 'circle')))
        self.assertEqual(census(loop)['census']['histogram'], [dict(genus=1, multiplicity=1)])

    def test_nonorientable_bordered_base(self):
        source = model(chi=-1, boundary=2, orientable=False)
        self.assertEqual(census(source)['census']['histogram'], [dict(genus=1, multiplicity=1)])

    def test_multiple_disk_intervals_create_cycles(self):
        source = model(chi=1, boundary=1,
                       attached=((0, 'interval'), (0, 'interval'), (0, 'interval')))
        result = make_certificate(source)
        self.assertEqual(result['census']['histogram'], [dict(genus=2, multiplicity=1)])
        self.assertTrue(verify_certificate(source, result['certificate']))

    def test_saturated_bases_never_get_a_census(self):
        for chi, b, orientable in ((1, 1, True), (0, 1, False), (0, 2, True)):
            source = model(chi=chi, boundary=b, orientable=orientable,
                           attached=tuple((0, 'circle') for _ in range(b)))
            result = make_certificate(source)
            self.assertEqual(result['reason'], 'saturated_bundle_base')
            self.assertNotIn('certificate', result)
            self.assertNotIn('census', result)

    def test_closed_and_empty_cases(self):
        source = model(chi=2, boundary=0, attached=())
        self.assertEqual(census(source)['reason'], 'closed_bundle_base')
        result = make_certificate(dict(cores=[], bases=[], attachments=[]))
        self.assertFalse(result['census']['one_ball'])
        self.assertTrue(verify_certificate(dict(cores=[], bases=[], attachments=[]),
                                            result['certificate']))

    def test_binary_isolated_counts_and_roundtrip(self):
        source = model(cores=(), chi=1, boundary=1, attached=())
        source['bases'][0]['multiplicity'] = (1 << 20000) + 7
        result = make_certificate(source)
        proof = json.loads(json.dumps(encode(result['certificate'])))
        self.assertTrue(verify_certificate(source, proof))
        self.assertEqual(result['census']['ball_components'], (1 << 20000) + 7)

    def test_replay_rejects_tampering_and_does_not_call_producer(self):
        source = model()
        result = make_certificate(source)
        with patch('unsaturated_bundles.finite.census', side_effect=AssertionError):
            self.assertTrue(verify_certificate(source, result['certificate']))
        for mutate in ('genus', 'boolean', 'source', 'rank'):
            proof = deepcopy(result['certificate'])
            if mutate == 'genus':
                proof['census']['histogram'][0]['genus'] += 1
            elif mutate == 'boolean':
                proof['census']['histogram'][0]['multiplicity'] = True
            elif mutate == 'source':
                proof['input_sha256'] = '0' * 64
            else:
                proof['census']['reductions'][0]['one_handles'] += 1
            self.assertFalse(verify_certificate(source, proof))

    def test_bad_models_do_not_reach_topology(self):
        bad = []
        source = model()
        source['bases'][0]['multiplicity'] = 2
        bad.append(source)
        source = model()
        source['attachments'][0]['core'] = 10
        bad.append(source)
        source = model()
        source['cores'][0]['genus'] = False
        bad.append(source)
        source = model(chi=0, boundary=1)
        bad.append(source)
        for source in bad:
            with self.assertRaises(ValueError):
                census(source)

    def test_random_graphs_against_relative_handle_counts(self):
        rng = random.Random(26101219)
        for _ in range(700):
            n = rng.randrange(1, 8)
            source = dict(cores=[dict(id=i, genus=rng.randrange(5)) for i in range(n)],
                          bases=[], attachments=[])
            for b in range(rng.randrange(9)):
                orientable = bool(rng.randrange(2))
                boundary = rng.randrange(1, 6)
                defect = 2 * rng.randrange(4) if orientable else rng.randrange(1, 6)
                chi = 2 - boundary - defect
                source['bases'].append(dict(id=b, chi=chi, boundary=boundary,
                    orientable=orientable, multiplicity=1))
                circles = rng.randrange(boundary)
                intervals = rng.randrange(4)
                for kind in ['circle'] * circles + ['interval'] * intervals:
                    source['attachments'].append(dict(id=len(source['attachments']),
                        base=b, core=rng.randrange(n), kind=kind))
            result = make_certificate(source)
            self.assertTrue(verify_certificate(source, result['certificate']))


if __name__ == '__main__':
    unittest.main()
