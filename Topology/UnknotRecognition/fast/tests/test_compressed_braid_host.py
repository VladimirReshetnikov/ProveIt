"""Native kernel binding, shared budgets, input provenance and public CLI."""
from copy import deepcopy
import itertools
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from fastunknot.braid import braid_certificate
from fastunknot.diagram import DiagramError
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_braid import Builder, recognize, verify, InvalidCertificate
from fastunknot.compressed_braid.engine import recognize as produce_three
from fastunknot.compressed_braid.forest import recognize_forest as produce_forest
from compressed_braid_research.families import sleeve, singleton_forest


class CompressedBraidHostTests(unittest.TestCase):
    def test_actual_explicit_gateway_and_native_kernel(self):
        for length in range(5):
            for word in itertools.product((1, -1, 2, -2), repeat=length):
                b = Builder()
                data = b.data(b.word(word))
                result = recognize(data)
                try:
                    expected = braid_certificate(3, word)['status']
                except DiagramError:
                    expected = 'LINK'
                self.assertEqual(result['status'], expected)
                self.assertTrue(result['verified'])
                self.assertEqual(verify(data, result['certificate']), expected)

    def test_huge_source_grammar_has_no_expansion(self):
        for negative in (False, True):
            data = sleeve(512, negative=negative)
            with patch.object(WordArena, 'expand', side_effect=AssertionError):
                result = recognize(data)
                self.assertEqual(result['status'], 'KNOTTED' if negative else 'UNKNOT')
                self.assertEqual(verify(data, result['certificate']), result['status'])
            self.assertGreater(int(result['certificate']['length_hex'], 16), 1 << 512)
            self.assertGreater(result['stats']['max_height'], 0)

    def test_work_and_nodes_are_shared_through_replay(self):
        data = sleeve(8)
        full = recognize(data)
        self.assertEqual(full['status'], 'UNKNOT')
        self.assertEqual(full['resources']['arenas'], 2)
        work, nodes = (full['resources'][key] for key in ('work', 'allocated_nodes'))
        self.assertEqual(recognize(data, max_work=work, max_nodes=nodes)['status'], 'UNKNOT')
        for options in (dict(max_work=work-1), dict(max_nodes=nodes-1)):
            limited = recognize(data, **options)
            self.assertEqual(limited['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', limited)
            self.assertNotIn('verified', limited)
        with self.assertRaises(CompressedLimit):
            verify(data, full['certificate'], max_work=0)

    def test_forest_shares_all_leaf_and_replay_arenas(self):
        data = singleton_forest(4, 12)
        result = recognize(data)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['resources']['arenas'], 8)
        self.assertEqual(len(result['certificate']['leaves']), 4)
        limited = recognize(data, max_work=result['resources']['work']-1)
        self.assertEqual(limited['status'], 'INCONCLUSIVE')
        self.assertNotIn('certificate', limited)
        bad = recognize(singleton_forest(4, 12, negative_index=2))
        self.assertEqual(bad['status'], 'KNOTTED')
        self.assertTrue(bad['verified'])

    def test_unsupported_wider_leaf_stays_inconclusive(self):
        data = dict(strands=4, rules=[['e']], root=0)
        for g in [1, 2, -3]*3:
            index = len(data['rules'])
            data['rules'].extend([['g', g], ['c', data['root'], index]])
            data['root'] = index+1
        result = recognize(data)
        self.assertEqual(result['status'], 'INCONCLUSIVE')
        self.assertTrue(result['verified'])
        self.assertEqual(verify(data, result['certificate']), 'INCONCLUSIVE')
        self.assertIsNone(result['certificate']['leaves'][0]['certificate'])

    def test_input_certificate_and_time_caps(self):
        data = sleeve(5)
        for options in (dict(max_input_rules=1), dict(max_input_bytes=1),
                        dict(max_certificate_bytes=1), dict(seconds=0), dict(max_work=0)):
            result = recognize(data, **options)
            self.assertEqual(result['status'], 'INCONCLUSIVE')
            self.assertNotIn('certificate', result)
        for options in (dict(max_nodes=True), dict(max_work=-1), dict(seconds=float('nan')),
                        dict(max_input_bytes=True), dict(prefix_probe_steps=-1)):
            with self.assertRaises(ValueError):
                recognize(data, **options)

    def test_global_cancellation_in_metadata_and_replay(self):
        class Cancelled(RuntimeError):
            pass
        data = sleeve(8)
        cert = recognize(data)['certificate']
        for operation in (lambda check: recognize(data, check=check),
                          lambda check: verify(data, cert, check=check)):
            calls = 0
            def check():
                nonlocal calls
                calls += 1
                if calls == 20:
                    raise Cancelled
            with self.assertRaises(Cancelled):
                operation(check)
            self.assertEqual(calls, 20)

    def test_native_replay_does_not_use_reducer_or_prefix_search(self):
        data = sleeve(32, reassociated=True)
        result = recognize(data, equality_probe_steps=0, prefix_probe_steps=0)
        with patch('fastunknot.compressed_braid.engine._normal_form', side_effect=AssertionError), \
             patch.object(WordArena, 'lcp', side_effect=AssertionError):
            self.assertEqual(verify(data, result['certificate'], equality_probe_steps=0), 'UNKNOT')

    def test_boolean_certificate_aliases_are_rejected(self):
        data = sleeve(4)
        cert = recognize(data)['certificate']
        damaged = deepcopy(cert)
        damaged['reduced_roots'][0] = False
        with self.assertRaises(InvalidCertificate):
            verify(data, damaged)
        damaged = deepcopy(cert)
        position = damaged['permutation'].index(0)
        damaged['permutation'][position] = False
        with self.assertRaises(InvalidCertificate):
            verify(data, damaged)
        data = singleton_forest(2, 3)
        cert = recognize(data)['certificate']
        damaged = deepcopy(cert)
        damaged['leaves'][0]['low'] = True
        with self.assertRaises(InvalidCertificate):
            verify(data, damaged)
        damaged = deepcopy(cert)
        rules = damaged['leaves'][0]['grammar']['rules']
        next(rule for rule in rules if rule == ['g', 1])[1] = True
        with self.assertRaises(InvalidCertificate):
            verify(data, damaged)

    def test_invalid_source_and_producer_failure_are_not_verdicts(self):
        with self.assertRaises(ValueError):
            recognize(dict(strands=3, rules=[['e'], ['c', 1, 0]], root=1))
        with patch('fastunknot.compressed_braid._produce_three', side_effect=ArithmeticError):
            with self.assertRaises(ArithmeticError):
                recognize(sleeve(1))

    def test_legacy_delivery_certificates_and_large_strand_gap(self):
        # Low-level schemas remain identical; the host adds resource control.
        for data, producer in ((sleeve(8), produce_three), (singleton_forest(3, 6), produce_forest)):
            certificate = producer(data)['certificate']
            self.assertEqual(verify(data, certificate), 'UNKNOT')
        result = recognize(dict(strands=10**100, rules=[['e']], root=0))
        self.assertEqual(result['status'], 'LINK')
        self.assertEqual(result['resources']['allocated_nodes'], 0)

    def test_cli_recognition_replay_and_bounded_file_read(self):
        with tempfile.TemporaryDirectory() as directory:
            data = Path(directory)/'input.json'
            cert = Path(directory)/'proof.json'
            data.write_text(json.dumps(sleeve(5)))
            base = [sys.executable, '-B', '-m', 'fastunknot.compressed_braid']
            result = subprocess.run(base+['recognize', str(data)], check=True, capture_output=True, text=True)
            payload = json.loads(result.stdout)
            self.assertEqual(payload['status'], 'UNKNOT')
            cert.write_text(json.dumps(payload['certificate']))
            result = subprocess.run(base+['verify', str(data), '--certificate', str(cert)],
                                    check=True, capture_output=True, text=True)
            self.assertEqual(json.loads(result.stdout)['status'], 'UNKNOT')
            result = subprocess.run(base+['recognize', str(data), '--max-input-bytes', '1'],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 3)
            self.assertEqual(json.loads(result.stdout)['status'], 'INCONCLUSIVE')


if __name__ == '__main__':
    unittest.main()
