"""Source-bound saturation certificates, independent replay, and dispatch."""
from copy import deepcopy
import json
from pathlib import Path
import random
import subprocess
import sys
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.compressed_search import compressed_certificate
from fastunknot.group_certificate import group_decide, verify_group_certificate
from fastunknot.scan import khovanov_rank


class RawSaturationIntegrationTests(unittest.TestCase):
    def test_actual_source_uses_existing_batch_certificate_and_independent_replay(self):
        for strands in (4, 8, 17, 33):
            diagram = Diagram.from_braid(strands, list(range(1, strands)))
            old = compressed_certificate(diagram)
            self.assertEqual(old, compressed_certificate(diagram, raw_saturation=False))
            proof = compressed_certificate(diagram, raw_saturation=True)
            self.assertEqual(proof['version'], 8)
            self.assertEqual(len(proof['moves']), 1)
            self.assertEqual(proof['moves'][0]['kind'], 'elimination_batch')
            for compressed in (False, True):
                with patch('fastunknot.raw_saturation.find_rank_one_plan',
                           side_effect=AssertionError('producer called')), \
                     patch('fastunknot.elimination_batch.apply_batch',
                           side_effect=AssertionError('producer called')):
                    self.assertTrue(verify_group_certificate(diagram, proof,
                                                             compressed=compressed))
                    self.assertTrue(verify_group_certificate(diagram, old,
                                                             compressed=compressed))
            bad = deepcopy(proof)
            bad['moves'][0]['entries'][0]['generator'] = True
            self.assertFalse(verify_group_certificate(diagram, bad, compressed=True))
            foreign = Diagram.from_braid(2, [1, 1, 1])
            bad = deepcopy(proof)
            bad['input_pd'] = [list(row) for row in foreign.pd]
            self.assertFalse(verify_group_certificate(foreign, bad, compressed=True))

    def test_small_actual_diagrams_agree_with_complete_homology(self):
        rng = random.Random(2026100901)
        tested = positive = 0
        while tested < 50:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 10))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            tested += 1
            result = group_decide(diagram, raw_saturation=True, seconds=None,
                                  max_work=1_000_000, relator_moves=True)
            if result['status'] == 'UNKNOT':
                positive += 1
                self.assertEqual(khovanov_rank(diagram.pd)['reduced_rank'], 1)
                self.assertTrue(verify_group_certificate(diagram, result['certificate'],
                                                         compressed=True))
        self.assertGreater(positive, 10)

    def test_options_limits_cancellation_and_cli(self):
        diagram = Diagram.from_braid(5, [1, 2, 3, 4])
        for bad in (1, None, 'yes'):
            with self.assertRaises(ValueError):
                compressed_certificate(diagram, raw_saturation=bad)
            with self.assertRaises(ValueError):
                group_decide(diagram, raw_saturation=bad)
            with self.assertRaises(ValueError):
                recognize(diagram, group_raw_saturation=bad)
        with self.assertRaises(ValueError):
            group_decide(diagram, raw_saturation=True, adaptive_search=True)
        for limits in ({'max_work': 0}, {'max_nodes': 0}, {'max_letters': 0}):
            self.assertEqual(group_decide(diagram, raw_saturation=True, seconds=None,
                                          **limits)['status'], 'INCONCLUSIVE')
        def cancel():
            raise ValueError('caller cancellation')
        with self.assertRaisesRegex(ValueError, 'caller cancellation'):
            group_decide(diagram, raw_saturation=True, check=cancel)
        proc = subprocess.run(
            [sys.executable, '-B', '-m', 'fastunknot', 'recognize', '-',
             '--group-raw-saturation', '--group-seconds', '2'],
            input=json.dumps({'pd': diagram.pd}), text=True, capture_output=True,
            cwd=Path(__file__).resolve().parents[1])
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(json.loads(proc.stdout)['status'], 'UNKNOT')


if __name__ == '__main__':
    unittest.main()
