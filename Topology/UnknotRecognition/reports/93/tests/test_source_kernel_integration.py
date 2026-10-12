"""Check the handoff from verified source decompositions to graph kernels."""

import json
from pathlib import Path
import unittest

from attachment_kernel import kernel_from_decomposition
from attachment_kernel_verify import verify_attachment_kernel
from unused_handles import decompose_unused_handles, verify_unused_handle_certificate


ROOT = Path(__file__).resolve().parents[1]


class SourceKernelIntegrationTests(unittest.TestCase):
    def test_all_source_packets_feed_the_independent_graph_checker(self):
        records = json.loads((ROOT / 'data/unused_handles_source_corpus.json').read_text())['records']
        self.assertEqual(len(records), 48)
        for row in records:
            source = row['triangulation']
            result = decompose_unused_handles(source)
            self.assertTrue(verify_unused_handle_certificate(source, result['certificate']))
            decomposition = result['decomposition']
            certificate = kernel_from_decomposition(decomposition)
            edges = [{'id': e['one_handle'], 'ends': e['ends']}
                     for e in decomposition['unused_handles']]
            self.assertTrue(verify_attachment_kernel(
                decomposition['components'], edges, certificate), row['id'])
            kernel = certificate['kernel']
            self.assertEqual(kernel['euler_deficit'], 1)
            self.assertEqual(len(kernel['vertices']), 1)
            self.assertEqual(len(kernel['edges']),
                             1 if result['torus_case'] == 'cycle' else 0)
            # This same numerical quotient is intentionally accepted for the
            # reducible controls.  Neither adapter makes a knot verdict.
            self.assertNotIn('status', certificate)
            self.assertIn('require source irreducibility', certificate['trust'])


if __name__ == '__main__':
    unittest.main()
