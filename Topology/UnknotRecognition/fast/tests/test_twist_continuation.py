"""Public CLI/API checks for the additive run-encoded research frontend."""
from __future__ import annotations

from contextlib import redirect_stdout
import io
import json
import unittest
from unittest.mock import patch

from fastunknot.twist.continuation import compute, load_runs, main
from fastunknot.twist.core import Budget, Run, homology
from fastunknot.twist.streaming import StreamBudget
from fastunknot.twist.tail import expand_profile


class ContinuationInterface(unittest.TestCase):
    def test_validated_rle_schema(self):
        value = {'strands': 3, 'runs': [[1, 3], [2, -1]]}
        expected = (3, (Run(1, 3), Run(2, -1)))
        self.assertEqual(load_runs(value), expected)
        self.assertEqual(load_runs({'braid': value}), expected)
        for bad in ([], {}, {'strands': 2, 'word': [1]},
                    {'strands': 2, 'runs': [[1, 0]]},
                    {'strands': 2, 'runs': [[1, True]]},
                    {'strands': 2, 'runs': [[2, 1]]},
                    {'strands': 2, 'runs': [1]},
                    {'strands': 2, 'runs': [], 'word': []}):
            with self.subTest(value=bad), self.assertRaises(ValueError):
                load_runs(bad)

    def test_recognition_uses_structural_certificate_first(self):
        magnitude = 10**100 + 1
        for method in ('tail', 'macro', 'streaming'):
            budget = StreamBudget(max_states=0) if method == 'streaming' else Budget(max_states=0)
            answer = compute(2, [Run(1, magnitude)], method=method, budget=budget)
            self.assertEqual(answer['status'], 'KNOTTED')
            self.assertEqual(answer['method'], 'structural-braid')
            self.assertNotIn('homology', answer)
            self.assertEqual(answer['certificate']['crossings'], magnitude)

    def test_original_parity_and_link_homology(self):
        odd = compute(2, [Run(1, 101)], mode='homology', check_d2=True)
        self.assertEqual(odd['homology']['components'], 1)
        self.assertEqual(odd['homology']['reference']['components'], 2)
        even = compute(2, [Run(1, 100)], mode='homology')
        self.assertEqual(even['homology']['components'], 2)
        self.assertEqual(even['homology']['reduced_rank'], 100)
        for mode in ('recognize', 'profile'):
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                compute(2, [Run(1, 100)], mode=mode)

    def test_homology_bypasses_structural_decisions_and_is_complete(self):
        runs = [Run(1, 1), Run(2, -1), Run(1, 1), Run(2, -1)]
        expected = homology(3, runs, check_d2=True)
        for method in ('tail', 'streaming', 'macro'):
            answer = compute(3, runs, mode='homology', method=method, check_d2=True)
            self.assertEqual(answer['status'], 'COMPUTED')
            self.assertTrue(answer['homology_complete'])
            self.assertEqual(answer['homology']['reduced_rank'], expected['reduced_rank'])
            got = answer['homology']
            by_degree = expand_profile(got['degree_profile']) if method == 'tail' else got['by_degree']
            self.assertEqual(by_degree, expected['by_degree'])
            self.assertNotIn('certificate', answer)

    def test_inconclusive_structure_reaches_each_exact_backend(self):
        # sigma_1^3 sigma_1^-2 is an unknot with a positive-genus, mixed-sign
        # supplied Seifert surface. Structural bounds include zero.
        runs = [Run(1, 3), Run(1, -2)]
        for method in ('tail', 'streaming', 'macro'):
            answer = compute(2, runs, method=method, check_d2=True)
            self.assertEqual(answer['status'], 'UNKNOT')
            self.assertEqual(answer['certificate']['status'], 'INCONCLUSIVE')
            self.assertEqual(answer['homology']['reduced_rank'], 1)

    def test_resource_exhaustion_stays_unknown(self):
        runs = [Run(1, 3), Run(1, -2)]
        for method in ('tail', 'streaming', 'macro'):
            budget = StreamBudget(max_states=0) if method == 'streaming' else Budget(max_states=0)
            answer = compute(2, runs, method=method, budget=budget)
            self.assertEqual(answer['status'], 'UNKNOWN')
            self.assertEqual(answer['certificate']['status'], 'INCONCLUSIVE')
        # A structural decision must not replace requested exact homology.
        answer = compute(2, [Run(1, 101)], mode='homology', budget=Budget(max_states=2))
        self.assertEqual(answer['status'], 'UNKNOWN')
        self.assertEqual(compute(2, [Run(1, 3)], budget=Budget(seconds=0))['status'], 'UNKNOWN')

    def test_profile_returns_only_original_structural_certificate(self):
        answer = compute(2, [Run(1, 3), Run(1, -2)], mode='profile')
        self.assertEqual(answer['status'], 'INCONCLUSIVE')
        self.assertNotIn('homology', answer)
        self.assertEqual(answer['certificate']['source'], 'original checked braid')
        self.assertEqual(answer['certificate']['crossings'], 5)

    def test_configuration_validation(self):
        runs = [Run(1, 3)]
        for kwargs in ({'mode': 'guess'}, {'method': 'guess'},
                       {'run_index': True}, {'run_index': 1},
                       {'method': 'macro', 'run_index': 0},
                       {'method': 'streaming', 'budget': Budget()},
                       {'method': 'tail', 'budget': StreamBudget()}):
            with self.subTest(kwargs=kwargs), self.assertRaises(ValueError):
                compute(2, runs, **kwargs)
        bad = StreamBudget()
        bad.max_states = -1
        with self.assertRaises(ValueError):
            compute(2, runs, method='streaming', budget=bad)

    def test_cli_json_stdin_exit_codes_and_exact_profile(self):
        def invoke(value, *flags):
            source = value if isinstance(value, str) else json.dumps(value)
            output = io.StringIO()
            with patch('sys.stdin', io.StringIO(source)), redirect_stdout(output):
                code = main(['-', *flags])
            return code, json.loads(output.getvalue())

        code, result = invoke({'strands': 2, 'runs': [[1, 101]]}, '--mode', 'homology')
        self.assertEqual(code, 0)
        self.assertEqual(result['homology']['reduced_rank'], 101)
        self.assertEqual(len(result['homology']['degree_profile']['intervals']), 1)
        code, result = invoke({'strands': 2, 'runs': [[1, 3], [1, -2]]}, '--max-states', '0')
        self.assertEqual((code, result['status']), (3, 'UNKNOWN'))
        code, result = invoke({'strands': 2, 'runs': [[1, 100]]})
        self.assertEqual((code, result['status']), (2, 'INVALID'))
        code, result = invoke('{ malformed')
        self.assertEqual((code, result['status']), (2, 'INVALID'))
        code, result = invoke({'strands': 2, 'runs': [[1, 3]]},
                              '--mode', 'homology', '--method', 'streaming', '--check-d2')
        self.assertEqual((code, result['status']), (0, 'COMPUTED'))
        self.assertTrue(result['homology']['homology_complete'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
