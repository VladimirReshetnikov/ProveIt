"""Native worker isolation, exact conversion, and adaptive failure handling."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from time import monotonic
import unittest
from unittest.mock import patch

from fastunknot import Diagram, recognize, Result
from fastunknot.normal_surface import (_invoke, NormalTimeout, input_digest,
                                      regina_decide, regina_pd)
from fastunknot.scan import ScanLimit

ROOT = Path(__file__).resolve().parents[1]
HAVE_REGINA = importlib.util.find_spec('regina') is not None


def load(name):
    return Diagram.from_json(json.loads((ROOT/'normal_research'/(name+'.json')).read_text()))


def response(d):
    return dict(version=1, engine='regina', engine_version='test', distribution_version='test',
                input_digest=input_digest(d.pd), input_crossings=d.crossings,
                simplified_crossings=0, tetrahedra=2, status='UNKNOT',
                trust='external-engine verdict; no independently checked normal-surface certificate')


class NormalSurfaceTests(unittest.TestCase):
    def test_pd_conversion_preserves_every_crossing(self):
        for d in (load('gordian'), load('monster'), load('gst'), load('gordian').mirror()):
            rows = regina_pd(d)
            for before, after, (incoming, _) in zip(d.pd, rows, d.incoming_slots()):
                normalized = tuple(x-1 for x in after)
                self.assertEqual(normalized, before[incoming:]+before[:incoming])
                self.assertIn(incoming, (0, 2))
            self.assertEqual(Diagram.from_pd(rows).writhe(), d.writhe())

    def test_worker_is_reaped_on_local_and_global_cancellation(self):
        created = []
        original = subprocess.Popen
        def spawn(*args, **kwargs):
            child = original(*args, **kwargs)
            created.append(child)
            return child
        command = [sys.executable, '-B', '-c', 'import sys,time;sys.stdin.read();time.sleep(10)']
        with patch('subprocess.Popen', side_effect=spawn):
            with self.assertRaises(NormalTimeout):
                _invoke(command, '{}', monotonic()+0.1, lambda: None)
            ticks = []
            def stop():
                ticks.append(1)
                if len(ticks) > 2:
                    raise ScanLimit('global cancellation')
            with self.assertRaises(ScanLimit):
                _invoke(command, '{}', None, stop)
        self.assertEqual(len(created), 2)
        for child in created:
            self.assertIsNotNone(child.poll())
            self.assertTrue(child.stdin.closed and child.stdout.closed and child.stderr.closed)

    def test_communication_retains_input_across_polls(self):
        command = [sys.executable, '-B', '-c',
            'import sys,time;time.sleep(.12);data=sys.stdin.read();sys.stdout.write(data);sys.stderr.write("note")']
        payload = 'x'*500000
        code, out, err = _invoke(command, payload, monotonic()+3, lambda: None)
        self.assertEqual((code, out, err), (0, payload, 'note'))

    def test_communication_drains_both_outputs_while_input_is_pending(self):
        command = [sys.executable, '-B', '-c',
            'import sys,time;sys.stdout.write("o"*500000);sys.stdout.flush();'
            'sys.stderr.write("e"*600000);sys.stderr.flush();time.sleep(.12);'
            'data=sys.stdin.read();sys.stdout.write(data)']
        payload = 'in\n'*150000
        code, out, err = _invoke(command, payload, monotonic()+3, lambda: None)
        self.assertEqual((code, out, err), (0, 'o'*500000+payload, 'e'*600000))

    def test_blocked_input_cancellation_reaps_and_closes_pipes(self):
        # The child never reads stdin, so input remains pending on cancellation.
        # Both local and caller cancellation must finish without its 10 s sleep.
        created = []
        original = subprocess.Popen
        def spawn(*args, **kwargs):
            child = original(*args, **kwargs)
            created.append(child)
            return child
        command = [sys.executable, '-B', '-c', 'import time;time.sleep(10)']
        payload = 'x'*500000
        started = monotonic()
        with patch('subprocess.Popen', side_effect=spawn):
            with self.assertRaises(NormalTimeout):
                _invoke(command, payload, monotonic()+0.1, lambda: None)
            ticks = []
            def stop():
                ticks.append(1)
                if len(ticks) > 2:
                    raise TimeoutError('caller cancelled during pipe writes')
            with self.assertRaisesRegex(TimeoutError, 'caller cancelled'):
                _invoke(command, payload, None, stop)
        self.assertLess(monotonic()-started, 3)
        self.assertEqual(len(created), 2)
        for child in created:
            self.assertIsNotNone(child.poll())
            self.assertTrue(child.stdin.closed and child.stdout.closed and child.stderr.closed)

    def test_missing_dependency_and_invalid_worker_cannot_decide(self):
        d = load('monster')
        with patch('importlib.util.find_spec', return_value=None), patch(
                'fastunknot.normal_surface._invoke', side_effect=AssertionError('launched unavailable engine')):
            self.assertEqual(regina_decide(d)['status'], 'INCONCLUSIVE')
        valid = response(d)
        changes = [('version', True), ('input_digest', 'wrong'), ('input_crossings', True),
                   ('status', 'UNKNOWN'), ('engine', 'other'), ('tetrahedra', 0),
                   ('simplified_crossings', 99), ('trust', 'independently verified')]
        responses = [(0, 'not JSON', ''), (1, json.dumps(valid), '')]
        for key, value in changes:
            changed = copy.deepcopy(valid)
            changed[key] = value
            responses.append((0, json.dumps(changed), ''))
        with patch('importlib.util.find_spec', return_value=object()):
            for bad in responses:
                with patch('fastunknot.normal_surface._invoke', return_value=bad):
                    self.assertEqual(regina_decide(d)['status'], 'INCONCLUSIVE')
            with patch('fastunknot.normal_surface._invoke', return_value=(0, json.dumps(valid), '')):
                self.assertEqual(regina_decide(d)['status'], 'UNKNOT')
                self.assertEqual(regina_decide(d, seconds=0)['status'], 'INCONCLUSIVE')
            with patch('subprocess.Popen', side_effect=OSError('cannot start child')):
                self.assertEqual(regina_decide(d)['status'], 'INCONCLUSIVE')
            # A caller's cancellation exception must not be mistaken for
            # a child-launch/pipe failure merely because it is an OSError.
            with patch('fastunknot.normal_surface._invoke', side_effect=TimeoutError('caller cancelled')):
                with self.assertRaises(TimeoutError):
                    regina_decide(d)

    def test_pipeline_dispatch_and_fallback(self):
        # GST is rejected by Alexander before the optional expensive stage.
        with patch('fastunknot.normal_surface.regina_decide', side_effect=AssertionError('unnecessary probe')):
            self.assertEqual(recognize(load('gst'), use_regina=True).status, 'KNOTTED')
            self.assertEqual(recognize(load('monster'), use_regina=True).status, 'UNKNOT')
        d = load('gordian')
        options = dict(use_regina=True, use_seifert=False, use_reduction=False,
            use_descending=False, use_factorization=False, use_modular=False,
            use_jones=False, use_alexander=False, use_r3=False, max_objects=0)
        with patch('fastunknot.normal_surface.regina_decide', return_value=response(d)) as native:
            result = recognize(d, **options)
            self.assertEqual(result.method, 'regina-solid-torus')
            self.assertEqual(native.call_args.args[0].pd, d.pd)
            self.assertIn('external-engine', result.to_json()['worst_case'])
        with patch('fastunknot.normal_surface.regina_decide', return_value=dict(status='INCONCLUSIVE')):
            result = recognize(d, **options)
            self.assertEqual(result.status, 'UNKNOWN')
            self.assertIn('objects would exceed', result.evidence['reason'])
        nested = Result('UNKNOT', 'connected-sum-all-factors-trivial', 10, 10, 0,
                        dict(factors=[dict(regina=response(load('monster')))]))
        self.assertIn('external-engine', nested.to_json()['worst_case'])
        for bad in (True, -1, float('nan'), float('inf')):
            with self.assertRaises(ValueError):
                recognize(d, use_regina=True, regina_seconds=bad)
            with self.assertRaises(ValueError):
                regina_decide(d, seconds=bad)
        with self.assertRaises(ValueError):
            recognize(d, use_regina=1)

    @unittest.skipUnless(HAVE_REGINA, 'optional Regina dependency')
    def test_actual_worker_exact_verdicts(self):
        cases = [(Diagram.from_pd([]), 'UNKNOT'), (load('monster'), 'UNKNOT')]
        for word in ([1, 1, 1], [1, -1, 1], [-1, -1, -1], [1, -2]*2):
            cases.append((Diagram.from_braid(max(map(abs, word))+1, word),
                          'UNKNOT' if word == [1, -1, 1] else 'KNOTTED'))
        for d, expected in cases:
            result = regina_decide(d, seconds=10)
            self.assertEqual(result['status'], expected, result)
            self.assertEqual(result['input_digest'], input_digest(d.pd))
            from importlib.metadata import version
            self.assertEqual(result['distribution_version'], version('regina'))

    @unittest.skipUnless(HAVE_REGINA, 'optional Regina dependency')
    def test_actual_global_deadline(self):
        result = recognize(load('gordian'), use_regina=True, seconds=0.05, regina_seconds=10)
        self.assertEqual(result.status, 'UNKNOWN')
        self.assertLess(result.seconds, 2)

    @unittest.skipUnless(HAVE_REGINA, 'optional Regina dependency')
    def test_actual_cli_external_verdict(self):
        run = subprocess.run([sys.executable, '-B', '-m', 'fastunknot', 'recognize',
            str(ROOT/'normal_research/gordian.json'), '--regina', '--regina-seconds', '8',
            '--seconds', '12'], capture_output=True, text=True, timeout=15, check=True)
        result = json.loads(run.stdout)
        self.assertEqual(result['status'], 'UNKNOT')
        self.assertEqual(result['method'], 'regina-solid-torus')
        self.assertIn('external-engine', result['worst_case'])


if __name__ == '__main__':
    unittest.main()
