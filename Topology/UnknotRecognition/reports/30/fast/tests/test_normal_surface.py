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

    def test_cancellation_during_blocked_payload_reaps_child_and_pipe_thread(self):
        import threading
        children, threads = [], []
        original_popen, original_thread = subprocess.Popen, threading.Thread

        def spawn(*args, **kwargs):
            child = original_popen(*args, **kwargs)
            children.append(child)
            return child

        def start_thread(*args, **kwargs):
            thread = original_thread(*args, **kwargs)
            threads.append(thread)
            return thread

        polls = 0

        def cancel():
            nonlocal polls
            polls += 1
            if polls == 5:
                raise ScanLimit('cancel while the payload is blocked')

        command = [sys.executable, '-B', '-c',
            'import sys,time;time.sleep(10);sys.stdout.write(sys.stdin.read())']
        start = monotonic()
        with patch('subprocess.Popen', side_effect=spawn), \
             patch('threading.Thread', side_effect=start_thread):
            with self.assertRaisesRegex(ScanLimit, 'payload is blocked'):
                _invoke(command, 'x'*2000000, None, cancel)
        self.assertLess(monotonic()-start, 3)
        self.assertEqual(len(children), 1)
        self.assertTrue(any(thread.name.startswith('fastunknot-normal-pipes-') for thread in threads))
        self.assertTrue(all(not thread.is_alive() for thread in threads))
        child = children[0]
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
            children, original_popen = [], subprocess.Popen

            def spawn(*args, **kwargs):
                child = original_popen(*args, **kwargs)
                children.append(child)
                return child

            for failure in (RuntimeError('cannot start pipe thread'),
                            OSError('pipe thread resource failure')):
                with patch('subprocess.Popen', side_effect=spawn), \
                     patch('threading.Thread.start', side_effect=failure):
                    result = regina_decide(d)
                    self.assertEqual(result['status'], 'INCONCLUSIVE')
                    self.assertIn(str(failure), result['reason'])
                child = children[-1]
                self.assertIsNotNone(child.poll())
                self.assertTrue(child.stdin.closed and child.stdout.closed and child.stderr.closed)
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
