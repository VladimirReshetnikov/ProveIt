"""Closure certificates, exact continuation, restart options and probe budgets."""
import copy
from contextlib import redirect_stdout, redirect_stderr
import io
import json
from pathlib import Path
import random
import tempfile
import unittest
from unittest.mock import patch

from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot import __main__ as cli
from fastunknot.cyclic_garside import (Budget, LimitExceeded, preprocess,
    verify, verify_radius, normal_form_candidate)
from fastunknot.cyclic_garside.verify import CertificateError
from fastunknot.cyclic_garside.radius import _dictionary, _trie
from fastunknot.cyclic_garside.oracles import old_barrier
from fastunknot.garside_probe import propose
from fastunknot.geometry import ScanLimit

NO_FILTERS = dict(use_braid=False, use_seifert=False, use_reduction=False,
                  use_descending=False, use_alexander=False, use_jones=False,
                  use_factorization=False)


def replay(b, word, certificate, **kwargs):
    checker = verify if certificate['schema'].endswith('v1') else verify_radius
    return checker(b, word, certificate, **kwargs)


class CyclicGarsideProductionTests(unittest.TestCase):
    def test_normalized_homology_after_cyclic_kernel(self):
        rng = random.Random(202610081933)
        count = 0
        while count < 60:
            b = rng.randrange(2,5)
            word = tuple(rng.choice((-1,1))*rng.randrange(1,b)
                         for _ in range(rng.randrange(1,10)))
            try:
                original = Diagram.from_braid(b, word)
            except ValueError:
                continue
            result = preprocess(b, word, radius=1 + count % 2)
            short = replay(b, word, result['certificate'])
            changed = Diagram.from_braid(b, short)
            profiles = []
            for diagram in (original, changed):
                raw = khovanov_rank(diagram.pd, check_d_squared=True)['by_degree']
                shift = diagram.signs().count(-1)
                profiles.append({h-shift:v for h,v in raw.items()})
            self.assertEqual(*profiles, (b, word, short))
            count += 1

    def test_restart_keeps_source_and_pd_provenance_separate(self):
        original = Diagram.from_braid(4, old_barrier(2))
        result = recognize(original, use_garside=True, garside_seconds=None,
                           garside_max_ticks=None, **NO_FILTERS)
        self.assertEqual(result.status, 'UNKNOT')
        self.assertTrue(result.method.startswith('garside-'))
        self.assertEqual(result.input_crossings, original.crossings)
        proof = result.evidence['before_garside']['garside']
        self.assertTrue(proof['used'])
        self.assertEqual(len(replay(4, old_barrier(2), proof['certificate'])), 3)
        self.assertIn('after_garside', result.evidence)
        # Equal to the current PD size is insufficient, even if it beats source size.
        proposal = propose(original, 3, seconds=None, max_ticks=None)
        self.assertIsNone(proposal.candidate)
        self.assertEqual(proposal.evidence['status'], 'verified')
        self.assertFalse(proposal.evidence['used'])

    def test_restart_preserves_backend_and_reduction_options(self):
        diagram = Diagram.from_braid(4, old_barrier(1))
        for backend in ('standard','shared','twist','barcode','fitting'):
            with self.subTest(backend=backend):
                result = recognize(diagram, use_garside=True, garside_seconds=None,
                                   backend=backend, **NO_FILTERS)
                self.assertEqual(result.status, 'UNKNOT')
                self.assertTrue(result.method.startswith('garside-'))
        for reduction in ('graded-adaptive','corridor-adaptive','disk-adaptive'):
            result = recognize(diagram, use_garside=True, garside_seconds=None,
                               reduction=reduction, **NO_FILTERS)
            self.assertEqual(result.evidence['after_garside']['khovanov']['reduction'], reduction)
        result = recognize(diagram, use_garside=True, garside_seconds=None,
                           composition='component-dense', tail=2, **NO_FILTERS)
        self.assertEqual(result.status, 'UNKNOT')

    def test_local_failure_falls_back_global_failure_is_unknown(self):
        diagram = Diagram.from_braid(4, old_barrier(1))
        for options in ({'garside_seconds':0}, {'garside_max_ticks':0}):
            result = recognize(diagram, use_garside=True, **options, **NO_FILTERS)
            self.assertEqual(result.status, 'UNKNOT')
            self.assertEqual(result.evidence['garside']['status'], 'skipped')
        with patch('fastunknot.garside_probe.preprocess', side_effect=MemoryError):
            result = recognize(diagram, use_garside=True, **NO_FILTERS)
            self.assertEqual(result.status, 'UNKNOT')
            self.assertEqual(result.evidence['garside']['status'], 'skipped')
        with patch('fastunknot.garside_probe.verify_radius', side_effect=ScanLimit('global expiry')):
            result = recognize(diagram, use_garside=True, garside_seconds=None, **NO_FILTERS)
            self.assertEqual(result.status, 'UNKNOWN')
        self.assertEqual(recognize(diagram, use_garside=True, seconds=0).status, 'UNKNOWN')

    def test_replay_and_shortcuts_poll_global_hooks(self):
        def stop():
            raise ScanLimit('global deadline')
        with self.assertRaises(ScanLimit):
            preprocess(3, (1,2), budget=Budget(hook=stop))
        cert = normal_form_candidate(4, old_barrier(1))['certificate']
        with self.assertRaises(ScanLimit):
            verify_radius(4, old_barrier(1), cert, check=stop)
        calls = 0
        def midway():
            nonlocal calls
            calls += 1
            if calls == 5:
                stop()
        with self.assertRaises(ScanLimit):
            verify_radius(4, old_barrier(1), cert, check=midway)
        self.assertEqual(calls, 5)
        with patch('fastunknot.cyclic_garside.portfolio.normal_form', side_effect=AssertionError):
            self.assertEqual(len(verify_radius(4, old_barrier(1), cert)), 3)

    def test_dictionary_trie_and_final_boundary_have_shared_limits(self):
        with self.assertRaises(LimitExceeded):
            _dictionary(4, 2, None, Budget(max_ticks=2))
        with self.assertRaises(LimitExceeded):
            _trie([(),(1,),(-1,)], Budget(max_ticks=0))
        with self.assertRaises(LimitExceeded):
            preprocess(3, (1,1,2,-1), radius=1, max_targets=1)
        self.assertEqual(_dictionary(1, 10**100, 1), [()])
        diagram = Diagram.from_braid(4, old_barrier(1))
        expired = False
        real_preprocess = preprocess
        def producer(*args, **kwargs):
            nonlocal expired
            result = real_preprocess(*args, **kwargs)
            expired = True
            return result
        def check():
            if expired:
                raise ScanLimit('expiry after producer')
        with patch('fastunknot.garside_probe.preprocess', side_effect=producer):
            with self.assertRaises(ScanLimit):
                propose(diagram, diagram.crossings, seconds=None, max_ticks=None, check=check)

    def test_bad_certificate_is_an_error_not_a_verdict(self):
        word = old_barrier(1)
        result = preprocess(4, word)
        result['certificate']['output'] = [1]
        with patch('fastunknot.garside_probe.preprocess', return_value=result):
            with self.assertRaises(CertificateError):
                recognize(Diagram.from_braid(4, word), use_garside=True,
                          garside_seconds=None, **NO_FILTERS)

    def test_cheap_certificates_and_missing_source_bypass_probe(self):
        with patch('fastunknot.garside_probe.propose', side_effect=AssertionError('unexpected probe')):
            self.assertEqual(recognize(Diagram.from_braid(2,[1]*3), use_garside=True).status, 'KNOTTED')
            d = Diagram.from_braid(4,old_barrier(1))
            self.assertEqual(recognize(d, use_garside=True).status, 'UNKNOT')
            self.assertEqual(recognize(Diagram.from_pd(d.pd), use_garside=True).status, 'UNKNOT')

    def test_options_validated_before_early_certificates(self):
        diagram = Diagram.from_braid(2,[1]*3)
        for options in ({'use_garside':1}, {'garside_radius':True}, {'garside_radius':0},
                        {'garside_seconds':-1}, {'garside_seconds':float('nan')},
                        {'garside_max_ticks':-1}, {'garside_max_ticks':True},
                        {'garside_max_targets':0}):
            with self.assertRaises(ValueError):
                recognize(diagram, **options)
        with self.assertRaises(ValueError):
            preprocess(2,(1,),max_targets=0)

    def test_modular_obstruction_precedes_probe_and_later_filters_remain(self):
        diagram = Diagram.from_braid(4, old_barrier(1)[:-3]+(1,-2,1,-2,3))
        base = dict(NO_FILTERS)
        with patch('fastunknot.garside_probe.propose', side_effect=AssertionError('probe before filter')):
            result = recognize(diagram, use_garside=True, **(base | dict(use_alexander=True)))
            self.assertEqual(result.status, 'KNOTTED')
            self.assertEqual(result.method, 'alexander-modular')
        for options, method in ((dict(use_jones=True), 'jones-modular'),
                                (dict(use_alexander=True, use_modular=False), 'alexander-polynomial')):
            result = recognize(diagram, use_garside=True, garside_seconds=0, **(base | options))
            self.assertEqual(result.status, 'KNOTTED')
            self.assertEqual(result.method, method)
            self.assertEqual(result.evidence['garside']['status'], 'skipped')
        # A successful source branch can avoid computing Jones on the large PD.
        with patch('fastunknot.recognize._invariant_obstruction', side_effect=AssertionError('late filter')):
            result = recognize(Diagram.from_braid(4, old_barrier(1)), use_garside=True,
                               garside_seconds=None, **(base | dict(use_seifert=True, use_jones=True)))
            self.assertEqual(result.status, 'UNKNOT')
            self.assertEqual(result.method, 'garside-seifert-genus-zero')

    def test_inconclusive_filters_and_order_are_reused_after_local_limit(self):
        import importlib
        module = importlib.import_module('fastunknot.recognize')
        diagram = Diagram.from_braid(4, old_barrier(1))
        options = dict(NO_FILTERS) | dict(use_alexander=True, use_jones=True)
        with patch.object(module, 'alexander_obstruction', wraps=module.alexander_obstruction) as probe:
            with patch.object(module, 'best_scan_order', wraps=module.best_scan_order) as order:
                result = recognize(diagram, use_garside=True, garside_seconds=0, **options)
        self.assertEqual(result.status, 'UNKNOT')
        self.assertEqual(result.evidence['garside']['status'], 'skipped')
        self.assertEqual(probe.call_count, 1)
        self.assertEqual(order.call_count, 1)

    def test_both_cli_parsers_and_invalid_allowance(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)/'input.json'
            p.write_text(json.dumps({'braid':{'strands':4,'word':list(old_barrier(1))}}))
            flags = ['--no-braid','--no-seifert','--no-reduction','--no-descending',
                     '--no-alexander','--no-jones','--no-factor']
            for radius in (['--garside-radius','2'], ['--garside-radius=2']):
                out = io.StringIO()
                with redirect_stdout(out):
                    code = cli.main(['recognize',str(p),'--garside','--garside-seconds','5',*radius,*flags])
                self.assertEqual(code,0)
                self.assertTrue(json.loads(out.getvalue())['method'].startswith('garside-'))
            with redirect_stderr(io.StringIO()):
                self.assertEqual(cli.main(['recognize',str(p),'--garside-seconds','nan']),2)


if __name__ == '__main__':
    unittest.main()
