"""Default late signed stage, shared source budgets and cancellation contracts."""
from contextlib import ExitStack
from copy import deepcopy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from fastunknot import normal_cut_handlebodies as portfolio
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.compressed_words import CompressedLimit, WordArena
from fastunknot.cyclic_basis import literal_cyclic_basis
from fastunknot.cyclic_basis_verify import verify_cyclic_basis
from fastunknot.signed_annulus_source import signed_annulus_source
from fastunknot.signed_annulus_source_verify import verify_signed_annulus_source
from fastunknot.signed_annulus_basis import signed_annulus_basis
from fastunknot.signed_annulus_basis_verify import replay_signed_annulus_basis
from tests.test_signed_annulus_source import native_parts


class LateStop:
    def __init__(self, count=2, exception=ValueError): self.left,self.exception=count,exception
    def __bool__(self): return False
    def __call__(self):
        self.left-=1
        if self.left==0: raise self.exception('cooperative stop')


class SignedPortfolioTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases=json.loads((Path(__file__).parents[1]/'signed_annulus_research/corpus.json').read_text())
        c=cls.cases['cases'][0];cls.args=c['triangulation'],c['coordinates']
        cls.parts=native_parts('pilot/fibonacci_lst_05/0')
        cls.source=signed_annulus_source(*cls.parts)
        cls.basis=signed_annulus_basis(*cls.parts)[0]

    def test_shared_queries_and_cached_geometric_core(self):
        for method,helper in [('masks','normal_parallelity_boundary_words'),('moments','_compile_moment_boundary')]:
            with self.subTest(method=method):
                with patch.object(portfolio,'core_handlebody_certificate',wraps=portfolio.core_handlebody_certificate) as core:
                    old=portfolio.normal_cut_handlebodies(*self.args,boundary_method=method,annulus_method='counts')
                    calls=core.call_count
                self.assertEqual(old['status'],'INCONCLUSIVE')
                with ExitStack() as stack:
                    core=stack.enter_context(patch.object(portfolio,'core_handlebody_certificate',wraps=portfolio.core_handlebody_certificate))
                    source=stack.enter_context(patch.object(portfolio,'normal_cut_parallelity',wraps=portfolio.normal_cut_parallelity))
                    boundary=stack.enter_context(patch.object(portfolio,helper,wraps=getattr(portfolio,helper)))
                    r=portfolio.normal_cut_handlebodies(*self.args,boundary_method=method,record_certificate=True)
                    self.assertEqual(source.call_count,1);self.assertEqual(boundary.call_count,1)
                    self.assertEqual(core.call_count,calls)
                self.assertEqual(r['status'],'COMPLETE')
                self.assertEqual(r['stats']['lower_forest_attempts'][-1]['strategy'],'signed_rank_two')
                self.assertTrue(verify_normal_cut_handlebodies(*self.args,r['certificate']))
                plain=portfolio.normal_cut_handlebodies(*self.args,boundary_method=method)
                self.assertEqual(plain['census'],r['census']);self.assertNotIn('certificate',plain)

    def test_exact_cycle_and_nielsen_operation_budgets(self):
        for method in ('masks','moments'):
            with self.subTest(method=method):
                r=portfolio.normal_cut_handlebodies(*self.args,boundary_method=method,record_certificate=True)
                cycles=sum(s['orbit_cycles'] for s in r['stats']['parallelity'].values())
                cycles+=sum(s['orbit_cycles'] for s in r['stats']['boundary'].values() if isinstance(s,dict) and 'orbit_cycles' in s)
                exact=portfolio.normal_cut_handlebodies(*self.args,boundary_method=method,record_certificate=True,max_cycles=cycles)
                self.assertEqual(exact['certificate'],r['certificate'])
                low=portfolio.normal_cut_handlebodies(*self.args,boundary_method=method,max_cycles=cycles-1)
                self.assertEqual(low['status'],'INCONCLUSIVE')
                p=r['certificate']; count=0
                for name in ('vertex_selector','boundary_selector','polygon_weights','fibre_cover'):
                    proof=p['parallelity'][name]
                    if name.endswith('selector'):proof=proof['weighted_certificate']
                    count+=len(proof['orbit_proof']['operations'])
                for name in (('census',) if method=='moments' else ('vertex_partition','gap_cover')):
                    if p['boundary'][name] is not None:count+=len(p['boundary'][name]['orbit_proof']['operations'])
                moves=sum(len(c['basis']['moves']) for c in p['signed_annuli']['components'])
                self.assertGreater(moves,0)
                self.assertTrue(verify_normal_cut_handlebodies(*self.args,p,max_operations=count+moves))
                self.assertFalse(verify_normal_cut_handlebodies(*self.args,p,max_operations=count+moves-1))

    def test_independent_replay_all_five_native_packets(self):
        names=['signed_annulus_source.signed_annulus_source','signed_annulus_basis.signed_annulus_basis',
               'signed_annulus_basis.compile_signed_quotient','cyclic_basis.cyclic_basis_blocks',
               'cyclic_basis.compile_nielsen','cyclic_basis.rank_two_lift',
               'normal_cut_handlebodies._signed_cut','normal_cut_handlebodies.normal_cut_handlebodies']
        for c in self.cases['cases']:
            args=c['triangulation'],c['coordinates']
            r=portfolio.normal_cut_handlebodies(*args,record_certificate=True)
            self.assertEqual(r['status'],'COMPLETE',c['id'])
            with ExitStack() as stack:
                for name in names:stack.enter_context(patch('fastunknot.'+name,side_effect=AssertionError(name)))
                self.assertTrue(verify_normal_cut_handlebodies(*args,r['certificate']),c['id'])
            p=deepcopy(r['certificate']);p['signed_annuli']['components'][0]['basis']['moves']={}
            self.assertFalse(verify_normal_cut_handlebodies(*args,p))

    def test_late_falsey_source_and_basis_callbacks_propagate(self):
        for exception in (ValueError,TypeError,ArithmeticError,CompressedLimit):
            with self.subTest(exception=exception):
                with self.assertRaisesRegex(exception,'cooperative stop'):
                    verify_signed_annulus_source(*self.parts,self.source,check=LateStop(exception=exception))
                with self.assertRaisesRegex(exception,'cooperative stop'):
                    replay_signed_annulus_basis(*self.parts,self.basis,check=LateStop(exception=exception))
                with patch('fastunknot.signed_annulus_basis.signed_annulus_source',return_value=self.source):
                    with self.assertRaisesRegex(exception,'cooperative stop'):
                        signed_annulus_basis(*self.parts,check=LateStop(exception=exception))

    def test_late_word_callback_propagates_and_is_restored(self):
        proof=literal_cyclic_basis([[1,2]],[1,2])['certificate']
        for exception in (ValueError,TypeError,CompressedLimit):
            arena=WordArena();root=arena.from_word([1,2]);callback=LateStop(exception=exception);arena.check=callback
            with self.assertRaisesRegex(exception,'cooperative stop'):
                verify_cyclic_basis(arena,[root],[1,2],proof)
            self.assertIs(arena.check,callback)

    def test_exact_integer_transport_and_malformed_exponents(self):
        r=portfolio.normal_cut_handlebodies(*self.args,record_certificate=True)
        def encoded(value):
            if type(value) is int: return hex(value)
            if type(value) is list: return [encoded(x) for x in value]
            if type(value) is dict: return {k:encoded(v) for k,v in value.items()}
            return value
        proof=deepcopy(r['certificate']);proof['signed_annuli']=encoded(proof['signed_annuli'])
        self.assertTrue(verify_normal_cut_handlebodies(*self.args,proof))
        moves=next(c['basis']['moves'] for c in proof['signed_annuli']['components']
                   if any(m['kind']=='multiply' for m in c['basis']['moves']))
        move=next(m for m in moves if m['kind']=='multiply')
        for bad in ('0xgarbage', True, 1.0):
            move['exponent']=bad
            self.assertFalse(verify_normal_cut_handlebodies(*self.args,proof))

    def test_local_word_budget_refuses_without_a_topological_verdict(self):
        self.assertIsNone(signed_annulus_basis(*self.parts,max_work=0))
        self.assertIsNone(replay_signed_annulus_basis(*self.parts,self.basis,max_work=0))

if __name__=='__main__':unittest.main()
