"""Exact edge-first optimization, source topology and independent replay."""
from contextlib import ExitStack
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

from fastunknot import Diagram,recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed,CocycleLimit
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_lex import minimize_cocycle_edge_span
from fastunknot.cocycle_lex_verify import verify_cocycle_edge_span,inspect_lex_cocycle_certificate
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import NormalOrbitError
from fastunknot.integer_codec import json_safe


def source(strands=2,word=(1,)):
    d=Diagram.from_braid(strands,list(word));raw=diagram_exterior(d);seed=rank_one_cocycle_seed(raw)
    return d,raw,seed


def outer(d,raw,seed,answer):
    return dict(schema='diagram-cocycle-lex-v1',input_pd=[list(r) for r in d.pd],triangulation=raw,
        heights=seed['heights'],coordinates=answer['coordinates'],optimality_certificate=answer['certificate'])


class CocycleLexTests(unittest.TestCase):
    def test_exact_network_and_span_dual_reuse_agree(self):
        for strands,word in [(2,[1]),(2,[1,1,1]),(3,[1,-2,1,-2])]:
            d,raw,seed=source(strands,word)
            old=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
            network=minimize_cocycle_edge_span(raw,seed['heights'])
            reused=minimize_cocycle_edge_span(raw,seed['heights'],minimum_span=old)
            self.assertEqual(network['euler_characteristic'],reused['euler_characteristic'])
            self.assertEqual(network['normal_pieces'],reused['normal_pieces'])
            self.assertTrue(network['stats']['secondary_network'])
            self.assertFalse(reused['stats']['secondary_network'])
            for answer in (network,reused):
                self.assertTrue(verify_cocycle_edge_span(raw,seed['heights'],answer['certificate']))
                summary=inspect_lex_cocycle_certificate(d,outer(d,raw,seed,answer))
                self.assertEqual(summary['components'],1)
                self.assertEqual(summary['euler_characteristic'],answer['euler_characteristic'])
                self.assertEqual(verify_normal_seed_certificate(d,outer(d,raw,seed,answer)),word==[1])

    def test_complete_source_fields_mutations_and_primitive_class(self):
        d,raw,seed=source();answer=minimize_cocycle_edge_span(raw,seed['heights']);proof=outer(d,raw,seed,answer)
        for field in proof:
            bad=deepcopy(proof);del bad[field]
            self.assertFalse(verify_normal_seed_certificate(d,bad))
        arithmetic=answer['certificate']
        for field in arithmetic:
            bad=deepcopy(arithmetic);del bad[field]
            self.assertFalse(verify_cocycle_edge_span(raw,seed['heights'],bad))
        for field,value in [('schema','wrong'),('vertex_ids',[]),('normal_pieces',True),
                            ('euler_characteristic',True),('secondary',{}),('extra',0)]:
            bad=deepcopy(arithmetic);bad[field]=value
            self.assertFalse(verify_cocycle_edge_span(raw,seed['heights'],bad))
        for kind in ('primary','secondary'):
            bad=deepcopy(arithmetic);part=bad['primary'] if kind=='primary' else bad['secondary']['certificate']
            part['objective']+=1
            self.assertFalse(verify_cocycle_edge_span(raw,seed['heights'],bad))
        self.assertFalse(verify_normal_seed_certificate(Diagram.from_braid(2,[1,1,1]),proof))
        bad=deepcopy(proof);bad['coordinates'][0][0]+=1
        self.assertFalse(verify_normal_seed_certificate(d,bad))
        doubled=[[2*v for v in row] for row in seed['heights']]
        a=minimize_cocycle_edge_span(raw,doubled);bad=outer(d,raw,dict(seed,heights=doubled),a)
        self.assertTrue(verify_cocycle_edge_span(raw,doubled,a['certificate']))
        self.assertIsNone(inspect_lex_cocycle_certificate(d,bad))
        shifted=deepcopy(proof)
        shifted['optimality_certificate']['primary']['potential']=[v+17 for v in shifted['optimality_certificate']['primary']['potential']]
        shifted['optimality_certificate']['secondary']['certificate']['potential']=[v+17 for v in shifted['optimality_certificate']['secondary']['certificate']['potential']]
        self.assertTrue(verify_normal_seed_certificate(d,shifted))

    def test_no_optimization_or_orbit_producer_in_replay(self):
        d,raw,seed=source();span=minimize_cocycle_span(seed['vertices'],seed['heights'])['certificate']
        proofs=[outer(d,raw,seed,minimize_cocycle_edge_span(raw,seed['heights'],minimum_span=reuse)) for reuse in (None,span)]
        disabled=['fastunknot.cocycle_lex.minimize_cocycle_edge_span','fastunknot.cocycle_lex._prepared_minimize_edge_span',
            'fastunknot.cocycle_lex._minimize_difference','fastunknot.cocycle_euler_flow._minimize_difference',
            'fastunknot.cocycle_span.minimize_cocycle_span','fastunknot.normal_cocycle.rank_one_cocycle_seed',
            'fastunknot.normal_cocycle.local_coordinates','fastunknot.interval_orbits.count_orbits',
            'fastunknot.interval_orbits._count_orbits']
        with ExitStack() as stack:
            for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in replay')))
            for proof in proofs:self.assertTrue(verify_normal_seed_certificate(d,proof))

    def test_integer_encoding_source_gauges_and_cancellation(self):
        d,raw,seed=source();heights=[[v+(1<<20000) for v in row] for row in seed['heights']]
        answer=minimize_cocycle_edge_span(raw,heights)
        wire=json.loads(json.dumps(json_safe(outer(d,raw,dict(seed,heights=heights),answer))))
        self.assertTrue(verify_normal_seed_certificate(d,wire))
        proof=outer(d,raw,dict(seed,heights=heights),answer)
        for operation in (lambda c:minimize_cocycle_edge_span(raw,heights,check=c),
                          lambda c:verify_normal_seed_certificate(d,proof,check=c)):
            calls=[0]
            def tick():calls[0]+=1
            operation(tick);total=calls[0]
            for error in (ValueError,NormalOrbitError):
                for stop in (1,total//2,total):
                    calls[0]=0
                    def cancel():
                        tick()
                        if calls[0]==stop:raise error('caller cancellation')
                    with self.assertRaisesRegex(error,'caller cancellation'):operation(cancel)
        with self.assertRaises(CocycleLimit):minimize_cocycle_edge_span(raw,seed['heights'],max_work=0)

    def test_opt_in_seed_policy_and_shelling_pipeline(self):
        for shell in (False,True):
            for d in (Diagram.from_braid(2,[1]),Diagram.from_braid(2,[1,1,1])):
                before=normal_seed_decide(d,shellings=shell)
                disabled=normal_seed_decide(d,shellings=shell,edge_span=False)
                self.assertEqual(before,disabled)
                result=normal_seed_decide(d,shellings=shell,edge_span=True,optimize=False,tree_trials=0)
                if result['status']=='UNKNOT':self.assertTrue(verify_normal_seed_certificate(d,result['certificate']))
        for bad in (0,1,None,'yes'):
            with self.assertRaises(ValueError):normal_seed_decide(Diagram.from_braid(2,[1]),edge_span=bad)
            with self.assertRaises(ValueError):recognize(Diagram.from_braid(2,[1]),normal_seed_edge_span=bad)


if __name__=='__main__':unittest.main()
