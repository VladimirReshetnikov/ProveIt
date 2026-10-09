import copy
import itertools
import random
import sys
import unittest
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT/'experiments')]
from sparse_incidence.api import analyze,dense_ablation
from sparse_incidence.reconstruct import discover,ResourceExhausted
from sparse_incidence.verify import verify
from sparse_incidence.signed import analyze_signed,verify_signed
from sparse_incidence.geometry import prepare,selected_union,cone_rows
from sparse_incidence.oracle import OrbitZetaOracle
from sparse_incidence.kernels import load_kernel
from sparse_incidence import codec
from common import literal,literal_signed,random_case,parallel_chain

class SparseTests(unittest.TestCase):
    def setUp(self):
        self.case=(10,[[0,4,5,9,1]],[[(0,2)],[(6,9)],[(0,1),(9,10)]])

    def test_empty_universe(self):
        for ports in ([],[[],[],[]]):
            result=analyze(0,[],ports,record_certificate=True)
            self.assertEqual(result['histogram'],[])
            self.assertTrue(verify(0,[],ports,result['certificate']))

    def test_no_ports_huge(self):
        result=analyze(1 << 16000,[],[],record_certificate=True)
        self.assertEqual(result['histogram'],[[0,1 << 16000]])
        self.assertTrue(verify(1 << 16000,[],[],result['certificate']))

    def test_exact_huge_multiplicity(self):
        n=1 << 4000
        result=analyze(n,[],[[(0,n)]]*80)
        self.assertEqual(result['histogram'],[[(1 << 80)-1,n]])
        self.assertEqual(result['stats']['supports'],1)
        self.assertEqual(result['stats']['orbit_calls'],2)

    def test_exhaustive_positive_rank_three(self):
        for weights in itertools.product(range(3),repeat=8):
            expected={m:w for m,w in enumerate(weights) if w}
            def get(mask):return sum(w for m,w in expected.items() if m&mask==m)
            for strategy in ('flat','balanced'):
                answer=discover(3,get,strategy=strategy)
                self.assertEqual(dict(answer['entries']),expected)

    def test_random_histograms(self):
        rng=random.Random(1048001)
        for _ in range(300):
            rank=rng.randrange(1,80)
            expected={rng.randrange(1 << rank):rng.randrange(1,1 << 100)
                      for _ in range(rng.randrange(1,15))}
            answer=discover(rank,lambda u:sum(w for t,w in expected.items() if t&u==t))
            self.assertEqual(dict(answer['entries']),expected)

    def test_balanced_singleton_query_bound(self):
        rank=1024; target=1 << 729;calls=[]
        answer=discover(rank,lambda u:(calls.append(u),int(u&target==target))[1])
        self.assertEqual(answer['entries'],[(target,1)])
        self.assertLessEqual(answer['stats']['block_tests'],21)

    def test_balanced_support_sensitive_bound(self):
        rng=random.Random(194)
        for rank in range(1,65):
            mask=rng.randrange(1,1 << rank);d=mask.bit_count()
            answer=discover(rank,lambda u:int(u&mask==mask))
            bound=1+2*sum(min(1 << level,d) for level in range((rank-1).bit_length()))
            self.assertLessEqual(answer['stats']['block_tests'],bound)

    def test_literal_random_relations(self):
        rng=random.Random(1048002)
        for _ in range(150):
            case=random_case(rng)
            result=analyze(*case,record_certificate=True)
            self.assertEqual(dict(result['histogram']),literal(*case))
            self.assertTrue(verify(*case,result['certificate']))
            self.assertEqual(dict(dense_ablation(*case)['histogram']),literal(*case))

    def test_noncanonical_input_and_adjacent_marks(self):
        case=(8,[[4,7,0,3,-1]], [[(3,5),(0,3),(2,4),(8,8)],[]])
        result=analyze(*case,record_certificate=True)
        self.assertEqual(dict(result['histogram']),literal(*case))
        self.assertTrue(verify(*case,result['certificate']))

    def test_signed_literal(self):
        rng=random.Random(1048003)
        for _ in range(100):
            n,rows,ports=random_case(rng,max_size=20,max_rank=6)
            signed=[row+[rng.randrange(2)] for row in rows]
            result=analyze_signed(n,signed,ports,record_certificate=True)
            self.assertEqual({m:[a,b] for m,a,b in result['histogram']},
                             literal_signed(n,signed,ports))
            self.assertTrue(verify_signed(n,signed,ports,result['certificate']))

    def test_signed_self_loop_is_not_order_reversal(self):
        result=analyze_signed(5,[[0,4,0,4,1,1]], [[(0,5)]],record_certificate=True)
        self.assertEqual(result['histogram'],[[1,0,5]])
        self.assertTrue(verify_signed(5,[[0,4,0,4,1,1]],[[(0,5)]],result['certificate']))

    def test_signed_budget_is_shared(self):
        result=analyze_signed(7,[],[[(0,7)]],max_queries=2,record_certificate=True)
        self.assertEqual(result['status'],'INCONCLUSIVE')
        self.assertIsNone(result['histogram'])
        self.assertIsNone(result['certificate'])
        self.assertLessEqual(result['stats']['orbit_calls'],2)

    def test_parallel_huge_chain(self):
        for shape in ('disjoint','nested','coincident'):
            case=parallel_chain(1 << 500,8,6,shape)
            result=analyze(*case,record_certificate=True)
            self.assertEqual(sum(w for m,w in result['histogram']),1 << 500)
            self.assertTrue(verify(*case,result['certificate']))

    def test_replay_does_not_call_producer(self):
        result=analyze(*self.case,record_certificate=True)
        kernel=load_kernel('interval_orbits')
        with patch.object(kernel,'count_orbits',side_effect=RuntimeError('producer disabled')):
            self.assertTrue(verify(*self.case,result['certificate']))

    def test_multiplicity_mutation(self):
        result=analyze(*self.case,record_certificate=True)
        cert=result['certificate'];cert['entries'][0][1]+=1
        self.assertFalse(verify(*self.case,cert))

    def test_omitted_support(self):
        cert=analyze(*self.case,record_certificate=True)['certificate']
        cert['entries'].pop()
        self.assertFalse(verify(*self.case,cert))

    def test_input_rebinding(self):
        cert=analyze(*self.case,record_certificate=True)['certificate']
        cert['ports'][0]=[[0,1]]
        self.assertFalse(verify(*self.case,cert))

    def test_duplicate_entry(self):
        cert=analyze(*self.case,record_certificate=True)['certificate']
        cert['entries'].insert(0,cert['entries'][0])
        self.assertFalse(verify(*self.case,cert))

    def test_boolean_entry_rejected(self):
        cert=analyze(*self.case,record_certificate=True)['certificate']
        cert['entries'][0][1]=True
        self.assertFalse(verify(*self.case,cert))

    def test_local_trace_mutation(self):
        cert=analyze(*self.case,record_certificate=True)['certificate']
        cert['baseline']['operations'].pop()
        self.assertFalse(verify(*self.case,cert))

    def test_missing_or_duplicate_union_proof(self):
        cert=analyze(*self.case,record_certificate=True)['certificate']
        missing=copy.deepcopy(cert);missing['union_proofs'].pop()
        self.assertFalse(verify(*self.case,missing))
        cert['union_proofs'].append(copy.deepcopy(cert['union_proofs'][0]))
        self.assertFalse(verify(*self.case,cert))

    def test_wrong_deletion_witness_is_rejected(self):
        # Same total and empty count, but move two singleton masses to their union.
        case=(2,[],[[(0,1)],[(1,2)]])
        cert=analyze(*case,record_certificate=True)['certificate']
        cert['entries']=[[3,2]]
        self.assertFalse(verify(*case,cert))

    def test_cycle_budget(self):
        for limit in range(8):
            result=analyze(*self.case,max_cycles=limit,record_certificate=True)
            self.assertLessEqual(result['stats']['cycles'],limit)
            if result['status']=='INCONCLUSIVE':
                self.assertIsNone(result['histogram']);self.assertIsNone(result['certificate'])

    def test_query_and_support_budget(self):
        for kw in ({'max_queries':0},{'max_queries':2},{'max_entries':0}):
            result=analyze(*self.case,**kw,record_certificate=True)
            self.assertEqual(result['status'],'INCONCLUSIVE')
            self.assertIsNone(result['histogram'])

    def test_certificate_budget_not_reset(self):
        case=(32,[],[[(i,i+1)] for i in range(5)])
        unc=analyze(*case)
        cert=analyze(*case,record_certificate=True,max_queries=unc['stats']['orbit_calls'])
        self.assertLessEqual(cert['stats']['orbit_calls'],unc['stats']['orbit_calls'])
        if cert['status']=='COMPLETE': self.assertTrue(verify(*case,cert['certificate']))

    def test_callback_exceptions_propagate(self):
        def cancel():raise RuntimeError('cancelled')
        with self.assertRaisesRegex(RuntimeError,'cancelled'):analyze(*self.case,check=cancel)
        cert=analyze(*self.case,record_certificate=True)['certificate']
        with self.assertRaisesRegex(RuntimeError,'cancelled'):verify(*self.case,cert,check=cancel)

    def test_hex_roundtrip(self):
        n=1 << 16000
        result=analyze(n,[],[[(0,n//2)]],record_certificate=True)
        import json
        restored=codec.decode(json.loads(codec.dumps(result)))
        self.assertTrue(verify(n,[],[[(0,n//2)]],restored['certificate']))

    def test_bad_input(self):
        for case in ((True,[],[]),(3,[[0,1,1,2,True]],[]),
                     (3,[],[[(0,4)]]),(3,[],[[(2,1)]]),
                     (3,[[0,1,1,1,1]],[])):
            with self.assertRaises(ValueError):analyze(*case)

    def test_dense_guard(self):
        with self.assertRaises(ValueError):dense_ablation(0,[],[[]]*17)

    def test_oracle_exact_union_cache(self):
        oracle=OrbitZetaOracle(20,[],[[(0,10)]]*6)
        self.assertEqual({oracle(u) for u in range(64)},{10,20})
        self.assertEqual(oracle.stats['orbit_calls'],2)

    def test_exact_certificate_budget_boundary(self):
        case=(17, [[4,12,2,10,-1],[0,12,4,16,-1],[1,16,0,15,-1],
                   [2,16,0,14,-1]],
              [[[8,16],[7,8]],[],[],[],[[1,11],[7,11],[11,16]],
               [[8,9],[1,14]],[[3,17],[0,15],[7,12]],[[5,8]],[[1,13],[8,15]]])
        before=analyze(*case)
        full=analyze(*case,record_certificate=True)
        self.assertGreater(full['stats']['orbit_calls'],before['stats']['orbit_calls'])
        limited=analyze(*case,record_certificate=True,
                        max_queries=before['stats']['orbit_calls'])
        self.assertEqual(limited['status'],'INCONCLUSIVE')
        self.assertIsNone(limited['histogram'])
        self.assertIsNone(limited['certificate'])

    def test_incidence_is_not_attachment_equivalence(self):
        ports=[[(0,2)],[(2,4)]]
        direct=[[0,0,2,2,1],[1,1,3,3,1]]
        crossed=[[0,0,3,3,1],[1,1,2,2,1]]
        self.assertEqual(analyze(4,direct,ports)['histogram'],[[3,2]])
        self.assertEqual(analyze(4,crossed,ports)['histogram'],[[3,2]])
        self.assertEqual(analyze(4,direct+direct,ports)['histogram'],[[3,2]])
        self.assertEqual(analyze(4,crossed+direct,ports)['histogram'],[[3,1]])

    def test_unused_valid_proof_rejected(self):
        cert=analyze(5,[],[],record_certificate=True)['certificate']
        cert['union_proofs']=[{'union':[[0,1]],'proof':copy.deepcopy(cert['baseline'])}]
        self.assertFalse(verify(5,[],[],cert))

if __name__=='__main__':unittest.main()
