import copy
import random
import unittest
from itertools import product
from pivotwidth import Instance,Decomposition,min_fill_decomposition,optimize,replay,StateLimitExceeded
from pivotwidth.verify import transport
from pivotwidth.core import Edge,Value,join
from pivotwidth.transfer import compile_transfer,power_certificate,expand,inspect_program
from pivotwidth.transfer_verify import verify_power,reference_transfer
from scripts.oracles import subset_value,positive_value,alternating_value,private_value
from examples.templates import defect_tile,path_tile


class MatrixTests(unittest.TestCase):
    def check(self,a,w=None):
        w=[1]*len(a) if w is None else w
        out=optimize(Instance.from_dense(a,w));replay(a,w,out)
        self.assertEqual(out['retained_weight'],subset_value(a,w))
        return out

    def test_empty(self):self.check([])
    def test_empty_rows(self):self.check([[],[],[]])
    def test_empty_columns(self):self.assertEqual(optimize(Instance.from_dense([],columns=7))['retained_weight'],0)
    def test_identity(self):self.assertEqual(self.check([[1,0],[0,1]])['retained_weight'],2)
    def test_unimodular_stopping(self):self.assertEqual(self.check([[1,1],[1,2]])['deferred_weight'],1)
    def test_cycle_forbidden(self):self.assertEqual(self.check([[1,1],[1,1]])['retained_weight'],1)
    def test_nonunit_is_not_pivot(self):self.assertEqual(self.check([[2]])['retained_weight'],0)
    def test_weighted_choice(self):self.assertEqual(self.check([[1,1],[1,2]],[11,3])['retained_weight'],11)
    def test_zero_weights(self):self.check([[1,1],[1,2]],[0,0])
    def test_private_active_passive(self):
        a=[[1,1],[1,2]];out=self.check(a,[7,1]);trace=replay(a,[7,1],out)
        tr=transport(a,trace['schedule']);self.assertEqual(tr['remaining_rows'],out['deferred_rows'])
        self.assertIn('1',tr['rows'])
    def test_forbidden_column(self):
        a=[[1,0],[0,1]];x=optimize(Instance.from_dense(a,forbidden_columns=[0]))
        self.assertEqual(x['retained_weight'],1);replay(a,[1,1],x,forbidden_pivots={(0,0)})
    def test_forbidden_row(self):
        a=[[1,1],[1,2]];x=optimize(Instance.from_dense(a,forbidden_rows=[0]))
        self.assertEqual(x['matching'],[[1,0]])
    def test_bad_counts(self):
        for a in [[[True]], [[-1]],[[1.0]],[[1],[1,2]]]:
            with self.assertRaises(ValueError):Instance.from_dense(a)
    def test_bad_weights(self):
        for w in [[],[-1],[True],[1.0]]:
            with self.assertRaises(ValueError):Instance.from_dense([[1]],w)
    def test_missing_vertex(self):
        with self.assertRaises(ValueError):optimize(Instance.from_dense([[1]]),Decomposition((frozenset({0}),),(None,),0))
    def test_uncovered_edge(self):
        with self.assertRaises(ValueError):optimize(Instance.from_dense([[1]]),Decomposition((frozenset({0}),frozenset({1})),(1,None),1))
    def test_disconnected_occurrence(self):
        inst=Instance.from_dense([[0]])
        with self.assertRaises(ValueError):optimize(inst,Decomposition((frozenset({0}),frozenset({1}),frozenset({0})),(1,2,None),2))
    def test_parent_cycle(self):
        with self.assertRaises(ValueError):Decomposition((frozenset(),)*3,(1,0,None),2).validate(Instance.from_dense([]))
    def test_resource_inconclusive(self):
        with self.assertRaises(StateLimitExceeded):optimize(Instance.from_dense([[1,1],[1,1]]),state_limit=1)
    def test_join_disjoint_flags(self):
        order=(0,1);v=Value(1,None)
        self.assertFalse(join({(order,1):v},{(order,1):v}))
        self.assertEqual(join({(order,1):v},{(order,2):v})[(order,3)].score,2)
    def test_exhaustive_binary_three_by_three(self):
        for x in product(range(2),repeat=9):self.check([list(x[0:3]),list(x[3:6]),list(x[6:9])])
    def test_random_weighted(self):
        rng=random.Random(738)
        for _ in range(70):
            m,n=rng.randrange(1,6),rng.randrange(1,6)
            a=[[rng.choice([0,0,0,1,1,2]) for j in range(n)] for i in range(m)]
            self.check(a,[rng.randrange(8) for i in range(m)])
    def test_arbitrary_positive_pivots(self):
        for x in product(range(3),repeat=6):
            a=[list(x[:3]),list(x[3:])]
            self.assertEqual(positive_value(a),subset_value(a))
    def test_alternating_permanent_oracle(self):
        rng=random.Random(517)
        for _ in range(50):
            a=[[rng.randrange(3) for j in range(3)] for i in range(3)]
            self.assertEqual(alternating_value(a),subset_value(a))
    def test_forged_cycle(self):
        bad={'schema':'ordered-pivot-plan-v1','matching':[[0,0],[1,1]],'deferred_rows':[],
             'retained_weight':2,'deferred_weight':0}
        with self.assertRaises(ValueError):replay([[1,1],[1,1]],[1,1],bad)
    def test_forged_objective(self):
        x=self.check([[1]]);x['retained_weight']=9
        with self.assertRaises(ValueError):replay([[1]],[1],x)


class TransferTests(unittest.TestCase):
    def test_defect_table(self):self.assertEqual(compile_transfer(defect_tile())['matrix'],[[1,1],[1,1]])
    def test_weighted_table(self):self.assertEqual(compile_transfer(defect_tile(3,7))['matrix'],[[7,3],[7,3]])
    def test_path_table(self):self.assertEqual(compile_transfer(path_tile(4))['matrix'],[[4,4],[0,4]])
    def test_zero_power(self):self.assertEqual(verify_power(power_certificate(defect_tile(),0))['retained_weight'],0)
    def test_small_expansions(self):
        for template in [defect_tile(),defect_tile(7,3),path_tile(4)]:
            for q in range(6):
                c=power_certificate(template,q);verify_power(c);x=expand(template,q)
                p=optimize(Instance.from_dense(x['matrix'],x['weights'],columns=x['columns']))
                self.assertEqual(c['retained_weight'],p['retained_weight'])
    def test_independent_leaf(self):
        for vals in product([1,2],repeat=4):
            p=defect_tile(3,7,*vals)
            self.assertEqual(compile_transfer(p)['matrix'],reference_transfer(p)[0])
    def test_huge_binary_power(self):
        c=power_certificate(defect_tile(3,7),1<<1024)
        self.assertEqual(c['deferred_weight'],3*(1<<1024));verify_power(c)
        self.assertLess(c['stats']['proof_nodes'],1030)
    def test_bad_coefficient(self):
        p=defect_tile();p['commands'][2]['count']=-1
        with self.assertRaises(ValueError):compile_transfer(p)
    def test_duplicate_edge(self):
        p=defect_tile();p['commands'].insert(3,copy.deepcopy(p['commands'][2]))
        with self.assertRaises(ValueError):compile_transfer(p)
    def test_input_input_edge(self):
        p={'inputs':[{'name':'r','side':'R','weight':1},{'name':'c','side':'C'}],
           'commands':[{'op':'edge','row':'r','column':'c','count':1}], 'outputs':{'r':'r','c':'c'}}
        with self.assertRaises(ValueError):compile_transfer(p)
    def test_type_mismatch(self):
        p=path_tile();p['outputs']={'q':'other'}
        with self.assertRaises(ValueError):power_certificate(p,2)
    def test_bad_output_bijection(self):
        p=path_tile();p['outputs']={}
        with self.assertRaises(ValueError):compile_transfer(p)
    def test_forged_base(self):
        c=power_certificate(path_tile(),3);c['nodes'][1]['matrix'][0][0]+=1
        with self.assertRaises(ValueError):verify_power(c)
    def test_forged_upper_bound(self):
        c=power_certificate(path_tile(),3);c['nodes'][c['root']]['matrix'][0][0]+=1
        with self.assertRaises(ValueError):verify_power(c)
    def test_forged_minus_infinity(self):
        c=power_certificate(path_tile(),3);c['nodes'][c['root']]['matrix'][0][0]=None
        with self.assertRaises(ValueError):verify_power(c)
    def test_forged_witness(self):
        c=power_certificate(path_tile(),3);c['nodes'][c['root']]['middle'][0][0]=99
        with self.assertRaises(ValueError):verify_power(c)
    def test_forged_cycle(self):
        c=power_certificate(path_tile(),3);r=c['root'];c['nodes'][r]['left']=r
        with self.assertRaises(ValueError):verify_power(c)
    def test_forged_exponent(self):
        c=power_certificate(path_tile(),3);c['exponent']=4
        with self.assertRaises(ValueError):verify_power(c)
    def test_forged_objective(self):
        c=power_certificate(path_tile(),3);c['deferred_weight']=1
        with self.assertRaises(ValueError):verify_power(c)



class PreprocessingTests(unittest.TestCase):
    def test_random_equivalence(self):
        from pivotwidth.preprocess import peel_then_optimize
        rng=random.Random(63791)
        for _ in range(100):
            a=[[rng.choice([0,0,1,2]) for j in range(5)] for i in range(5)]
            w=[rng.randrange(7) for i in range(5)];inst=Instance.from_dense(a,w)
            dec=min_fill_decomposition(inst);out=peel_then_optimize(inst,dec)
            replay(a,w,out);self.assertEqual(out['retained_weight'],subset_value(a,w))
    def test_complete_prepass(self):
        from pivotwidth.preprocess import peel_then_optimize
        out=peel_then_optimize(Instance.from_dense([[1,0],[0,1]]))
        self.assertEqual(out['stats']['prepeeled_rows'],2);self.assertEqual(out['stats']['peak_states'],0)
    def test_zero_rows_preserved(self):
        from pivotwidth.preprocess import peel_then_optimize
        out=peel_then_optimize(Instance.from_dense([[0,0],[0,0]]))
        self.assertEqual(out['deferred_rows'],[0,1])
    def test_sparse_native_labels(self):
        from integration.occurrence_adapter import propose_occurrence_reduction
        out=propose_occurrence_reduction({7:{100:1,102:1},17:{100:1,102:2}},weights={7:3,17:9})
        self.assertEqual(out['status'],'REDUCTION_PLAN');self.assertEqual(out['remaining_rows'],[7])
    def test_adapter_budget_is_inconclusive(self):
        from integration.occurrence_adapter import propose_occurrence_reduction
        out=propose_occurrence_reduction({1:{2:1}},max_dense_cells=0)
        self.assertEqual(out['status'],'INCONCLUSIVE')
    def test_inspected_min_fill_is_not_partial_optimum(self):
        from scripts.oracles import inspected_min_fill_rule
        a=[[2,0,1,0],[0,1,1,0],[1,1,0,1],[0,1,1,2]]
        trace=inspected_min_fill_rule(a)
        self.assertEqual(trace,[[1,1],[2,0]])
        transport(a,trace)
        cert=optimize(Instance.from_dense(a));checked=replay(a,[1]*4,cert)
        self.assertEqual(cert['retained_weight'],3)
        self.assertTrue(all(sum(row[j] for row in a)==3 for j in range(4)))
        self.assertEqual(transport(a,checked['schedule'])['rows'],{'3':{'0':10}})
    def test_scalar_profiles_not_interchangeable(self):
        left=[[1,0],[1,1],[0,1]];right=[[1,0,0],[1,1,1],[1,1,2],[0,0,1]]
        self.assertEqual(optimize(Instance.from_dense(left,[3,1,3]))['retained_weight'],6)
        self.assertEqual(optimize(Instance.from_dense(right,[3,1,1,3]))['retained_weight'],7)

if __name__=='__main__':unittest.main()
