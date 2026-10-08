import json
import math
import unittest
from itertools import product
from fastunknot.twist import Budget, ResourceLimit, Run, components, homology, recognize, runs_from_word, size_estimate
from fastunknot.twist.core import build_complex, validate_runs, verify_d_squared
from fastunknot.twist.__main__ import load_braid
from fastunknot.twist.reference import cube_homology


def h(b,w):
    return homology(b,runs_from_word(b,w),check_d2=True)['by_degree']


class AlgebraAndTopology(unittest.TestCase):
    def test_empty_unknot(self): self.assertEqual(h(1,[]),{0:1})
    def test_unlink(self): self.assertEqual(h(4,[]),{0:8})
    def test_positive_kink(self): self.assertEqual(h(2,[1]),{0:1})
    def test_negative_kink(self): self.assertEqual(h(2,[-1]),{0:1})
    def test_positive_trefoil(self): self.assertEqual(h(2,[1]*3),{0:1,2:1,3:1})
    def test_negative_trefoil(self): self.assertEqual(h(2,[-1]*3),{-3:1,-2:1,0:1})
    def test_figure_eight(self): self.assertEqual(h(3,[1,-2,1,-2]),{-2:1,-1:1,0:1,1:1,2:1})
    def test_torus_family(self):
        for m in (3,5,7,21,101):
            self.assertEqual(homology(2,[Run(1,m)],check_d2=True)['reduced_rank'],m)
    def test_inverse_pair(self): self.assertEqual(h(2,[1,-1]),h(2,[]))
    def test_opposite_blocks(self): self.assertEqual(h(2,[1]*4+[-1]*3),h(2,[1]))
    def test_braid_relation_positive(self): self.assertEqual(h(3,[1,2,1,2]),h(3,[2,1,2,2]))
    def test_braid_relation_negative(self): self.assertEqual(h(3,[-1,-2,-1,2]),h(3,[-2,-1,-2,2]))
    def test_far_commutation(self): self.assertEqual(h(4,[1,3,2,1,2]),h(4,[3,1,2,1,2]))
    def test_positive_stabilization(self): self.assertEqual(h(2,[1]*3),h(3,[1]*3+[2]))
    def test_negative_stabilization(self): self.assertEqual(h(2,[1]*3),h(3,[1]*3+[-2]))
    def test_mirror(self):
        w=[1,1,-2,1,-2,-2]
        self.assertEqual(h(3,[-x for x in w]),{-k:v for k,v in h(3,w).items()})
    def test_conjugation(self): self.assertEqual(h(3,[1,1,-2,-2]),h(3,[2,1,1,-2,-2,-2]))
    def test_cyclic_closure(self): self.assertEqual(h(3,[1,1,-2,1,-2]),h(3,[-2,1,1,-2,1]))
    def test_split_same_sign_run(self):
        a=homology(3,[Run(1,4),Run(2,-3)],check_d2=True)
        b=homology(3,[Run(1,2),Run(1,2),Run(2,-3)],check_d2=True)
        self.assertEqual(a['by_degree'],b['by_degree'])
    def test_component_parity(self):
        self.assertEqual(components(2,[Run(1,101)]),1)
        self.assertEqual(components(2,[Run(1,100)]),2)
    def test_sparse_huge_components(self): self.assertEqual(components(10**12,[Run(1,1)]),10**12-1)
    def test_exact_size_formula(self):
        runs=[Run(1,3),Run(2,-2),Run(1,1)]
        self.assertEqual(size_estimate(3,runs)['exact_basis'],build_complex(3,runs).stats['basis'])
    def test_size_formula_empty(self): self.assertEqual(size_estimate(4,[])['exact_basis'],8)
    def test_size_formula_budget(self): self.assertIsNone(size_estimate(3,[Run(1,2),Run(2,3)],max_supports=3)['exact_basis'])
    def test_size_upper_bound(self):
        r=[Run(1,3),Run(2,3),Run(1,-2)]
        s=size_estimate(3,r)
        self.assertLessEqual(s['exact_basis'],2**2*7*7*5)
    def test_d_squared_detects_corruption(self):
        from fastunknot.twist.core import Complex
        with self.assertRaises(ArithmeticError): verify_d_squared(Complex({0:1,1:1,2:1},{0:[1],1:[1],2:[0]},{}))
    def test_cube_reference(self):
        for w in ([1,1,-2,-2,1,-2],[1,-1,2],[-2,-2,1,1,-2]):
            self.assertEqual(h(3,w),cube_homology(3,w)['by_degree'])


class InterfaceAndLimits(unittest.TestCase):
    def test_group_runs(self): self.assertEqual(runs_from_word(3,[1,1,-1,2,2]),(Run(1,2),Run(1,-1),Run(2,2)))
    def test_optional_free_cancel(self): self.assertEqual(runs_from_word(3,[1,2,-2,-1],cancel=True),())
    def test_invalid_strands(self):
        for b in (0,-1,True,1.5):
            with self.assertRaises(ValueError): validate_runs(b,())
    def test_invalid_run(self):
        for r in (Run(0,1),Run(2,1),Run(1,0),Run(1,True)):
            with self.assertRaises(ValueError): validate_runs(2,[r])
    def test_invalid_word(self):
        for w in ([0],[2],[True]):
            with self.assertRaises(ValueError): runs_from_word(2,w)
    def test_invalid_budget(self):
        for kwargs in ({'max_states':-1},{'max_basis':1.5},{'seconds':float('nan')},{'seconds':float('inf')}):
            with self.assertRaises(ValueError): Budget(**kwargs)
    def test_recognize_unknot(self): self.assertEqual(recognize(2,[Run(1,1)])['status'],'UNKNOT')
    def test_recognize_trefoil(self): self.assertEqual(recognize(2,[Run(1,3)])['status'],'KNOTTED')
    def test_links_rejected(self):
        with self.assertRaises(ValueError): recognize(2,[Run(1,2)])
    def test_state_limit(self): self.assertEqual(recognize(2,[Run(1,101)],budget=Budget(max_states=10))['status'],'UNKNOWN')
    def test_basis_limit(self): self.assertEqual(recognize(2,[Run(1,3)],budget=Budget(max_basis=1))['status'],'UNKNOWN')
    def test_matrix_limit(self): self.assertEqual(recognize(2,[Run(1,3)],budget=Budget(max_matrix_bits=0))['status'],'UNKNOWN')
    def test_time_limit(self): self.assertEqual(recognize(2,[Run(1,3)],budget=Budget(seconds=0))['status'],'UNKNOWN')
    def test_xor_limit(self): self.assertEqual(recognize(3,runs_from_word(3,[1,-2,1,-2]),budget=Budget(max_xors=0),check_d2=True)['status'],'UNKNOWN')
    def test_binary_exponent_preflight(self):
        self.assertEqual(recognize(2,[Run(1,10**100+1)],budget=Budget(max_states=10))['status'],'UNKNOWN')
    def test_load_word(self): self.assertEqual(load_braid({'braid':{'strands':2,'word':[1,1,1]}}),(2,(Run(1,3),)))
    def test_load_runs(self): self.assertEqual(load_braid({'strands':2,'runs':[[1,-3]]}),(2,(Run(1,-3),)))
    def test_pd_rejected(self):
        with self.assertRaises(ValueError): load_braid({'pd':[]})
    def test_ambiguous_input_rejected(self):
        with self.assertRaises(ValueError): load_braid({'strands':2,'runs':[],'word':[]})
    def test_json_round_trip(self):
        result=recognize(2,[Run(1,3)],check_d2=True)
        self.assertEqual(json.loads(json.dumps(result))['homology']['reduced_rank'],3)

if __name__=='__main__': unittest.main()

class TemperleyLiebPreflight(unittest.TestCase):
    def test_trace_matches_subset_formula(self):
        from fastunknot.twist.preflight import basis_size
        for r in ([Run(1,3)],[Run(1,2),Run(2,-3),Run(1,4)],[Run(1,1),Run(3,2),Run(2,-1)]):
            b=max(x.generator for x in r)+1
            self.assertEqual(basis_size(b,r)['exact_basis'],size_estimate(b,r)['exact_basis'])
    def test_trace_huge_exponent(self):
        from fastunknot.twist.preflight import basis_size
        self.assertEqual(basis_size(2,[Run(1,10**100)])['exact_basis'],10**100+2)
    def test_merge_gap(self):
        from fastunknot.twist.preflight import basis_size
        a=basis_size(2,[Run(1,3),Run(1,5)])['exact_basis']
        b=basis_size(2,[Run(1,8)])['exact_basis']
        self.assertEqual(a-b,2*3*5)
    def test_opposite_sign_gap(self):
        from fastunknot.twist.preflight import basis_size
        a=basis_size(2,[Run(1,3),Run(1,-5)])['exact_basis']
        b=basis_size(2,[Run(1,-2)])['exact_basis']
        self.assertEqual(a-b,3+5+2*3*5-2)
    def test_preflight_resource_limit(self):
        from fastunknot.twist.preflight import basis_size
        with self.assertRaises(ResourceLimit): basis_size(2,[Run(1,3)],max_matchings=1)

class SharperBounds(unittest.TestCase):
    def test_generator_bound(self):
        from fastunknot.twist.preflight import basis_size,generator_basis_bound
        r=[Run(1,2),Run(2,3),Run(1,-4),Run(2,2)]
        self.assertLessEqual(basis_size(3,r)['exact_basis'],generator_basis_bound(3,r))
    def test_bound_sharp_two_strands(self):
        from fastunknot.twist.preflight import basis_size,generator_basis_bound
        r=[Run(1,2),Run(1,-3),Run(1,4)]
        self.assertEqual(basis_size(2,r)['exact_basis'],generator_basis_bound(2,r))
    def test_bound_sharp_distinct_generators(self):
        from fastunknot.twist.preflight import basis_size,generator_basis_bound
        r=[Run(1,2),Run(2,3),Run(3,4)]
        self.assertEqual(basis_size(4,r)['exact_basis'],generator_basis_bound(4,r))
    def test_weaving_chain_recurrence(self):
        from fastunknot.twist.preflight import basis_size
        a,b=2,7
        self.assertEqual(basis_size(3,[])['exact_basis'],a+2)
        for k in range(1,12):
            r=[Run(1,1),Run(2,-1)]*k
            self.assertEqual(basis_size(3,r)['exact_basis'],b+2)
            a,b=b,7*b-9*a
    def test_unused_strands_bound(self):
        from fastunknot.twist.preflight import basis_size,generator_basis_bound
        self.assertEqual(basis_size(5,[])['exact_basis'],generator_basis_bound(5,[]))

class DimensionProfiles(unittest.TestCase):
    def test_positive_profile(self):
        from fastunknot.twist.preflight import degree_profile
        r=[Run(1,3),Run(2,2)]
        self.assertEqual(degree_profile(3,r)['chain_dimensions'],build_complex(3,r).dimensions)
    def test_negative_profile(self):
        from fastunknot.twist.preflight import degree_profile
        r=[Run(1,-3),Run(2,-2)]
        self.assertEqual(degree_profile(3,r)['chain_dimensions'],build_complex(3,r).dimensions)
    def test_mixed_profile(self):
        from fastunknot.twist.preflight import degree_profile
        r=[Run(1,-2),Run(2,3),Run(1,-2)]
        p=degree_profile(3,r);c=build_complex(3,r)
        self.assertEqual(p['chain_dimensions'],c.dimensions)
        self.assertEqual(p['matrix_bit_upper_bound'],c.stats['matrix_bit_upper_bound'])
    def test_empty_profile(self):
        from fastunknot.twist.preflight import degree_profile
        self.assertEqual(degree_profile(3,[])['chain_dimensions'],{0:4})
    def test_profile_limit(self):
        from fastunknot.twist.preflight import degree_profile
        with self.assertRaises(ResourceLimit): degree_profile(2,[Run(1,10001)])

if __name__ == '__main__':
    unittest.main()
