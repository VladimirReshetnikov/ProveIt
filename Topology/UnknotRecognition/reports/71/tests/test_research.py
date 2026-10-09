import copy
import itertools
import random
import sys
import unittest
from collections import Counter
from math import comb
from pathlib import Path
from unittest.mock import patch
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'code'))
from envelope_kernel import (Budget, Candidate, Envelope, ResourceLimit, canonical,
    complementary_pairing, count, disk_compatible, exterior_row, join, partitions,
    reduce_family, refines, root_feature, validate)
from checker import (check_reduction, check_run, direct_compatible, slow_transition,
                     universal_envelopes, _feature, _incidence, nullspace)
from grammar import (Grammar, Patch, compile_envelopes, digest, from_data, solve,
                     to_data, transition)
from fixtures import (identity_patch, merge_patch, random_grammar,
                      restricted_grammar, wide_envelope)
from surface_replay import replay, replay_pair, replay_witness


def binary_rank(rows):
    pivots = {}
    for value in rows:
        while value:
            p = value.bit_length() - 1
            if p not in pivots:
                pivots[p] = value
                break
            value ^= pivots[p]
    return len(pivots)


def brute(g):
    """Enumerate every full assignment, with a literal final PL replay."""
    best = None
    domains = [range(len(g.initial))] + [range(len(l)) for l in g.layers] + [range(len(g.caps))]
    for w in itertools.product(*domains):
        cost = g.initial[w[0]].cost + g.caps[w[-1]].cost
        sector = g.initial[w[0]].sector ^ g.caps[w[-1]].sector
        for i, layer in enumerate(g.layers):
            cost += layer[w[i + 1]].cost
            sector ^= layer[w[i + 1]].sector
        if sector not in g.target_sectors:
            continue
        if replay_witness(g, w)['disk'] and (best is None or cost < best):
            best = cost
    return best


class AlgebraTests(unittest.TestCase):
    def test_partitions_and_validation(self):
        self.assertEqual([len(list(partitions(r))) for r in range(7)], [1,1,2,5,15,52,203])
        for p in partitions(6): self.assertEqual(validate(p),p)
        for p in ((),(1,),(0,2),(0,-1),(0,True)):
            with self.assertRaises(ValueError): validate(p)

    def test_invalid_candidates(self):
        for kwargs in ({'cost':True},{'sector':4},{'witness':(-1,)},{'sector':True}):
            with self.assertRaises(ValueError): Candidate((0,),**kwargs)
        self.assertEqual(Candidate([0,0]).partition,(0,0))

    def test_invalid_envelopes_and_sides(self):
        with self.assertRaises(ValueError): Envelope((0,),(0,1))
        e=Envelope((0,0),(0,0))
        for call in (lambda:e.feature((0,0),'x'),lambda:e.viable((0,0),'x'),
                     lambda:e.coordinate_partition(0,'x')):
            with self.assertRaises(ValueError): call()
        with self.assertRaises(ValueError): Envelope((0,1),(0,0)).feature((0,0))

    def test_factorization_every_envelope_through_four(self):
        for r in range(1,5):
            ps=list(partitions(r))
            for sigma in ps:
                for rho in ps:
                    e=Envelope(sigma,rho)
                    for p in ps:
                        if not refines(p,sigma): continue
                        for q in ps:
                            if not refines(q,rho): continue
                            v=0 if not e.connected else complementary_pairing(e.feature(p),e.feature(q,'future'),e.lam)
                            self.assertEqual(v,disk_compatible(p,q))

    def test_direct_matrix_rank_and_grading(self):
        for r in range(1,5):
            ps=list(partitions(r))
            for sigma in ps:
                for rho in ps:
                    e=Envelope(sigma,rho)
                    left=[p for p in ps if refines(p,sigma)]
                    right=[q for q in ps if refines(q,rho)]
                    rows=[sum(direct_compatible(p,q)<<i for i,q in enumerate(right)) for p in left]
                    self.assertEqual(binary_rank(rows),0 if not e.connected else 1<<e.lam)
                    if e.connected:
                        for j in range(e.lam+1):
                            self.assertEqual(binary_rank([row for p,row in zip(left,rows) if count(p)==count(sigma)+j]),comb(e.lam,j))

    def test_chord_detachment_permutation(self):
        for r in range(1,6):
            for rho in partitions(r):
                e=Envelope((0,)*r,rho)
                for mask in range(1<<e.lam):
                    p=e.coordinate_partition(mask)
                    self.assertEqual(e.feature(p),1<<mask)
                    q=e.coordinate_partition(mask,'future')
                    self.assertEqual(e.feature(q,'future'),1<<mask)

    def test_zero_rows_exactly_disconnected_split(self):
        for r in range(1,6):
            for rho in partitions(r):
                e=Envelope((0,)*r,rho)
                for p in partitions(r):
                    self.assertEqual(e.feature(p)!=0,e.viable(p))

    def test_homogeneous_support(self):
        e=Envelope((0,)*7,(0,0,0,0,1,2,3))
        for p in partitions(7):
            value=e.feature(p)
            while value:
                bit=value&-value;value-=bit
                self.assertEqual((bit.bit_length()-1).bit_count(),count(p)-1)

    def test_disconnected_envelope(self):
        e=Envelope((0,0,1),(0,1,2))
        self.assertFalse(e.connected)
        self.assertEqual(e.feature((0,0,1)),0)
        self.assertEqual(reduce_family([Candidate((0,0,1))],e).retained,())

    def test_tree_envelope_has_only_coarse_survivor(self):
        e=Envelope((0,0,1,2),(0,1,1,2))
        self.assertFalse(e.connected)
        e=Envelope((0,0,1,2),(0,1,1,1))
        self.assertEqual(e.lam,0)
        for p in partitions(4):
            if refines(p,e.sigma):self.assertEqual(bool(e.feature(p)),p==e.sigma)

    def test_parallel_edges_not_one_arc(self):
        e=Envelope((0,0),(0,0))
        self.assertEqual(e.lam,1)
        self.assertFalse(disk_compatible((0,0),(0,0)))
        self.assertTrue(disk_compatible((0,),(0,)))

    def test_wide_low_cycle_interface(self):
        e=Envelope(*wide_envelope(256,3))
        self.assertEqual((e.r,e.lam),(256,3))
        items=[Candidate(e.coordinate_partition(mask),mask-5) for mask in range(8)]
        result=reduce_family(items,e)
        self.assertEqual(len(result.retained),8)
        self.assertTrue(check_reduction(items,e.sigma,e.rho,result.certificate)[0])

    def test_cycle_and_root_allocation_guards(self):
        with self.assertRaises(ResourceLimit): Envelope((0,)*8,(0,)*8,max_cycle_rank=3)
        with self.assertRaises(ResourceLimit): root_feature((0,)*24)
        self.assertEqual(Envelope(*wide_envelope(128,2),max_cycle_rank=2).lam,2)

    def test_basis_change_keeps_identities(self):
        rng=random.Random(41)
        for _ in range(30):
            rho=canonical(rng.randrange(4) for _ in range(6))
            e=Envelope((0,)*6,rho)
            items=[Candidate(p,rng.randrange(-5,6)) for p in partitions(6)]
            red=reduce_family(items,e)
            incidence,_=_incidence(e.sigma,e.rho)
            basis=nullspace(incidence,e.r)
            if len(basis)>1:basis[0]^=basis[1]
            values=[_feature(c.partition,e.sigma,basis) for c in items]
            for i,expansion in enumerate(red.certificate['expansions']):
                v=0
                for j in expansion:v^=values[j]
                self.assertEqual(v,values[i])

    def test_empty_wedge_and_dependent_constraints(self):
        self.assertEqual(exterior_row([],0),1)
        self.assertEqual(exterior_row([1,1],2),0)
        self.assertEqual(exterior_row([0],3),0)


class RepresentativeTests(unittest.TestCase):
    def setUp(self):
        self.e=Envelope((0,)*5,(0,0,0,1,2))
        self.items=[Candidate(p,(7*i)%13-6,i%4,(i,)) for i,p in enumerate(partitions(5))]

    def test_all_weighted_queries(self):
        red=reduce_family(self.items,self.e)
        for q in partitions(5):
            if not refines(q,self.e.rho):continue
            for sector in range(4):
                def opt(indices):
                    return min((self.items[i].cost for i in indices if self.items[i].sector==sector and disk_compatible(self.items[i].partition,q)),default=None)
                self.assertEqual(opt(range(len(self.items))),opt(red.retained))

    def test_huge_signed_costs(self):
        items=[Candidate(c.partition,(1<<4096)*(c.cost-2),c.sector,c.witness) for c in self.items]
        red=reduce_family(items,self.e)
        self.assertTrue(check_reduction(items,self.e.sigma,self.e.rho,red.certificate)[0])

    def test_empty_family(self):
        red=reduce_family([],self.e)
        self.assertEqual(red.retained,())
        self.assertTrue(check_reduction([],self.e.sigma,self.e.rho,red.certificate)[0])

    def test_checker_independent_of_producer(self):
        red=reduce_family(self.items,self.e)
        with patch.object(Envelope,'feature',side_effect=AssertionError('must not be called')):
            self.assertTrue(check_reduction(self.items,self.e.sigma,self.e.rho,red.certificate)[0])

    def test_mutated_expansion(self):
        red=reduce_family(self.items,self.e)
        bad=copy.deepcopy(red.certificate)
        i=next(i for i,x in enumerate(bad['expansions']) if x)
        bad['expansions'][i]=[]
        self.assertFalse(check_reduction(self.items,self.e.sigma,self.e.rho,bad)[0])

    def test_mutated_source_cost_partition_and_witness(self):
        cert=reduce_family(self.items,self.e).certificate
        first=self.items[0]
        for changed in (Candidate(first.partition,first.cost+1,first.sector,first.witness),
                        Candidate((0,1,2,3,4),first.cost,first.sector,first.witness),
                        Candidate(first.partition,first.cost,first.sector,(999,))):
            altered=[changed]+self.items[1:]
            self.assertFalse(check_reduction(altered,self.e.sigma,self.e.rho,cert)[0])

    def test_mutated_indices_and_schema(self):
        cert=reduce_family(self.items,self.e).certificate
        for bad in (dict(cert,extra=True),dict(cert,retained=[999]),dict(cert,mode='wrong'),
                    dict(cert,expansions=[]),dict(cert,source_sha256='0'*64)):
            self.assertFalse(check_reduction(self.items,self.e.sigma,self.e.rho,bad)[0])

    def test_sector_cost_checks_even_with_true_identity(self):
        e=Envelope((0,),(0,))
        items=[Candidate((0,),1,0),Candidate((0,),0,1)]
        cert=reduce_family(items,e).certificate
        cert['expansions'][0]=[1]
        self.assertFalse(check_reduction(items,e.sigma,e.rho,cert)[0])

    def test_unjustified_future_widening_loses_answer(self):
        e=Envelope((0,0),(0,1))
        items=[Candidate((0,0),0),Candidate((0,1),1)]
        red=reduce_family(items,e)
        self.assertEqual(red.retained,(0,))
        self.assertTrue(disk_compatible(items[1].partition,(0,0)))
        self.assertFalse(any(disk_compatible(items[i].partition,(0,0)) for i in red.retained))

    def test_budget_exhaustion_is_exception(self):
        with self.assertRaises(ResourceLimit): reduce_family(self.items,self.e,tick=Budget(steps=0))
        with self.assertRaises(ResourceLimit): reduce_family(self.items,self.e,tick=Budget(seconds=0))


class GrammarTests(unittest.TestCase):
    def test_envelope_compiler_independent(self):
        rng=random.Random(501)
        for _ in range(50):
            g=random_grammar(rng)
            self.assertEqual(compile_envelopes(g),universal_envelopes(g))

    def test_transition_independent(self):
        for r in range(1,4):
            for p in partitions(r):
                for option in partitions(r+2):
                    self.assertEqual(transition(p,option,2),slow_transition(p,option,2))

    def test_three_solvers_and_run_checker(self):
        rng=random.Random(20261009)
        for _ in range(60):
            g=random_grammar(rng)
            answers=[solve(g,m) for m in ('exact','root','cycle')]
            self.assertEqual(len({(a['status'],a['cost_hex']) for a in answers}),1)
            for a in answers:
                self.assertTrue(check_run(g,a)[0],check_run(g,a))
                if a['witness']:self.assertTrue(replay_witness(g,a['witness'])['disk'])

    def test_bruteforce_mesh_all_assignments(self):
        rng=random.Random(712)
        for _ in range(10):
            g=random_grammar(rng,max_width=3,depth=1)
            answer=solve(g)
            got=None if answer['cost_hex'] is None else int(answer['cost_hex'],16)
            self.assertEqual(got,brute(g))

    def test_structured_search_compression(self):
        g=restricted_grammar(6,2,3)
        exact,root,cycle=[solve(g,m) for m in ('exact','root','cycle')]
        self.assertEqual(len({a['cost_hex'] for a in (exact,root,cycle)}),1)
        self.assertEqual(max(s['retained'] for s in cycle['statistics']),4)
        self.assertGreater(root['statistics'][0]['retained'],4)

    def test_json_roundtrip(self):
        g=restricted_grammar(4,1,2)
        self.assertEqual(g,from_data(to_data(g)))
        self.assertEqual(digest(g),digest(from_data(to_data(g))))

    def test_bad_grammar_rejected(self):
        with self.assertRaises(ValueError):Grammar((0,),(),(),())
        with self.assertRaises(ValueError):Grammar((2,), (Candidate((0,)),),(),())
        with self.assertRaises(ValueError):from_data({'schema':'bad'})
        with self.assertRaises(ValueError):Grammar((1,1),(),((Patch((0,)),),),())

    def test_empty_languages(self):
        for g in (Grammar((1,),(),(),(Candidate((0,)),)),
                  Grammar((1,1),(Candidate((0,)),),((),),(Candidate((0,)),)),
                  Grammar((1,),(Candidate((0,)),),(),())):
            a=solve(g)
            self.assertEqual(a['status'],'NO_DISK_IN_GRAMMAR')
            self.assertTrue(check_run(g,a)[0])

    def test_no_success_when_sector_target_missing(self):
        g=Grammar((1,),(Candidate((0,),sector=1),),(),(Candidate((0,)),),(0,))
        self.assertEqual(solve(g)['status'],'NO_DISK_IN_GRAMMAR')

    def test_witness_and_negative_run_mutations(self):
        g=restricted_grammar(4,1,2)
        a=solve(g)
        for bad in (dict(a,status='NO_DISK_IN_GRAMMAR'),dict(a,cost_hex='0xdead'),
                    dict(a,witness=[999]),dict(a,grammar_sha256='0'*64),dict(a,stages=[])):
            self.assertFalse(check_run(g,bad)[0])

    def test_modified_source_options_rejected(self):
        g=restricted_grammar(4,1,2)
        a=solve(g)
        changed=Grammar(g.widths,g.initial,(g.layers[0][:-1],)+g.layers[1:],g.caps)
        self.assertFalse(check_run(changed,a)[0])

    def test_run_checker_does_not_call_solver(self):
        g=restricted_grammar(4,1,2);a=solve(g)
        with patch('grammar.solve',side_effect=AssertionError('solver must not run')):
            self.assertTrue(check_run(g,a)[0])

    def test_grammar_budget_never_returns_partial_negative(self):
        g=restricted_grammar(5,2,4)
        with self.assertRaises(ResourceLimit):solve(g,tick=Budget(steps=25))


class SurfaceTests(unittest.TestCase):
    def test_literal_surface_pairings(self):
        for r in range(1,5):
            for p in partitions(r):
                for q in partitions(r):
                    self.assertEqual(replay_pair(p,q)['disk'],disk_compatible(p,q))

    def test_annulus_and_twisted_band(self):
        p=(0,0)
        annulus=replay_pair(p,p)
        self.assertEqual((annulus['euler'],annulus['boundary_components']), (0,2))
        mobius=replay([p,p],[(0,0,1,0,True),(0,1,1,1,False)])
        self.assertEqual((mobius['euler'],mobius['boundary_components'],mobius['orientable']),(0,1,False))

    def test_reused_arc_rejected(self):
        with self.assertRaises(ValueError):replay([(0,),(0,)],[(0,0,1,0,True),(0,0,1,0,True)])

    def test_positive_defect_persists(self):
        result=replay([(0,0,0),(0,0),(0,)],[(0,0,1,0,True),(0,1,1,1,True),(0,2,2,0,True)])
        self.assertEqual(result['euler'],0)
        self.assertFalse(result['disk'])

if __name__=='__main__':unittest.main(verbosity=2)
