import copy,itertools,random,unittest
from collections import Counter
from shear_kernel import *
from shear_kernel.flow import Arc,min_cost_circulation,balanced_potentials
from shear_kernel.reference import *
from shear_kernel.optimize import fingerprint

class GrammarTests(unittest.TestCase):
    def test_empty(self):
        g=Grammar(); o=optimize(g,[0]); self.assertEqual(o.certificate['optimal_length'],0)
        self.assertTrue(verify_optimization(g,[0],o.certificate))
    def test_invalid_letter(self):
        for x in (0,True,1.0):
            with self.assertRaises(ValueError): Grammar().letter(x)
    def test_invalid_power(self):
        g=Grammar(); n=g.letter(1)
        for k in (-1,True,0.5):
            with self.assertRaises(ValueError): g.power(n,k)
    def test_nonreduced(self):
        g=Grammar(); root=g.word([1,-1,2])
        with self.assertRaises(ValueError): optimize(g,[root])
    def test_noncyclic(self):
        g=Grammar(); root=g.word([1,2,-1])
        with self.assertRaises(ValueError): optimize(g,[root])
    def test_bad_repeat(self):
        g=Grammar(); root=g.power(g.word([1,2,-1]),2)
        with self.assertRaises(ValueError): optimize(g,[root])
    def test_roundtrip(self):
        g=Grammar(); r=g.power(g.word([1,2,-3]),8); h,rs=Grammar.from_dict(g.to_dict([r,r,0]))
        self.assertEqual(h.expand(rs[0]),g.expand(r)); self.assertEqual(rs[0],rs[1])
    def test_forward_reference(self):
        with self.assertRaises(ValueError): Grammar.from_dict({'version':1,'nodes':[['e'],['c',1,0]],'roots':[1]})
    def test_binary_power(self):
        g=Grammar(); r=g.power(g.word([1,2]),137); h,rs=g.binary([r]); self.assertEqual(h.expand(rs[0]),g.expand(r))
        self.assertFalse(any(q[0]=='p' for q in h.rules))
    def test_expansion_limit(self):
        g=Grammar(); r=g.run(1,2**500)
        with self.assertRaises(ValueError): g.expand(r)

class ProfileTests(unittest.TestCase):
    def test_exhaustive_short_profiles(self):
        for length in range(5):
            for w in itertools.product([1,-1,2,-2],repeat=length):
                if list(w)!=cyclic_reduce(w): continue
                g=Grammar(); root=g.word(w)
                for a in (1,-1,2,-2):
                    p=profile(g,[root,root,0],a); c,h=literal_histogram(list(w),a)
                    self.assertEqual((p.constant,p.gaps),(2*c,{k:2*v for k,v in h.items()}))
                    q=reference_profile(g,[root,root,0],a); self.assertEqual(p.gaps,q.gaps)
    def test_shared_huge(self):
        g=Grammar(); x=g.concat(g.letter(2),g.run(1,2**500)); r=g.power(x,2**300)
        p=profile(g,[r,r],1); self.assertEqual(p.gaps,{(2,-2,2**500):2**301})
        self.assertEqual(p.gaps,reference_profile(g,[r,r],1).gaps)
    def test_inverse_neighbor_unchanged(self):
        g=Grammar(); r=g.word([2,1,1,-2,3]); p=profile(g,[r],1)
        self.assertIn((2,2,2),p.gaps)
        out,roots=reduced_image(g,[r],p,{2:5,-2:-7,3:3,-3:9})
        self.assertIn((2,2,2),profile(out,roots,1).gaps)
    def test_pure_roots(self):
        g=Grammar(); roots=[g.run(1,-100),g.run(2,7),0]
        p=profile(g,roots,1); self.assertEqual(p.constant,107)
        self.assertEqual(p.value({2:0,-2:0}),107)
    def test_direct_images_random(self):
        rng=random.Random(702)
        for _ in range(500):
            w=cyclic_reduce([rng.choice([1,-1,2,-2,3,-3]) for _ in range(rng.randrange(1,25))])
            g=Grammar(); r=g.word(w); a=rng.choice([1,-1,2,-2,3,-3])
            z={v:rng.randint(-4,4) for v in [-3,-2,-1,1,2,3] if abs(v)!=abs(a)}
            p=profile(g,[r],a); h,rs=reduced_image(g,[r],p,z); got=h.expand(rs[0])
            self.assertEqual(canonical(got),canonical(literal_shear(w,a,z)))
            self.assertEqual(canonical(literal_shear(got,a,{v:-k for v,k in z.items()})),canonical(w))
    def test_signed_multiplier_symmetry(self):
        g=Grammar(); r=g.word([2,1,1,3,-1,2]); p=profile(g,[r],1); q=profile(g,[r],-1)
        z={2:2,-2:-3,3:1,-3:0}; self.assertEqual(p.value(z),q.value({v:-x for v,x in z.items()}))

class FlowTests(unittest.TestCase):
    def test_balanced_cycle(self):
        gaps={(0,1,3):5,(1,2,-1):2,(2,0,-2):7}; s=solve_tension(gaps)
        self.assertTrue(s.balanced); self.assertEqual(s.value,0)
    def test_unbalanced_cycle(self):
        gaps={(0,1,2):2,(1,2,3):3,(2,0,1):1}; s=solve_tension(gaps)
        self.assertEqual(s.value,6); self.assertTrue(verify_tension(gaps,s.potentials,s.dual,s.value))
    def test_self_loop(self):
        s=solve_tension({(1,1,-7):4}); self.assertEqual(s.value,28)
    def test_parallel_opposites(self):
        gaps={(0,1,5):3,(0,1,-2):4}; s=solve_tension(gaps); self.assertEqual(s.value,21)
    def test_zero_cost(self):
        s=solve_tension({(1,2,0):2**500},balanced_fast_path=False); self.assertEqual(s.value,0)
    def test_big_capacity(self):
        n=2**500; gaps={(0,1,2):2*n,(1,2,3):3*n,(2,0,1):n}; s=solve_tension(gaps)
        self.assertEqual(s.value,6*n); self.assertLessEqual(s.phases,502)
    def test_empty_network(self):
        s=min_cost_circulation(0,[]); self.assertEqual(s.flows,[])
    def test_invalid_cap(self):
        with self.assertRaises(ValueError): min_cost_circulation(2,[Arc(0,1,-1,1)])
    def test_cap_is_inconclusive(self):
        with self.assertRaises(WorkLimit): solve_tension({(0,1,2):3,(1,0,2):4},forest_fast_path=False,budget=Budget(0))
    def test_exhaustive_small_potentials(self):
        rng=random.Random(902)
        for _ in range(70):
            n=rng.randint(2,4); gaps={}
            # connected graph, hence one gauge is sufficient
            for v in range(1,n): gaps[(v-1,v,rng.randint(-2,2))]=rng.randint(1,5)
            for _ in range(4):
                k=(rng.randrange(n),rng.randrange(n),rng.randint(-2,2)); gaps[k]=gaps.get(k,0)+rng.randint(1,4)
            s=solve_tension(gaps,balanced_fast_path=False); radius=2*(n-1)
            best=min(sum(w*abs(e+z[u]-z[v]) for (u,v,e),w in gaps.items())
                     for tail in itertools.product(range(-radius,radius+1),repeat=n-1)
                     for z in [(0,)+tail])
            self.assertEqual(s.value,best)
    def test_dual_tampering(self):
        gaps={(0,1,2):2,(1,2,3):3,(2,0,1):1}; s=solve_tension(gaps)
        f=s.dual.copy(); f[(0,1,2)]+=1
        with self.assertRaises(ValueError): verify_tension(gaps,s.potentials,f,s.value)

class OptimizationTests(unittest.TestCase):
    def case(self):
        g=Grammar(); roots=[g.power(g.concat(g.letter(2),g.run(1,2**500)),2),g.power(g.word([3,1]),3)]
        return g,roots
    def test_huge_optimum(self):
        g,r=self.case(); o=optimize(g,r); self.assertEqual(o.certificate['optimal_length'],5)
        self.assertTrue(verify_optimization(g,r,o.certificate))
    def test_strict_direction_gap(self):
        g,r=self.case(); _,_,s=selected_line_step(g,r,[1,2,3]); self.assertEqual(s['gain'],5)
        o=optimize(g,r); self.assertGreater(o.certificate['initial_length']-5,2**500)
    def test_certificate_omitted_multiplier(self):
        g,r=self.case(); c=optimize(g,r).certificate; c['solutions'].pop()
        with self.assertRaises(ValueError): verify_optimization(g,r,c)
    def test_certificate_wrong_binding(self):
        g,r=self.case(); c=optimize(g,r).certificate; c['source_sha256']='0'*64
        with self.assertRaises(ValueError): verify_optimization(g,r,c)
    def test_certificate_boolean_potential(self):
        g,r=self.case(); c=optimize(g,r).certificate; c['solutions'][0]['potentials'][0][1]=True
        with self.assertRaises(ValueError): verify_optimization(g,r,c)
    def test_certificate_duplicate_potential(self):
        g,r=self.case(); c=optimize(g,r).certificate; c['solutions'][0]['potentials'].append(c['solutions'][0]['potentials'][0])
        with self.assertRaises(ValueError): verify_optimization(g,r,c)
    def test_replay_factorization(self):
        g=Grammar(); w=[2,1,1,3,-1,-2,1,3]; roots=[g.word(w)]; o=optimize(g,roots)
        value=w
        for move in replay_moves(o.certificate):
            a=move['multiplier']; t=move.get('exponent',1); z={v:t for v in move['subset'] if abs(v)!=abs(a)}
            value=literal_shear(value,a,z)
        self.assertEqual(canonical(value),canonical(o.grammar.expand(o.roots[0])))
    def test_fixed_power_cut(self):
        rng=random.Random(553)
        for _ in range(80):
            w=cyclic_reduce([rng.choice([1,-1,2,-2,3,-3]) for _ in range(15)])
            g=Grammar(); r=g.word(w); p=profile(g,[r],1); t=rng.randrange(1,5)
            vertices=sorted({v for u,v,e in p.gaps}|{u for u,v,e in p.gaps})
            value,_=fixed_power(p,t)
            self.assertEqual(value,min(p.value(dict(zip(vertices,(t*x for x in mask))))
                                       for mask in itertools.product([0,1],repeat=len(vertices))))
    def test_all_rank_random_witnesses(self):
        rng=random.Random(713)
        for _ in range(120):
            g=Grammar(); roots=[g.word(cyclic_reduce([rng.choice([1,-1,2,-2,3,-3,4,-4])
                              for _ in range(rng.randrange(1,30))])) for _ in range(3)]
            o=optimize(g,roots); self.assertTrue(verify_optimization(g,roots,o.certificate))
            self.assertLessEqual(o.certificate['optimal_length'],o.certificate['initial_length'])
    def test_braid_inverse(self):
        for s in range(2,6):
            for i in range(1,s): self.assertEqual(artin_presentation(s,[i,-i])[0],[[] for _ in range(s)])
    def test_braid_relation(self):
        a,_=artin_presentation(3,[1,2,1]); b,_=artin_presentation(3,[2,1,2])
        self.assertEqual([canonical(w) for w in a],[canonical(w) for w in b])


class PresentationTests(unittest.TestCase):
    def test_terminal_free_products(self):
        from shear_kernel.presentation import pure_power_terminal
        g=Grammar(); roots=[g.run(2,12),g.run(2,13)]
        self.assertTrue(pure_power_terminal(g,roots,[1,2])['is_infinite_cyclic'])
        self.assertFalse(pure_power_terminal(g,[g.run(2,12)],[1,2])['is_infinite_cyclic'])
        self.assertFalse(pure_power_terminal(g,[],[1,2])['is_infinite_cyclic'])
    def test_large_z_presentation(self):
        from shear_kernel.presentation import reduce_presentation,verify_presentation_reduction
        g=Grammar(); roots=[]
        for j in range(2,8):
            u=g.concat(g.letter(j),g.run(1,2**500+j))
            roots.extend([g.power(u,2**200+j),g.power(u,2**200+j+1)])
        _,_,record=reduce_presentation(g,roots,list(range(1,8)))
        self.assertEqual(len(record['steps']),1)
        self.assertTrue(record['terminal']['is_infinite_cyclic'])
        self.assertTrue(verify_presentation_reduction(g,roots,list(range(1,8)),record))
    def test_phase_cap(self):
        from shear_kernel.presentation import reduce_presentation
        g=Grammar(); r=g.word([1,2]); _,_,rec=reduce_presentation(g,[r],[1,2],max_phases=0)
        self.assertEqual(rec['status'],'inconclusive_phase_cap')
    def test_linear_rule_growth(self):
        rng=random.Random(222)
        for _ in range(50):
            g=Grammar(); roots=[]
            for j in range(4):
                w=cyclic_reduce([rng.choice([1,-1,2,-2,3,-3]) for _ in range(10)])
                roots.append(g.power(g.word(w),rng.randint(1,100)))
            before=len(g.reachable(roots))+len(roots)+3+2; o=optimize(g,roots,[1,2,3])
            after=len(o.grammar.reachable(o.roots))+len(roots)+3+2
            self.assertLessEqual(after,8*before)
    def test_adapter_fixture(self):
        from shear_kernel.adapter import prepare_step,install_prepared
        class Arena:
            def __init__(self): self.g=Grammar(); self.sync()
            def sync(self):
                self.rules=self.g.rules; self.lengths=[m.length for m in self.g.meta]
            def _reachable(self,rs): return self.g.reachable(rs)
            def tick(self,*args): pass
            def letter(self,x): n=self.g.letter(x); self.sync(); return n
            def concat(self,a,b): n=self.g.concat(a,b); self.sync(); return n
            def power(self,a,k):
                ans=0
                while k:
                    if k&1: ans=self.concat(ans,a)
                    k>>=1
                    if k: a=self.concat(a,a)
                return ans
        arena=Arena(); x=arena.concat(arena.letter(2),arena.power(arena.letter(1),100))
        roots=[arena.power(x,2),arena.power(x,3)]
        original_roots=roots[:]
        result,moves=prepare_step(arena,roots,{1,2}); new=install_prepared(arena,result)
        self.assertEqual(sum(arena.lengths[n] for n in new),5)
        self.assertEqual(roots,original_roots)

class ForestTests(unittest.TestCase):
    def test_parallel_offsets(self):
        gaps={(1,2,5):3,(1,2,8):7,(2,1,-8):2,(1,1,-20):6}
        a=solve_tension(gaps); b=solve_tension(gaps,balanced_fast_path=False,forest_fast_path=False)
        self.assertEqual(a.method,'forest'); self.assertEqual(a.value,b.value)
        self.assertTrue(verify_tension(gaps,a.potentials,a.dual,a.value))
    def test_random_forests(self):
        rng=random.Random(3885)
        for trial in range(120):
            gaps={}; n=rng.randrange(2,14)
            for v in range(1,n):
                u=rng.randrange(v)
                for _ in range(rng.randrange(1,8)):
                    e=rng.randrange(-100,101); p,q=(u,v) if rng.randrange(2) else (v,u)
                    gaps[(p,q,e)]=rng.randrange(1,2**30)
            a=solve_tension(gaps); b=solve_tension(gaps,balanced_fast_path=False,forest_fast_path=False)
            self.assertEqual(a.value,b.value)
    def test_cycle_fallback(self):
        s=solve_tension({(1,2,1):2,(2,3,1):2,(3,1,1):2})
        self.assertEqual(s.method,'flow'); self.assertEqual(s.value,6)
    def test_huge_rank_two(self):
        n=2**500
        s=solve_tension({(1,2,n):2**600,(1,2,n+1):2**600+1})
        self.assertEqual(s.method,'forest'); self.assertEqual(s.value,2**600)
    def test_boolean_objective_rejected(self):
        g=Grammar(); roots=[g.word([1,2])]; c=optimize(g,roots).certificate
        c['optimal_length']=True
        with self.assertRaises(ValueError): verify_optimization(g,roots,c)



class IndependentReplayTests(unittest.TestCase):
    def test_decorated_replay(self):
        from shear_kernel.replay import reference_image
        rng=random.Random(977)
        for _ in range(180):
            g=Grammar(); roots=[]
            for j in range(3):
                w=cyclic_reduce([rng.choice([1,-1,2,-2,3,-3]) for _ in range(18)])
                roots.append(g.power(g.word(w),rng.randrange(1,8)))
            a=rng.choice([1,-1,2,-2,3,-3]); z={x:rng.randrange(-5,6) for x in [1,-1,2,-2,3,-3] if abs(x)!=abs(a)}
            p=profile(g,roots,a); first,r1=reduced_image(g,roots,p,z); second,r2=reference_image(g,roots,a,z)
            for u,v in zip(r1,r2): self.assertEqual(first.expand(u),second.expand(v))
    def test_multiphase_replay(self):
        from shear_kernel.presentation import reduce_presentation,verify_presentation_reduction
        rng=random.Random(6108); found=0
        for _ in range(100):
            g=Grammar(); roots=[g.word(cyclic_reduce([rng.choice([1,-1,2,-2,3,-3]) for _ in range(12)]))]
            _,_,record=reduce_presentation(g,roots,[1,2,3],max_phases=3)
            self.assertTrue(verify_presentation_reduction(g,roots,[1,2,3],record))
            found+=len(record['steps'])>=2
        self.assertGreater(found,0)
    def test_automorphic_plateau(self):
        from shear_kernel.presentation import reduce_presentation
        g=Grammar(); n=2**500; roots=[g.run(1,n),g.run(1,n+1),g.word([1,2,-1,-2])]
        o=optimize(g,roots,[1,2]); self.assertEqual(o.certificate['optimal_length'],2*n+5)
        _,_,record=reduce_presentation(g,roots,[1,2]); self.assertEqual(record['status'],'inconclusive_stall')

if __name__=='__main__': unittest.main()
