import itertools
import random
import unittest
from fractions import Fraction
from math import gcd
from su2budget.slp import Arena,Presentation,from_words,export_word_arena,LimitExceeded
from su2budget import dihedral as D
from su2budget import univariate as U
from su2budget.quaternion import multiply as qm, conjugate, noncommutativity
from su2budget.fixtures import trefoil,cyclic_meridians,torus_nonmeridional,huge_braid_relation,braid_closure,braid_wirtinger
from su2budget.degrees import profile,greedy_cap,best_small_dag,optimal_tree_cap,flatten_tree
from su2budget.multivariate import compile_formula
from su2budget.wirtinger import minimum_degrees,verify_profile,compile_seeds,find_small_seeds


def qpower(q,k):
    if k<0:q,k=conjugate(q),-k
    out=(1,0,0,0)
    while k:
        if k&1:out=qm(out,q)
        k>>=1
        if k:q=qm(q,q)
    return out


class SLPTests(unittest.TestCase):
    def test_validation(self):
        for rank,rules,pairs in [(0,(None,),()),(1,(None,('t',2)),()),
                                 (1,(None,('c',1,0)),()),(1,(None,),((1,0),))]:
            with self.assertRaises(ValueError):Presentation(rank,rules,pairs)

    def test_export_live_only(self):
        arena=Arena(); a=arena.letter(7);b=arena.letter(11)
        root=arena.concat(a,arena.inverse(b));arena.power(arena.letter(99),1000)
        p=export_word_arena(arena,[root],[7,11],meridians=True)
        self.assertEqual(len(p.rules)-1,len(p.live()))
        self.assertLess(len(p.rules),len(arena.rules))
        self.assertEqual(D.solve(p)['status'],'NONE')
        with self.assertRaises(ValueError):export_word_arena(arena,[root],[7])

    def test_inverse_and_identity(self):
        a=Arena(); root=a.word([1,2,-1,2]);inv=a.inverse(root)
        p=a.presentation(2,[(a.concat(root,inv),0)],meridians=True)
        self.assertEqual(D.normal_forms(p)[0],((0,0,0),))

    def test_roundtrip(self):
        p=trefoil();q=Presentation.from_dict(p.to_dict())
        self.assertEqual(p,q);self.assertEqual(p.digest(),q.digest())
        data=p.to_dict();data['meridian_generators']='false'
        with self.assertRaises(ValueError):Presentation.from_dict(data)


class DihedralTests(unittest.TestCase):
    def test_associativity_exhaustive(self):
        values=list(itertools.product(range(2),range(-2,3),range(2)))
        for a,b,c in itertools.product(values,repeat=3):
            self.assertEqual(D.multiply(D.multiply(a,b),c),D.multiply(a,D.multiply(b,c)))

    def test_inverse(self):
        for x in itertools.product(range(2),range(-25,26),range(2)):
            self.assertEqual(D.multiply(x,D.inverse(x)),D.IDENTITY)
            self.assertEqual(D.multiply(D.inverse(x),x),D.IDENTITY)

    def test_rational_quaternion_word_evaluation(self):
        rng=random.Random(732)
        for _ in range(160):
            word=[rng.choice((-2,-1,1,2)) for _ in range(rng.randrange(31))]
            form=D.IDENTITY
            for x in word:form=D.multiply(form,D.LETTERS[x])
            for t in (Fraction(1,2),Fraction(1),Fraction(2),Fraction(3)):
                A=(0,1,0,0);B=(0,(1-t*t)/(1+t*t),2*t/(1+t*t),0)
                out=(1,0,0,0)
                for x in word:
                    q=A if abs(x)==1 else B
                    out=qm(out,conjugate(q) if x<0 else q)
                e,k,s=form
                canonical=qpower(qm(A,B),k)
                if s:canonical=qm(canonical,A)
                if e:canonical=tuple(-x for x in canonical)
                self.assertEqual(out,canonical)

    def test_small_known_knots(self):
        self.assertEqual(D.solve(trefoil())['gcd'],3)
        self.assertEqual(D.solve(trefoil())['phase'],[1,3])
        self.assertEqual(D.solve(cyclic_meridians())['status'],'NONE')
        for exponent in range(-15,16,2):
            p,components=braid_closure(2,[1 if exponent>0 else -1]*abs(exponent))
            self.assertEqual(components,1)
            self.assertEqual(D.solve(p)['status'],'NONE' if abs(exponent)==1 else 'EXISTS')

    def test_all_obstruction_types(self):
        cases=[([(0,1,1)],'odd A parity'), ([(1,0,0)],'central minus identity'),
               ([(0,2,0),(1,4,0)],'incompatible central parity'),
               ([(0,2,0)],'only commuting endpoint phases')]
        for forms,reason in cases:self.assertEqual(D.analyze(forms)['obstruction'],reason)
        self.assertEqual(D.analyze([])['count'],'continuum')
        self.assertEqual(D.analyze([(1,2,0)])['phase'],[1,2])

    def test_huge_compression(self):
        p=huge_braid_relation(1000);a=D.solve(p)
        self.assertEqual(a['gcd'],2**1001+1)
        self.assertEqual(a['count'],2**1000)
        self.assertLess(a['live_nodes'],1020)
        self.assertTrue(D.verify(p,a))

    def test_caps_and_tampering(self):
        p=huge_braid_relation(100)
        self.assertEqual(D.solve(p,max_exponent_bits=10)['status'],'UNKNOWN')
        self.assertEqual(D.solve(p,max_nodes=1)['status'],'UNKNOWN')
        cert=D.solve(p);cert['gcd']+=1
        self.assertFalse(D.verify(p,cert))
        with self.assertRaises(ValueError):D.solve(torus_nonmeridional())

    def test_independent_univariate_comparison(self):
        rng=random.Random(885)
        for _ in range(300):
            pairs=[]
            for j in range(rng.randrange(1,4)):
                pairs.append(([rng.choice((-2,-1,1,2)) for k in range(rng.randrange(10))],
                              [rng.choice((-2,-1,1,2)) for k in range(rng.randrange(10))]))
            p=from_words(2,pairs,meridians=True,label='synthetic group, not claimed knot')
            d,u=D.solve(p),U.solve(p)
            self.assertEqual(d['status'],u['status'])
            if 'count' in d:
                self.assertEqual(None if d['count']=='continuum' else d['count'],u['roots']['count'])


class UnivariateTests(unittest.TestCase):
    def test_sturm_endpoints_and_multiplicities(self):
        self.assertEqual(U.positive_roots((0,))['count'],None)
        self.assertEqual(U.positive_roots((1,))['count'],0)
        # t^2*(t-1)^2*(t+2)^3: only one distinct positive root.
        f=U.mul((0,0,1),U.mul(U.power((-1,1),2),U.power((2,1),3)))
        self.assertEqual(U.positive_roots(f)['count'],1)
        self.assertEqual(U.positive_roots((1,0,1))['count'],0)
        self.assertEqual(U.positive_roots((-2,0,1))['count'],1)

    def test_known_gcd(self):
        result=U.solve(trefoil())
        self.assertEqual(result['gcd'],[0,-3,0,1])
        self.assertEqual(result['roots']['count'],1)
        self.assertTrue(U.verify(trefoil(),result))
        result['residuals'][0]=[1]
        self.assertFalse(U.verify(trefoil(),result))

    def test_unknown_and_rejected_provenance(self):
        self.assertEqual(U.solve(huge_braid_relation(100),budget=U.Budget(max_degree=100))['status'],'UNKNOWN')
        self.assertEqual(U.solve(trefoil(),budget=U.Budget(max_pairs=0))['status'],'UNKNOWN')
        with self.assertRaises(ValueError):U.solve(torus_nonmeridional())

    def test_polynomial_arithmetic(self):
        rng=random.Random(7)
        for _ in range(100):
            a=U.trim([rng.randint(-5,5) for _ in range(rng.randrange(1,8))])
            b=U.trim([rng.randint(-5,5) for _ in range(rng.randrange(1,6))]) or (1,)
            q,r=U.divrem(a,b)
            self.assertEqual(U.add(U.mul(q,b),r),a)
            self.assertLess(len(r),len(b))


class CheckpointTests(unittest.TestCase):
    def test_profile_includes_definition_degree(self):
        a=Arena();x=a.letter(1);y=a.concat(x,x);z=a.concat(y,y)
        p=a.presentation(1,[(z,0)])
        self.assertEqual(profile(p,[z]).delta,4)  # resetting does not erase its equation
        self.assertEqual(profile(p,[y,z]).delta,2)

    def test_dead_nodes(self):
        a=Arena();x=a.letter(1);p=a.power(x,2**100);r=a.word([1,1])
        obj=a.presentation(1,[(r,0)])
        self.assertEqual(profile(obj).delta,2)

    def test_greedy_caps(self):
        for bits in range(12):
            p=huge_braid_relation(bits)
            for cap in range(2,20):self.assertLessEqual(greedy_cap(p,cap).delta,cap)

    def test_small_dag_optimizer(self):
        p=trefoil();result=best_small_dag(p)
        self.assertLessEqual(result.kappa,profile(p).kappa)
        self.assertLessEqual(result.kappa,profile(p,p.products()).kappa)

    def test_tree_dp_against_exhaustion(self):
        def trees(n):
            if n==1:return [1]
            return [(a,b) for k in range(1,n) for a in trees(k) for b in trees(n-k)]
        for n in range(1,7):
            for tree in trees(n):
                nodes=flatten_tree(tree);internal=[i for i,c in enumerate(nodes) if c is not None]
                for cap in range(2,7):
                    best=10**6
                    for mask in range(1<<len(internal)):
                        cuts={v for j,v in enumerate(internal) if (mask>>j)&1}
                        degrees={};valid=True
                        for v in reversed(range(len(nodes))):
                            c=nodes[v]
                            d=1 if c is None else degrees[c[0]]+degrees[c[1]]
                            if v in cuts and d>cap:valid=False;break
                            degrees[v]=1 if v in cuts else d
                        if valid and degrees[0]<=cap:best=min(best,len(cuts))
                    self.assertEqual(optimal_tree_cap(tree,cap)['cost'],best)


class FormulaTests(unittest.TestCase):
    def test_wrong_commutativity_shortcut(self):
        A=(0,1,0,0);B=(-1,0,0,0)
        self.assertNotEqual(A,B);self.assertEqual(noncommutativity([A,B]),0)
        p=from_words(2,[([2],[1,1])],label='cyclic b=a^2')
        f=compile_formula(p)
        point=A+B
        self.assertTrue(all(x.evaluate(point)==0 for x in f.residuals))
        self.assertEqual(f.obstruction.evaluate(point),0)

    def test_checkpointed_evaluation(self):
        rng=random.Random(171)
        Q=[tuple(s if j==k else 0 for j in range(4)) for k in range(4) for s in (-1,1)]
        for _ in range(35):
            pairs=[([rng.choice((-2,-1,1,2)) for _ in range(rng.randrange(1,7))],[])]
            p=from_words(2,pairs)
            cuts=[v for v in p.products() if rng.randrange(2)]
            f=compile_formula(p,cuts)
            images=[rng.choice(Q),rng.choice(Q)]
            values={0:(1,0,0,0)}
            for v in p.live():
                r=p.rules[v]
                if r[0]=='t':
                    q=images[abs(r[1])-1]
                    values[v]=conjugate(q) if r[1]<0 else q
                else:values[v]=qm(values[r[1]],values[r[2]])
            point=sum(images,())+sum((values[v] for v in sorted(cuts)),())
            # Norm and checkpoint equations vanish by construction.
            self.assertTrue(all(x.evaluate(point)==0 for x in f.residuals[:2+4*len(cuts)]))
            self.assertEqual(f.obstruction.evaluate(point),noncommutativity(images))
            h=f.aggregate()
            self.assertEqual(h.evaluate(point),sum(x.evaluate(point)**2 for x in f.residuals))
            self.assertLessEqual(h.degree(),2*f.delta)

    def test_caps_and_meridian_precondition(self):
        with self.assertRaises(LimitExceeded):compile_formula(trefoil(),max_degree=2)
        with self.assertRaises(LimitExceeded):compile_formula(trefoil(),max_pairs=1)
        with self.assertRaises(LimitExceeded):compile_formula(trefoil(),max_variables=1)
        with self.assertRaises(ValueError):compile_formula(torus_nonmeridional(),traceless=True)

    def test_wolfram_export(self):
        s=compile_formula(trefoil()).wolfram()
        self.assertIn('Resolve[Exists[',s);self.assertIn('Reals',s);self.assertIn('>0',s)


class WirtingerTests(unittest.TestCase):
    def test_generalized_dijkstra_against_relaxation(self):
        rng=random.Random(220)
        for _ in range(400):
            n=rng.randrange(2,13)
            crossings=[tuple(rng.randrange(n) for _ in range(3))+(rng.choice((-1,1)),)
                       for _ in range(rng.randrange(1,25))]
            seeds=rng.sample(range(n),rng.randrange(1,min(n,4)+1))
            out=minimum_degrees(n,crossings,seeds)
            inf=float('inf');d=[1 if v in seeds else inf for v in range(n)]
            for iteration in range(n+1):
                changed=False
                for o,u,v,_ in crossings:
                    for a,b in ((u,v),(v,u)):
                        trial=d[a]+2*d[o]
                        if trial<d[b]:d[b]=trial;changed=True
                if not changed:break
            self.assertEqual(out['degrees'],[None if x==inf else x for x in d])
            self.assertTrue(verify_profile(n,crossings,out))

    def test_tampered_certificate(self):
        n,c,co=braid_wirtinger(3,[1,-2,1,-2])
        cert=minimum_degrees(n,c,[0,1]);cert['degrees'][2]+=1
        self.assertFalse(verify_profile(n,c,cert))
        cert=minimum_degrees(n,c,[0,1]);cert['seeds'].append(0)
        self.assertFalse(verify_profile(n,c,cert))
        with self.assertRaises(ValueError):compile_seeds(n,c,cert)

    def test_real_braid_fixture_two_seed_closure(self):
        n,c,components=braid_wirtinger(3,[1,-2,1,-2])
        self.assertEqual(components,1)
        cert=minimum_degrees(n,c,[0,1]);p=compile_seeds(n,c,cert)
        self.assertEqual(D.solve(p)['gcd'],5)
        self.assertEqual(U.solve(p)['roots']['count'],2)
        self.assertEqual(len(p.relations),len(c))

    def test_small_seed_search(self):
        n,c,components=braid_wirtinger(3,[1,-2,1,-2])
        found=find_small_seeds(n,c)
        self.assertEqual(found['status'],'FOUND');self.assertEqual(found['rank'],2)
        self.assertTrue(verify_profile(n,c,found['certificate']))
        self.assertEqual(find_small_seeds(n,c,max_attempts=0)['status'],'UNKNOWN')
        self.assertEqual(find_small_seeds(n,c,max_rank=1)['status'],'NOT_FOUND')

    def test_all_overpass_bound(self):
        rng=random.Random(31)
        for _ in range(160):
            strands=rng.randrange(2,6)
            word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(5,25))]
            n,c,components=braid_wirtinger(strands,word)
            if components!=1:continue
            seeds={o for o,_,_,_ in c}
            cert=minimum_degrees(n,c,seeds)
            self.assertNotIn(None,cert['degrees'])
            self.assertLessEqual(max(cert['degrees']),2*len(c)+1)
            p=compile_seeds(n,c,cert)
            self.assertEqual(p.rank,len(seeds))

if __name__=='__main__':unittest.main()
