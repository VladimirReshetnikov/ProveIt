import itertools, math, unittest
from abstract_models import BooleanSystem, Rule, brute_endpoints
from layered_search import Action, Stats, SearchExhausted, layered_traces, find_layered, normal_form, ancestor_cone
from dart_kernel import *
from connected_kernel import connected_sets, kernel_unlock
from verify_certificate import serialize, verify

class AlgebraTests(unittest.TestCase):
    def test_independent_trace_count(self):
        for m in range(1,6):
            sys=BooleanSystem([Rule(1<<i,0,0) for i in range(m)])
            for k in range(1,6):
                count=sum(1 for _ in layered_traces(sys,0,k))
                self.assertEqual(count,math.comb(k+m,m)-1)
    def test_support_padding_inverse(self):
        # Exact counterexample recorded in synthesis/causal_r3.tex.
        rules=[Rule(3,12,0),Rule(4,1,0),Rule(8,2,0)]
        sys=BooleanSystem(rules,lambda x:x&12==12)
        out=find_layered(sys,0,4,max_roots=1)
        self.assertIsNotNone(out); self.assertEqual(out.length,4)
        self.assertEqual(out.layers[0][0].key,(0,))
        self.assertEqual(out.layers[1][0].key,(0,))
    def test_foata_fork_and_join(self):
        a=Action((0,),frozenset((0,1))); b=Action((1,),frozenset((0,2)))
        c=Action((2,),frozenset((1,3))); d=Action((3,),frozenset((2,3)))
        self.assertEqual([len(x) for x in normal_form([a,b,c,d])],[1,2,1])
    def test_reject_invalid_parameters(self):
        sys=BooleanSystem([Rule(1,0,0)])
        for k in [-1,True,1.5]:
            with self.assertRaises(ValueError): list(layered_traces(sys,0,k))
    def test_caps(self):
        sys=BooleanSystem([Rule(1,0,0)])
        with self.assertRaises(SearchExhausted): list(layered_traces(sys,0,2,max_trials=0))
    def test_callback_exception(self):
        def stop(): raise RuntimeError("stop")
        with self.assertRaises(RuntimeError): list(layered_traces(BooleanSystem([]),0,1,check=stop))
    def test_cone(self):
        aa=[Action((0,),frozenset((0,))),Action((1,),frozenset((4,))),
            Action((2,),frozenset((0,2)))]
        kept,s=ancestor_cone(aa,frozenset((2,3)))
        self.assertEqual([a.key for a in kept],[(0,),(2,)])
        self.assertEqual(s,frozenset((0,2,3)))
    def test_all_small_boolean_models(self):
        for rules in itertools.combinations([Rule(1,0,0),Rule(2,1,0),Rule(2,1,1),
                                             Rule(4,2,0),Rule(4,2,2)],3):
            sys=BooleanSystem(rules)
            for x in range(8):
                for b in (1,2,3):
                    expected,_=brute_endpoints(sys,x,4,b)
                    got={x}|{y for y,_ in layered_traces(sys,x,4,max_roots=b)}
                    self.assertEqual(got,expected)

class GraphTests(unittest.TestCase):
    def test_connected_sets_unique_complete(self):
        for n in range(1,5):
            edges=list(itertools.combinations(range(n),2))
            for mask in range(1<<len(edges)):
                adj=[set() for _ in range(n)]
                for i,(u,v) in enumerate(edges):
                    if mask>>i&1: adj[u].add(v); adj[v].add(u)
                expected=set()
                for m in range(1,1<<n):
                    S=frozenset(i for i in range(n) if m>>i&1)
                    seen={min(S)}; todo=list(seen)
                    while todo:
                        u=todo.pop()
                        for v in adj[u]&S-seen: seen.add(v); todo.append(v)
                    if seen==S: expected.add(S)
                out=list(connected_sets(adj,n))
                self.assertEqual(len(out),len(set(out)))
                self.assertEqual(set(out),expected)

class KnotTests(unittest.TestCase):
    def test_braid_validation(self):
        for s,w in [(2,[1]*3),(3,[1,2]*4),(4,[1,2,3])]: from_braid(s,w).validate()
        with self.assertRaises(ValueError): from_braid(2,[1,1])
    def test_reduction(self):
        self.assertEqual(reduce_12(from_braid(4,[1,2,3]))[0].n,0)
    def test_face_identity(self):
        s=from_pd(((5,4,0,1),(1,0,2,3),(2,4,5,3)))
        legal=list(R3System().actions(s))
        self.assertEqual(len(legal),2)
        self.assertNotEqual(R3System().apply(s,legal[0]),R3System().apply(s,legal[1]))
    def test_inverse_and_support(self):
        for w in ([1,2]*4,[1,1,-1,-2,2,1,2,-1]):
            try: s=from_braid(3,w)
            except ValueError: continue
            for a in R3System().actions(s):
                t=R3System().apply(s,a); t.validate()
                self.assertLessEqual(len(a.footprint),18)
                self.assertEqual({s.alpha[d] for d in a.footprint},set(a.footprint))
                self.assertEqual({t.alpha[d] for d in a.footprint},set(a.footprint))
                inv=tuple(sorted(d^2 for d in a.payload))
                found=next(b for b in R3System().actions(t) if b.key==inv)
                self.assertEqual(R3System().apply(t,found),s)
    def test_certificate_zero(self):
        s=from_braid(3,[1,2]); out=find_layered(R3System(),s,0)
        self.assertTrue(verify(serialize(s,out,0))["verified"])
    def test_certificate_tamper(self):
        s=from_braid(3,[1,2]); out=find_layered(R3System(),s,0); data=serialize(s,out,0)
        data["terminal"]["face"]=[True]
        with self.assertRaises(ValueError): verify(data)
    def test_kernel_failure_does_not_mutate(self):
        s=from_braid(3,[1,2]*4); before=s.alpha
        out,_=kernel_unlock(s,2)
        self.assertIsNone(out); self.assertEqual(before,s.alpha)
    def test_core_region_and_support_modes(self):
        s=from_braid(3,[1,2]*4)
        for k in (0,1,2):
            a,_=kernel_unlock(s,k,region_mode="core")
            b,_=kernel_unlock(s,k,region_mode="support")
            self.assertEqual(a is None,b is None)
        import json
        from pathlib import Path
        data=json.loads((Path(__file__).parents[1]/"artifacts/witness_00.json").read_text())
        positive=from_pd(data["pd"])
        witness,_=kernel_unlock(positive,1)
        self.assertIsNotNone(witness)
        self.assertTrue(verify(serialize(positive,witness,1))["verified"])
    def test_initial_core_star(self):
        s=from_braid(3,[1,2]*10);sys=R3System();G=projection_graph(s)
        for a in sys.actions(s):
            C={d//4 for d in a.key}|{0,5};out=sys.apply(s,a);H=projection_graph(out)
            initial=footprint(s,tuple(4*c for c in C))
            final=footprint(out,tuple(4*c for c in C))
            self.assertEqual(initial,final)
            def parts(adj):
                left=set(C);result=[]
                while left:
                    seen={min(left)};todo=list(seen)
                    while todo:
                        u=todo.pop()
                        for v in (adj[u]&C)-seen:seen.add(v);todo.append(v)
                    result.append(frozenset(seen));left-=seen
                return set(result)
            self.assertEqual(parts(G),parts(H))
    def test_projection_degree(self):
        s=from_braid(3,[1,2]*7)
        self.assertLessEqual(max(map(len,projection_graph(s))),4)
    def test_independent_diagram_actions_commute(self):
        sys=R3System(); s=from_braid(3,[1,2]*10); tested=0
        for a,b in itertools.combinations(list(sys.actions(s)),2):
            if a.footprint.isdisjoint(b.footprint):
                self.assertEqual(sys.apply(sys.apply(s,a),b),sys.apply(sys.apply(s,b),a)); tested+=1
        self.assertGreater(tested,0)

class AdapterTests(unittest.TestCase):
    def make_state(self):
        from types import SimpleNamespace
        s=from_braid(3,[1,2])
        return s,SimpleNamespace(alpha=list(s.alpha),alive=[True]*s.n)
    def test_batch_equals_sequential(self):
        s=from_braid(3,[1,2]*10);sys=R3System()
        for a,b in itertools.combinations(list(sys.actions(s)),2):
            if a.footprint.isdisjoint(b.footprint):
                self.assertEqual(sys.apply_layer(s,(a,b)),sys.apply(sys.apply(s,a),b))
    def test_commit(self):
        from production_adapter import snapshot,commit_verified
        s,mutable=self.make_state(); snap=snapshot(mutable); path=[]
        w=find_layered(R3System(),s,0)
        face=commit_verified(mutable,snap,w,path)
        self.assertEqual(face,w.terminal[1]);self.assertEqual(mutable.alpha,list(s.alpha))
    def test_commit_rollback(self):
        from production_adapter import snapshot,commit_verified
        s,mutable=self.make_state();snap=snapshot(mutable);path=[];w=find_layered(R3System(),s,0)
        calls=[0]
        def fail():
            calls[0]+=1
            if calls[0]==4: raise RuntimeError("injected cancellation")
        with self.assertRaises(RuntimeError):commit_verified(mutable,snap,w,path,check=fail)
        self.assertEqual(mutable.alpha,list(s.alpha));self.assertEqual(path,[])
    def nontrivial_fixture(self):
        import json
        from pathlib import Path
        data=json.loads((Path(__file__).parents[1]/"artifacts/witness_00.json").read_text())
        s=from_pd(data["pd"]);sys=R3System();cur=s;layers=[]
        for keys in data["layers"]:
            legal={a.key:a for a in sys.actions(cur)}
            layer=tuple(legal[tuple(key)] for key in keys)
            layers.append(layer);cur=sys.apply_layer(cur,layer)
        from layered_search import Witness
        return s,Witness(tuple(layers),(data["terminal"]["kind"],tuple(data["terminal"]["face"])),cur)
    def test_nontrivial_commit_deleted_labels(self):
        from types import SimpleNamespace
        from production_adapter import snapshot,commit_verified
        s,w=self.nontrivial_fixture()
        mapping=tuple(4*(2*c+1)+j for c in range(s.n) for j in range(4))
        alpha=list(range(8*s.n));alive=[False,True]*s.n
        for d,x in enumerate(mapping):alpha[x]=mapping[s.alpha[d]]
        state=SimpleNamespace(alpha=alpha,alive=alive);snap=snapshot(state);path=[]
        face=commit_verified(state,snap,w,path)
        self.assertEqual(snapshot(state).diagram,w.final_state)
        self.assertEqual(len(path),w.length)
        self.assertEqual(face,tuple(mapping[d] for d in w.terminal[1]))
    def test_commit_ignores_untrusted_payload(self):
        from types import SimpleNamespace
        from dataclasses import replace
        from production_adapter import snapshot,commit_verified
        s,w=self.nontrivial_fixture()
        forged=replace(w,layers=tuple(tuple(replace(a,payload=(999999,)) for a in L) for L in w.layers))
        state=SimpleNamespace(alpha=list(s.alpha),alive=[True]*s.n);path=[]
        commit_verified(state,snapshot(state),forged,path)
        self.assertTrue(all(len(face)==3 and max(face)<4*s.n for face in path))
    def test_commit_rejects_forged_final_state(self):
        from types import SimpleNamespace
        from dataclasses import replace
        from production_adapter import snapshot,commit_verified
        s,w=self.nontrivial_fixture();state=SimpleNamespace(alpha=list(s.alpha),alive=[True]*s.n)
        with self.assertRaises(ValueError):commit_verified(state,snapshot(state),replace(w,final_state=s),[])
        self.assertEqual(state.alpha,list(s.alpha))
    def test_stale_snapshot(self):
        from production_adapter import snapshot,commit_verified
        s,mutable=self.make_state();snap=snapshot(mutable);w=find_layered(R3System(),s,0)
        mutable.alpha[0]=0
        with self.assertRaises(ValueError):commit_verified(mutable,snap,w,[])

if __name__=="__main__": unittest.main()
