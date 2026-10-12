"""Reproducible finite checks. No native ProveIt/Regina execution is implied."""
from __future__ import annotations
import copy, itertools, json, platform, random, sys, time, unittest
from collections import Counter
from fractions import Fraction
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'code'))
from cographic import (Graph, InvalidInput, decode_side_census, side_histogram,
                       maximum_batch, components_after_cut, tree_return,
                       finite_routing_forest)
from verify import verify_batch, verify_routing, verify_trace, verify_reuse
from reuse import plan_reuse
from causal import (PersistentCounters, path_bounds, path_sum_reference,
                    dependency_height, Range, supports_overlap, invalidate, amplification, causal_potential)
COUNTS = Counter()


def components(n, edges, removed=()):
    removed = set(removed)
    adj = [set() for _ in range(n)]
    for i,(u,v) in enumerate(edges):
        if i not in removed:
            adj[u].add(v); adj[v].add(u)
    seen=set(); count=0
    for v in range(n):
        if v in seen: continue
        count+=1; todo=[v]; seen.add(v)
        while todo:
            for y in adj[todo.pop()]:
                if y not in seen: seen.add(y); todo.append(y)
    return count


def subsets(m):
    for mask in range(1 << m):
        yield tuple(i for i in range(m) if mask>>i&1)


def brute_reward(n, edges, weights):
    return max(sum(weights[i] for i in s) for s in subsets(len(edges))
               if components(n,edges,s)==1)


def rank2(rows):
    piv={}
    for row in rows:
        while row:
            p=row.bit_length()-1
            if p in piv: row ^= piv[p]
            else: piv[p]=row; break
    return len(piv)


def rankq(rows):
    a=[list(map(Fraction,row)) for row in rows]
    if not a: return 0
    r=0
    for col in range(len(a[0])):
        pivot=next((j for j in range(r,len(a)) if a[j][col]),None)
        if pivot is None: continue
        a[r],a[pivot]=a[pivot],a[r]; q=a[r][col]
        a[r]=[x/q for x in a[r]]
        for j in range(r+1,len(a)):
            q=a[j][col]
            if q: a[j]=[x-q*y for x,y in zip(a[j],a[r])]
        r+=1
    return r


def partitions(n):
    """Set partitions as disjoint nonempty integer bit masks."""
    if n==0: yield (); return
    def rec(j,blocks):
        if j==n: yield tuple(blocks); return
        for i in range(len(blocks)):
            blocks[i] |= 1<<j
            yield from rec(j+1,blocks)
            blocks[i] ^= 1<<j
        blocks.append(1<<j)
        yield from rec(j+1,blocks)
        blocks.pop()
    yield from rec(0,[])


def random_graph(rng, max_vertices=7, max_edges=11):
    n=rng.randint(1,max_vertices)
    edges=[(rng.randrange(i),i) for i in range(1,n)]
    edges += [(rng.randrange(n),rng.randrange(n))
              for _ in range(rng.randint(0,max_edges-len(edges)))]
    rng.shuffle(edges)
    edges=[(b,a) if rng.randrange(2) else (a,b) for a,b in edges]
    return Graph(n,tuple(edges),tuple(rng.randrange(0,50) for _ in edges))


class ResearchTests(unittest.TestCase):
    def test_all_connected_simple_graphs(self):
        for n in range(1,6):
            possible=list(itertools.combinations(range(n),2))
            for s in subsets(len(possible)):
                edges=tuple(possible[i] for i in s)
                if components(n,edges)!=1: continue
                g=Graph(n,edges,(1,)*len(edges)); p=maximum_batch(g)
                self.assertTrue(verify_batch(p))
                self.assertEqual(len(p['chosen']),len(edges)-n+1)
                cycles=[]
                for e in p['chosen']:
                    path=tree_return(g,p['tree'],e)
                    vector=[0]*len(edges); boundary=[0]*n
                    for j,sgn in path:
                        vector[j]+=sgn
                        a,b=edges[j]; boundary[a]-=sgn; boundary[b]+=sgn
                    self.assertEqual(boundary,[0]*n)
                    self.assertEqual([vector[j] for j in p['chosen']],
                                     [int(j==e) for j in p['chosen']])
                    cycles.append(vector)
                    COUNTS['signed_fundamental_cycles']+=1
                for chosen in subsets(len(edges)):
                    cc=components(n,edges,chosen)
                    self.assertEqual(components_after_cut(g,chosen),cc)
                    rows=[sum((abs(row[j])%2)<<i for i,j in enumerate(chosen)) for row in cycles]
                    self.assertEqual(rank2(rows),len(chosen)+1-cc)
                    COUNTS['subset_rank_connectivity_checks']+=1
                COUNTS['connected_simple_graphs']+=1

    def test_every_small_side_partition(self):
        for k in range(5):
            for masks in partitions(2*k):
                COUNTS['side_partitions']+=1
                if not k:
                    self.assertEqual(decode_side_census(0,((0,1),)),Graph(1,(),()))
                    COUNTS['valid_side_partitions']+=1
                    continue
                loc={j:v for v,m in enumerate(masks) for j in range(2*k) if m>>j&1}
                edges=tuple((loc[2*i],loc[2*i+1]) for i in range(k))
                valid=components(len(masks),edges)==1
                if not valid:
                    with self.assertRaises(InvalidInput):
                        decode_side_census(k,tuple((m,1) for m in masks))
                    continue
                decoded=decode_side_census(k,tuple((m,1) for m in reversed(masks)))
                self.assertEqual(sorted(m for m,_ in side_histogram(decoded)),sorted(masks))
                self.assertTrue(verify_batch(maximum_batch(decoded)))
                COUNTS['valid_side_partitions']+=1

    def test_weighted_multigraphs_against_all_subsets(self):
        rng=random.Random(2026101201)
        for _ in range(320):
            g=random_graph(rng)
            p=maximum_batch(g)
            self.assertTrue(verify_batch(p))
            self.assertEqual(p['reward'],brute_reward(g.vertices,g.edges,g.weights))
            for e in p['chosen']:
                row=[0]*len(g.edges)
                for j,s in tree_return(g,p['tree'],e): row[j]+=s
                self.assertEqual([row[j] for j in p['chosen']],
                                 [int(j==e) for j in p['chosen']])
            COUNTS['weighted_multigraphs']+=1

    def test_rational_rank_and_integral_cycles(self):
        rng=random.Random(2026101202)
        for _ in range(240):
            g=random_graph(rng); p=maximum_batch(g)
            cycles=[]
            for e in p['chosen']:
                row=[0]*len(g.edges)
                for j,s in tree_return(g,p['tree'],e): row[j]+=s
                cycles.append(row)
            chosen=[j for j in range(len(g.edges)) if rng.randrange(2)]
            rows=[[row[j] for j in chosen] for row in cycles]
            self.assertEqual(rankq(rows),len(chosen)+1-components(g.vertices,g.edges,chosen))
            COUNTS['rational_rank_checks']+=1

    def test_parallel_meridians_and_bridges(self):
        g=Graph(2,((0,1),(0,1)),(7,11))
        self.assertEqual([components_after_cut(g,s) for s in [(),(0,),(1,),(0,1)]],[1,1,1,2])
        self.assertEqual(maximum_batch(g)['chosen'],[1])
        g=Graph(3,((0,1),(1,2),(2,2)),(10,10,1))
        self.assertEqual(maximum_batch(g)['chosen'],[2])

    def test_census_aliases_and_huge_weights(self):
        # Two distinct side markers share an atom; add their weights.
        weights_by_atom={}
        locations=[17,17,3,17]
        for j,a in enumerate(locations):
            weights_by_atom[a]=weights_by_atom.get(a,0)+(1<<j)
        self.assertEqual(weights_by_atom[17],11)
        g=decode_side_census(2,[(11,1),(4,1)],[1<<16384,1])
        self.assertEqual(g.edges,((0,0),(1,0)))
        self.assertEqual(maximum_batch(g)['reward'],1<<16384)
        self.assertTrue(verify_batch(maximum_batch(g)))
        for rows in [[(3,2)],[(0,1),(15,1)],[(3,1),(3,1)],[(7,1)],[(31,1)]]:
            with self.assertRaises(InvalidInput): decode_side_census(2,rows)

    def test_reject_bad_graph_and_certificate(self):
        # Reject absurd binary dimensions before allocating an explicit namespace.
        with self.assertRaises(InvalidInput): Graph(1<<16384,(),())
        with self.assertRaises(InvalidInput): decode_side_census(1<<16384,[(3,1)])
        with self.assertRaises(InvalidInput): finite_routing_forest(1<<16384,[],[])
        for args in [(0,(),()),(2,(),()),(1,((0,1),),(1,)),(1,((0,0),),(-1,)),(True,(),())]:
            with self.assertRaises((ValueError,InvalidInput)): Graph(*args)
        p=maximum_batch(Graph(3,((0,1),(1,2),(0,2)),(1,2,9)))
        mutators=[lambda q:q.update(reward=10), lambda q:q.update(tree=[0,0]),
                  lambda q:q.update(chosen=[0]),lambda q:q.update(scope='knot-triviality'),
                  lambda q:q['graph'].update(vertices=4),
                  lambda q:q.update(tree=[0,2],chosen=[1],reward=2)]
        for f in mutators:
            q=copy.deepcopy(p); f(q); self.assertFalse(verify_batch(q)); COUNTS['tampered_packets_rejected']+=1
        for q in [None,{}, {'schema':'x'}]: self.assertFalse(verify_batch(q))

    def test_finite_source_routing(self):
        rng=random.Random(2026101203)
        for _ in range(450):
            g=random_graph(rng)
            sizes=[rng.randint(1,9) for _ in range(g.vertices)]
            groups=[]; count=0; interior=[]
            for size in sizes:
                group=list(range(count,count+size)); groups.append(group); count+=size
                for i in range(1,size): interior.append((group[i],rng.choice(group[:i])))
                interior += [(rng.choice(group),rng.choice(group)) for _ in range(size//2)]
            rng.shuffle(interior)
            gates=[(rng.choice(groups[u]),rng.choice(groups[v])) for u,v in g.edges]
            p=finite_routing_forest(count,interior,gates,g.weights)
            self.assertTrue(verify_routing(p))
            self.assertEqual(p['batch']['reward'],maximum_batch(g)['reward'])
            arena=Graph(count,tuple(interior+gates),(1,)*(len(interior)+len(gates)))
            tree=p['forest']+[len(interior)+j for j in p['batch']['tree']]
            for j in p['batch']['chosen']:
                cycle=tree_return(arena,tree,len(interior)+j)
                selected_gates=[e-len(interior) for e,s in cycle if e>=len(interior) and e-len(interior) in p['batch']['chosen']]
                self.assertEqual(selected_gates,[j])
                COUNTS['lifted_source_cycles']+=1
            q=copy.deepcopy(p); q['atom_count']+=1
            self.assertFalse(verify_routing(q))
            COUNTS['tampered_packets_rejected']+=1
            COUNTS['finite_source_arenas']+=1

    def test_path_recurrence_against_literal_paths(self):
        rng=random.Random(2026101204)
        for _ in range(1500):
            n=rng.randint(0,12); caps=tuple(rng.randrange(5) for _ in range(n))
            parents=tuple(tuple(j for j in range(i) if rng.random()<0.25) for i in range(n))
            self.assertEqual(path_bounds(caps,parents),path_sum_reference(caps,parents))
            h=dependency_height(parents); g=max(caps,default=0); delta=max(map(len,parents),default=0)
            bound=n*g*sum((delta*(g+1))**r for r in range(h+1))
            self.assertLessEqual(sum(path_bounds(caps,parents)),bound)
            COUNTS['dependency_dags']+=1

    def test_legal_random_histories(self):
        rng=random.Random(2026101205)
        for _ in range(600):
            n=rng.randint(1,9); caps=tuple(rng.randrange(4) for _ in range(n))
            parents=tuple(tuple(j for j in range(i) if rng.random()<0.23) for i in range(n))
            model=PersistentCounters(caps,parents)
            for t in range(500):
                legal=model.legal_events()
                if not legal: break
                model.apply(*rng.choice(legal))
            self.assertTrue(verify_trace(caps,parents,model.events))
            self.assertTrue(all(v<=b for v,b in zip(model.versions,path_bounds(caps,parents))))
            COUNTS['legal_history_events']+=len(model.events)
            COUNTS['legal_histories']+=1

    def test_sharp_chains(self):
        for g in range(1,4):
            for n in range(1,7):
                caps=(g,)*n; parents=((),)+tuple((i-1,) for i in range(1,n))
                model=PersistentCounters(caps,parents).finish(limit=10000)
                expected=tuple((g+1)**(i+1)-1 for i in range(n))
                self.assertEqual(tuple(model.versions),expected)
                self.assertEqual(path_bounds(caps,parents),expected)
                self.assertTrue(verify_trace(caps,parents,model.events))
                COUNTS['sharp_chain_events']+=len(model.events)
                COUNTS['sharp_chains']+=1

    def test_eventwise_amortized_potential(self):
        rng=random.Random(2026101209)
        for _ in range(400):
            n=rng.randint(1,10)
            caps=tuple(rng.randrange(4) for _ in range(n))
            initial=tuple(rng.randrange(g+1) for g in caps)
            parents=tuple(tuple(j for j in range(i) if rng.random()<0.25) for i in range(n))
            costs=tuple(rng.randrange(1,11) for _ in range(n))
            m=PersistentCounters(caps,parents,initial)
            def potential():
                return causal_potential(caps,parents,m.remaining,m.versions,m.snapshots,costs)
            starting=potential(); charged=0
            self.assertEqual(starting,sum(x*y for x,y in zip(initial,amplification(caps,parents,costs))))
            for _ in range(400):
                legal=m.legal_events()
                if not legal: break
                op,i=rng.choice(legal); before=potential(); m.apply(op,i); after=potential()
                self.assertLessEqual(after,before-costs[i])
                if op=='repair': self.assertEqual(after,before-costs[i])
                charged+=costs[i]
                self.assertLessEqual(charged+after,starting)
                COUNTS['eventwise_potential_checks']+=1
            self.assertTrue(verify_trace(caps,parents,m.events,initial))
            COUNTS['potential_histories']+=1
        with self.assertRaises(ValueError): causal_potential((1,1),((),(0,)),(1,1),(0,0),((),(1,)))

    def test_partial_progress_and_reverse_amplification(self):
        rng=random.Random(2026101206)
        for _ in range(450):
            n=rng.randint(1,10)
            caps=tuple(rng.randrange(5) for _ in range(n))
            d=tuple(rng.randrange(g+1) for g in caps)
            parents=tuple(tuple(j for j in range(i) if rng.random()<0.28) for i in range(n))
            costs=tuple(rng.randrange(1,30) for _ in range(n))
            b=path_bounds(caps,parents,d); a=amplification(caps,parents,costs)
            self.assertEqual(b,path_sum_reference(caps,parents,d))
            self.assertEqual(sum(c*x for c,x in zip(costs,b)),sum(x*y for x,y in zip(d,a)))
            m=PersistentCounters(caps,parents,d).finish(limit=30000)
            self.assertTrue(verify_trace(caps,parents,m.events,d))
            self.assertTrue(all(x<=y for x,y in zip(m.versions,b)))
            COUNTS['partial_progress_dags']+=1
            COUNTS['partial_progress_events']+=len(m.events)
        for d in [(-1,), (2,), (True,), ()]:
            with self.assertRaises(ValueError): path_bounds((1,),((),),d)

    def test_causally_weighted_optimal_reuse(self):
        rng=random.Random(2026101207)
        for _ in range(180):
            raw=random_graph(rng,max_vertices=5,max_edges=9)
            k=len(raw.edges)
            caps=tuple(rng.randrange(1,6) for _ in range(k))
            saved=tuple(rng.randrange(g+1) for g in caps)
            parents=tuple(tuple(j for j in range(i) if rng.random()<0.3) for i in range(k))
            costs=tuple(rng.randrange(1,8) for _ in range(k))
            a=amplification(caps,parents,costs)
            g=Graph(raw.vertices,raw.edges,tuple(s*t for s,t in zip(saved,a)))
            p=maximum_batch(g)
            def work(chosen):
                chosen=set(chosen)
                d=tuple(cap-(saved[i] if i in chosen else 0) for i,cap in enumerate(caps))
                return sum(x*y for x,y in zip(costs,path_bounds(caps,parents,d)))
            selected=work(p['chosen'])
            oracle=min(work(j) for j in subsets(k) if components(g.vertices,g.edges,j)==1)
            self.assertEqual(selected,oracle)
            self.assertEqual(work(())-selected,p['reward'])
            composite=plan_reuse(g.vertices,g.edges,caps,parents,saved,costs=costs)
            self.assertTrue(verify_reuse(composite))
            self.assertEqual(composite['retained_work_bound'],oracle)
            for field in ['baseline_work_bound','retained_work_bound']:
                bad=copy.deepcopy(composite); bad[field]+=1
                self.assertFalse(verify_reuse(bad))
                COUNTS['tampered_packets_rejected']+=1
            COUNTS['optimal_causal_reuse_instances']+=1

    def test_antichains_and_zero_caps(self):
        for n in range(0,31):
            caps=tuple(i%4 for i in range(n)); parents=((),)*n
            m=PersistentCounters(caps,parents).finish()
            self.assertEqual(sum(m.versions),sum(caps))
        # A zero-potential dependent task still rebuilds on changes of its parent.
        m=PersistentCounters((2,0),((),(0,))).finish()
        self.assertEqual(tuple(m.versions),(2,2))
        self.assertEqual(path_bounds((2,0),((),(0,))),(2,2))
        self.assertEqual(path_bounds((0,0),((),(0,))),(0,0))

    def test_stale_snapshots_and_rejected_traces(self):
        caps=(1,1,1); parents=((),(0,),(1,))
        bad=[[('rebuild',1)], [('repair',0),('repair',2)],
             [('repair',0),('rebuild',2)], [('repair',0),('repair',0)],
             [('repair',3)], [('x',0)], [('repair',True)]]
        for trace in bad:
            self.assertFalse(verify_trace(caps,parents,trace)); COUNTS['illegal_traces_rejected']+=1
        good=[('repair',0),('rebuild',1),('rebuild',2),('repair',2)]
        self.assertTrue(verify_trace(caps,parents,good))
        for caps,ps in [((-1,),((),)),((1,),((0,),)),((1,1),((),(0,0)))]:
            with self.assertRaises(ValueError): path_bounds(caps,ps)

    def test_support_read_sets_and_big_binary_indices(self):
        x=1<<16384
        surface=(Range('chambers',x,x+2),)
        loop=(Range('chambers',x+100,x+103),)
        incidence=(Range('face-charts',7,8),)
        writes=(Range('chambers',x+101,x+102),)
        self.assertEqual(invalidate(writes,[surface]),())
        self.assertEqual(invalidate(writes,[surface+loop+incidence]),(0,))
        self.assertFalse(supports_overlap([Range('a',0,1)],[Range('a',1,2)]))
        self.assertFalse(supports_overlap([Range('a',0,2)],[Range('b',0,2)]))
        self.assertEqual(invalidate([Range('face-charts',7,8)],[surface+loop+incidence]),(0,))
        b=path_bounds((x,0,3),((),(0,),(1,)))
        self.assertEqual(b,(x,x,3+4*x))
        COUNTS['maximum_test_integer_bits']=16385


if __name__=='__main__':
    started=time.perf_counter()
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(ResearchTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    record={'scope':'finite graph/census/routing/version model; not native geometry or recognition',
            'python':platform.python_version(),'platform':platform.platform(),
            'tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),
            'skips':len(result.skipped),'elapsed_seconds':time.perf_counter()-started,
            'counts':dict(sorted(COUNTS.items())),
            'native_ProveIt_run':False,'Regina_run':False}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results'/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
    sys.exit(not result.wasSuccessful())
