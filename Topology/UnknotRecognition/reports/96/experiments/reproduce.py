#!/usr/bin/env python3
"""Fresh evidence; deterministic cases, exact checks, shuffled paired timings.

Run from the package root: python experiments/reproduce.py --out /tmp/new-evidence
No downloaded code, solver, or topology package is required.
"""
import argparse, csv, json, platform, random, statistics, sys, time
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from scalar_separators import *
from scalar_separators.exact import *
from scalar_separators.fixtures import *


def random_model(rng):
    count=rng.randrange(1,5)
    parent=(-1,)+tuple(rng.randrange(v) for v in range(1,count))
    nodes=[]
    for v in range(count):
        b=rng.randrange(1,3)
        ports=tuple(([v] if v else [])+[i for i in range(1,count) if parent[i]==v])
        k=b+len(ports)
        rows=tuple(tuple(rng.randrange(-2,3) for _ in range(k)) for __ in range(rng.randrange(3)))
        pairs=((0,1),) if b==2 and rng.random()<.4 else ()
        nodes.append(Node(tuple(f'x{v}_{i}' for i in range(b)),ports,rows,pairs))
    return Model(parent,tuple(nodes)).validate()


def audit_random(count=96):
    rng=random.Random(12102026)
    result={'seed':12102026,'models':count,'queries':0,'positive':0,'negative':0,
            'independent_replays':0,'compiled_queries':0,'compiled_positive_extreme_checks':0,
            'source_recompilations':0,'coordinate_face_queries':0,'cases':[]}
    for case in range(count):
        model=random_model(rng)
        A,names,pairs=source_from_model(model)
        n=len(names)
        rays=rays_by_supports(A,n,pairs)
        prepared=Prepared(model)
        idx={s:j for j,s in enumerate(names)}
        bags=[tuple(idx[s] for s in node.names) for node in model.nodes]
        compiled,w=compile_source(A,n,bags,model.parent,pairs)
        assert verify_source_compilation(A,n,bags,model.parent,pairs,compiled,w)
        cp=Prepared(compiled)
        result['source_recompilations']+=1
        record={'case':case,'coordinates':n,'nodes':len(model.nodes),'global_admissible_rays':len(rays),'queries':[]}
        for q in range(8):
            cv=[F(rng.randrange(-5,6),rng.randrange(1,4)) for _ in names]
            c=dict(zip(names,cv))
            zero_indices={j for j in range(n) if q>=4 and rng.random()<.22}
            zeros={names[j] for j in zero_indices}
            expected=any(dot(cv,r)>0 and all(r[j]==0 for j in zero_indices) for r in rays)
            answer=prepared.solve(c,zeros)
            assert (answer['status']=='POSITIVE')==expected,(case,q)
            assert verify(model,c,answer,zeros),(case,q,'replay')
            cc={str(j):v for j,v in enumerate(cv)}
            zz={str(j) for j in zero_indices}
            ca=cp.solve(cc,zz)
            assert (ca['status']=='POSITIVE')==expected,(case,q,'compiler')
            assert verify(compiled,cc,ca,zz),(case,q,'compiled replay')
            if expected:
                x=[F(ca['coordinates'][str(j)]) for j in range(n)]
                S=[j for j,v in enumerate(x) if v]
                assert all(dot(row,x)==0 for row in A)
                assert len(nullspace([[row[j] for j in S] for row in A],len(S)))==1,(case,q,'extreme')
                result['compiled_positive_extreme_checks']+=1
                result['positive']+=1
            else: result['negative']+=1
            result['queries']+=1; result['compiled_queries']+=1; result['independent_replays']+=2
            result['coordinate_face_queries']+=bool(q>=4)
            record['queries'].append({'coefficients':[str(v) for v in cv],'zero_indices':sorted(zero_indices),'status':answer['status']})
        result['cases'].append(record)
    return result


def normal_audit():
    result=[]
    for tag,tri in [('one_tetrahedron',solid_torus()),('capped_two_tetrahedra',capped_solid_torus())]:
        A,n,pairs=normal_matching(tri)
        model,w=compile_source(A,n,[tuple(range(n))],[-1],pairs)
        prepared=Prepared(model)
        # Source matrices are small, but 2**14 support oracle is intentionally
        # used once rather than in every independent certificate replay.
        oracle=rays_by_supports(A,n,pairs)
        assert prepared.rays[0]==oracle
        positive=0
        chi=normal_euler(tri)
        euler_queries=[]
        for t in range(n//7):
            for q in range(4):
                zero=7*t+q
                ec={str(j):chi[j] for j in range(n)}
                ea=prepared.solve(ec,zeros=[str(zero)])
                ee=any(r[zero]==0 and dot(chi,r)>0 for r in oracle)
                assert (ea['status']=='POSITIVE')==ee
                if ee:
                    assert verify(model,ec,ea,[str(zero)])
                    xx=[F(ea['coordinates'][str(j)]) for j in range(n)]
                    S=[j for j in range(n) if xx[j]]
                    assert len(nullspace([[row[j] for j in S] for row in A],len(S)))==1
                euler_queries.append({'zero_triangle':zero,'status':ea['status']})
        for j in range(n):
            c={str(j):1}; a=prepared.solve(c)
            exp=any(r[j] for r in oracle)
            assert (a['status']=='POSITIVE')==exp
            if exp:
                assert verify(model,c,a); positive+=1
        ray=prepared.solve({'6':1},zeros=['2'])
        assert ray['status']=='POSITIVE'
        x=[F(ray['coordinates'][str(j)]) for j in range(n)]
        assert all(dot(row,x)==0 for row in A)
        tetra_bags=[tuple(range(7*t,7*t+7)) for t in range(n//7)]
        decomposable=True; reason=None; cut=None
        try:
            split,cut=compile_source(A,n,tetra_bags,[-1]+[0]*(n//7-1),pairs)
        except ValueError as e:
            decomposable=False; reason=str(e)
        result.append({'fixture':tag,'source':tri,'matrix':A,'coordinates':n,'matching_rank':rank(A,n),
                       'admissible_rays':len(oracle),'positive_coordinate_queries':positive,
                       'tetrahedron_bag_rank_one':decomposable,'rejection_reason':reason,
                       'meridian_search_witness':ray,'local_stats':prepared.stats,'euler_coefficients':[str(a) for a in chi],
                       'euler_anchor_queries':euler_queries,
                       'tetrahedron_cut_rank':None if n==7 else rank([[row[j] for j in range(7)] for row in A],7)+rank([[row[j] for j in range(7,14)] for row in A],7)-rank(A,n)})
    return result


def explicit_chain(m,threshold):
    # Exact exhaustive branch language baseline. Intentionally no DP or
    # duplicate endpoint elimination; it enumerates all 2**m branch histories.
    best=None
    for mask in range(1<<m):
        t=1
        for j in range(m):
            t*=3 if mask>>j&1 else 2
        value=t-threshold
        if best is None or value>best:
            best=value
    return best>0


def timing_benchmark():
    rng=random.Random(420126)
    rows=[]
    for m in (1,4,8,12,16,18):
        threshold=3**m
        def native():
            model,c=gain_chain(m,threshold)
            return Prepared(model).solve(c)['status']=='POSITIVE'
        def literal(): return explicit_chain(m,threshold)
        assert native()==literal()==False
        # Warmup then independently shuffled A, B, and identical-code A' arms.
        native(); literal(); native()
        samples=[]
        for rep in range(7):
            order=['native','literal','control']; rng.shuffle(order)
            record={'round':rep,'order':order}
            for arm in order:
                f=literal if arm=='literal' else native
                begin=time.perf_counter_ns(); ans=f(); end=time.perf_counter_ns()
                assert ans==False
                record[arm+'_seconds']=(end-begin)/1e9
            samples.append(record)
        rows.append({'stages':m,'histories':2**m,'local_rays':2*m+2,
                     'median_native_seconds':statistics.median(s['native_seconds'] for s in samples),
                     'median_literal_seconds':statistics.median(s['literal_seconds'] for s in samples),
                     'median_paired_literal_native':statistics.median(s['literal_seconds']/s['native_seconds'] for s in samples),
                     'median_paired_control_native':statistics.median(s['control_seconds']/s['native_seconds'] for s in samples),
                     'samples':samples})
    large=[]
    for m in (64,256,1024):
        start=time.perf_counter_ns()
        model,c=gain_chain(m)
        p=Prepared(model); a=p.solve(c)
        elapsed=(time.perf_counter_ns()-start)/1e9
        assert a['status']=='NONPOSITIVE'
        large.append({'stages':m,'history_exponent':m,'local_rays':sum(s['rays'] for s in p.stats),
                      'candidate_zero_sets':sum(s['candidates'] for s in p.stats),
                      'maximum_message_numerator_bits':max(abs(F(val).numerator).bit_length() for d in a['messages'].values() for val in d.values() if val is not None),
                      'seconds_single_run_not_paired':elapsed})
    return {'scope':'Complete supplied algebraic-chain query, including model construction, local ray enumeration, and scalar search; no native knot-recognition timing. Independent certificate replay is outside both timed arms.',
            'baseline':'Literal enumeration of all binary branch histories, not the best algorithm for this analytically soluble family.',
            'repeats':7,'paired':rows,'large':large}


def source_benchmark():
    tri=capped_solid_torus()
    separated=[tuple(j for j in range(14) if j not in (0,1,10)),(0,1,10)]
    def run(split):
        A,n,pairs=normal_matching(tri); chi=normal_euler(tri)
        bags=separated if split else [tuple(range(n))]
        parents=[-1,0] if split else [-1]
        model,w=compile_source(A,n,bags,parents,pairs)
        assert verify_source_compilation(A,n,bags,parents,pairs,model,w)
        p=Prepared(model); c={str(j):chi[j] for j in range(n)}
        out=[]
        for zero in (0,1,2,3,7,8,9,10):
            answer=p.solve(c,[str(zero)])
            assert answer['status']=='POSITIVE'
            assert verify(model,c,answer,[str(zero)])
            out.append(answer['status'])
        return {'statuses':out,'candidates':sum(d['candidates'] for d in p.stats),
                'local_rays':sum(d['rays'] for d in p.stats),'generators':w}
    base=run(False); split=run(True)
    rng=random.Random(17171); samples=[]
    for r in range(7):
        order=['one_bag','split','control'];rng.shuffle(order);d={'round':r,'order':order}
        for arm in order:
            begin=time.perf_counter_ns(); out=run(arm=='split');elapsed=time.perf_counter_ns()-begin
            assert out['statuses']==base['statuses']; d[arm+'_seconds']=elapsed/1e9
        samples.append(d)
    return {'scope':'Actual two-tetrahedron source fixture: matching and Euler construction, source compilation and rank replay, local ray construction, eight anchored Euler queries and positive arithmetic verification. Not the upstream recognizer.',
            'split_bags':separated,'one_bag':base,'split':split,'repeats':7,'samples':samples,
            'median_one_bag_seconds':statistics.median(d['one_bag_seconds'] for d in samples),
            'median_split_seconds':statistics.median(d['split_seconds'] for d in samples),
            'median_paired_one_bag_split':statistics.median(d['one_bag_seconds']/d['split_seconds'] for d in samples),
            'median_paired_control_one_bag':statistics.median(d['control_seconds']/d['one_bag_seconds'] for d in samples)}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,default=Path('evidence'))
    ap.add_argument('--skip-timings',action='store_true'); args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    start=time.perf_counter()
    result={'environment':{'python':sys.version,'platform':platform.platform()},'random_audit':audit_random(),
            'normal_fixture_audit':normal_audit(),
            'two_port_counter':{'stages':list(range(1,13)),'distinct_slopes':[2**m for m in range(1,13)],
                                'checked':all({sum(bit*(2**j) for j,bit in enumerate(bits)) for bits in __import__('itertools').product((0,1),repeat=m)}==set(range(2**m)) for m in range(1,13))}}
    if not args.skip_timings:
        result['benchmark']=timing_benchmark()
        result['source_benchmark']=source_benchmark()
    result['total_seconds']=time.perf_counter()-start
    (args.out/'results.json').write_text(json.dumps(result,indent=2,default=str)+'\n')
    if 'benchmark' in result:
        records=result['benchmark']['paired']
        fields=[k for k in records[0] if k!='samples']
        with (args.out/'benchmark.csv').open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
            for r in records: writer.writerow({k:r[k] for k in fields})
    print(json.dumps({k:v for k,v in result['random_audit'].items() if k!='cases'},indent=2))
    print('normal fixtures:',[(r['fixture'],r['admissible_rays'],r['tetrahedron_bag_rank_one']) for r in result['normal_fixture_audit']])
    print('elapsed:',result['total_seconds'])

if __name__=='__main__': main()
