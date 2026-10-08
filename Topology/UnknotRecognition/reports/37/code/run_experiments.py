#!/usr/bin/env python3
"""Reproduce correctness audits and paired terminal-stage benchmarks.

All timings are local research-kernel timings, not fastunknot recognition times.
The complete cube is exponential and restricted to small diagrams.
"""
from __future__ import annotations
import argparse, csv, gc, json, platform, random, statistics, sys, time
from pathlib import Path
from separator_transfer.core import (DAG,F2,dense_transfer,factor_at_cut,minimum_vertex_cut,binary_basis)
from separator_transfer.cube import (ChainComplex,reduced_cube,closure_components,acyclic_matching,
                                     morse_graphs,analyze_complex)
from separator_transfer.decision import terminal_rank_one_test
from separator_transfer.certificates import make_braid_certificate,verify_braid_certificate

ROOT=Path(__file__).resolve().parents[1]


def dense_rank(g, reverse=False):
    rows,_=dense_transfer(g,F2(),reverse)
    return len(binary_basis([sum(row[j]<<i for i,row in enumerate(rows))
                             for j in range(len(g.sources))]))


def cut_rank(g):
    cut=minimum_vertex_cut(g)
    return factor_at_cut(g,cut.cut,F2()).binary_rank()


def sleeve(R,M):
    """Valid two-term complex with a specified acyclic matching; not a knot family."""
    # Sources s; matched degree-zero L0, Li, L1; matched degree-one B0, Bi, B1; targets t.
    src=list(range(R)); L0=R; Li=list(range(R+1,R+M+1)); L1=R+M+1
    B0=R+M+2; Bi=list(range(B0+1,B0+M+1)); B1=B0+M+1
    tgt=list(range(B1+1,B1+1+R)); n=B1+1+R
    degree=[0]*n
    for v in [B0,*Bi,B1,*tgt]: degree[v]=1
    pairs=[(L0,B0),*zip(Li,Bi),(L1,B1)]
    edges=[*pairs,*((s,B0) for s in src),*((L0,b) for b in Bi),
           *((l,B1) for l in Li),*((L1,t) for t in tgt)]
    complex_=ChainComplex(tuple(degree),(0,)*n,tuple(sorted(edges)))
    counts,graphs=morse_graphs(complex_,pairs)
    g=graphs[0,0]
    assert g.n==2*R+2*M+4 and len(g.edges)==2*R+3*M+2
    return complex_,tuple(pairs),g


def paired(arms,rounds=7,seed=612):
    rng=random.Random(seed); raw=[]
    # Identical setup and fresh algorithm-local arrays in every call. Warm all arms.
    for fn in arms.values(): fn()
    for r in range(rounds):
        names=list(arms); rng.shuffle(names)
        for name in names:
            gc.collect()
            start=time.perf_counter_ns(); value=arms[name](); elapsed=time.perf_counter_ns()-start
            raw.append(dict(round=r,arm=name,seconds=elapsed/1e9,value=value))
    return dict(samples=raw,median_seconds={name:statistics.median(
        x['seconds'] for x in raw if x['arm']==name) for name in arms})


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--output',default=str(ROOT/'results'))
    ap.add_argument('--rounds',type=int,default=7); ap.add_argument('--corpus-size',type=int,default=80)
    args=ap.parse_args(); out=Path(args.output); out.mkdir(parents=True,exist_ok=True)
    environment=dict(python=sys.version,platform=platform.platform(),processor=platform.processor(),
                     timer='perf_counter_ns',rounds=args.rounds,seed=20261008,
                     production_fastunknot_benchmarked=False)
    rng=random.Random(20261008)
    corpus=[('unknot',1,[]),('positive_RI',2,[1]),('negative_RI',2,[-1]),
            ('trefoil',2,[1]*3),('figure_eight',3,[1,-2]*2),('torus_2_5',2,[1]*5),
            ('stabilized_unknot',3,[1,2]),('cancelled_unknot',2,[1,-1,1])]
    while len(corpus)<args.corpus_size:
        s=rng.randint(2,4); n=rng.randint(2,7)
        w=[rng.choice((-1,1))*rng.randint(1,s-1) for _ in range(n)]
        if closure_components(s,w)==1: corpus.append((f'random_{len(corpus):03d}',s,w))
    audit=[]; actual_graphs=[]
    for index,(name,s,w) in enumerate(corpus):
        c=reduced_cube(s,w); direct=c.homology()
        for limit in (12,None):
            pairs=acyclic_matching(c,limit); result=analyze_complex(c,pairs)
            assert result['homology']==direct
            pre=terminal_rank_one_test(c,pairs)
            assert pre['lower']<=sum(direct.values())
            if pre['exact_rank'] is not None: assert pre['exact_rank']==sum(direct.values())
            if pre['lower']>1: assert sum(direct.values())>1 and pre['evaluated_maps']==0
            result['homology']=[dict(h=h,j=j,rank=b) for (h,j),b in sorted(result['homology'].items())]
            audit.append(dict(name=name,strands=s,word=w,matching_edge_limit=limit,
                              preflight=pre,**result))
            if limit==12 and index in (3,4,5):
                _,graphs=morse_graphs(c,pairs)
                actual_graphs.append((name,list(graphs.values())))
    with (out/'knot_audit.json').open('w') as f: json.dump(audit,f,indent=2)
    actual=[]
    for name,graphs in actual_graphs:
        def forward(): return sum(dense_rank(g) for g in graphs)
        def reverse(): return sum(dense_rank(g,True) for g in graphs)
        def cut(): return sum(cut_rank(g) for g in graphs)
        timing=paired(dict(forward=forward,control=forward,reverse=reverse,cut_factor=cut),args.rounds)
        assert len({x['value'] for x in timing['samples']})==1
        actual.append(dict(name=name,maps=len(graphs),vertices=sum(g.n for g in graphs),
                           edges=sum(len(g.edges) for g in graphs),**timing))
    synthetic=[]
    for R in (8,16,32,64):
        M=R*R+1; c,pairs,g=sleeve(R,M)
        cut=minimum_vertex_cut(g); factors=factor_at_cut(g,cut.cut,F2())
        f,fw=dense_transfer(g,F2()); b,bw=dense_transfer(g,F2(),True)
        assert f==b==factors.expand(F2()) and factors.binary_rank()==1 and cut.capacity==1
        assert fw.compositions==R*(3*M+R+3) and bw.compositions==fw.compositions
        # Optimizer's first minimum cut may be B0 or L0; both have the same work.
        assert factors.work.compositions==3*M+2*R+2
        decision=terminal_rank_one_test(c,pairs)
        assert decision['lower']==2*R-2 and decision['evaluated_maps']==0
        timing=paired(dict(forward=lambda:dense_rank(g),control=lambda:dense_rank(g),
                           reverse=lambda:dense_rank(g,True),cut_factor=lambda:cut_rank(g)),args.rounds)
        assert all(x['value']==1 for x in timing['samples'])
        synthetic.append(dict(R=R,M=M,vertices=g.n,edges=len(g.edges),cut_capacity=cut.capacity,
            forward_compositions=fw.compositions,reverse_compositions=bw.compositions,
            factor_compositions=factors.work.compositions,critical=2*R,homology=2*R-2,
            decision=decision,**timing))
    with (out/'benchmarks.json').open('w') as f:
        json.dump(dict(environment=environment,actual=actual,synthetic=synthetic,
          scope='Graph construction and Morse matching excluded. Exact matrix-rank query in every arm. '
                'cut_factor includes min-cut construction, optimization, certificate verification, '
                'first-hit factor construction and factorized binary rank. '
                'forward/control/reverse include endpoint matrix construction and binary rank. '
                'No production sparse-cancellation or end-to-end recognizer is benchmarked.'),f,indent=2)
    ex=ROOT/'examples'; ex.mkdir(exist_ok=True)
    for name,s,w in corpus[:6]:
        cert=make_braid_certificate(s,w,12)
        assert verify_braid_certificate(cert)
        (ex/f'{name}.json').write_text(json.dumps(cert,indent=2)+'\n')
    summary=dict(environment=environment,diagrams=len(corpus),presentations=len(audit),
        transferred_maps=sum(len(a['details']) for a in audit),
        cube_generators=sum(a['generators'] for a in audit[::2]),
        preflight_rejections=sum(a['preflight']['exact_rank'] is None for a in audit),
        preflight_rejections_partial=sum(a['preflight']['exact_rank'] is None for a in audit if a['matching_edge_limit']==12),
        preflight_rejections_full=sum(a['preflight']['exact_rank'] is None for a in audit if a['matching_edge_limit'] is None),
        actual_knotted_diagrams=sum(a['exact_rank']>1 for a in audit[::2]),
        strict_sharp_over_global=sum(a['sharp_lower']>a['global_lower'] for a in audit),
        strict_sharp_over_local=sum(a['sharp_lower']>a['graded_lower'] for a in audit),
        disagreements=0,independently_verified_braid_certificates=6,
        actual=[dict(name=a['name'],**a['median_seconds']) for a in actual],
        synthetic=[dict(R=a['R'],M=a['M'],vertices=a['vertices'],edges=a['edges'],
                        forward_compositions=a['forward_compositions'],factor_compositions=a['factor_compositions'],
                        **a['median_seconds']) for a in synthetic])
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    with (out/'benchmark_medians.csv').open('w',newline='') as f:
        writer=csv.writer(f); writer.writerow(['family','case','forward_s','control_s','reverse_s','cut_factor_s','forward_over_cut'])
        for family,rows in [('knot',actual),('synthetic',synthetic)]:
            for row in rows:
                t=row['median_seconds']; writer.writerow([family,row.get('name',row.get('R')),
                   t['forward'],t['control'],t['reverse'],t['cut_factor'],t['forward']/t['cut_factor']])
    print(json.dumps(summary,indent=2))

if __name__=='__main__': main()
