#!/usr/bin/env python3
"""Deterministic audits and paired kernel benchmarks. No network or native imports.

Run from the package root. --out selects fresh evidence; default evidence-new
avoids changing delivered data. Timings are raw observations, not asymptotic
proofs or production-recognizer measurements.
"""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import argparse,json,random,platform,statistics,time,csv
from fractions import Fraction as F
from itertools import combinations
from projective_ports import Block,Prepared,enumerate_rays,enumerate_rays_by_zeros
from projective_ports.source import (Source,compile_two_block,compile_variable_separator,
    synchronized_source,extreme_witness)
from projective_ports.verify import verify_vector,verify_synchronized
from projective_ports.fixtures import sleeve_blocks,sleeve_costs,capped_solid_torus,matching,euler,nonextreme_assembly
from experiments.oracle import all_rays,positive,cartesian_modes


def encode(obj):
    if isinstance(obj,F):return str(obj)
    if isinstance(obj,(set,frozenset)):return sorted(obj)
    raise TypeError(type(obj).__name__)


def save(out,name,data):
    out.mkdir(parents=True,exist_ok=True)
    (out/name).write_text(json.dumps(data,indent=2,default=encode)+'\n')


def environment():
    return {'python':sys.version,'platform':platform.platform(),
            'processor':platform.processor(),'clock':'time.perf_counter_ns',
            'scope':'standalone exact algebra/source-query kernels; not native recognition',
            'seed':20261012}


def audit(models):
    rng=random.Random(20261012);log=[];queries=checks=descents=scorechecks=localchecks=0
    for index in range(models):
        d=1+index%3;n=3 if d==3 else (3+index%2);blocks=[]
        for i in range(2):
            equations=((1,1,-1)+(0,)*(n-3),) if rng.randrange(2) else ()
            ports=tuple(tuple(rng.randrange(4) for _ in range(n)) for _ in range(d))
            conflicts=tuple(pair for pair in combinations(range(n),2) if rng.random()<.22)
            blocks.append(Block(n,equations,ports,conflicts))
        blocks=tuple(blocks);p=Prepared(blocks)
        for b,rr in zip(blocks,p.raw_rays):
            oracle=set(all_rays(b.n,b.equations,b.conflicts))
            assert set(rr)==oracle;localchecks+=1
            assert set(enumerate_rays_by_zeros(b))==oracle;localchecks+=1
        source,_,offsets=synchronized_source(blocks,tuple((0,)*b.n for b in blocks))
        rays=all_rays(source.n,source.equations,source.conflicts)
        for q in range(8):
            c=tuple(tuple(rng.randrange(-6,7) for _ in range(b.n)) for b in blocks)
            master=tuple(rng.randrange(-3,4) for _ in range(d))
            zeros=tuple(tuple(j for j in range(b.n) if rng.random()<.18) for b in blocks)
            _,cost,_=synchronized_source(blocks,c,master)
            globalzeros=tuple(off+j for off,z in zip(offsets,zeros) for j in z)
            a=p.solve(c,master=master,zeros=zeros)
            expected=positive(rays,cost,globalzeros)
            assert (a['status']=='POSITIVE')==bool(expected),(index,q,a,expected)
            queries+=1
            if a['kind']!='zero-port':
                scores=[]
                for r in rays:
                    if any(r[j] for j in globalzeros):continue
                    port=blocks[0].image(r[:blocks[0].n]);h=sum(port,F(0))
                    if h: scores.append(sum((x*y for x,y in zip(cost,r)),F(0))/h)
                best=max(scores) if scores else None
                assert a['value']==best,(index,q,a['value'],best)
                scorechecks+=1
            if expected:
                assert verify_synchronized(blocks,c,a,master=master,zeros=zeros);checks+=1
                x=tuple(v for vector in a['vectors'] for v in vector)
                w=extreme_witness(source,x,cost)
                assert verify_vector(source.n,source.equations,source.conflicts,cost,w['coordinates'],zeros=globalzeros,extreme=True)
                assert w['coordinates'] in rays
                assert not verify_vector(source.n,source.equations,source.conflicts,cost,tuple(2*v for v in w['coordinates']),extreme=True)
                checks+=2;descents+=len(w['descent'])
            log.append({'model':index,'query':q,'d':d,'global_rays':len(rays),
                        'atlas_vertices':len(p.vertices),'status':a['status'],'kind':a['kind'],'value':a['value']})
    return {'environment':environment(),'models':models,'queries':queries,'independent_local_ray_checks':localchecks,
            'normalized_optimum_comparisons':scorechecks,'certificate_and_tamper_checks':checks,
            'support_descent_steps':descents,'results':log}


def normal_audit():
    tri=capped_solid_torus();s=matching(tri);chi=euler(tri);co=compile_two_block(s,range(7));p=Prepared(co.blocks)
    rays=all_rays(s.n,s.equations,s.conflicts);rng=random.Random(12102026);records=[];positive_count=0;steps=0
    anchors=[(10,j) for j in (0,1,2,3,7,8,9,11)]
    cases=[(chi,z,'Euler') for z in anchors]
    cases += [(tuple(F(rng.randrange(-4,5)) for _ in range(s.n)),
               tuple(j for j in range(s.n) if rng.random()<.12),'random-linear') for _ in range(96)]
    for c,z,label in cases:
        cc,cm,zz=co.query(c,z);a=p.solve(cc,master=cm,zeros=zz)
        expected=positive(rays,c,z)
        assert (a['status']=='POSITIVE')==bool(expected)
        row={'label':label,'objective':c,'zeros':z,'status':a['status'],'kind':a['kind'],'value':a['value'],'port':a['port']}
        if expected:
            x=co.reconstruct(a['vectors']);w=extreme_witness(s,x,c)
            assert verify_vector(s.n,s.equations,s.conflicts,c,w['coordinates'],zeros=z,extreme=True)
            assert w['coordinates'] in rays;positive_count+=1;steps+=len(w['descent']);row['certificate']=w
        records.append(row)
    # Independent variable-separator compiler audit, against the original source.
    variable_cases=0
    for masters in ((0,1),(0,1,2),(7,8,9)):
        cv=compile_variable_separator(s,masters);pv=Prepared(cv.blocks)
        for c,z,_ in cases[:8]:
            cc,cm,zz=cv.query(c,z);a=pv.solve(cc,master=cm,zeros=zz)
            assert (a['status']=='POSITIVE')==bool(positive(rays,c,z))
            if a['status']=='POSITIVE':
                x=cv.reconstruct(a['vectors']);assert verify_vector(s.n,s.equations,s.conflicts,c,x,zeros=z)
            variable_cases+=1
    return {'environment':environment(),'triangulation':tri,'matching':s.equations,'euler':chi,
            'local_ray_counts':list(map(len,p.raw_rays)),'global_ray_count':len(rays),'atlas':p.stats,
            'queries':len(cases),'positive_certificates':positive_count,'support_descent_steps':steps,
            'variable_compiler_queries':variable_cases,'source_fixture_only':True,'records':records}


def descent_audit():
    from projective_ports.exact import primitive
    records=[]
    for b in range(1,65):
        q=2**b+1;blocks=nonextreme_assembly(q);costs=((1,)*4,(1,))
        p=Prepared(blocks);a=p.solve(costs);s,c,_=synchronized_source(blocks,costs)
        x=tuple(v for vv in a['vectors'] for v in vv)
        assert not verify_vector(s.n,s.equations,s.conflicts,c,primitive(x),extreme=True)
        w=extreme_witness(s,x,c)
        assert len(w['descent'])==1
        assert verify_vector(s.n,s.equations,s.conflicts,c,w['coordinates'],extreme=True)
        assert w['coordinates'] in all_rays(s.n,s.equations,s.conflicts)
        records.append({'q_bits':q.bit_length(),'q':str(q),'assembled':primitive(x),'certificate':w})
    return {'environment':environment(),'cases':len(records),'nonextreme_before':len(records),
            'independently_extreme_after':len(records),'records':records}


def measured(fn):
    start=time.perf_counter_ns();value=fn();return value,(time.perf_counter_ns()-start)/1e6


def benchmark_modes(trials,max_m):
    output=[]
    for m in (1,2,4,8,12,16):
        if m>max_m:continue
        b=sleeve_blocks(m);c=sleeve_costs(m);p=Prepared(b)
        target=cartesian_modes(c);assert p.solve(c)['value']==target
        samples=[]
        for t in range(trials):
            funcs=[('cartesian',lambda:cartesian_modes(c)),('atlas_query',lambda:p.solve(c)['value']),
                   ('atlas_prepare_query',lambda:Prepared(b).solve(c)['value'])]
            if t%2:funcs.reverse()
            sample={}
            for name,fn in funcs:
                value,ms=measured(fn);assert value==target;sample[name]=ms
            samples.append(sample)
        med={k:statistics.median(r[k] for r in samples) for k in samples[0]}
        output.append({'blocks':m,'global_mode_histories':2**m,'atlas':p.stats,
                       'optimum':target,'samples_ms':samples,'median_ms':med,
                       'full_kernel_ratio':med['cartesian']/med['atlas_prepare_query'],
                       'reused_query_ratio':med['cartesian']/med['atlas_query']})
    return {'environment':environment(),'trials':trials,'scope':'same supplied local rays/modes; baseline enumerates Cartesian histories',
            'rows':output}


def normal_workload(split):
    tri=capped_solid_torus();s=matching(tri);c=euler(tri);zeros=[(10,j) for j in (0,1,2,3,7,8,9,11)]
    answers=[];packets=[]
    if split:
        co=compile_two_block(s,range(7));p=Prepared(co.blocks)
        for z in zeros:
            cc,cm,zz=co.query(c,z);a=p.solve(cc,master=cm,zeros=zz);status=a['status']=='POSITIVE';answers.append(status)
            if status:
                w=extreme_witness(s,co.reconstruct(a['vectors']),c)
                assert verify_vector(s.n,s.equations,s.conflicts,c,w['coordinates'],zeros=z,extreme=True)
                packets.append(w)
    else:
        # Same production ray enumerator, but without decomposition or a port atlas.
        rays=enumerate_rays(Block(s.n,s.equations,((1,)*s.n,),s.conflicts))
        for z in zeros:
            witness=next((r for r in rays if not any(r[j] for j in z)
                and sum((a*b for a,b in zip(c,r)),F(0))>0),None)
            answers.append(witness is not None)
            if witness is not None:
                assert verify_vector(s.n,s.equations,s.conflicts,c,witness,zeros=z,extreme=True)
                packets.append({'coordinates':witness})
    # Include actual evidence serialization in both measured workloads.
    json.dumps({'answers':answers,'packets':packets},default=encode)
    return answers


def benchmark_normal(trials):
    assert normal_workload(False)==normal_workload(True)
    samples=[]
    for t in range(trials):
        row={}
        for split in ((False,True) if t%2==0 else (True,False)):
            ans,ms=measured(lambda:normal_workload(split));row['split' if split else 'unsplit']=ms
        samples.append(row)
    med={k:statistics.median(x[k] for x in samples) for k in samples[0]}
    return {'environment':environment(),'trials':trials,'samples_ms':samples,'median_ms':med,
            'ratio':med['unsplit']/med['split'],'answers':normal_workload(True),
            'scope':'face matching, Euler coefficients, preparation, 8 anchored queries, source witness extraction, independent positive checking, serialization; not native full-knot recognition'}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('mode',choices=['audit','normal','descent','modes','timing','all'])
    ap.add_argument('--out',type=Path,default=Path('evidence-new'));ap.add_argument('--models',type=int,default=120)
    ap.add_argument('--trials',type=int,default=5);ap.add_argument('--max-m',type=int,default=16);args=ap.parse_args()
    jobs={'audit':('random_audit.json',lambda:audit(args.models)),
          'normal':('normal_audit.json',normal_audit),
          'descent':('descent_audit.json',descent_audit),
          'modes':('mode_benchmark.json',lambda:benchmark_modes(args.trials,args.max_m)),
          'timing':('normal_benchmark.json',lambda:benchmark_normal(args.trials))}
    for key,(name,fn) in jobs.items():
        if args.mode not in ('all',key):continue
        start=time.perf_counter();result=fn();save(args.out,name,result)
        print(key,'OK',round(time.perf_counter()-start,3),'seconds',flush=True)


if __name__=='__main__':main()
