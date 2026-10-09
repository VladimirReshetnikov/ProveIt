"""Paired finite-interface measurements; never a whole-knot timing claim."""
from __future__ import annotations
import argparse, json, platform, random, statistics, time
from itertools import combinations
from pathlib import Path
from signed_continuations.core import Candidate, SignedPartition, partitions, reduce_family, optimum
from signed_continuations.transitions import optional_signed_edges


def ask(rows, queries):
    answers=[]; probes=0
    for q in queries:
        answer=None
        for v,c in rows:
            probes+=1
            if (v&q).bit_count()&1:
                answer=c; break
        answers.append(answer)
    return answers,probes


def timed(fn):
    start=time.perf_counter(); out=fn(); return out,time.perf_counter()-start


def static_case(r,repeats,query_count):
    fam=[Candidate(p,-p.blocks,str(i)) for i,p in enumerate(partitions(r))]
    rng=random.Random(8300+r)
    # Alternate the discrete completion (connectivity required from the prefix)
    # with random completions. Input family and query generation are excluded.
    qs=[SignedPartition.discrete(r) if i%2==0 else rng.choice(fam).partition for i in range(query_count)]
    queries=[q.vector() for q in qs]; records=[]
    for repeat in range(repeats):
        # Both routes get their own required preprocessing. Alternate route order.
        def full_route():
            start=time.perf_counter()
            rows=sorted([(c.partition.vector(),c.cost) for c in fam],key=lambda x:x[1])
            setup=time.perf_counter()-start
            (answers,probes),query_time=timed(lambda: ask(rows,queries))
            (_,one_probes),one_time=timed(lambda: ask(rows,queries[:1]))
            return dict(setup_s=setup,query_s=query_time,total_s=setup+query_time,
                        one_query_s=one_time,one_total_s=setup+one_time,probes=probes,
                        one_probes=one_probes,answers=answers)
        def reduced_route():
            start=time.perf_counter(); reduction=reduce_family(fam)
            rows=[(c.partition.vector(),c.cost) for c in reduction.candidates]
            setup=time.perf_counter()-start
            (answers,probes),query_time=timed(lambda: ask(rows,queries))
            (_,one_probes),one_time=timed(lambda: ask(rows,queries[:1]))
            return dict(setup_s=setup,query_s=query_time,total_s=setup+query_time,
                        one_query_s=one_time,one_total_s=setup+one_time,probes=probes,
                        one_probes=one_probes,selected=len(reduction.candidates),xor_count=reduction.xors,answers=answers)
        if repeat%2:
            small=reduced_route(); full=full_route()
        else:
            full=full_route(); small=reduced_route()
        assert full.pop('answers')==small.pop('answers')
        records.append({'full':full,'basis':small})
    med={route:{key:statistics.median(rec[route][key] for rec in records)
                for key in records[0][route]} for route in ('full','basis')}
    return {'ports':r,'candidates':len(fam),'dimension':1<<(r-1),'queries':query_count,
            'repeats':repeats,'raw':records,'median':med,
            'whole_batch_speedup':med['full']['total_s']/med['basis']['total_s'],
            'one_query_speedup':med['full']['one_total_s']/med['basis']['one_total_s']}


def dynamic_case(r,repeats):
    rng=random.Random(1610+r)
    edges=[(i,j,rng.randrange(-13,17),rng.randrange(-13,17)) for i,j in combinations(range(r),2)]
    rng.shuffle(edges); raw=[]
    for _ in range(repeats):
        full,ft=timed(lambda:optional_signed_edges(r,edges,reduced=False))
        small,st=timed(lambda:optional_signed_edges(r,edges,reduced=True))
        fa,fs=full;sa,ss=small
        fc=optimum(fa,SignedPartition.discrete(r));sc=optimum(sa,SignedPartition.discrete(r))
        assert fc is not None and sc is not None and fc.cost==sc.cost
        # Additional independent terminal queries, not just the all-discrete one.
        for q in list(partitions(r))[:20]:
            a,b=optimum(fa,q),optimum(sa,q)
            assert (a.cost if a else None)==(b.cost if b else None)
        raw.append({'full_s':ft,'basis_s':st,'full_states':len(fa),'basis_states':len(sa),
                    'full_generated':fs['generated'],'basis_generated':ss['generated'],
                    'optimum':fc.cost,'full_history':fs['history'],'basis_history':ss['history']})
    return {'ports':r,'edges':len(edges),'raw':raw,'median_full_s':statistics.median(x['full_s'] for x in raw),
            'median_basis_s':statistics.median(x['basis_s'] for x in raw)}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='results/benchmark.json');ap.add_argument('--repeats',type=int,default=3);ap.add_argument('--queries',type=int,default=1024)
    args=ap.parse_args()
    data={'scope':'Finite signed-interface kernels; not knot recognizer timings',
          'python':platform.python_version(),'platform':platform.platform(),'clock':'perf_counter',
          'input_generation_excluded':True,'static':[],'dynamic':[]}
    for r in (5,6,7,8):
        data['static'].append(static_case(r,args.repeats,args.queries));print('static',r,flush=True)
    for r in (5,6,7):
        data['dynamic'].append(dynamic_case(r,args.repeats));print('dynamic',r,flush=True)
    p=Path(args.out);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
