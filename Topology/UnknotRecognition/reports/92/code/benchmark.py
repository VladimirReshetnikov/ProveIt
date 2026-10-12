"""Paired graph-stage benchmark against exhaustive subset search.

Neither arm invokes ProveIt, normal surfaces, the weighted orbit producer, or a
knot recognizer. Both arms decode the same given census, solve the same weighted
batch problem, build a packet, and run the same independent verifier. All raw
samples and the identical exhaustive/exhaustive control are retained.
"""
from __future__ import annotations
import itertools, json, platform, random, statistics, time
from pathlib import Path
from cographic import Graph, side_histogram, decode_side_census, maximum_batch
from verify import verify_batch
ROOT=Path(__file__).resolve().parents[1]


def connected(n,edges,keep):
    adj=[[] for _ in range(n)]
    for i in keep:
        a,b=edges[i]; adj[a].append(b); adj[b].append(a)
    seen={0}; todo=[0]
    while todo:
        for y in adj[todo.pop()]:
            if y not in seen: seen.add(y); todo.append(y)
    return len(seen)==n


def exhaustive(g):
    m=len(g.edges); best=None
    for mask in range(1<<m):
        chosen=[i for i in range(m) if mask>>i&1]
        keep=[i for i in range(m) if not mask>>i&1]
        if not connected(g.vertices,g.edges,keep): continue
        reward=sum(g.weights[i] for i in chosen)
        key=(reward,len(chosen))
        if best is None or key>best[0]: best=(key,chosen,keep)
    key,chosen,keep=best
    return {'schema':'cographic-batch-v1','scope':'relative-to-authenticated-chamber-graph',
            'graph':g.packet(),'tree':keep,'chosen':chosen,'reward':key[0]}


def call(rows,weights,method):
    g=decode_side_census(len(weights),rows,weights)
    p=maximum_batch(g) if method=='optimized' else exhaustive(g)
    if not verify_batch(p): raise AssertionError('independent verification failed')
    return p['reward']


def main():
    rng=random.Random(2026101208)
    cases=[('empty',1,()),('one_loop',1,((0,0),)),
           ('parallel_pair',2,((0,1),(0,1))),
           ('triangle',3,((0,1),(1,2),(2,0))),
           ('bouquet_8',1,((0,0),)*8)]
    for n,m in [(5,10),(6,14),(7,18)]:
        edges=[(i,i+1) for i in range(n-1)]
        edges += [(rng.randrange(n),rng.randrange(n)) for _ in range(m-len(edges))]
        cases.append((f'multi_{n}_{m}',n,tuple(edges)))
    records=[]
    for name,n,edges in cases:
        weights=tuple(rng.randrange(1,50) for _ in edges)
        g=Graph(n,edges,weights); rows=side_histogram(g)
        expected=call(rows,weights,'exhaustive')
        assert call(rows,weights,'optimized')==expected
        reps=500 if len(edges)<4 else (20 if len(edges)<=8 else 1)
        samples=[]
        for round_id in range(7):
            arms=['optimized','exhaustive','control']; rng.shuffle(arms)
            sample={'round':round_id,'order':arms}
            for arm in arms:
                started=time.perf_counter_ns()
                for _ in range(reps):
                    value=call(rows,weights,arm)
                elapsed=(time.perf_counter_ns()-started)*1e-9/reps
                assert value==expected
                sample[arm]=elapsed
            samples.append(sample)
        records.append({'case':name,'vertices':n,'edges':len(edges),'repetitions_per_sample':reps,
                        'input':g.packet(),'census':rows,'reward':expected,'samples':samples,
                        'median_optimized_ms':1000*statistics.median(s['optimized'] for s in samples),
                        'median_exhaustive_ms':1000*statistics.median(s['exhaustive'] for s in samples),
                        'median_paired_old_over_new':statistics.median(s['exhaustive']/s['optimized'] for s in samples),
                        'median_identical_control':statistics.median(s['control']/s['exhaustive'] for s in samples)})
    result={'scope':__doc__,'python':platform.python_version(),'platform':platform.platform(),
            'seed':2026101208,'rounds':7,'cases':records,'native_recognition_benchmark':False}
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
    lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',
           r'Case & $k$ & New (ms) & Exhaustive (ms) & Ratio & Control \\',r'\midrule']
    for r in records:
        lines.append(f"{r['case'].replace('_',r'\_')} & {r['edges']} & {r['median_optimized_ms']:.4f} & {r['median_exhaustive_ms']:.4f} & {r['median_paired_old_over_new']:.2f} & {r['median_identical_control']:.3f} \\\\")
    lines += [r'\bottomrule',r'\end{tabular}']
    (ROOT/'results'/'benchmark_table.tex').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__': main()
