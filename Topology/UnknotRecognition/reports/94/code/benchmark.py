"""Paired supplied-matching queries, not knot recognition benchmarks.

Both timed arms start with the same immutable interval packet and include
structural interval validation and the complete acyclicity/critical-cell query.
The compressed arm discovers offsets and independently replays its rank proof;
the explicit arm expands the directed Hasse graph and runs Kahn's algorithm.
Source construction/authentication, serialization and cleanup are outside timers.
An identical explicit second arm provides an A/A control. All raw rounds retained.
"""
from __future__ import annotations
import sys, json, random, time, statistics, platform, gc
from pathlib import Path
from math import gcd
from ranked_morse import prepare,synthesize_modular,verify_modular,one_critical_vertex,explicit_acyclic,dumps_certificate
from sources import modular_path,product_source,disk_fan,simplex_faces,compare_product_geometry,surface_is_disk
ROOT=Path(__file__).resolve().parents[1]


def compressed_query(packet,N,step,scale,start=0):
    p=prepare(packet)
    inv=pow(step,-1,N)
    a={f.name:-inv for f in packet.families}
    c={f.name:inv*start+N-1 for f in packet.families}
    proof=synthesize_modular(p,N,scale,a,c)
    return proof is not None and verify_modular(p,proof),p.counts


def explicit_query(packet):
    p=prepare(packet)
    return explicit_acyclic(p),p.counts


def timed(fn):
    gc.collect()
    t=time.perf_counter_ns()
    out=fn()
    return (time.perf_counter_ns()-t)/1e9,out


def main():
    rng=random.Random(5122026)
    cases=[]
    for kind,N in [('path',3),('path',65),('path',4097),('prism',3),('prism',9),('prism',33),('prism',129),('prism',513),('prism',2049)]:
        if kind=='path':
            packet,_=modular_path(N,2);scale=2
        else:
            facets=disk_fan(4)
            packet,metadata,bm=product_source(N,2,facets)
            assert surface_is_disk(facets)
            assert compare_product_geometry(packet,metadata,N,2,facets,base_matching=bm)
            scale=2*len(simplex_faces(facets))+4
        functions={'compressed':lambda:compressed_query(packet,N,2,scale),
                   'explicit':lambda:explicit_query(packet),
                   'explicit_control':lambda:explicit_query(packet)}
        warmup={};rounds=[]
        for label in functions:
            elapsed,answer=timed(functions[label]);assert answer[0] and answer[1][0]==1 and not any(answer[1][1:])
            warmup[label]=elapsed
        for round_id in range(7):
            labels=list(functions);rng.shuffle(labels)
            record={'round':round_id,'order':labels}
            for label in labels:
                elapsed,answer=timed(functions[label]);assert answer[0]
                record[label]=elapsed
            rounds.append(record)
        row={'kind':kind,'N':N,'physical_cells':sum(f.hi-f.lo+1 for f in packet.families),
             'families':len(packet.families),'covers':len(packet.covers),'matches':len(packet.matching),
             'warmup':warmup,'rounds':rounds,
             'compressed_median_ms':1000*statistics.median(x['compressed'] for x in rounds),
             'explicit_median_ms':1000*statistics.median(x['explicit'] for x in rounds),
             'median_paired_ratio':statistics.median(x['explicit']/x['compressed'] for x in rounds),
             'AA_control':statistics.median(x['explicit_control']/x['explicit'] for x in rounds)}
        cases.append(row)
        print(kind,N,f"{row['compressed_median_ms']:.4f}ms {row['explicit_median_ms']:.4f}ms ratio {row['median_paired_ratio']:.3f}",flush=True)
    huge=[]
    for bits in [64,1024,4096,16384]:
        N=2**bits+1;facets=disk_fan(4);packet,_,_=product_source(N,2,facets);scale=2*len(simplex_faces(facets))+4
        samples=[]
        for _ in range(7):
            elapsed,answer=timed(lambda:compressed_query(packet,N,2,scale));assert answer[0];samples.append(elapsed)
        p=prepare(packet);inverse=pow(2,-1,N)
        proof=synthesize_modular(p,N,scale,{f.name:-inverse for f in packet.families},
                                 {f.name:N-1 for f in packet.families})
        huge.append({'N_bits':N.bit_length(),'families':len(packet.families),'covers':len(packet.covers),
                     'samples_seconds':samples,'median_ms':1000*statistics.median(samples),
                     'certificate_bytes':len(dumps_certificate(packet,proof).encode()),
                     'explicit_baseline':'not attempted'})
    result={'schema':'modular-morse-benchmark-v1','python':platform.python_version(),
            'platform':platform.platform(),'timer':'perf_counter_ns','rounds_per_case':7,
            'seed':5122026,'native_knot_benchmark':False,
            'scope':'supplied-matching acyclicity and critical-cell counts; source geometry and serialization outside timing',
            'cases':cases,'huge_binary_cases':huge}
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
    lines=[r'\begin{tabular}{lrrrrr}',r'\toprule',r'Source / $N$ & Cells & Compressed ms & Explicit ms & Ratio & A/A\\',r'\midrule']
    for x in cases:
        lines.append(f"{x['kind']} / {x['N']:,} & {x['physical_cells']:,} & {x['compressed_median_ms']:.3f} & {x['explicit_median_ms']:.3f} & {x['median_paired_ratio']:.2f} & {x['AA_control']:.2f} "+r'\\')
    lines +=[r'\bottomrule',r'\end{tabular}']
    (ROOT/'results'/'benchmark_table.tex').write_text('\n'.join(lines)+'\n')
    lines=[r'\begin{tabular}{rrrrr}',r'\toprule',r'Bits in $N$ & Families & Covers & Query ms & Proof bytes\\',r'\midrule']
    for x in huge:
        lines.append(f"{x['N_bits']:,} & {x['families']} & {x['covers']} & {x['median_ms']:.3f} & {x['certificate_bytes']:,} "+r'\\')
    lines +=[r'\bottomrule',r'\end{tabular}']
    (ROOT/'results'/'binary_table.tex').write_text('\n'.join(lines)+'\n')

if __name__=='__main__':main()
