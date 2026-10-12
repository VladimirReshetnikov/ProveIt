"""Paired local representation queries, not native knot-recognition timings.

Both arms receive the same supplied affine source atlas. Encoded: construct,
independently replay, serialize all flag charts. Literal: construct every flag
cell, check ordered/regular face incidences, serialize. Source construction,
cleanup and result comparisons are outside timers. A/A runs identical literal
arms. Convex-catalog caches are warmed for all arms.
"""
from pathlib import Path
import time,random,statistics,json,sys,platform,gc
from atlas import simplex,dumps
from sources import polytope_ball,product_with_line
from flags import compile_flags,certificate_data,inventory
from replay import verify
from reference import literal_flags,regular_check,explicit_serializable,compare_compiled
ROOT=Path(__file__).resolve().parents[1]


def encoded(a):
    c=compile_flags(a)
    if not verify(a,c): raise AssertionError('symbolic replay failed')
    text=dumps(certificate_data(c))
    return inventory(c.result)['cell_counts'],len(text.encode())


def literal(a):
    data=literal_flags(a,cap=300000)
    regular_check(data[0],data[1])
    text=dumps(explicit_serializable(data))
    counts=[sum(d==j for d in data[0].values()) for j in range(4)]
    return counts,len(text.encode())


def timed(fn,a):
    gc.collect(); start=time.perf_counter(); result=fn(a); elapsed=time.perf_counter()-start
    return elapsed,result


def main():
    rng=random.Random(2026101202); rows=[]; all_samples=[]
    for n in (1,4,16,64,256):
        a=product_with_line(polytope_ball(simplex(2)),n,True)
        samples=[]
        # A complete independent equality check before measuring either format.
        compare_compiled(a,compile_flags(a),cap=300000)
        for trial in range(-1,5):
            order=['encoded','literal_A','literal_B']; rng.shuffle(order); outcome={}
            for name in order:
                elapsed,result=timed(encoded if name=='encoded' else literal,a)
                outcome[name]={'seconds':elapsed,'cell_counts':result[0],'serialized_bytes':result[1]}
            assert outcome['encoded']['cell_counts']==outcome['literal_A']['cell_counts']==outcome['literal_B']['cell_counts']
            assert outcome['literal_A']['serialized_bytes']==outcome['literal_B']['serialized_bytes']
            sample={'segments':n,'trial':trial,'order':order,**outcome}
            all_samples.append(sample)
            if trial>=0: samples.append(sample)
        row={'segments':n,'represented_cells':196*n,
             'encoded_median_seconds':statistics.median(s['encoded']['seconds'] for s in samples),
             'literal_median_seconds':statistics.median(s['literal_A']['seconds'] for s in samples),
             'paired_literal_over_encoded':statistics.median(s['literal_A']['seconds']/s['encoded']['seconds'] for s in samples),
             'paired_A_over_B':statistics.median(s['literal_A']['seconds']/s['literal_B']['seconds'] for s in samples),
             'encoded_bytes':samples[0]['encoded']['serialized_bytes'],'literal_bytes':samples[0]['literal_A']['serialized_bytes']}
        rows.append(row); print(json.dumps(row),flush=True)
    stress=[]
    for b in (64,1024,4096,16384):
        a=product_with_line(polytope_ball(simplex(2)),(1<<b)+1,True)
        encoded(a); trials=[]
        for _ in range(5):
            elapsed,result=timed(encoded,a); trials.append(elapsed)
        stress.append({'rank_bound_bits':b+1,'families':196,'charts':1289,'median_seconds':statistics.median(trials),
                       'seconds':trials,'serialized_bytes':result[1]})
    report={'python':sys.version,'platform':platform.platform(),'seed':2026101202,
            'benchmark_scope':__doc__,'rows':rows,'samples':all_samples,'binary_stress':stress,
            'pilot_limitation':'An earlier 1024-layer pre-timing literal equality check exceeded a 200-second whole-command limit; see benchmark_pilot_partial.txt. No 1024-layer timing is reported.',
            'all_trials_finished':True,'knot_recognition_speedup_claimed':False}
    (ROOT/'results/benchmark.json').write_text(json.dumps(report,indent=2)+'\n')
    tex=['\\begin{tabular}{rrrrrr}\\toprule',
         '$N$ & Cells & Encoded (ms) & Literal (ms) & Ratio & A/A\\\\\\midrule']
    for r in rows:
        tex.append(f"{r['segments']:,} & {r['represented_cells']:,} & {r['encoded_median_seconds']*1000:.2f} & {r['literal_median_seconds']*1000:.2f} & {r['paired_literal_over_encoded']:.2f} & {r['paired_A_over_B']:.2f}\\\\")
    tex.append('\\bottomrule\\end{tabular}')
    (ROOT/'results/timing_table.tex').write_text('\n'.join(tex)+'\n')
    tex=['\\begin{tabular}{rrrr}\\toprule','Rank bits & Families / charts & Query (ms) & Serialized bytes\\\\\\midrule']
    for r in stress:
        tex.append(f"{r['rank_bound_bits']:,} & 196 / 1289 & {r['median_seconds']*1000:.2f} & {r['serialized_bytes']:,}\\\\")
    tex.append('\\bottomrule\\end{tabular}')
    (ROOT/'results/stress_table.tex').write_text('\n'.join(tex)+'\n')

if __name__=='__main__': main()
