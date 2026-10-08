#!/usr/bin/env python3
"""Compare outputs and measured costs, not like-for-like speedups, of radii 1/2."""
import sys, json, random, statistics, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from cyclic_garside import compress, compress_radius, verify, verify_radius, preprocess

def family(m):
    return (-1,)*m+(3,)*m+(1,)*(m+1)+(-3,)*(m-1)+(2,)

rng=random.Random(202610073)
raw=[];summary=[]
for m in (2,8,32):
    word=family(m)
    for rnd in range(7):
        arms=[1,2];rng.shuffle(arms)
        for radius in arms:
            start=time.perf_counter_ns()
            result=compress(4,word) if radius==1 else compress_radius(4,word,radius=2)
            checker=verify if radius==1 else verify_radius
            checker(4,word,result['certificate'])
            seconds=(time.perf_counter_ns()-start)/1e9
            assert len(result['word']) == (len(word) if radius==1 else 3)
            raw.append(dict(m=m,round=rnd,radius=radius,seconds=seconds,stats=result['stats']))
    row=dict(m=m,n=len(word),radius_one_k=len(word),radius_two_k=3)
    for r in (1,2):
        row[f'radius_{r}_ms']=1000*statistics.median(x['seconds'] for x in raw if x['m']==m and x['radius']==r)
    summary.append(row)
    print(row,flush=True)
    if m in (2,8):
        inp=ROOT/'certificates'/f'rectangle_m{m}.json'
        inp.write_text(json.dumps(dict(strands=4,word=list(word)),indent=2)+'\n')
        result=compress_radius(4,word,radius=2)
        (ROOT/'certificates'/f'rectangle_m{m}_radius2_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
# Separate portfolio rounds: do not label these as a paired speedup estimate.
for row in summary:
    word=family(row['m']); times=[]
    for rnd in range(7):
        start=time.perf_counter_ns()
        result=preprocess(4,word,radius=2)
        times.append((time.perf_counter_ns()-start)/1e9)
        assert len(result['word'])==3
    row['portfolio_ms']=1000*statistics.median(times)
    row['portfolio_seconds']=times
    row['portfolio_stage']=result['stats']['stage']
(ROOT/'data/radius_experiment.json').write_text(json.dumps(dict(seed=202610073,rounds=7,
        whole_recognizer=False,raw=raw,summary=summary,
        portfolio_note='separate seven-round run; includes internal independent replay; not a paired speedup estimate'),indent=2)+'\n')
lines=[r'\begin{tabular}{rrrrrrr}',r'\toprule',r'$m$ & $n$ & $\kappa_1$ & $\kappa_2$ & Radius 1 & Radius 2 & Portfolio \\',r'\midrule']
for row in summary:
    lines.append(f'{row["m"]} & {row["n"]} & {row["radius_one_k"]} & 3 & {row["radius_1_ms"]:.2f} & {row["radius_2_ms"]:.2f} & {row["portfolio_ms"]:.2f} '+r'\\')
lines.extend([r'\bottomrule',r'\end{tabular}'])
(ROOT/'docs/radius_table.tex').write_text('\n'.join(lines)+'\n')
