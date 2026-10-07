"""Interleaved A/B/A microbenchmark against the INCLUDED crossing-cube reference.

This is NOT a benchmark against ProveIt's optimized fastunknot scanner.
No simplification, filters, free cancellation, or d^2 checking is timed.
All timings are elapsed seconds; raw rounds and deterministic dimensions are saved.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
import statistics as st
import sys
import time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from twistkh import homology, runs_from_word
from twistkh.reference import cube_homology
from twistkh.preflight import basis_size


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--rounds',type=int,default=7)
    args=parser.parse_args()
    if args.rounds<3: parser.error('at least three rounds are required')
    cases=[('T(2,3)',2,[1]*3),('T(2,5)',2,[1]*5),('T(2,7)',2,[1]*7),('T(2,9)',2,[1]*9),
           ('mixed-3-strand-8',3,[1]*3+[-2]*3+[1,2]),
           ('mixed-4-strand-9',4,[1]*3+[-2]*3+[3]*3),
           ('alternating-3-strand-8',3,[1,-2]*4)]
    rows=[]
    for name,b,w in cases:
        r=runs_from_word(b,w)
        def a(): return cube_homology(b,w,check_d2=False)
        def z(): return homology(b,r,check_d2=False)
        old=a();new=z()
        assert old['by_degree']==new['by_degree']
        rounds=[]
        for j in range(args.rounds):
            times={}
            for label,fn in ([('A1',a),('B',z),('A2',a)] if j%2==0 else [('A2',a),('B',z),('A1',a)]):
                t=time.perf_counter();out=fn();times[label]=time.perf_counter()-t
                assert out['by_degree']==new['by_degree']
            times['B_over_A']=times['B']/((times['A1']+times['A2'])/2)
            times['AA_ratio']=times['A2']/times['A1']
            rounds.append(times)
        ratios=[x['B_over_A'] for x in rounds]
        row={'name':name,'strands':b,'word':w,'n':len(w),'t':len(r),
             'cube_basis':old['basis'],'macro_basis':new['stats']['basis'],
             'cube_states':old['cube_states'],'macro_states':new['stats']['macro_states'],
             'cube_entries':old['entries'],'macro_entries':new['stats']['differential_entries'],
             'reduced_rank':new['reduced_rank'],'components':new['components'],
             'median_cube_seconds':st.median((x['A1']+x['A2'])/2 for x in rounds),
             'median_macro_seconds':st.median(x['B'] for x in rounds),
             'median_B_over_A':st.median(ratios),'min_B_over_A':min(ratios),'max_B_over_A':max(ratios),
             'median_AA_ratio':st.median(x['AA_ratio'] for x in rounds),'raw_rounds':rounds}
        rows.append(row)
        print(name,row['cube_basis'],row['macro_basis'],row['median_B_over_A'],flush=True)
    long=[]
    for m in (101,1001,10001):
        from twistkh import Run
        result=homology(2,[Run(1,m)],check_d2=True)
        assert result['reduced_rank']==m
        long.append({'name':f'T(2,{m})','rank':m,'stats':result['stats'],'seconds':result['seconds'],
                     'd_squared_checked':True,'preflight':basis_size(2,[Run(1,m)])})
    report={'python':sys.version,'platform':platform.platform(),'rounds_per_case':args.rounds,
            'baseline':'included independent exponential crossing-cube reference, NOT fastunknot',
            'timed_d_squared':False,'comparisons':rows,'macro_only_long_runs':long}
    Path('results/benchmark.json').write_text(json.dumps(report,indent=2)+'\n')
    fields=[k for k in rows[0] if k not in ('word','raw_rounds')]
    with open('results/benchmark.csv','w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
        writer.writerows({k:r[k] for k in fields} for r in rows)

if __name__=='__main__': main()
