"""Same-code A/B/A ablation: singleton crossing runs vs maximal signed runs.

Both sides use twistkh.core, identical budgets, bitset ranks, and map routines.
Only local block decomposition changes. This is NOT the upstream scanner.
"""
import json
import platform
import statistics as st
import sys
import time
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from twistkh import Run, homology, runs_from_word

old=json.loads(Path('results/benchmark.json').read_text())
rows=[]
for case in old['comparisons']:
    b,w=case['strands'],case['word']
    singleton=tuple(Run(abs(x),1 if x>0 else -1) for x in w)
    grouped=runs_from_word(b,w)
    def a(): return homology(b,singleton)
    def z(): return homology(b,grouped)
    first=a();second=z();assert first['by_degree']==second['by_degree']
    timings=[]
    for j in range(7):
        d={}
        for name,fn in ([('A1',a),('B',z),('A2',a)] if j%2==0 else [('A2',a),('B',z),('A1',a)]):
            t=time.perf_counter();r=fn();d[name]=time.perf_counter()-t
            assert r['by_degree']==second['by_degree']
        d['B_over_A']=d['B']/((d['A1']+d['A2'])/2)
        d['AA_ratio']=d['A2']/d['A1'];timings.append(d)
    row={'name':case['name'],'strands':b,'word':w,'n':len(w),'t':len(grouped),
         'singleton_basis':first['stats']['basis'],'grouped_basis':second['stats']['basis'],
         'rank':second['reduced_rank'],'singleton_stats':first['stats'],'grouped_stats':second['stats'],
         'median_A_seconds':st.median((d['A1']+d['A2'])/2 for d in timings),
         'median_B_seconds':st.median(d['B'] for d in timings),
         'median_B_over_A':st.median(d['B_over_A'] for d in timings),
         'median_AA_ratio':st.median(d['AA_ratio'] for d in timings),'raw_rounds':timings}
    rows.append(row)
    print(row['name'],row['median_A_seconds'],row['median_B_seconds'],row['median_B_over_A'],flush=True)
Path('results/ablation.json').write_text(json.dumps({'python':sys.version,'platform':platform.platform(),
    'rounds_per_case':7,'baseline':'same macro backend with every crossing a separate run; NOT upstream fastunknot',
    'rows':rows},indent=2)+'\n')
