#!/usr/bin/env python3
"""Run bounded causal depth-three search at every non-initial native state.

Native74 has a separately completed depth-three search. Every other state
gets a 5-million-transition budget. Reaching the budget is inconclusive.
"""
from pathlib import Path
import json,subprocess,concurrent.futures,time
HERE=Path(__file__).resolve().parent
OUT=HERE/'causal_all';OUT.mkdir(exist_ok=True)
states=sorted({int(line.split()[0])for line in (HERE/'runtime193.native.tm').read_text().splitlines()if line.strip()})
def job(q):
    args=[str(HERE/'causal_startup'),str(HERE/'runtime193.native.tm'),str(HERE/'expanded_edits.tsv'),str(HERE/'templates.tsv'),'200000','3',str(q),'100000',str(OUT/f'hits_{q}.jsonl'),'5000000']
    p=subprocess.run(args,capture_output=True,text=True,check=True)
    r=json.loads(p.stdout);(OUT/f'result_{q}.json').write_text(json.dumps(r,indent=2)+'\n')
    if p.stderr:(OUT/f'log_{q}.txt').write_text(p.stderr)
    return r
t0=time.time();results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=4)as pool:
    for r in pool.map(job,[q for q in states if q!=74]):
        results.append(r)
        if len(results)%20==0 or r['frame_hits']:print('completed',len(results),'last',r['start'],'hits',r['frame_hits'],'seconds',time.time()-t0,flush=True)
results.append(json.loads((HERE/'causal3_result.json').read_text()));results.sort(key=lambda x:x['start'])
summary={'working_starts':len(states),'all_starts_examined':len(results),'depth':3,'fuel_per_run':200000,'per_start_transition_budget_except74':5000000,'results':results}
for k in ['simulations','transitions','halts','outward_rays','bounded','frame_hits']:summary['total_'+k]=sum(r[k]for r in results)
summary['capped_starts']=[r['start']for r in results if r.get('cap_reached')or r.get('transition_cap_reached')]
summary['seconds_this_batch']=time.time()-t0
(HERE/'causal_all_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items()if k!='results'},indent=2))
