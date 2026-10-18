#!/usr/bin/env python3
"""Delete any noninitial state with one nonself incoming edge, rewriting it."""
import sys,json,time,random,itertools,argparse
from collections import defaultdict
from search_repair import HERE,BASE,base,run,compiler,cases
from search_rotated_merges import macro_check

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--original',action='store_true');args=ap.parse_args()
    start=time.monotonic()
    if args.original:n,r,t=compiler.load();cc=list(cases(n,r))
    else:
        n,r,t,cc=base()
        t['218',0]=(0,'R','105');t['208',0]=(0,'R','23');t['208',1]=(1,'R','70');t['237',0]=(0,'R','208')
    states=sorted({q for q,b in t},key=int);byq={q:[] for q in states}
    rr=random.Random(274299);rr.shuffle(cc)
    tracked=compiler.Tracking(t)
    for i,c in enumerate(cc):
        tracked.used.clear();run(tracked,c)
        for q in {q for q,b in tracked.used}:byq[q].append(i)
    incoming=defaultdict(list)
    for k,(w,d,q) in t.items():
        if q!=k[0]:incoming[q].append(k)
    results=[];tested=affinepass=0
    for q in sorted(states,key=lambda x:(x!='208',int(x))):
        if q in ('95','96') or len(incoming[q])!=1 or not byq[q]:continue
        edge=incoming[q][0];u={k:v for k,v in t.items() if k[0]!=q}
        survivors=[]
        for w,d,r in itertools.product((0,1),('L','R'),states):
            if r==q:continue
            tested+=1;u[edge]=(w,d,r)
            try:
                for i in byq[q]:run(u,cc[i])
            except (AssertionError,KeyError):continue
            affinepass+=1
            try:macro_check(u)
            except (AssertionError,KeyError):continue
            print('PROVISIONAL PASS',q,edge,(w,d,r),flush=True)
            survivors.append((w,d,r))
            (HERE/f'{"original" if args.original else "rotated"}245_incoming_{q}_{edge[0]}_{edge[1]}_{w}{d}{r}.tm').write_text('#! start 95\n'+''.join(f'{v} {b} {x} {m} {s}\n' for (v,b),(x,m,s) in sorted(u.items(),key=lambda kv:(int(kv[0][0]),kv[0][1]))))
        results.append(dict(deleted=q,incoming=edge,survivors=survivors))
        if len(results)%15==0:print('progress',len(results),q,tested,affinepass,'seconds',round(time.monotonic()-start,2),flush=True)
    report=dict(scope='All four write/direction choices and retained state targets replacing the unique nonself incoming edge of every noninitial, affine-visited working state in the selected correct 246 table; 1500 affine-rule fuel and independent macro proof replay.',original=args.original,tested=tested,affine_pass=affinepass,results=results,seconds=time.monotonic()-start)
    (HERE/f'{"original" if args.original else "rotated"}_single_incoming_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2),flush=True)

if __name__=='__main__':main()
