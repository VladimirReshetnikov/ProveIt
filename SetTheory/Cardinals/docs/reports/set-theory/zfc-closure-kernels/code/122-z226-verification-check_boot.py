#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import argparse, hashlib, json
from verify_runtime import read_table

def run(p, target=None, fixed_steps=None):
    t,start,halt=read_table(p);q=start;h=0;ones=set();used=Counter();guard=[]
    for tick in range(2000001):
        matched = (tick == fixed_steps) if fixed_steps is not None else (tick and (q,h,ones)==target)
        if matched:
            return dict(file=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),steps=tick,
                state=q,head=h,one_cells=sorted(ones),ones=len(ones),visited_rows=[[*k,v] for k,v in sorted(used.items())],
                guard140_violations=guard)
        if q==halt:raise AssertionError(('startup halted',p,tick))
        if tick==2000000:raise AssertionError('no finite startup certificate')
        b=int(h in ones)
        if q==140 and b==1 and h+1 not in ones:guard.append(tick)
        used[q,b]+=1;w,d,q=t[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('tables',type=Path,nargs='+');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    base=run(a.tables[0],fixed_steps=408419)
    results=[base]+[run(p,(base['state'],base['head'],set(base['one_cells']))) for p in a.tables[1:]]
    for r in results:
        assert (r['state'],r['head'],r['one_cells'])==(base['state'],base['head'],base['one_cells'])
        assert r['ones']==351
    result=dict(status='EXACT_BLANK_STARTUP_COMMON_WHOLE_FRAME',tables=results)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in r.items() if k not in ('one_cells','visited_rows')} for r in results],indent=2))
if __name__=='__main__':main()
