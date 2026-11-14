#!/usr/bin/env python3
"""Optional finite search over one-row spare-tail replacements for Runtime193.

Each candidate starts at native198 on cell0, with ones at-3 and-1, all
other cells to the right blank, and an arbitrary prefix left of-3. Reading
that prefix is forbidden. An accepted path returns to40 at-3 and leaves a
valid finite unary register list to its right. This experiment is not a
blank-initialization proof and the finite negative results are not a lower
bound. See README.md for the exact domain and default bounds.
"""
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parents[1]

def search(table_path,steps,head_limit):
    rows={}
    for ln in table_path.read_text().splitlines():
        if not ln.strip() or ln.lstrip().startswith('#'):continue
        q,b,w,d,n=ln.split()
        rows[int(q),int(b)]=int(w),1 if d=='R' else -1,int(n)
    states=sorted({q for q,b in rows})
    hits=[]
    stats={}
    for n in states:
        for w in (0,1):
            for d in (-1,1):
                act=w,d,n
                rows[198,0]=act
                q,h,ones=198,0,{-3,-1}
                seen=set()
                trace=[]
                status='bound'
                for k in range(steps):
                    if k and q==40 and h==-3:
                        if not ones or min(ones)!=-3 or -2 in ones:
                            status='bad-prefix';break
                        tail=sorted(ones-{-3})
                        vals=[]
                        pos=-1
                        while tail:
                            if tail[0]!=pos:break
                            length=1
                            while length<len(tail) and tail[length]==pos+length:
                                length+=1
                            vals.append(length-1)
                            pos+=length+1
                            tail=tail[length:]
                        if tail:
                            status='bad-tail';break
                        hits.append({'action':act,'steps':k,'appended':vals,'trace':trace})
                        status='valid';break
                    if h < -3 or h > head_limit or q==254:
                        status='outside';break
                    key=q,h,tuple(sorted(ones))
                    if key in seen:
                        status='loop';break
                    seen.add(key)
                    b=int(h in ones)
                    ww,dd,nn=rows[q,b]
                    trace.append([q,h,b,ww,dd,nn])
                    (ones.add if ww else ones.discard)(h)
                    q=nn;h+=dd
                stats[status]=stats.get(status,0)+1
    return {'tested':4*len(states),'hits':hits,'classification':stats,
            'steps_bound':steps,'right_head_limit':head_limit,
            'scope':'Tail198/0 on blank suffix after101; permits any finite appended register-value list; preserves arbitrary prefix left of-3.'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--table',type=Path,default=ROOT/'inputs/runtime193.native.tm')
    p.add_argument('--steps',type=int,default=100)
    p.add_argument('--head-limit',type=int,default=100)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.steps<=0 or a.head_limit<0:p.error('Bounds must be positive/nonnegative')
    result=search(a.table,a.steps,a.head_limit)
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'tested':result['tested'],'classification':result['classification'],
                     'hits':[{'action':x['action'],'steps':x['steps'],'appended':x['appended']} for x in result['hits']]},indent=2))

if __name__=='__main__':main()
