#!/usr/bin/env python3
"""Search both-branch state identifications with fixed whole-tape providers.
Evidence is finite and explicitly bounded; no lower-bound conclusion is valid.
"""
from pathlib import Path
import argparse,itertools,json,time,hashlib
from collections import defaultdict
import build221 as b
from local_history_search import contexts,block

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--radius',type=int,default=5);ap.add_argument('--limit',type=int,default=31);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    raw=a.table.read_bytes();start=int(raw.decode('ascii').splitlines()[0].split()[-1])
    T=b.read_table(raw.replace(f'#! start {start}'.encode(),b'#! start 0',1));C=contexts(T,start,a.radius);states=sorted(C);t=time.monotonic();rows={};tot=0
    for i,key in enumerate(sorted(T)):
        q,bit=key;w,d,target=T[key];ms=[m for m in sorted(C[q])if((m>>a.radius)&1)==bit]
        choices={}
        for z in states:
            for direction in (-1,1):
                for write in (0,1):
                    action=(write,direction,z);used=set();dur=set();ok=True
                    for m in ms:
                        r=block(T,q,m,a.radius,action,target,w,d,{q},a.limit)
                        if r is None:ok=False;break
                        dur.add(r[0]);used.update(r[1])
                    if ok:choices[action]=(used,dur)
        rows[key]=choices;tot+=len(choices)
        if(i+1)%50==0:print('rows',i+1,'choices',tot,'seconds',time.monotonic()-t,flush=True)
    survivors=[];pair_bit_counts=defaultdict(int)
    for q,r in itertools.combinations(states,2):
        if q==start or r==start:continue
        opts=[]
        for bit in (0,1):
            shared=set(rows[q,bit])&set(rows[r,bit]);allowed=[]
            for action in sorted(shared):
                used=rows[q,bit][action][0]|rows[r,bit][action][0]
                if any(z in(q,r)for z,bv in used):continue
                allowed.append((action,sorted(used),sorted(rows[q,bit][action][1]|rows[r,bit][action][1])))
            if allowed:pair_bit_counts[bit]+=1
            opts.append(allowed)
        if all(opts):survivors.append(dict(keep=q,drop=r,choices=opts))
    receipt=dict(table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),radius=a.radius,limit=a.limit,contexts=sum(map(len,C.values())),pair_bit_counts=dict(pair_bit_counts),survivors=survivors,seconds=time.monotonic()-t,rows=[dict(key=k,alternatives=[dict(action=a,used=sorted(v[0]),durations=sorted(v[1]))for a,v in d.items()])for k,d in rows.items()])
    a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='rows'},indent=2))
if __name__=='__main__':main()
