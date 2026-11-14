#!/usr/bin/env python3
"""Try all pairs folded with one original row from each state."""
import symbolic as S
import time,json,itertools
from pathlib import Path
from collections import defaultdict

def main():
    m=S.load_machine();cs=S.contracts();first=defaultdict(list)
    start=time.monotonic()
    for c in cs:
        i,branch,br,s,t=c
        trace=[];assert S.execute(m,br,s,t,record=trace)
        seen=set()
        for tag,v,row in trace:
            q=v[0]
            if tag=='step' and q not in seen:
                first[q].append((br,v,t,i,branch));seen.add(q)
    protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS}|{S.ROOT,0}
    states=sorted(set(q for q,b in m)-protected)
    hits=[];tested=0
    for q,r in itertools.combinations(states,2):
        if m[q,0]==m[r,0] or m[q,1]==m[r,1]:continue
        for a0,a1 in [(m[q,0],m[r,1]),(m[r,0],m[q,1])]:
            nm={k:(w,d,q if n==r else n) for k,(w,d,n) in m.items() if k[0]!=r}
            nm[q,0]=(a0[0],a0[1],q if a0[2]==r else a0[2])
            nm[q,1]=(a1[0],a1[1],q if a1[2]==r else a1[2])
            if not S.check_engine(nm):continue
            # Both changed row directions considered promptly.
            examples=[]
            for j in range(max(len(first[q]),len(first[r]))):
                for source in (q,r):
                    if j<len(first[source]):examples.append(first[source][j])
            good=True
            for br,v,t,i,branch in examples:
                v=(q,)+v[1:]
                if S.execute(nm,br,v,t,fuel=1024) is None:
                    good=False;break
            tested+=1
            if good:
                print('HIT',q,r,a0,a1,flush=True)
                summary,_=S.verify(nm)
                hits.append((q,r,a0,a1,summary))
                Path(__file__).with_name(f'mixed_{q}_{r}.json').write_text(json.dumps(hits))
                Path(__file__).with_name(f'mixed_{q}_{r}.tm').write_text(''.join(f'{s} {b} {w} {"R" if d==1 else "L"} {t}\n' for (s,b),(w,d,t) in sorted(nm.items())))
        if tested%500==0:print('progress',tested,round(time.monotonic()-start,1),flush=True)
    print('DONE',tested,time.monotonic()-start,json.dumps(hits),flush=True)

if __name__=='__main__':main()
