#!/usr/bin/env python3
"""Search direct folds using exact symbolic source contracts."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import symbolic as S
import time,json,pickle
from pathlib import Path
from collections import defaultdict

def main():
    m=S.load_machine();m[125,0]=(0,-1,39);S.check_engine=lambda n:all(n.get(k)==m[k]for k in S.ENGINE_ROWS);cs=S.contracts();first=defaultdict(list)
    start=time.monotonic()
    for c in cs:
        i,branch,br,s,t=c
        trace=[];assert S.execute(m,br,s,t,record=trace)
        seen=set()
        for tag,v,row in trace:
            q=v[0]
            if tag=='step' and q not in seen:
                first[q].append((br,v,t,i,branch));seen.add(q)
    protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS}|{S.ROOT}
    states=sorted(set(q for q,b in m))
    hits=[];tested=0
    for q in states:
        if q in protected:continue
        examples=first[q]
        for r in states:
            if r==q:continue
            nm={k:(w,d,r if n==q else n) for k,(w,d,n) in m.items() if k[0]!=q}
            if not S.check_engine(nm):continue
            # Diverse branches first, then all remaining contexts.
            good=True
            for br,v,t,i,branch in examples:
                v=(r,)+v[1:]
                if S.execute(nm,br,v,t,fuel=1024) is None:
                    good=False;break
            tested+=1
            if good:
                print('HIT',q,r,flush=True)
                Path(__file__).with_name(f'append_zero_direct_{q}_{r}.tm').write_text(''.join(f'{u} {b} {w} {"R" if d==1 else "L"} {v}\n'for(u,b),(w,d,v)in sorted(nm.items())))
                summary,_=S.verify(nm)
                hits.append((q,r,summary))
                Path(__file__).with_name(f'direct_{q}_{r}.json').write_text(json.dumps(hits))
        print('state',q,'tested',tested,'elapsed',round(time.monotonic()-start,1),flush=True)
    print('DONE',json.dumps(hits),flush=True)

if __name__=='__main__':main()
