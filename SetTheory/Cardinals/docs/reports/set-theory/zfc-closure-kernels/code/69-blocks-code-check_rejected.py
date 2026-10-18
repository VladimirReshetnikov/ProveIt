#!/usr/bin/env python3
"""Check the exact rejected tables and the unconditional three-step tail trap."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]

def read(path):
    table={}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split()
        key=(int(q),int(b))
        assert key not in table
        assert b in ('0','1') and w in ('0','1') and d in ('L','R')
        table[key]=(int(w),1 if d=='R' else -1,int(t))
    states={q for q,b in table}
    assert set(table)=={(q,b) for q in states for b in (0,1)}
    assert all(t in states|{254} for w,d,t in table.values())
    return table

def main():
    if not __debug__:raise SystemExit('Assertions required.')
    base=read(ROOT/'reference/context246/machine/zfc_prefix246_old.tm')
    trap=read(ROOT/'rejected/tail_trap245.tm')
    detector=read(ROOT/'rejected/short_detector245.tm')
    expected={k:v for k,v in base.items() if k[0]!=255}
    expected[75,0]=(0,1,63);expected[48,0]=(1,-1,131)
    assert trap==expected and len(trap)==490
    expected={k:v for k,v in base.items() if k[0]!=74}
    expected[58,0]=(0,-1,84)
    assert detector==expected and len(detector)==490
    closed={48,63,112,131}
    assert all(trap[q,b][1]==-1 and trap[q,b][2] in closed for q in closed for b in (0,1))
    q,h,ones=95,0,set();prefix=[(q,h)]
    for _ in range(3):
        w,d,q=trap[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d;prefix.append((q,h))
    assert prefix==[(95,0),(109,1),(75,2),(63,3)]
    assert q in closed and 254 not in closed
    out=dict(status='PASS',tail_states=len(trap)//2,detector_states=len(detector)//2,
        tail_prefix=prefix,closed_set=sorted(closed),
        statement='The tail table is unconditionally nonhalting by finite-control induction; it is not a consistency-machine solution.')
    (ROOT/'results/rejected-table-check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
