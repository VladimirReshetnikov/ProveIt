#!/usr/bin/env python3
"""Find a complete admissible root frame, then independently replay its prefix.

Search is finite; a PASS records every nonzero tape cell and an exact step count.
The sparse/dense implementations independently construct the transition tables.
"""
from pathlib import Path
import argparse
import hashlib
import json

PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('table', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--limit', type=int, default=2000000)
    a = ap.parse_args()
    table = {}
    for line in a.table.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q,b,w,d,t = line.split()
        key = int(q),int(b)
        assert key not in table
        table[key] = int(w), (1 if d=='R' else -1), int(t)
    states = {q for q,b in table}
    assert len(table)==2*len(states)
    assert {t for w,d,t in table.values()}-states == {254}
    ones = set()
    q,h = start,0
    used = {}
    for steps in range(a.limit+1):
        if q == 96 and ones and min(ones)==h-1:
            right = sorted(x for x in ones if x >= h)
            if right and right[0]-h>=64:
                header,maximum = right[0],right[-1]
                p=header+1
                values=[]
                good=True
                while p<=maximum:
                    if p in ones or p+1 not in ones:
                        good=False
                        break
                    j=p+1
                    while j in ones:
                        j+=1
                    values.append(j-p-2)
                    p=j
                if good and len(values)>=10:
                    logical=[values[i] for i in PHYSICAL]
                    if logical[1]==logical[2]==logical[5]==0:
                        break
        if q==254:
            raise AssertionError(('HALTED_BEFORE_FRAME',steps))
        bit=int(h in ones)
        used[q,bit]=used.get((q,bit),0)+1
        w,d,q=table[q,bit]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h+=d
    else:
        raise AssertionError(('NO_FRAME_IN_BOUND',a.limit,q,h,len(ones)))
    cells=bytearray(2*steps+3)
    offset=steps+1
    position=offset
    state=start
    flat={}
    for line in a.table.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        s,b,w,d,t=line.split()
        flat[2*int(s)+int(b)]=int(w),d,int(t)
    for _ in range(steps):
        w,d,state=flat[2*state+cells[position]]
        cells[position]=w
        position += (1 if d=='R' else -1)
    other=[i-offset for i,b in enumerate(cells) if b]
    assert (state,position-offset,other)==(q,h,sorted(ones))
    result=dict(status='PASS_EXACT_TWO_INTERPRETER_BOOT',
                table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),
                working_states=len(states), start=start, steps=steps,
                dispatcher=q, head=h, marker=h-1, header=header,
                header_distance=header-h, pc='',
                physical_registers=values[:9], logical_registers=logical,
                spare_values=values[9:], spare_count=len(values)-9,
                one_count=len(ones), all_one_positions=sorted(ones),
                used_rows=[[s,b,n] for (s,b),n in sorted(used.items())],
                all_other_cells_zero=True, independent_sparse_dense_agreement=True,
                scope='Exact finite blank initialization. Runtime and source/logical correspondence are separate obligations.')
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('all_one_positions','spare_values','used_rows')},indent=2))

if __name__=='__main__':
    main()
