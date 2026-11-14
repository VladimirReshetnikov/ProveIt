"""Sound nonrelational zero-invariant screen for physical register coalescing."""
import json, sys
from collections import deque
from pathlib import Path

def analyze(path):
    data=json.loads(Path(path).read_text())
    ins=data.get('instructions',data) if isinstance(data,dict) else data
    # At each source point, values 0 and 1 denote possible zero/nonzero status.
    status=[None]*len(ins); status[25]=tuple(2 if r==0 else 1 for r in range(9))
    queue=deque([25]); updates=0
    while queue:
        pc=queue.popleft(); vals=list(status[pc]); row=ins[pc]; op=row[0]
        if op=='halt': succ=[]
        elif op=='jump': succ=[(row[1],vals)]
        elif op=='inc':
            vals[row[1]]=2;succ=[(row[2],vals)]
        elif op=='dec':
            r,z,p=row[1:];succ=[]
            if vals[r]&1:
                a=vals.copy();a[r]=1;succ.append((z,a))
            if vals[r]&2:
                a=vals.copy();a[r]=3;succ.append((p,a))
        else:raise ValueError(row)
        for nxt,out in succ:
            joined=tuple(out) if status[nxt] is None else tuple(a|b for a,b in zip(status[nxt],out))
            if joined!=status[nxt]:status[nxt]=joined;queue.append(nxt);updates+=1
    pairs=[]
    for a in range(9):
        for b in range(a+1,9):
            violations=[]
            for pc,row in enumerate(ins):
                if status[pc] is not None and row[0] in ('inc','dec') and row[1] in (a,b):
                    other=b if row[1]==a else a
                    if status[pc][other]!=1:violations.append(pc)
            pairs.append(dict(registers=[a,b],violations=len(violations),examples=violations[:10]))
    return dict(path=str(path),sites=len(ins),reachable=sum(x is not None for x in status),updates=updates,pairs=pairs)

if __name__=='__main__':
    report=[analyze(p) for p in sys.argv[1:]]
    print(json.dumps(report,indent=2))
