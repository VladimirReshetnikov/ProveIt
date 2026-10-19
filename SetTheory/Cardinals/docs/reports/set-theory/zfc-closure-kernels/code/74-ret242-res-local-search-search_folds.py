from pathlib import Path
from collections import defaultdict, deque
from itertools import product
import json, sys, os

SCRIPT_ROOT=Path(__file__).resolve().parent
BASE=Path(os.environ.get('LOCAL_RESULTS',SCRIPT_ROOT))
BASE.mkdir(exist_ok=True,parents=True)
T={}
TABLE_PATH=Path(os.environ.get('LOCAL_TABLE',SCRIPT_ROOT/'base243.tm'))
for line in TABLE_PATH.read_text().splitlines():
    if not line or line.startswith('#'):continue
    q,b,w,d,r=line.split()
    T[int(q),int(b)]=(int(w), 1 if d=='R' else -1,int(r))
Q=sorted({q for q,b in T})

def reachable_windows(k=3):
    width=2*k+1; mask=(1<<width)-1
    seen={q:set() for q in Q}; seen[254]=set()
    # All tapes at the shared old start: weaker than blank initialization.
    todo=deque((95,p) for p in range(mask+1))
    seen[95].update(range(mask+1))
    while todo:
        q,p=todo.popleft()
        if q==254:continue
        b=(p>>k)&1
        w,d,r=T[q,b]
        p=(p&~(1<<k)) | (w<<k)
        vals=(p>>1,(p>>1)|(1<<(width-1))) if d==1 else (((p<<1)&mask),((p<<1)&mask)|1)
        for v in vals:
            if v not in seen[r]:seen[r].add(v);todo.append((r,v))
    return seen

def step(q,h,env,constraints,table=T):
    # Values absent from env are symbolic original input bits named by position.
    val=env.get(h,('x',h))
    if isinstance(val,tuple):
        if val[1] not in constraints:return None
        val=constraints[val[1]]
    if (q,val) not in table:return None
    w,d,r=table[q,val]
    env=dict(env)
    original=constraints.get(h,('x',h))
    if w==original:env.pop(h,None)
    else:env[h]=w
    return r,h+d,env

def trail(q,p,k,limit=12,table=T):
    constraints={i-k:(p>>i)&1 for i in range(2*k+1)}
    env={};h=0
    out=[]
    for n in range(limit):
        z=step(q,h,env,constraints,table)
        if z is None or q==254:return out
        q,h,env=z
        out.append((q,h,tuple(sorted(env.items()))))
        if q==254:return out
    return out

def search(k=3,limit=12):
    seen=reachable_windows(k)
    (BASE/f'windows{k}.json').write_text(json.dumps({q:sorted(v) for q,v in seen.items()}))
    print('windows',k,'total',sum(map(len,seen.values())),'min', sorted((len(p),q) for q,p in seen.items())[:20],flush=True)
    # Compare equality after strictly positive bounded clocks.
    trials={}
    for q in Q:
        trials[q]={p:set(trail(q,p,k,limit)) for p in seen[q]}
    solutions=[]
    for q in Q:
        if q==95:continue
        for r in Q:
            if q==r:continue
            # Cheap pretest on one local window, followed by all allowed windows.
            ok=True
            newT={key:(w,d,r if target==q else target) for key,(w,d,target) in T.items() if key[0]!=q}
            for p in seen[q]:
                a=trials[q][p]
                b=set(trail(r,p,k,limit,newT))
                if not any(x[0]!=q and x in b for x in a):ok=False;break
            if ok:
                solutions.append((q,r))
                print('FOLD',q,r,'windows',len(seen[q]),flush=True)
    return solutions

if __name__=='__main__':
    print(search(int(sys.argv[1]) if len(sys.argv)>1 else 3))
