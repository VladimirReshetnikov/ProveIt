import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
"""Filter numerical engine survivors with symbolic external instruction paths.
This is a screen, not a universal proof of the changed engine contracts.
"""
import core
from core import *
from collections import defaultdict
import time
base,labels=machine();cs=contracts()
uses=defaultdict(set)
for ci,c in enumerate(cs):
    run(base,c,observe=lambda s:uses[s[0]].add(ci))
opts=[]
for line in Path('tail_search.log').read_text().splitlines():
    z=re.match(r'SURVIVOR (\d+) -> (\d+) choice (\d+)',line)
    if z:opts.append(tuple(map(int,z.groups())))
print('candidates',len(opts),flush=True)
surv=[];start=time.monotonic()
for j,(a,b,choice) in enumerate(opts):
    def al(q):return b if q==a else q
    if len({al(q) for q in SK})!=len(SK) or al(64)==al(0):continue
    rows={}
    for (q,bit),act in base.items():
        if q==a:continue
        if q==b:act=base[a if choice>>bit&1 else b,bit]
        w,d,n=act;rows[q,bit]=w,d,al(n)
    def oracle(q,br,x):
        _,kind,r=x
        if kind=='none':
            for rr,qq in enumerate(SK):
                if q==al(qq):return al(1 if rr==0 else 3),('x','mark',rr),False
        if kind=='mark' and r<9:
            if q==al(64):return al(40),('x','inc',r),False
            if q==al(0) and br is not None and br[0]==r:
                return (al(97),PLAIN,False) if br[1] else (al(40),('x','dec',r),True)
    core.oracle=oracle
    def conv(c):
        i,br,s,t=c
        return i,br,(al(s[0]),*s[1:]),None if t is None else(al(t[0]),*t[1:])
    priority=list(uses[b])+list(uses[a]-uses[b])
    ok=all(run(rows,conv(cs[k])) is not None for k in priority)
    if ok:ok=all(run(rows,conv(c)) is not None for c in cs)
    if ok:
        print('SURVIVOR',a,b,choice,flush=True);surv.append([a,b,choice])
        Path('tail_symbolic_survivors.json').write_text(json.dumps(surv,indent=2))
    if j%500==0:print('progress',j,'seconds',time.monotonic()-start,flush=True)
Path('tail_filter_result.json').write_text(json.dumps({'candidates':len(opts),'survivors':surv,'elapsed_seconds':time.monotonic()-start},indent=2))
