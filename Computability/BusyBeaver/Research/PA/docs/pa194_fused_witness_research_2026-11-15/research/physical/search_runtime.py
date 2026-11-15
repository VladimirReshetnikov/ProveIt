#!/usr/bin/env python3
"""Screen arithmetic-state pair identifications; finite tests, not proofs."""
from pathlib import Path
from itertools import combinations, product
import json, random, time

HERE=Path(__file__).resolve().parent
raw={}
for line in (HERE/'unfolded201.native.tm').read_text().splitlines():
    q,b,w,d,n=line.split();raw[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
folds=json.loads((HERE/'folds.json').read_text())
alias={a:b for a,b,acts in folds}
newacts={b:[(w,1 if d else -1,n) for w,d,n in acts] for a,b,acts in folds}
M={(q,bit):(w,d,alias.get(n,n)) for (q,bit),old in raw.items() if q not in alias for w,d,n in [newacts[q][bit] if q in newacts else old]}
BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
SK=[51,36,25,48,32,33,22,55,60]
STATES=sorted({q for q,b in M})

def encode(vs,mark=None):
    tape=set();h=0
    for r,v in enumerate(vs):
        h+=1
        tape.update(range(h,h+v+1))
        if r==mark:tape.remove(h)
        h+=v+1
    return tape

def test_cases():
    rng=random.Random(291)
    for vs in ([0]*10, [1]*10, [2]*10, [0,1,2,3,4,4,3,2,1,0], [4,0,3,0,2,0,1,0,0,1]):
        for r in range(9):
            # state, initial ones, expected state/head/ones, category
            yield SK[r],encode(vs),1 if r==0 else 3,-1,encode(vs,r),('mark',r,vs)
            vp=list(vs);vp[r]+=1;vp+=[1]
            yield 64,encode(vs,r),40,-1,encode(vp),('inc',r,vs)
            if vs[r]==0:
                yield 0,encode(vs,r),97,-1,encode(vs),('dec0',r,vs)
            else:
                vp=list(vs);vp[r]-=1
                yield 0,encode(vs,r),40,0,{0}|{x+1 for x in encode(vp)},('decp',r,vs)

def run_case(m,case,aliases={},fuel=5000):
    q,ini,eq,eh,et,tag=case
    q=aliases.get(q,q);eq=aliases.get(eq,eq)
    h=0;t=set(ini)
    for step in range(fuel):
        w,d,q=m.get((q,int(h in t)),(0,0,254))
        if w:t.add(h)
        else:t.discard(h)
        h+=d
        if q==eq and h==eh and t==et:return True
        if q==254 or abs(h)>400:return False
    return False

def merge(a,b,choice):
    acts=[M[(a,b1)] if choice[b1] else M[(b,b1)] for b1 in (0,1)]
    return {(q,bit):(w,d,b if n==a else n) for (q,bit),old in M.items() if q!=a for w,d,n in [acts[bit] if q==b else old]}

def main():
    cases=list(test_cases())
    for c in cases:assert run_case(M,c),c[-1]
    results=[];t0=time.time()
    for a,b in combinations(sorted(BOX),2):
        for choice in product((0,1),repeat=2):
            m=merge(a,b,choice)
            for i,c in enumerate(cases):
                if not run_case(m,c,{a:b}):break
            else:results.append((a,b,choice));print('SURVIVOR',results[-1],flush=True)
    result={'tested_pairs':len(BOX)*(len(BOX)-1)//2,'choices_per_pair':4,'physical_cases':len(cases),'survivors':results,'seconds':time.time()-t0}
    (HERE/'pair_merge_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
