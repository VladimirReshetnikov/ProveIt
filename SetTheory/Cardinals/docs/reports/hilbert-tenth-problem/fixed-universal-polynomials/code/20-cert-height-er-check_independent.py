#!/usr/bin/env python3
"""Bounded corroboration only; no upstream code/schedules are imported or run."""
import hashlib, json, math
from pathlib import Path

ROOT = Path(__file__).resolve().parent

def pell(a,n):
    x,y=1,0
    for _ in range(n):
        x,y=a*x+(a*a-1)*y,x+a*y
    return x,y

def need(x,msg):
    if not x: raise RuntimeError(msg)

counts={}
# Every residue in a complete known 4m period; parity-separated sets.
cases=0
for a in range(2,15):
    for m in range(1,36):
        F=pell(a,m)[0]
        sets=[set(),set()]
        x,y=1,0
        for n in range(4*m):
            sets[n%2].add(y%F)
            sets[n%2].add((-y)%F)
            x,y=(a*x+(a*a-1)*y)%F,(x+a*y)%F
        need(not sets[0].intersection(sets[1]),('parity intersection',a,m))
        for parity in (0,1):
            reps={eps*pell(a,j)[1]%F for j in range(m+1) if j%2==parity for eps in (-1,1)}
            need(reps==sets[parity],('representatives',a,m,parity))
        cases+=1
counts['full_period_residue_parity_cases']=cases
# Coprimality needed for auxiliary-square normalization.
cases=0
for a in range(2,22,2):
    for e in range(1,24,2):
        C=pell(a,e)[1]
        for m in range(1,61):
            need(math.gcd(pell(a,m)[0],C)==1,('gcd failed',a,e,m))
            cases+=1
counts['odd_index_coprimality_cases']=cases
# Strong lattice and unit obstruction for composites A=chi_a(e).
cases=0
for a in range(2,12,2):
    for e in (1,3,5,7):
        A,C=pell(a,e)
        D=A*A-1
        for m in range(1,14):
            f,bm=pell(a,m);S=(a*a-1)*C*bm
            need(D*f*f-S*S==D,('strong identity',a,e,m))
            # All odd t modulo known period 4m of the fundamental residue.
            for p in (2,4,6,8):
                c=pell(A,p)[1]
                for t in range(1,4*m,2):
                    q=pell(A,t)[1]%f
                    need((q+c)%f!=0 and (q-c)%f!=0,('unit obstruction failed',a,e,m,p,t))
                    cases+=1
counts['nonsquarefree_lattice_residue_cases']=cases
# Explicit counterexample to the naive original-A lattice assertion.
need(675*2*2-45*45==675,'nonsquarefree example')
need(pell(2,3)==(26,15),'fundamental nesting example')
# Exhaustive small positive factor products. These do not prove the theorem.
cases=0;hits=[]
for A in (4,6,8,10,12,14):
    D=A*A-1
    for f in range(1,41):
        # Every S with |Ns|<=D, a necessary consequence of Na Ns=D.
        lo=max(1,math.isqrt(max(0,D*f*f-D)))
        hi=math.isqrt(D*f*f+D)
        for S in range(lo,hi+1):
            Ns=D*f*f-S*S
            if not Ns or D%Ns:continue
            Na=D//Ns
            # Positive branch predicted only Ns=D; negative only f1,SA.
            if Na>0:
                z=math.isqrt(Na)
                # Na must be square if an auxiliary solution exists, so filter this necessary condition.
                if z*z==Na:
                    need(z==1,('positive strong divisor found',A,f,S,Na,Ns))
            else:
                # The source sign lemma also requires |Na|>=S²−1.
                if -Na>=S*S-1:
                    need((f,S,Na,Ns)==(1,A,-D,-1),('negative branch failed',A,f,S,Na,Ns))
            cases+=1
counts['small_strong_divisor_candidates']=cases
result={'status':'PASS','scope':'bounded arithmetic corroboration only; source authentication is separate and the unbounded theorem is proved in PROOF.md','counts':counts}
print(json.dumps(result,indent=2))
