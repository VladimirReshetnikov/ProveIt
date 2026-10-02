"""Independent literal-seed interval DP versus viable-layer greedy parser."""
from itertools import product
from random import Random
from json import dumps
rng=Random(20261001)
counts=dict(automata=0,nonempty_slices=0,rank_comparisons=0)

def image(mask, rows):
    z=0
    for q,r in enumerate(rows):
        if mask>>q&1:z|=r
    return z

def check(rows,I,F,max_n):
    s=len(rows[0]); E=[rows[0][q]|rows[1][q] for q in range(s)]
    counts['automata']+=1
    for n in range(1,max_n+1):
        words=list(product(range(2),repeat=n))
        seeds=[]
        for w in words:
            z=I
            for c in w:z=image(z,rows[c])
            if z&F:seeds.append(w)
        if not seeds:continue
        counts['nonempty_slices']+=1
        alph=[sorted({w[i] for w in seeds}) for i in range(n)]
        # Oracle: literal slices of accepted seeds; no viable-layer computations.
        intervals={(i,j):{w[i:j] for w in seeds} for i in range(n) for j in range(i+1,n+1)}
        P=[I]
        for _ in range(n):P.append(image(P[-1],E))
        R=[F]
        for _ in range(n):R.append(sum(1<<q for q in range(s) if E[q]&R[-1]))
        S=[P[i]&R[n-i] for i in range(n+1)]
        for w in product(*alph):
            dp=[0]+[n+1]*n
            for j in range(1,n+1):
                dp[j]=min(dp[i]+1 for i in range(j) if w[i:j] in intervals[i,j])
            z=S[0]; rank=1
            for i,c in enumerate(w):
                nxt=image(z,rows[c])&S[i+1]
                if not nxt:
                    rank+=1;nxt=image(S[i],rows[c])&S[i+1]
                assert nxt
                z=nxt
            assert rank==dp[n], (rows,I,F,w,rank,dp[n])
            counts['rank_comparisons']+=1

# All epsilon-free binary NFAs on two states, all nonempty initial/final sets.
for a in product(range(4),repeat=2):
    for b in product(range(4),repeat=2):
        for I in range(1,4):
            for F in range(1,4):check((a,b),I,F,6)
# Seeded larger random NFAs.
for s in [3,4,5]:
    for _ in range(100):
        rows=tuple(tuple(rng.randrange(1<<s) for _ in range(s)) for _ in range(2))
        check(rows,rng.randrange(1,1<<s),rng.randrange(1,1<<s),8)
print(dumps({'status':'PASS','random_seed':20261001,**counts}, indent=2))
