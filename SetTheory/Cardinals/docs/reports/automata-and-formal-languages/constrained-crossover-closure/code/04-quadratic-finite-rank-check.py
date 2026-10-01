#!/usr/bin/env python3
"""Independent finite audits of the quadratic finite-rank construction."""
from itertools import product
from json import dumps

def automaton(m):
    out = [[set() for _ in range(m+2)] for _ in range(2)]
    for a in (0,1):
        for i in range(m-1): out[a][i].add(i+1)
        out[a][m-1].update((0,1))
    out[0][m].add(m)
    out[1][m+1].add(m+1)
    return out, {0,m,m+1}, {0,m,m+1}

def step(out, states, a):
    return set().union(*(out[a][q] for q in states))

def accepts(out, init, final, word):
    states = init
    for a in word: states=step(out,states,a)
    return bool(states & final)

def path_rank(out, init, final, word):
    n=len(word)
    if not n: return 1 if init & final else float('inf')
    edges=[out[0][q]|out[1][q] for q in range(len(out[0]))]
    p=[init]
    r=[final]
    for _ in range(n):
        p.append(set().union(*(edges[q] for q in p[-1])))
        r.append({q for q in range(len(edges)) if edges[q]&r[-1]})
    dp=[0]+[float('inf')]*n
    for i in range(n):
        states=p[i]
        for j in range(i+1,n+1):
            states=step(out,states,word[j-1])
            if states&r[n-j]: dp[j]=min(dp[j],dp[i]+1)
    return dp[n]

def literal_ranks(seeds,n):
    intervals={(i,j):{w[i:j] for w in seeds} for i in range(n) for j in range(i+1,n+1)}
    ans={}
    for w in product((0,1),repeat=n):
        dp=[0]+[float('inf')]*n
        for j in range(1,n+1):
            dp[j]=1+min(dp[i] for i in range(j) if w[i:j] in intervals[i,j])
        ans[w]=dp[n] if n else 1
    return ans

def in_gate(m,n):
    if n==0:return True
    return any((n-a*m)>=0 and (n-a*m)%(m-1)==0 for a in range(1,n//m+1))

counts={'unary_gate_lengths':0,'literal_rank_words':0,'path_rank_words':0}
for m in range(2,61):
    states={0}
    last_missing=0
    for n in range(2*m*m+1):
        assert ((0 in states)==in_gate(m,n)), (m,n,states)
        if n and 0 not in states: last_missing=n
        states={q+1 for q in states if q<m-1}|({0,1} if m-1 in states else set())
        counts['unary_gate_lengths']+=1
    assert last_missing==(m-1)**2, (m,last_missing)

for m in range(2,10):
    out,init,final=automaton(m)
    for n in range(10):
        words=list(product((0,1),repeat=n))
        seeds=[w for w in words if accepts(out,init,final,w)]
        literal=literal_ranks(seeds,n)
        for w in words:
            expected=1 if in_gate(m,n) else 1+sum(w[i]!=w[i-1] for i in range(1,n))
            assert literal[w]==expected, (m,w,literal[w],expected)
            counts['literal_rank_words']+=1
            assert path_rank(out,init,final,w)==expected, (m,w)
            counts['path_rank_words']+=1

extrema=[]
for m in range(2,21):
    out,init,final=automaton(m)
    n=(m-1)**2
    w=tuple(i%2 for i in range(n))
    rank=path_rank(out,init,final,w)
    assert rank==n,(m,n,rank)
    assert path_rank(out,init,final,w+(n%2,))==1
    counts['path_rank_words']+=2
    extrema.append({'m':m,'states':m+2,'last_missing_length':n,'rank':rank})

print(dumps({'status':'PASS','counts':counts,'extrema':extrema},indent=2))
