import itertools,json

def automaton(m):
    delta=[[i+1,i+1] for i in range(m-1)]+[[0,1]]
    r,a,b,z,o,d=range(m,m+6)
    delta += [[a,b],[z,0],[d,o],[z,d],[d,o],[d,d]]
    return delta,r,{0,z,o}

def layers(delta,r,F,n):
    P=[{r}]; R=[set(F)]
    for i in range(n):
        P.append({v for q in P[-1] for v in delta[q]})
        R.append({q for q in range(len(delta)) if any(v in R[-1] for v in delta[q])})
    return P,R

def rank(delta,r,F,w):
    n=len(w);P,R=layers(delta,r,F,n);cost=[0]+[n+1]*n
    for i in range(n):
        Q=P[i]
        for j in range(i,n):
            Q={delta[q][w[j]] for q in Q}
            if Q & R[n-j-1]:cost[j+1]=min(cost[j+1],cost[i]+1)
    return cost[-1]

checks=[]
for m in range(2,26):
    delta,r,F=automaton(m);g=(m-1)**2;n=g+2
    assert len(delta)==m+6
    P,R=layers(delta,r,F,2*g+8)
    assert set(range(m))<=P[g+3]
    assert set(range(m))<=R[g+1]
    Q={0}
    for j in range(g):Q={v for q in Q for v in delta[q]}
    assert 0 not in Q
    got=rank(delta,r,F,[i%2 for i in range(n)])
    assert got==n,(m,n,got)
    checks.append({'gate_states':m,'dfa_states':m+6,'witness_length_and_rank':got,'proved_rank_upper':g+4})

literal=0
for m in range(2,9):
    delta,r,F=automaton(m);g=(m-1)**2
    for n in range(2,11):
        seeds=[]
        for w in itertools.product(range(2),repeat=n):
            q=r
            for c in w:q=delta[q][c]
            if q in F:seeds.append(w)
        assert (0,)*n in seeds and (1,)*n in seeds
        if n==g+2: assert set(seeds)=={(0,)*n,(1,)*n}
        literal+=2**n

result={'status':'PASS','path_dp_witnesses':checks,'literal_seed_words_tested':literal}
print(json.dumps(result,indent=2))
