"""Independent audit of complete-DFA quadratic finite-rank family."""
import json

def machine(m):
    # Gate 0..m-1; extra root,a,b,z,o,sink.
    r,a,b,z,o,d=range(m,m+6)
    delta=[(i+1,i+1) for i in range(m-1)]+[(0,1)]
    delta += [(a,b),(z,0),(d,o),(z,d),(d,o),(d,d)]
    return delta,r,{0,z,o}

def rank(delta,init,final,w):
    n=len(w); P=[{init}];R=[final]
    for _ in range(n):
        P.append({v for q in P[-1] for v in delta[q]})
        R.append({q for q in range(len(delta)) if any(v in R[-1] for v in delta[q])})
    dp=[0]+[n+1]*n
    for i in range(n):
        curr=P[i]
        for j in range(i+1,n+1):
            curr={delta[q][w[j-1]] for q in curr}
            if curr&R[n-j]:dp[j]=min(dp[j],dp[i]+1)
    return dp[n]

completions=0;witnesses=[]
for m in range(2,61):
    delta,init,final=machine(m);g=(m-1)**2;B=g+1
    assert len(delta)==m+6 and all(len(row)==2 for row in delta)
    # Exact backward paths inside gate to its sole final q0.
    current={0}
    for _ in range(B):current={q for q in range(m) if any(v in current for v in delta[q])}
    assert current==set(range(m)),(m,B,current)
    completions+=m
    # At witness length, gate cannot return to q0.
    current={0}
    for _ in range(g):current={v for q in current for v in delta[q]}
    assert 0 not in current
    if m<=20:
        n=g+2;w=tuple(i%2 for i in range(n))
        value=rank(delta,init,final,w)
        assert value==n,(m,n,value)
        witnesses.append({'m':m,'states':m+6,'target_length':n,'rank':value})
print(json.dumps({'status':'PASS','gate_completion_state_checks':completions,'witnesses':witnesses},indent=2))
