"""Independent constructions, exact interval-partition DP, and graph distances."""
from collections import deque
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def step(rows,Z):
    ans=0
    while Z:
        bit=Z&-Z;ans|=rows[bit.bit_length()-1];Z-=bit
    return ans

def accepted(rows,I,F,w):
    for c in w:I=step(rows[int(c)],I)
    return bool(I&F)

def shortest_gate(s):
    # u=0,v=1,b=2; the rest are corridor states in forward order.
    zero=[0]*s;one=[1<<i for i in range(s)]
    zero[0]=1<<1;zero[2]=1<<2
    if s==3:one[1]|=1<<2;one[2]|=1
    else:
        one[1]|=1<<3;one[2]|=1<<3
        for i in range(3,s-1):one[i]|=1<<(i+1)
        one[-1]|=1|(1<<2)
    return [zero,one],1,2,'0'*(2*s-1)

def two_sided(s):
    # a=0,b=1, corridor=2,...,s-1.
    zero=[0]*s;one=[0]*s
    zero[0]=1;one[0]=1<<2
    zero[1]=(1<<1)|(1<<2);one[1]=1<<1
    for i in range(2,s-1):zero[i]=1<<(i+1)
    one[-1]=1;zero[-1]=1<<1
    return [zero,one],1,1,'1'*(2*s+1)

def interval_minimum(rows,I,F,w):
    s=len(rows[0]);N=len(w);E=[a|b for a,b in zip(*rows)]
    reverse=[sum(1<<u for u in range(s) if E[u]>>v&1) for v in range(s)]
    P=[I];R=[F]
    for _ in range(N):P.append(step(E,P[-1]));R.append(step(reverse,R[-1]))
    dp=[0]+[N+1]*N;admissible=[]
    for i in range(N):
        Z=P[i]
        for j in range(i+1,N+1):
            Z=step(rows[int(w[j-1])],Z)
            if Z&R[N-j]:
                dp[j]=min(dp[j],dp[i]+1);admissible.append((i,j))
    return dp[N],admissible,P,R

def distances(E):
    s=len(E);out=[]
    for start in range(s):
        d=[None]*s;d[start]=0;q=deque([start])
        while q:
            u=q.popleft()
            for v in range(s):
                if E[u]>>v&1 and d[v] is None:d[v]=d[u]+1;q.append(v)
        out.append(d)
    return out

checks=[]
for name,build,lo in [('shortest_gate',shortest_gate,3),('two_sided',two_sided,4)]:
    for s in range(lo,51):
        rows,I,F,w=build(s);rank,allowed,P,R=interval_minimum(rows,I,F,w)
        assert rank==2*s-1,(name,s,rank)
        full=(1<<s)-1;assert P[s-1]==full and R[s-1]==full
        assert all(Z==full for Z in P[s-1:]) and all(Z==full for Z in R[s-1:])
        assert any(rows[0][b]>>b&1 and rows[1][b]>>b&1 for b in range(s))
        if name=='shortest_gate':
            assert allowed==[(i,i+1) for i in range(len(w))]
            for i in range(len(w)):assert accepted(rows,I,F,'1'*i+'0'+'1'*(len(w)-i-1))
            D=distances([a|b for a,b in zip(*rows)])
            assert all(x is not None for row in D for x in row)
            assert D[0][2]==D[2][1]==max(map(max,D))==s-1
        else:
            loop='1'+'0'*(s-3)+'1';N=len(w)
            for i in range(N):
                a=i if i<=N-len(loop) else i-(s-2)
                seed='0'*a+loop+'0'*(N-a-len(loop))
                assert len(seed)==N and seed[i]=='1' and accepted(rows,I,F,seed)
        checks.append({'family':name,'states':s,'target_length':len(w),'interval_minimum':rank,'complete_upper_bound':2*s-1})
result={'passed':True,'number_of_automata':len(checks),'state_range_shortest_gate':[3,50],'state_range_two_sided':[4,50],'checks':checks}
(ROOT/'family_verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))

# Fully literal accepted-seed oracle for the four-state rank-seven example.
import sys
sys.path.insert(0,str(ROOT.parent))
from audit_literal import literal
r,I,F,_=shortest_gate(4)
A=sum(v<<(4*i) for i,v in enumerate(r[0]));B=sum(v<<(4*i) for i,v in enumerate(r[1]))
slices=[]
for N in range(1,9):
    rank,nt,w=literal(4,A,B,I,F,N)
    assert rank==min(N,7)
    slices.append({'length':N,'maximum_rank':rank,'hull_targets':nt,'witness':w})
(ROOT/'literal_rank_seven.json').write_text(json.dumps({'matrices':[A,B],'initial':I,'final':F,'slices':slices,'passed':True},indent=2)+'\n')
