from fractions import Fraction as Q
from collections import Counter
from itertools import combinations
import json
from pathlib import Path

def add(*ps):
    r=Counter()
    for p in ps:
        for k,v in p.items(): r[k]+=v
    return {k:v for k,v in r.items() if v}
def scale(p,c): return {k:c*v for k,v in p.items() if c*v}
def shift(p,j): return {k+j:v for k,v in p.items()}
def inv(p): return {-k:v for k,v in p.items()}
def mul(p,q):
    r=Counter()
    for i,a in p.items():
        for j,b in q.items():r[i+j]+=a*b
    return {k:v for k,v in r.items() if v}
def hist(s):
    h=Counter(); x=0
    for c in s:
        h[x]+=1; x+=1 if c=='0' else -1
    return dict(h)
def moments(p):
    n=sum(p.values());mu=Q(sum(k*v for k,v in p.items()),n)
    v=Q(sum(k*k*c for k,c in p.items()),n)-mu*mu
    return mu,v
def data(w):
    S=Counter();T=Counter();x=0
    for c in w:
        (S if c=='0' else T)[x]+=1
        x+=1 if c=='0' else -1
    return dict(S),dict(T)
def subst(s,w):return ''.join('1' if c=='0' else w for c in s)

checks=Counter();words=0
for a in range(2,8):
    for zeros in combinations(range(1,2*a-1),a):
        w=''.join('0' if i in zeros else '1' for i in range(2*a-1))
        S,T=data(w); assert T==shift(add(S,{0:-1}),1);checks['telescoping']+=1
        K0=add(S,T,{0:-1})
        K1=add(inv(K0),mul(inv(T),K0))
        assert min(K0.values())>0 and min(K1.values())>0
        assert sum(K0.values())==2*(a-1) and sum(K1.values())==2*a*(a-1)
        Delta=mul(S,inv(S));mu,v=moments(S)
        beta=v/Q(a+1)-Q(a)*mu*mu/Q((a-1)**2)+Q(1,4)
        m0=Q(1,2)+Q(a)*mu/Q(a-1)
        m1=-Q(1,2)-mu/Q(a-1)
        assert moments(K0)==(m0,Q(a)*v/Q(a-1)-Q(a)*mu*mu/Q((a-1)**2)+Q(1,4))
        assert moments(K1)==(m1,Q(2*a-1)*v/Q(a-1)-Q(a)*mu*mu/Q((a-1)**2)+Q(1,4))
        checks['auxiliary_moments']+=1
        hs=sorted(S);assert hs==list(range(min(hs),max(hs)+1))
        assert Q(a-1,a*a)<=v<=Q(a*a-1,12)
        eq=(v==Q(a*a-1,12))
        packed=any(w=='1'*r+'0'*a+'1'*(a-1-r) for r in range(1,a))
        assert eq==packed
        min_words={'10'*(a-1)+'0','10'+'01'*(a-2)+'0'}
        assert (v==Q(a-1,a*a))==(w in min_words)
        checks['variance_extrema']+=1
        H={}; c1='1'
        for r in range(4):
            L=Q(2*a**(r+1)+(-1)**(r+1)*(a-1),a+1)
            assert L==len(c1)
            actual=hist(c1); actual_mu,actual_v=moments(actual)
            mr=m1 if r%2==0 else m0
            eta=a*r if r%2==0 else r+1
            omega=(L-1)/L
            exact_v=omega*(r*v+beta)+2*v*eta/((a+1)*L)+omega*(1-omega)*mr*mr
            assert actual_mu==omega*mr and actual_v==exact_v
            checks['finite_moments']+=1
            target_m=(r+1)//2 if r%2 else r//2
            H={};
            for j in range(target_m):H=add({0:1},mul(Delta,H))
            expected=add({0:1},mul(K0 if r%2 else K1,H))
            assert actual==expected
            checks['exact_histograms']+=1
            c1=subst(c1,w)
        words+=1

for a in range(3,12):
    w='1'+'0'*a+'1'*(a-2)
    S,T=data(w);K0=add(S,T,{0:-1});K1=add(inv(K0),mul(inv(T),K0));D=mul(S,inv(S))
    H={}
    for m in range(1,11):
        H=add({0:1},mul(D,H));F=add({0:1},mul(K1,H))
        assert min(F)==-m*(a-1)-1 and max(F)==m*(a-1)
        assert sorted(F)==list(range(min(F),max(F)+1))
        checks['critical_support_extrema']+=1
    mu,v=moments(S)
    assert mu==Q(a-3,2) and v==Q(a*a-1,12)
    beta=v/Q(a+1)-Q(a)*mu*mu/Q((a-1)**2)+Q(1,4)
    assert beta==Q(7-a,6)-Q(1,(a-1)**2)
    checks['critical_closed_constants']+=1

record={'status':'passed','words_checked':words,'counts':dict(checks)}
rendered=json.dumps(record,indent=2)+"\n"
output=Path(__file__).resolve().parents[1]/"data"/"independent_general_moment_audit.json"
output.parent.mkdir(parents=True,exist_ok=True)
with output.open("w",encoding="utf-8",newline="\n") as stream:
    stream.write(rendered)
print(rendered,end="")
