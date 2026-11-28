"""Exact checks of the minimum-minor rule and sharp digit families."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb,lcm
from random import Random

def vp(x,p):
    if not x:return float('inf')
    if isinstance(x,Q):return vp(x.numerator,p)-vp(x.denominator,p)
    n=0
    while x%p==0:n+=1;x//=p
    return n

def w(k,p,r):
    n=k;v=0
    while n:n//=p;v+=n
    return k*r-v

def det(rows):
    a=[list(map(Q,row)) for row in rows]
    d=1
    for j in range(len(a)):
        q=next((i for i in range(j,len(a)) if a[i][j]),None)
        if q is None:return 0
        if q!=j:a[j],a[q]=a[q],a[j];d=-d
        z=a[j][j];d*=z
        for i in range(j+1,len(a)):
            c=a[i][j]/z
            if c:a[i]=[x-c*y for x,y in zip(a[i],a[j])]
    return d

def newton(cs,ns,p,r):
    a=[]
    for j in range(max(ns)+1):
        c=sum(x*comb(n,j) for n,x in zip(ns,cs) if n>=j)
        if c:a.append((vp(c,p)+j*r,-j))
    return -min(a)[1]

def cutoff(ns,p,r):
    W=max(w(k,p,r) for k in range(len(ns)))
    return [k for k in range(int(W/(r-Q(1,p-1)))+1) if w(k,p,r)<=W]

def audit():
    rng=Random(816)
    minors=0
    for p in [2,3,5,7]:
        for t in range(2,7):
            for _ in range(6):
                ns=sorted(rng.sample(range(18),t))
                r=Q(1,p-1)+rng.choice([Q(1,4),Q(1,2),Q(1)])
                ks=cutoff(ns,p,r)
                rows={k:tuple(n**k for n in ns) for k in ks}
                # Evaluation rows are related to remainder rows by a fixed
                # Vandermonde, so every determinant cost has the same shift.
                cert=[]
                for I in combinations(ks,t):
                    d=det([rows[k] for k in I]);minors+=1
                    if d:cert.append((vp(d,p)+sum(w(k,p,r) for k in I),-max(I),I))
                _,negi,I=min(cert)
                j=I.index(-negi)
                # A dual functional on a minimizing basis, via cofactors.
                cs=[(-1)**(i+j)*det([R[:i]+R[i+1:] for h in I if h!=I[j]
                                    for R in [rows[h]]]) for i in range(t)]
                d=lcm(*(Q(c).denominator for c in cs))
                cs=[int(c*d) for c in cs]
                assert newton(cs,ns,p,r)==-negi
    print('120 rational cofactor witnesses passed exact Newton checks;',minors,'minors.')

def family():
    for p,m in [(2,2),(2,3),(2,4),(2,5),(2,6),(3,1),(3,2),(3,3),
                (3,4),(5,1),(5,2),(5,3),(7,1),(7,2),(11,1),(11,2)]:
        t=p**m
        d=2 if p==2 else 1
        q=p**d
        i=t//q
        a=[(-1)**(t-j)*((q-1)*comb(t,j)-(q*comb(t-1,j) if j<t else 0))
           for j in range(t+1)]
        a[0]+=p**(d*t+1)
        ns=[j for j,c in enumerate(a) if c]
        assert ns==[j for j in range(t+1) if j!=i]
        assert sorted(n%i for n in ns)==sorted(n%i for n in range(t))
        # Exact translation check without a quadratic expansion:
        # the formula above is the binomial expansion of this shifted polynomial.
        assert newton([a[j] for j in ns],ns,p,Q(d))==t
        assert newton([a[j] for j in ns],ns,p,Q(d+1))==0
    print('16 sharp residue-digit examples checked.')

if __name__=='__main__':
    audit()
    family()
