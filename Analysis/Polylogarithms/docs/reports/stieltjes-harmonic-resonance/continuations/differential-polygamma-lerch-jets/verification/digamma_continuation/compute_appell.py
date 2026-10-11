from functools import lru_cache
from collections import Counter
from pathlib import Path
import json
import sympy as sp

OUT=Path(__file__).parent
y,t,v=sp.symbols('y t v')
h=sp.symbols('h1:10')
A=sp.symbols('A1:10')
z={r:sp.Symbol(f'z{r}') for r in range(2,12)}
p2=sp.Symbol('p2')

def even_reduce(x):
    return sp.expand(x.subs({z[r]:(-1)**(r//2+1)*sp.bernoulli(r)*2**(r-1)*p2**(r//2)/sp.factorial(r) for r in z if r%2==0}))

def nice(x):
    return sp.expand(x).subs(p2**3,945*z[6]).subs(p2**2,90*z[4]).subs(p2,6*z[2])

@lru_cache(None)
def stuffle(a,b):
    if not a:return {b:1}
    if not b:return {a:1}
    ans=Counter()
    for c,n in stuffle(a[1:],b).items():ans[(a[0],)+c]+=n
    for c,n in stuffle(a,b[1:]).items():ans[(b[0],)+c]+=n
    for c,n in stuffle(a[1:],b[1:]).items():ans[(a[0]+b[0],)+c]+=n
    return dict(ans)

@lru_cache(None)
def product_word(indices):
    out={():1}
    for r in indices:
        nxt=Counter()
        for a,c in out.items():
            for b,d in stuffle(a,(r,)).items():nxt[b]+=c*d
        out=dict(nxt)
    return out

def ordinary_words(poly,m):
    out={}
    for powers,c in sp.Poly(poly,v,*h[:m]).terms():
        q,*hp=powers
        assert q>=2
        indices=tuple(r for r,n in enumerate(hp,1) for _ in range(n))
        for w,mult in product_word(indices).items():
            key=(q,)+w;out[key]=out.get(key,0)+c*mult
    return {w:even_reduce(c) for w,c in sorted(out.items()) if even_reduce(c)!=0}

def mixed_derivative_words(poly,m):
    # poly uses h1=H_(n-1), A_r=strict upper tail sum(k>n) k^-r.
    out={}
    for powers,c in sp.Poly(poly,v,h[0],*A[1:m]).terms():
        q,hp,*ap=powers
        assert q>=1
        upper=tuple(r for r,n in enumerate(ap,2) for _ in range(n))
        assert upper or q>=2
        for up,um in product_word(upper).items():
            for low,lm in product_word((1,)*hp).items():
                w=up+(q,)+low;pos=len(up)
                key=(w,pos);out[key]=out.get(key,0)+c*um*lm
    return {w:even_reduce(c) for w,c in sorted(out.items()) if even_reduce(c)!=0}

def compute(m):
    # coefficients of ordinary centered Gamma-Appell polynomials
    B=[sp.Integer(1),sp.Integer(0)]
    for k in range(2,m+1):B.append(sp.expand(sum(z[r]*B[k-r] for r in range(2,k+1))/k))
    fcoef=[-1,h[0]]+[h[r-1]+(-1)**r*z[r] for r in range(2,m+1)]
    powers=[[sp.Integer(1)]+[sp.Integer(0)]*m]
    for k in range(1,m+1):
        prev=powers[-1]
        powers.append([sp.expand(sum(prev[i-j]*fcoef[j] for j in range(i+1))) for i in range(m+1)])
    p={j:sp.expand(sum(sp.factorial(m)*B[m-k]*powers[k][k-j]/sp.factorial(k) for k in range(j,m+1))) for j in range(1,m+1)}
    e=[sp.Integer(1)]
    for k in range(1,m):e.append(sp.expand(sum((-1)**(r-1)*h[r-1]*e[k-r] for r in range(1,k+1))/k))
    defect=even_reduce(p[1]+sp.factorial(m)*e[m-1])
    tail=even_reduce(defect.subs({h[r-1]:z[r]-A[r-1] for r in range(2,m)},simultaneous=True))
    assert sp.expand(tail.subs({a:0 for a in A}))==0
    shift={h[r-1]:h[r-1]+v**r for r in range(1,m+1)}
    Jpoly=even_reduce(sum(sp.expand(p[j].subs(shift,simultaneous=True)-p[j])*v**(j-1)/sp.Integer(j-1) for j in range(2,m+1)))
    Jwords=ordinary_words(Jpoly,m)
    # delta_n - delta_(n-1), in h1 at n-1 and A_r at n.
    dt=even_reduce(tail.subs(h[0],h[0]+v)-tail.subs({A[r-1]:A[r-1]+v**r for r in range(2,m)},simultaneous=True))
    Dwords=mixed_derivative_words(dt,m)
    assert all(len(w)<=m-3 for w,pos in Dwords) if m>=4 else not Dwords
    return dict(m=m,p=p,defect=defect,tail=tail,Jpoly=Jpoly,Jwords=Jwords,dt=dt,Dwords=Dwords)

def emit(m):
    d=compute(m)
    print('\nM',m)
    print('delta:',nice(d['tail']))
    print('difference:',nice(d['dt']))
    print('J words:',[(w,str(nice(c))) for w,c in d['Jwords'].items()])
    print('D words:',[(w,pos+1,str(nice(c))) for (w,pos),c in d['Dwords'].items()])
    records={k:(str(nice(val)) if not isinstance(val,dict) else {str(w):str(nice(c)) for w,c in val.items()}) for k,val in d.items()}
    (OUT/f'appell_{m}.json').write_text(json.dumps(records,indent=2))
    return d

if __name__=='__main__':
    for m in range(4,8):emit(m)
