"""Exact rational-weight Hankel-to-hyperlogarithm compiler.

Hyperlog words use 0 -> dz/z and 1 -> dz/(1-z); nonempty output words
end in 1. All algebra is exact. Input poles are k=-a, a >= 0 integral.
"""
from __future__ import annotations
from functools import lru_cache
from itertools import product
from collections import defaultdict
import sympy as S

M, z = S.symbols('M z')


def harmonic_symbol(j: int):
    return S.Symbol(f'H{j}')


def power_sum(j: int, a: int = 0):
    return S.expand((S.bernoulli(j+1, M+a+1)-S.bernoulli(j+1, a+1))/(j+1))


def validate(poles):
    out=[]
    for a, ell, c in poles:
        if not isinstance(a,int) or not isinstance(ell,int) or a<0 or ell<1:
            raise ValueError('Pole shifts must be nonnegative integers; orders positive integers.')
        out.append((a,ell,S.sympify(c)))
    return out


def moment(j: int, poles, polynomial=()):
    """polynomial[t] is the coefficient of k**t in the weight."""
    if j<0: raise ValueError('Moment degree must be nonnegative.')
    ans=sum(S.sympify(c)*power_sum(j+t) for t,c in enumerate(polynomial))
    for a,ell,c in validate(poles):
        for v in range(j+1):
            fac=c*S.binomial(j,v)*S.Integer(-a)**(j-v)
            if fac==0: continue
            e=v-ell
            if e>=0:
                term=power_sum(e,a)
            else:
                p=-e
                term=harmonic_symbol(p)+sum((M+b)**(-p)-S.Rational(1,b)**p for b in range(1,a+1))
            ans+=fac*term
    return S.factor(ans)


def hankel(r: int,poles,polynomial=()):
    if not isinstance(r, int) or isinstance(r, bool) or r<0:
        raise ValueError('Rank must be a nonnegative integer.')
    if r==0: return S.Integer(1)
    vals=[moment(j,poles,polynomial) for j in range(2*r-1)]
    return S.factor(S.Matrix(r,r,lambda i,j:vals[i+j]).det(method='domain-ge'))


def capacity(r: int,poles):
    orders={}
    for a,ell,c in validate(poles):
        if c!=0: orders[a]=max(orders.get(a,0),ell)
    best=0
    for ks in product(*(range(s+1) for s in orders.values())):
        if sum(ks)<=r:
            best=max(best,sum(k*(s-k+1) for k,s in zip(ks,orders.values())))
    return best


@lru_cache(None)
def stuffle(a:tuple[int,...], b:tuple[int,...]):
    if not a: return {b:1}
    if not b: return {a:1}
    d=defaultdict(int)
    for w,c in stuffle(a[1:],b).items(): d[(a[0],)+w]+=c
    for w,c in stuffle(a,b[1:]).items(): d[(b[0],)+w]+=c
    for w,c in stuffle(a[1:],b[1:]).items(): d[(a[0]+b[0],)+w]+=c
    return dict(d)


def harmonic_product(indices):
    d={():1}
    for p in indices:
        nd=defaultdict(int)
        for w,c in d.items():
            for v,b in stuffle(w,(p,)).items(): nd[v]+=c*b
        d=dict(nd)
    return d


def binary_word(indices):
    return tuple(b for p in indices for b in (0,)*(p-1)+(1,))


def clean(f):
    ans={}
    for w,c in f.items():
        c=S.cancel(c)
        if c!=0: ans[w]=c
    return ans


def add(*fs):
    d=defaultdict(lambda:S.Integer(0))
    for f in fs:
        for w,c in f.items():d[w]+=c
    return clean(d)


def scale(f,c):return clean({w:c*v for w,v in f.items()})


def theta(f):
    d=defaultdict(lambda:S.Integer(0))
    for w,c in f.items():
        d[w]+=z*S.diff(c,z)
        if w:d[w[1:]]+=z*c/(z if w[0]==0 else 1-z)
    return clean(d)


def rational_primitive_parts(R):
    """R=Q' + a/z + b/(1-z), all with exact rational coefficients."""
    Q=S.Integer(0); a=S.Integer(0); b=S.Integer(0)
    R=S.apart(S.cancel(R),z)
    for term in S.Add.make_args(R):
        num,den=S.fraction(term)
        if not den.has(z):
            Q+=S.integrate(term,z);continue
        P=S.Poly(den,z)
        factors=S.factor_list(P.as_expr(),z)[1]
        if len(factors)!=1:raise ValueError(f'Unexpected denominator {den}')
        fac,p=factors[0];root=S.solve(fac,z)[0]
        if root not in (0,1):raise ValueError(f'Unexpected singularity {root}')
        c=S.cancel(term*(z-root)**p)
        if c.has(z):raise ValueError('Partial fraction coefficient is not constant.')
        if p==1:
            if root==0:a+=c
            else:b-=c
        else:Q+=c*(z-root)**(1-p)/(1-p)
    return S.cancel(Q),S.cancel(a),S.cancel(b)


@lru_cache(None)
def integral_term(R,word):
    Q,a,b=rational_primitive_parts(R)
    f={():Q} if not word else {word:Q}
    if a:f=add(f,{(0,)+word:a})
    if b:f=add(f,{(1,)+word:b})
    if word and Q:
        ker=1/z if word[0]==0 else 1/(1-z)
        f=add(f,scale(integral_term(S.cancel(Q*ker),word[1:]),-1))
    return clean(f)


@lru_cache(None)
def word_series(word, n):
    """Taylor coefficients through degree n, for convergent-at-zero words."""
    if not word:return (S.Integer(1),)+(S.Integer(0),)*n
    if word[-1]!=1:raise ValueError('Nonanalytic word at zero.')
    tail=word_series(word[1:],n)
    a=[S.Integer(0)]*(n+1)
    if word[0]==0:
        for k in range(1,n+1):a[k]=tail[k]/k
    else:
        acc=S.Integer(0)
        for k in range(1,n+1):
            acc+=tail[k-1];a[k]=acc/k
    return tuple(a)


def taylor(f,n):
    ans=S.Integer(0)
    for w,c in clean(f).items():
        if w and w[-1]!=1:raise ValueError('A log(z) term failed to cancel.')
        # Conservative bound on the pole order at zero.
        den=S.denom(S.cancel(c)); p=S.degree(den,z) or 0
        ser=sum(v*z**j for j,v in enumerate(word_series(w,n+p+1)))
        ans+=S.series(c*ser,z,0,n+1).removeO()
    ans=S.expand(ans)
    return [S.expand(ans).coeff(z,i) for i in range(n+1)]


def primitive(f):
    out=add(*(integral_term(c,w) for w,c in f.items()))
    if any(w and w[-1]!=1 for w in out):raise ValueError('Nonanalytic primitive; input must be analytic at zero.')
    ct=taylor(out,0)[0]
    return add(out,{():-ct})


def inverse_shift(f,h:int,s:int=1):
    if h<0 or s<0:raise ValueError('Only nonnegative integer shifts and powers are supported.')
    for _ in range(s):
        f=scale(primitive(scale(f,z**(h-1))),z**(-h))
    return f


def base_generator(indices):
    if not indices:return {():z/(1-z)}
    return {binary_word(w):S.Rational(c)/(1-z) for w,c in harmonic_product(indices).items()}


def rational_operator(q,f):
    q=S.cancel(q)
    if q==0 or not f:
        return {}
    out={}
    for term in S.Add.make_args(S.apart(S.cancel(q),M)):
        num,den=S.fraction(term)
        if not den.has(M):
            pp=S.Poly(term,M);cur=f
            for k in range(pp.degree()+1):
                if pp.nth(k):out=add(out,scale(cur,pp.nth(k)))
                cur=theta(cur)
        else:
            factors=S.factor_list(den,M)[1]
            if len(factors)!=1:raise ValueError(f'Unexpected coefficient {term}')
            fac,p=factors[0];root=S.solve(fac,M)[0]
            h=-root
            if not (h.is_Integer and h>=0):raise ValueError('Nonintegral or negative endpoint shift.')
            c=S.cancel(term*(M+h)**p)
            if c.has(M):raise ValueError('Partial fraction failure.')
            out=add(out,scale(inverse_shift(f,int(h),int(p)),c))
    return out


def compile_expression(expr):
    hs=sorted((x for x in expr.free_symbols if x.name.startswith('H') and x.name[1:].isdigit()),key=lambda x:int(x.name[1:]))
    if not hs:return rational_operator(expr,base_generator(()))
    out={}
    for exps,c in S.Poly(expr,*hs).terms():
        indices=tuple(int(h.name[1:]) for h,e in zip(hs,exps) for _ in range(e))
        out=add(out,rational_operator(c,base_generator(indices)))
    return clean(out)


def compile_hankel(r,poles,polynomial=()):
    return compile_expression(hankel(r,poles,polynomial))


def encode(f):
    return [{'word':list(w),'coefficient':str(c)} for w,c in sorted(f.items())]


def direct_determinant(r,n,poles,polynomial=()):
    vals=[]
    for j in range(2*r-1):
        v=0
        for k in range(1,n+1):
            w=sum(S.sympify(c)*k**t for t,c in enumerate(polynomial))
            w+=sum(S.sympify(c)/S.Integer(k+a)**ell for a,ell,c in validate(poles))
            v+=k**j*w
        vals.append(v)
    return S.det(S.Matrix(r,r,lambda i,j:vals[i+j]))

if __name__=='__main__':
    f=compile_hankel(2,[(0,3,1)])
    print(encode(f));print(taylor(f,5))
