"""Exact finite-harmonic quasi-shuffle algebra, with explicit CT regularization.

The word (r1,...,rd) represents H_N(r1,...,rd) with strictly decreasing
indices. Products are finite identities. CT means the constant coefficient
in log N and is computed by eliminating leading ones before taking limits.
"""
import functools
from collections import defaultdict
import sympy as s

g,z2,z3,z4,z5=s.symbols('g z2 z3 z4 z5')
b,c,d,e,f,t=s.symbols('b c d e f t')
x=s.symbols('x')

@functools.cache
def stuffle(a,b):
    if not a:return {b:1}
    if not b:return {a:1}
    ans=defaultdict(int)
    for w,v in stuffle(a[1:],b).items():ans[(a[0],)+w]+=v
    for w,v in stuffle(a,b[1:]).items():ans[(b[0],)+w]+=v
    for w,v in stuffle(a[1:],b[1:]).items():ans[(a[0]+b[0],)+w]+=v
    return dict(ans)

def add(a,b):
    ans=defaultdict(lambda:0);ans.update(a)
    for w,v in b.items():ans[w]+=v
    return {w:s.expand(v) for w,v in ans.items() if v!=0}

def mul(a,b):
    ans=defaultdict(lambda:0)
    for wa,va in a.items():
        for wb,vb in b.items():
            for w,v in stuffle(wa,wb).items():ans[w]+=va*vb*v
    return {w:s.expand(v) for w,v in ans.items() if v!=0}

def scale(a,coef):return {w:s.expand(v*coef) for w,v in a.items()}
def word(w,coef=1):return {w:coef}
def combine(*args):
    ans={}
    for term in args:ans=add(ans,term)
    return ans

def power(a,k):
    ans={():1}
    for j in range(k):ans=mul(ans,a)
    return ans

h={b:{(1,):1,():-g},c:{(2,):1,():z2},d:{(3,):1,():-z3},e:{(4,):1,():z4},f:{(5,):1,():-z5}}
def to_words(expr):
    ans={}
    for exps,coef in s.Poly(s.expand(expr),b,c,d,e,f).terms():
        term={():coef}
        for var,exp in zip((b,c,d,e,f),exps):term=mul(term,power(h[var],exp))
        ans=add(ans,term)
    return ans

def sum_inner(words,outer,inclusive):
    ans={}
    for w,coef in words.items():
        ans=add(ans,{(outer,)+w:coef})
        if inclusive and w:ans=add(ans,{(outer+w[0],)+w[1:]:coef})
    return ans

Z={}
def zs(w):
    if w not in Z:Z[w]=s.Symbol('Z_'+'_'.join(map(str,w)))
    return Z[w]

@functools.cache
def reg(w):
    if not w:return s.Integer(1)
    if w==(1,):return g
    if w[0]!=1:return zs(w)
    a=w[1:]
    product=dict(stuffle((1,),a))
    coeff=product.pop(w)
    return s.expand((g*reg(a)-sum(v*reg(k) for k,v in product.items()))/coeff)

def ev(words):return s.expand(sum(v*reg(w) for w,v in words.items()))

ordinary={(k,):globals()['z'+str(k)] for k in range(2,6)}
ordinary.update({(2,1):z3,(3,1):z4/4,(2,2):3*z4/4,(2,1,1):z4,(4,1):2*z5-z2*z3,(3,2):3*z2*z3-s.Rational(11,2)*z5,(2,3):s.Rational(9,2)*z5-2*z2*z3,(2,2,1):3*z2*z3-s.Rational(11,2)*z5,(2,1,2):s.Rational(9,2)*z5-2*z2*z3,(3,1,1):2*z5-z2*z3,(2,1,1,1):z5})

def reduce_mzv(expr):
    sub={zs(w):v for w,v in ordinary.items()}
    return s.expand(expr.subs(sub)).subs(z2*z2,s.Rational(5,2)*z4).expand()
