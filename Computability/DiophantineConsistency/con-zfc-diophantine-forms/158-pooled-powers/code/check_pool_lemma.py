"""Independent exact arithmetic checks of the pooled power lemma."""
from fractions import Fraction
import json
import argparse
from pathlib import Path
from collections import defaultdict
from math import isqrt

class Polynomial:
    def __init__(self,terms=None):
        self.terms={m:c for m,c in (terms or {}).items() if c}
    @staticmethod
    def coerce(x):return x if isinstance(x,Polynomial) else Polynomial({():x})
    def __add__(self,other):
        out=defaultdict(int,self.terms)
        for m,c in self.coerce(other).terms.items():out[m]+=c
        return Polynomial(out)
    __radd__=__add__
    def __neg__(self):return Polynomial({m:-c for m,c in self.terms.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self
    def __mul__(self,other):
        out=defaultdict(int)
        for m,c in self.terms.items():
            for n,d in self.coerce(other).terms.items():out[tuple(sorted(m+n))]+=c*d
        return Polynomial(out)
    __rmul__=__mul__
    def square(self):return self*self

def symbol(name):return Polynomial({(name,):1})

def symbolic_check(summands):
    a,n,k,l=map(symbol,('A','n','K','L'))
    h=s=e=y2=gates=norms=Polynomial()
    for i in range(summands):
        m,x,y,z=(symbol(f'{prefix}{i}') for prefix in ('m','X','Y','Z'))
        h+=y*(m-x)
        s+=(m-x+z).square()-y.square()
        e+=(m-x+z-n*y).square()
        y2+=y.square()
        gates+=y*(z-a*y)
        norms+=x.square()+y.square()-z.square()-1
    t=2*a*n-n.square()-1
    row1=k-2*h-(2*a-n)*l
    row2=s-n*k+l
    difference=e-t*(l-y2)-row2-n*row1+2*n*gates
    if difference.terms:raise ValueError('exact formal polynomial identity')
    reduced=row2+norms
    difference_reduced=e-t*(l-y2)-reduced-n*row1+2*n*gates+norms
    if difference_reduced.terms:raise ValueError('norm-reduced formal identity')
    return {'summands':summands,'ordinary_identity':'zero polynomial',
            'norm_reduced_identity':'zero polynomial'}

def pell(a,k):
    x,y=1,0
    for _ in range(abs(k)):
        x,y=a*x+(a*a-1)*y,x+a*y
    return x, y if k>=0 else -y

def check():
    identities=[symbolic_check(s) for s in (1,3,11)]
    frames=0
    for w in range(3,33):
        a,y=pell(w+1,w)
        if y%w or (y//w)%2!=1: raise ValueError('original frame parity')
        if a<=w**w:raise ValueError('original frame size')
        frames+=1
    bounds=0
    for w in range(258,321):
        b=isqrt(w-1)
        if not b*b<w or not 2*b+1<=w or not 60<w:
            raise ValueError('square-frame hypotheses')
        if 60*b**(4*b)>=w**w:raise ValueError('square-frame error bound')
        bounds+=1
    exact=0
    signed_congruences=0
    for w in (258,260,270):
        b=isqrt(w-1)
        a0,_=pell(w+1,w)
        for a in (a0,-a0):
            for n in (-3,-2,-1,1,2,3):
                t=2*a*n-n*n-1
                for index in range(-3,4):
                    xx,yy=pell(a,index)
                    for proposed in (-2,-1,0,1,2):
                        residual=proposed-xx-(n-a)*yy
                        ordinary=proposed*n**b-n**(b+index)
                        if (n**b*residual-ordinary)%t:
                            raise ValueError('signed-index clearing congruence')
                        signed_congruences+=1
                indices=[-3,-2,-1,0,1,2,3] if abs(n)==1 else [0,1,2]
                indices=[k for k in indices if abs(Fraction(n)**k)<=b]
                values=[(k,int(Fraction(n)**k),*pell(a,k)) for k in indices]
                t=2*a*n-n*n-1
                h=sum(y*(m-x) for k,m,x,y in values)
                s=sum((m-x+a*y)**2-y*y for k,m,x,y in values)
                r=[m-x-(n-a)*y for k,m,x,y in values]
                if any(rr%t for rr in r):raise ValueError('canonical congruence')
                if (s-2*n*h)%t:raise ValueError('pooled divisibility')
                ell=(s-2*n*h)//t
                kap=2*h+(2*a-n)*ell
                if s-n*kap+ell:raise ValueError('second residual')
                if sum(rr*rr for rr in r)!=t*(ell-sum(y*y for k,m,x,y in values)):
                    raise ValueError('exact identity')
                exact+=1
    if Fraction(2**17,3**16)>=Fraction(1,32):raise ValueError('zero factorial margin')
    return {'status':'PASS','symbolic_identities':identities,
            'frame_instances':frames,'signed_power_families':exact,
            'square_frame_error_bounds':bounds,
            'signed_index_clearing_congruences':signed_congruences,
            'scope':'exact arithmetic checks; unbounded proof in accompanying review'}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    result=check()
    payload=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.receipt:args.receipt.write_text(payload)
    print(payload,end='')
