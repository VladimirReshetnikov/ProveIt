#!/usr/bin/env python3
"""Finite exact algebra, source and degree checks for normalized91.

No native accepting tuple is generated. These checks do not replace the
unbounded Pell/completeness arguments in NORMALIZED_ORDINATE_PROOF.md.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,random

ROOT=Path(__file__).resolve().parent
def require(condition,message):
    if not condition: raise ValueError(message)

class Poly:
    """Sparse integer polynomial in D,u,b,Q,z,f,V,A,B,p."""
    n=10
    def __init__(self, terms): self.t={m:c for m,c in terms.items() if c}
    @classmethod
    def c(cls,x): return cls({(0,)*cls.n:x})
    @classmethod
    def var(cls,i):
        m=[0]*cls.n;m[i]=1;return cls({tuple(m):1})
    def cast(self,o): return o if isinstance(o,Poly) else Poly.c(o)
    def __add__(self,o):
        o=self.cast(o);out=dict(self.t)
        for m,c in o.t.items():out[m]=out.get(m,0)+c
        return Poly(out)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o):return self+-self.cast(o)
    def __rsub__(self,o):return self.cast(o)+-self
    def __mul__(self,o):
        o=self.cast(o);out={}
        for m,c in self.t.items():
            for n,d in o.t.items():
                e=tuple(x+y for x,y in zip(m,n));out[e]=out.get(e,0)+c*d
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self,n):
        out=Poly.c(1)
        for _ in range(n):out=out*self
        return out

D,u,b,Q,z,f,V,A,B,p=[Poly.var(i) for i in range(10)]
W=1+(Q*z-z)*(Q*z-2)
y=Q*z-1
identities=[
    W-(1+(Q-1)*z*(Q*z-2)),
    y*y-1-Q*z*(Q*z-2),
    Q*V*V-(Q-1)*y*y-1-Q*(V*V-W),
    ((u*f-b)**2-W)-(D*u*u+b*b-W-2*u*b*f+u*u*(f*f-D)),
    A*A-D*B*B-((A-B*f)*(A+B*f)+B*B*(f*f-D)),
    4*(D*u*u)*(b*b)-D*(2*u*b)**2,
]
for j,x in enumerate(identities):require(not x.t,f'Polynomial identity {j} failed')

parent_bytes=(ROOT/'parent84.json').read_bytes()
require(hashlib.sha256(parent_bytes).hexdigest()=='8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf','Parent identity changed')
parent=json.loads(parent_bytes)['packet']
data=json.loads((ROOT/'equation91_degree269.json').read_text())
depends={'f','y_aux'}; kept=[]
for row in parent['source']:
    if row[2] in depends or row[3] in depends:depends.add(row[0])
    else:kept.append(row)
require(len(kept)==66 and data['source'][:66]==kept,'Retained source mismatch')
require(len(data['source'])==91 and len(data['witnesses'])==17,'Wrong sizes')
require(Counter(r[1] for r in data['source'])=={'*':50,'+':23,'-':18},'Operation ledger changed')
seen=set(data['free']);live={data['output']}
for name,op,l,r in data['source']:
    require(name not in seen and op in ['+','-','*'],'Bad source row')
    require(all(isinstance(x,int) or x in seen for x in [l,r]),'Forward reference')
    seen.add(name)
for name,op,l,r in reversed(data['source']):
    if name in live:
        live.update(x for x in [l,r] if isinstance(x,str))
require(set(data['free']).issubset(live) and all(r[0] in live for r in data['source']),'Dead source')

def eval_source(values):
    v=dict(values)
    for name,op,l,r in data['source']:
        a=v[l] if isinstance(l,str) else l
        b=v[r] if isinstance(r,str) else r
        v[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return v

rng=random.Random(20261025)
for j in range(20):
    vals={v:rng.randrange(-3,4) for v in data['free']}
    v=eval_source(vals)
    dd=1+v['A']*v['i']**2*v['R10a']**4
    bb=v['R10a']+v['r_lhs']*dd
    uu=v['R10a']*v['auxiliary_quotient']
    pp=dd*uu**2;qq=v['R16'];zz=v['ordinate_quotient']
    ww=1+(qq-1)*zz*(qq*zz-2)
    aa=pp+bb**2-ww
    p5=v['norm_first']*v['norm_main']*v['norm_input']*v['norm_index']*v['norm_transport']
    expected=p5*(aa**2-4*dd*uu**2*bb**2+1)-1
    require(v[data['output']]==expected,'Full source differs from independent formula')

def pell_y(s,n):
    a,b=0,1
    for _ in range(n):a,b=b,2*s*b-a
    return a
for s in range(2,20):
    for m in range(30):
        require((pell_y(s,2*m+1)-(-1)**m)%(4*s*s)==0,'Residue fixture failed')

# Exact integer norm fixture, independent of any native computation.
# D=9, u=2, b=1, Q=4, z=1 gives W=7, so no false zero is asserted.
# Actual local roots are found from arbitrary Pell parameters, retaining
# the entire normalized auxiliary identity and reconstructed f.
local_zeros=0
for delta in [3,8,15]:
    for ii in range(1,20):
        dd=1+delta*ii*ii
        ff=int(dd**0.5)
        if ff*ff!=dd:continue
        ss=delta*ii;qq=ss*ss
        yy=pell_y(ss,3);zz=(yy+1)//qq
        vv=4*qq-3
        # Let u=vv+1, b=u*ff-vv, ensuring V=u*f-b=vv.
        uu=vv+1;bb=uu*ff-vv
        pp=dd*uu*uu;ww=1+(qq*zz-zz)*(qq*zz-2)
        aa=pp+bb*bb-ww
        require(aa*aa==4*pp*bb*bb,'Local norm fixture failed')
        require(aa==2*uu*bb*ff,'Local integer root restoration failed')
        local_zeros+=1
require(local_zeros>0,'No local fixtures')

# Degree upper bound: the two exact cancellation identities are inherited
# and independently proved below at arbitrary scalar cut variables.
X,a,c,g,H=[Poly.var(i) for i in range(5)]
cancel=(X+a*c+g)**2-(a*a+H)*c*c-(X*X+2*X*g+g*g+2*a*c*X+2*a*c*g-H*c*c)
require(not cancel.t,'Norm degree cancellation identity failed')
degree={v:(0 if v in data['fixed_numerals'] else 1) for v in data['free']}
for name,op,l,r in data['source']:
    dl=degree[l] if isinstance(l,str) else 0;dr=degree[r] if isinstance(r,str) else 0
    degree[name]=dl+dr if op=='*' else max(dl,dr)
    if name=='norm_main':degree[name]=18
    if name=='norm_input':degree[name]=32
require(degree[data['output']]==269,'Degree upper bound differs')
require(degree['nr_P5']==81 and degree['nr_Wminus1']==94 and degree['nr_cross']==122,'Degree cuts differ')

# Whole-source univariate expansion modulo a prime certifies that degree269
# is attained in a numerical specialization. The uniform nonzero coefficient
# for every valid Bm1 is proved separately in the note.
prime=1000000007
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sign=1):
    out=[0]*max(len(a),len(b))
    for i,c in enumerate(a):out[i]=c
    for i,c in enumerate(b):out[i]=(out[i]+sign*c)%prime
    return trim(out)
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,c in enumerate(a):
        for j,d in enumerate(b):out[i+j]=(out[i+j]+c*d)%prime
    return trim(out)
vals={}
for i,v in enumerate(data['free']):
    vals[v]=[i+3] if v in data['fixed_numerals'] else [0,i+3]
for name,op,l,r in data['source']:
    aa=vals[l] if isinstance(l,str) else [l%prime]
    bb=vals[r] if isinstance(r,str) else [r%prime]
    vals[name]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
require(len(vals[data['output']])-1==269,'Attained degree differs')

receipt={'status':'PASS','rows':91,'positive_witnesses':17,'exact_degree':269,
 'counts':dict(Counter(r[1] for r in data['source'])),
 'polynomial_identities':len(identities)+1,'off_zero_full_source_checks':20,
 'pell_residue_fixtures':18*30,'local_norm_zero_fixtures':local_zeros,
 'source_sha256':hashlib.sha256((ROOT/'equation91_degree269.json').read_bytes()).hexdigest(),
 'degree_specialization_prime':prime,'degree_specialization_leading_coefficient':vals[data['output']][-1],
 'scope':'Finite algebra and artifact checks; no native halting witness or end-to-end formal proof.'}
print(json.dumps(receipt,indent=2))
