#!/usr/bin/env python3
"""Exact independent residual audit; Python standard library only."""
from collections import Counter, defaultdict
from pathlib import Path
import json
import math

ROOT=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok: raise ValueError(msg)

class Poly:
    """Sparse integer polynomials; four ports have degree weight zero."""
    N=17
    def __init__(self,terms): self.terms={k:v for k,v in terms.items() if v}
    @classmethod
    def const(cls,v): return cls({(0,)*cls.N:v})
    @classmethod
    def var(cls,i):
        e=[0]*cls.N; e[i]=1
        return cls({tuple(e):1})
    def __add__(self,other):
        if not isinstance(other,Poly): other=Poly.const(other)
        d=defaultdict(int,self.terms)
        for e,c in other.terms.items(): d[e]+=c
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({e:-c for e,c in self.terms.items()})
    def __sub__(self,other): return self+-other
    def __rsub__(self,other): return -self+other
    def __mul__(self,other):
        if not isinstance(other,Poly): other=Poly.const(other)
        d=defaultdict(int)
        for e,c in self.terms.items():
            for f,b in other.terms.items():
                d[tuple(x+y for x,y in zip(e,f))]+=c*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        require(isinstance(n,int) and n>=0,'power')
        ans=Poly.const(1); base=self
        while n:
            if n&1: ans=ans*base
            n//=2
            if n: base=base*base
        return ans
    def degree(self): return max((sum(e[:13]) for e in self.terms),default=-1)
    def head(self):
        d=self.degree()
        return Poly({e:c for e,c in self.terms.items() if sum(e[:13])==d})
    def __eq__(self,other):
        if not isinstance(other,Poly): other=Poly.const(other)
        return self.terms==other.terms

def step(op,x,y):
    if op=='+': return x+y
    if op=='-': return x-y
    if op=='*': return x*y
    raise ValueError('operation')

def main():
    p=json.loads((ROOT/'p13_degree30.json').read_text())
    vs=[Poly.var(k) for k in range(13)]
    ports=[Poly.var(k) for k in range(13,17)]
    env=dict(zip(p['witnesses']+p['fixed_numerals'],vs+ports))
    j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma=vs
    beta,K0,MC,MF=ports
    names=set(env)
    def val(z): return Poly.const(z) if isinstance(z,int) else env[z]
    last_res=max(k for k,row in enumerate(p['source']) if row[0] in p['residuals'])
    for name,op,x,y in p['source'][:last_res+1]:
        require(name not in names,'duplicate name')
        require(isinstance(x,int) or x in names,'forward edge')
        require(isinstance(y,int) or y in names,'forward edge')
        env[name]=step(op,val(x),val(y)); names.add(name)
    needed={p['output']}
    for name,op,x,y in reversed(p['source']):
        if name in needed: needed.update((x,y))
    require(all(row[0] in needed for row in p['source']),'dead gate')
    require(set(p['witnesses']+p['fixed_numerals'])<=needed,'dead input')
    require(len(p['source'])==p['operations']==93,'count')
    require(dict(Counter(row[1] for row in p['source']))==p['operation_breakdown'],'breakdown')

    # Independently transcribed formula: no import of the generator.
    J=3*j+1; q=beta*J+1; C=q-F-alpha
    E=X*Y; k=eta+zeta; c=k*Y+eta
    a=E+Y; H=4*a+3; delta=(a+2)**2-1
    ell=E*k*Y; I=i*c**2
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    r0=k-R-1; U=q*q*Y; L=q*Y
    Dstar=U*(X+a*c+H*gamma)+H*(L*X-r0)
    M=q**3*(q-1); W=(q-1)*k+1
    # Unfactored historical carrier, testing a distinct expression.
    Ttr=(q*K0+X)*C+q*(q-F-1)
    Z=M*(ell+k+q*W+r)+(q-1)*Y-q**3*W*Ttr
    V=f*f*(c*T-R)-c
    direct=[Z*Z-M*M*(ell*(ell+k)+1),
            Dstar*Dstar-U*U*(1+delta*c*c),
            (V+u)**2-delta*(f*f-1)*u*(2*V+u)-1,
            f*f-delta*I*I-1]
    q0=3*beta*j; k0=eta+zeta
    R0=q0**3*(q0-F)
    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    heads=[-2*q0**8*k0**2*X*Y**2*Bt0,
           8*q0**2*k0*X**2*Y**4*(q0**2*Y*gamma+R0),
           2*X**2*Y**2*f**4*u*R0,
           -i**2*k0**4*X**2*Y**6]
    degrees=[]; terms=[]
    for name,direct_expr,head in zip(p['residuals'],direct,heads):
        got=env[name]
        require(got==direct_expr,'formula mismatch '+name)
        degrees.append(got.degree()); terms.append(len(got.terms))
        require(got.head()==head,'leading form '+name)
    require(degrees==[15,13,13,14],'degree list')
    # Check only the final SOS circuit on four formal residuals.
    rs=[Poly.var(k) for k in range(4)]
    tail=dict(zip(p['residuals'],rs))
    for name,op,x,y in p['source'][last_res+1:]:
        require(name not in names,'duplicate tail name')
        require(x in tail and y in tail,'unexpected SOS edge')
        tail[name]=step(op,tail[x],tail[y]); names.add(name)
    require(tail[p['output']]==sum(z*z for z in rs),'SOS')
    # Unique top residual makes this a complete leading-degree certificate.
    lead=heads[0]**2
    mon=(16,0,2,0,0,0,4,4,0,4,0,0,0)
    coeff={e[13:]:c for e,c in lead.terms.items() if e[:13]==mon}
    require(coeff=={(16,0,0,0):4*3**16},'fixed coefficient certificate')

    # Diagnostics complement, and do not replace, the proof of the gcd lemma.
    cases=0
    for qq in range(2,63,3):
        for ss in range(1,22):
            yy=ss*qq**3
            for xx in range(1,15):
                hh=4*yy*(xx+1)+3
                gg=math.gcd(hh,qq*qq*yy)
                mu=qq*yy//gg
                require(gg==math.gcd(3,yy),'gcd diagnostic')
                require((yy//gg)%qq**3==0 and mu>=qq**4,'cofactor bound')
                require((4*xx*yy*yy)%mu==0,'modulus diagnostic')
                cases+=1
    receipt={'status':'passed','exact_residual_degrees':degrees,
             'expanded_residual_terms':terms,'exact_degree':30,
             'operations':93,'operation_breakdown':p['operation_breakdown'],
             'nonzero_coefficient':'4*(3*beta)^16',
             'exact_checks':['independent residual formulas','leading homogeneous forms',
                             'SOS structure','all input and gate liveness'],
             'bounded_gcd_diagnostic_cases':cases,
             'scope':'Finite algebra and data checks; inherited unbounded calibration remains separate.'}
    (ROOT/'CHECK13.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
