#!/usr/bin/env python3
"""Independent finite checks; the unbounded theorem is PROOF.md.

Python standard library only. Correctness checks are explicit exceptions,
so optimization does not disable them. No project builder is imported.
"""
import gzip
import hashlib
import json
import random
from collections import Counter
from math import gcd,isqrt
from pathlib import Path

HERE=Path(__file__).resolve().parent

def check(ok,why):
    if not ok: raise ValueError(why)

class Poly:
    """A tiny exact sparse integer polynomial ring, used for local identities."""
    def __init__(self,v=0):
        self.d=v if isinstance(v,dict) else ({():v} if v else {})
    @staticmethod
    def var(n): return Poly({((n,1),):1})
    def __add__(self,b):
        b=b if isinstance(b,Poly) else Poly(b);d=dict(self.d)
        for m,c in b.d.items():
            d[m]=d.get(m,0)+c
            if not d[m]: del d[m]
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self,b): return self+-aspoly(b)
    def __rsub__(self,b): return aspoly(b)+-self
    def __mul__(self,b):
        b=aspoly(b);d={}
        for m,c in self.d.items():
            for n,e in b.d.items():
                z=dict(m)
                for a,k in n:z[a]=z.get(a,0)+k
                t=tuple(sorted(z.items()));d[t]=d.get(t,0)+c*e
                if not d[t]:del d[t]
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        r=Poly(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,b):return self.d==aspoly(b).d
    def json(self):return [{'coefficient':c,'powers':dict(m)} for m,c in sorted(self.d.items())]

def aspoly(p):return p if isinstance(p,Poly) else Poly(p)

class Lead:
    """Exact leading homogeneous form when no unresolved cancellation occurs."""
    def __init__(self,degree,polynomial):self.degree=degree;self.p=aspoly(polynomial)
    @staticmethod
    def var(name,degree=1):return Lead(degree,Poly.var(name))
    def __add__(self,b):
        b=aslead(b)
        if self.degree>b.degree:return self
        if b.degree>self.degree:return b
        p=self.p+b.p
        check(bool(p.d),'Unresolved highest-degree cancellation in certificate')
        return Lead(self.degree,p)
    __radd__=__add__
    def __neg__(self):return Lead(self.degree,-self.p)
    def __sub__(self,b):return self+-aslead(b)
    def __rsub__(self,b):return aslead(b)+-self
    def __mul__(self,b):
        b=aslead(b);return Lead(self.degree+b.degree,self.p*b.p)
    __rmul__=__mul__
    def __pow__(self,n):return Lead(n*self.degree,self.p**n)

def aslead(x):return x if isinstance(x,Lead) else Lead(0,x)

def identities():
    v={n:Poly.var(n) for n in ['q','l','r','Y','U','H','D0','G','a','c','X','g','V','e','A']}
    q,l,r,Y,U,H,D0,G,a,c,X,g,V,e,A=[v[n] for n in v]
    pairs=[
        ((q**3*(l+r)+Y)**2-q**6*(l*(l+r-r+Poly.var('k'))+1),
         q**6*(2*l*r+r*r-l*Poly.var('k')-1)+2*q**3*Y*(l+r)+Y*Y),
        ((U*D0-H*r)**2-U**2*G,
         U**2*(D0**2-G)-2*U*H*r*D0+H**2*r**2),
        ((a*c+X+H*g)**2-((a*a+H)*c*c+1),
         2*a*c*(X+H*g)+(X+H*g)**2-H*c*c-1),
        (A*(V*V-(V+e)**2)+(V+e)**2,
         V*V-(A-1)*e*(2*V+e))]
    for j,(x,y) in enumerate(pairs):check(x==y,'Local formal identity '+str(j))
    return len(pairs)

def degree_certificate(witnesses,ports):
    x={n:Lead.var(n) for n in witnesses}
    x.update({n:Lead.var(n,0) for n in ports})
    J,F,alpha,z,f,i,T,Y,w,rho,eta,zeta,e,gamma=[x[n] for n in witnesses]
    beta,K0,MC,MF=[x[n] for n in ports]
    q=beta*J+1;C=q-F-alpha;X=w*q;E=X*Y;k=eta+zeta;c=k*Y+eta
    a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y;b0=X+a*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    r=k-R-1;U=Y*Y;I=i*c*c;Aaux=Delta*(f*f-1)
    V=f*f*(c*T-R)-c
    A0=q**6*(2*ell*rho+rho*rho-ell*k-1)+2*q**3*Y*(ell+rho)+Y*Y
    D0=b0+H*gamma
    D0gap=2*a*c*(X+H*gamma)+(X+H*gamma)**2-H*c*c-1
    M=U*U*D0gap-2*U*H*r*D0+H*H*r*r
    W=I*I-Aaux
    Na=V*V-(Aaux-1)*e*(2*V+e)
    Lt=(K0+w)*C-F-z*(q-1)
    P=A0*A0+M*M+W*W+Na*Na+Lt*Lt-1
    expected=4*Poly.var('beta')**10*Poly.var('J')**10*Poly.var('w')**4*Poly.var('Y')**4*Poly.var('f')**8*Poly.var('e')**2*(Poly.var('beta')*Poly.var('J')-Poly.var('F'))**2
    check(P.degree==30 and P.p==expected,'Exact leading form')
    return {n:{'degree':u.degree,'leading_form':u.p.json()} for n,u in
            [('A0',A0),('M',M),('W',W),('Na',Na),('Lt',Lt),('P',P)]}

def literal_formula(t,c):
    J,F,alpha,z,f,i,T,Y,w,rho,eta,zeta,e,gamma=t
    beta,K0,MC,MF=c
    q=beta*J+1;C=q-F-alpha;X=w*q;E=X*Y;k=eta+zeta;c=k*Y+eta
    a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y;b0=X+a*c;G=1+Delta*c*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    r=k-R-1;U=Y*Y;Dstar=U*b0+H*(U*gamma-r);M=Dstar*Dstar-U*U*G
    I=i*c*c;Aaux=Delta*(f*f-1);W=I*I-Aaux;V=f*f*(c*T-R)-c;y=V+e
    Na=Aaux*(V*V-y*y)+y*y;Lt=(K0+w)*C-F-z*(q-1)
    A0=(q**3*(ell+rho)+Y)**2-q**6*(ell*(ell+k)+1)
    return A0*A0+M*M+W*W+Na*Na+Lt*Lt-1

def graph_eval(d,vals,modulus=None):
    vals=dict(vals)
    for name,op,l,r in d['source']:
        a=l if isinstance(l,int) else vals[l];b=r if isinstance(r,int) else vals[r]
        t=a+b if op=='+' else a-b if op=='-' else a*b
        vals[name]=t if modulus is None else t%modulus
    return vals[d['output']]

class Ray:
    """Full exact polynomial in one variable over a finite prime field."""
    prime=1000003
    def __init__(self,a):self.a=self.trim(list(a) if isinstance(a,(list,tuple)) else [a])
    @classmethod
    def trim(cls,a):
        a=[x%cls.prime for x in a]
        while len(a)>1 and not a[-1]:a.pop()
        return a
    def __add__(self,b):
        b=b if isinstance(b,Ray) else Ray(b);n=max(len(self.a),len(b.a));c=[0]*n
        for i,v in enumerate(self.a):c[i]+=v
        for i,v in enumerate(b.a):c[i]+=v
        return Ray(c)
    __radd__=__add__
    def __neg__(self):return Ray([-v for v in self.a])
    def __sub__(self,b):return self+-(b if isinstance(b,Ray) else Ray(b))
    def __rsub__(self,b):return Ray(b)+-self
    def __mul__(self,b):
        b=b if isinstance(b,Ray) else Ray(b);c=[0]*(len(self.a)+len(b.a)-1)
        for i,v in enumerate(self.a):
            for j,w in enumerate(b.a):c[i+j]+=v*w
        return Ray(c)
    __rmul__=__mul__
    def __pow__(self,n):
        r=Ray(1)
        for _ in range(n):r=r*self
        return r

def main():
    d=json.loads((HERE/'polynomial.json').read_text());witnesses=d['witnesses'];ports=d['fixed_numerals']
    check(witnesses==['J','F','alpha','z','f','i','T','Y','w','rho','eta','zeta','e','gamma'],'Witness domain/order')
    check(d['witness_domain']=='strictly positive integers','Domain')
    initial=set(witnesses+ports);known=set(initial);deps={}
    for name,op,l,r in d['source']:
        check(op in ['+','-','*'] and name not in known,'Gate syntax/order')
        check(all(isinstance(v,int) or v in known for v in [l,r]),'Forward reference')
        deps[name]=[v for v in [l,r] if isinstance(v,str)];known.add(name)
    todo=[d['output']];live=set()
    while todo:
        n=todo.pop()
        if n in live:continue
        live.add(n);todo.extend(deps.get(n,[]))
    check(live==known,'Dead gate or port')
    count=Counter(r[1] for r in d['source'])
    check(len(d['source'])==83 and count=={'*':44,'+':23,'-':16},'Operation count')
    source_pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
    for p in source_pins['files']:
        raw=(HERE/p['path']).read_bytes()
        check(hashlib.sha256(raw).hexdigest()==p['sha256'],'Source hash '+p['path'])
        check(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==p['git_blob_sha1'],'Git blob '+p['path'])
    binding=json.loads((HERE/'native/COEFFICIENT_BINDING.json').read_text());bound={}
    for p in binding['materialization']['files']:
        packed=(HERE/'native'/p['file']).read_bytes();raw=gzip.decompress(packed)
        check(hashlib.sha256(packed).hexdigest()==p['gzip_sha256'],'Compressed coefficient')
        check(hashlib.sha256(raw).hexdigest()==p['sha256'],'Integer coefficient')
        bound[p['port']]=int.from_bytes(raw,'little')
    coeffs=[bound[n] for n in ['beta','K','MC','MF_source']]
    checks=0;rng=random.Random(20261023)
    for prime in [1000003,1000033,1000037]:
        cc=[v%prime for v in coeffs]
        for _ in range(200):
            t=[rng.randrange(-9,10) for _ in witnesses]
            vals=dict(zip(witnesses,t));vals.update(zip(ports,cc))
            check(graph_eval(d,vals,prime)==literal_formula(t,cc)%prime,'Independent transcription')
            checks+=1
    forms=degree_certificate(witnesses,ports);local=identities()
    rays=[]
    for prime in [1000003,1000033,1000037]:
        Ray.prime=prime;cc=[Ray(v%prime) for v in coeffs]
        tt=[Ray([0,1]) for _ in witnesses];vals=dict(zip(witnesses,tt));vals.update(zip(ports,cc))
        got=graph_eval(d,vals);direct=literal_formula(tt,cc)
        check(got.a==direct.a,'Full polynomial ray equality')
        beta=coeffs[0]%prime;lead=4*pow(beta,10,prime)*pow(beta-1,2,prime)%prime
        check(len(got.a)-1==30 and got.a[-1]==lead and lead!=0,'Actual-port degree ray')
        rays.append({'prime':prime,'degree':len(got.a)-1,'leading_coefficient':got.a[-1]})
    gcd_cases=0
    for q in range(16,49):
        for s in range(1,6):
            Y=s*q**3
            for w in range(1,8):
                X=w*q;H=4*Y*(X+1)+3;U=Y*Y
                check(gcd(Y,H) in [1,3] and gcd(U,H) in [1,3,9],'Gcd lemma finite case')
                check(U//gcd(U,H)>q**4 and 4*X*Y*Y%U==0,'Adaptive modulus finite case')
                gcd_cases+=1
    receipt={'status':'PASS','operations':83,'operation_counts':dict(count),
             'witnesses':14,'domain':'strictly positive integers','degree':30,
             'source_files_authenticated':len(source_pins['files']),
             'fixed_ports_authenticated':4,'formal_local_identities':local,
             'independent_scalar_checks':checks,'full_polynomial_rays':rays,
             'bounded_gcd_modulus_cases':gcd_cases,'leading_forms':forms,
             'limits':'Finite implementation/algebra checks only; unbounded equivalence is PROOF.md with named inherited dependencies.'}
    (HERE/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='leading_forms'},indent=2))

if __name__=='__main__':main()
