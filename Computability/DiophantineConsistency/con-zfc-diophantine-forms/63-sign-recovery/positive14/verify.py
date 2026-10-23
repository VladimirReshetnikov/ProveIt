#!/usr/bin/env python3
"""Finite arithmetic/transcription checks; not an unbounded compiler proof."""
from pathlib import Path
import argparse
from collections import Counter
import gzip
import hashlib
import json
import random
import build

HERE=Path(__file__).resolve().parent
EXPECTED={
 'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
 'K':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
 'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
 'MF_source':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722'}
ALIASES={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}

def require(condition,message):
    if not condition:raise ValueError(message)

class Poly:
    """Small exact multivariate polynomials, used only for local identities."""
    def __init__(self,terms=None):self.terms={m:c for m,c in (terms or {}).items() if c}
    @staticmethod
    def const(c):return Poly({():c})
    @staticmethod
    def var(v):return Poly({(v,):1})
    @staticmethod
    def coerce(p):return p if isinstance(p,Poly) else Poly.const(p)
    def __add__(self,b):
        b=Poly.coerce(b);d=dict(self.terms)
        for m,c in b.terms.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,b):return self+-Poly.coerce(b)
    def __rsub__(self,b):return Poly.coerce(b)+-self
    def __mul__(self,b):
        b=Poly.coerce(b);d={}
        for m,c in self.terms.items():
            for n,e in b.terms.items():
                key=tuple(sorted(m+n));d[key]=d.get(key,0)+c*e
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        p=Poly.const(1)
        for _ in range(n):p=p*self
        return p

def exact_identities():
    q,l,r,Y=[Poly.var(v) for v in ('q','ell','r','Y')];k=Poly.var('k')
    raw=(q**3*(l+r)+Y)**2-q**6*(l*(l+k)+1)
    reduced=q**6*(r*r+l*(2*r-k)-1)+2*q**3*(l+r)*Y+Y*Y
    require(not (raw-reduced).terms,'first carrier identity')
    M,X,a,c,H,Z=[Poly.var(v) for v in ('M','X','a','c','H','Z')]
    b=X+a*c;delta=a*a+H
    raw=(M*b+H*Z)**2-M*M*(1+delta*c*c)
    reduced=M*M*(X*X+2*a*c*X-H*c*c-1)+2*M*b*H*Z+H*H*Z*Z
    require(not (raw-reduced).terms,'main carrier cancellation')
    Q,V,u=[Poly.var(v) for v in ('Q','V','u')]
    raw=(V+u)**2-Q*u*(2*V+u)-1
    reduced=Q*V*V-(Q-1)*(V+u)**2-1
    require(not (raw-reduced).terms,'auxiliary gap identity')
    K,w,C,F,z,q=[Poly.var(v) for v in ('K','w','C','F','z','q')]
    old=(K+w)*C+q-F-(z+1)*(q-1)-1
    new=(K+w)*C-F-z*(q-1)
    require(not (old-new).terms,'transport shift identity')
    return ['first carrier','main carrier cancellation','auxiliary gap','transport shift']

def graph_check(p,expected_ops):
    inputs=set(p['variables']+p['fixed_numerals']);known=set(inputs)
    degrees={v:1 for v in p['variables']};degrees.update({v:0 for v in p['fixed_numerals']})
    for name,op,a,b in p['source']:
        require(name not in known,'repeated gate '+name);require(op in ('+','-','*'),'bad operation')
        require(isinstance(a,int) or a in known,'forward operand');require(isinstance(b,int) or b in known,'forward operand')
        da=0 if isinstance(a,int) else degrees[a];db=0 if isinstance(b,int) else degrees[b]
        degrees[name]=da+db if op=='*' else max(da,db);known.add(name)
    needed={p['output']}
    for name,op,a,b in reversed(p['source']):
        if name in needed:needed.update((a,b))
    require(all(row[0] in needed for row in p['source']),'dead gate')
    require(inputs<=needed,'dead advertised input')
    require(len(p['source'])==expected_ops==p['operations'],'operation count')
    require(dict(Counter(r[1] for r in p['source']))==p['operation_breakdown'],'operation breakdown')
    return degrees

def numeric(p,values,ports,mod):
    env={**values,**ports}
    def get(a):return a%mod if isinstance(a,int) else env[a]
    for name,op,a,b in p['source']:
        a,b=get(a),get(b)
        env[name]=(a+b if op=='+' else a-b if op=='-' else a*b)%mod
    return [env[r] for r in p['residuals']],env[p['output']]

def direct(values,ports,mod,shifted=True):
    J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,t=[values[v] for v in build.VARIABLES]
    beta,K0,MC,MF=[ports[v] for v in build.PORTS]
    q=(beta*J+1)%mod;C=(q-F-alpha)%mod;X=w*q%mod;E=X*Y%mod
    k=eta+zeta;c=(k*Y+eta)%mod;a=(E+Y)%mod;H=(4*a+3)%mod
    delta=(a*a+H)%mod;ell=E*k*Y%mod;b0=(X+a*c)%mod
    R=(((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J)%mod
    M=4*pow(q,4,mod)%mod;e=(k-R-1)%mod;W=(M*b0+H*(M*t-e))%mod
    I=i*c*c%mod;Q=delta*(f*f-1)%mod;V=(c*(T*f-1)-R*f*f)%mod
    residuals=[(pow(q,3,mod)*(ell+r)+Y)**2-pow(q,6,mod)*(ell*(ell+k)+1),
      W*W-M*M*(1+delta*c*c),
      (K0+w)*C-F-z*(q-1) if shifted else (K0+w)*C+q-F-z*(q-1)-1,
      f*f-delta*I*I-1,(V+u)**2-Q*u*(2*V+u)-1]
    residuals=[x%mod for x in residuals]
    return residuals,sum(x*x for x in residuals)%mod

def trim(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a
def univar(p,ports,mod):
    env={v:[0,1] for v in p['variables']};env.update({v:[n%mod] for v,n in ports.items()})
    env['r']=[0,2]  # Avoid the exceptional diagonal 2r=eta+zeta.
    def get(a):return [a%mod] if isinstance(a,int) else env[a]
    for name,op,a,b in p['source']:
        a,b=get(a),get(b)
        if op=='*':
            c=[0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%mod
        else:
            c=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%mod for i in range(max(len(a),len(b)))]
        env[name]=trim(c)
    return [env[r] for r in p['residuals']],env[p['output']]

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--coefficients-dir',type=Path,default=HERE.parent/'coefficients'/'payloads')
    args=parser.parse_args();binding=json.loads((args.coefficients_dir/'COEFFICIENT_BINDING.json').read_text())
    require(binding['variant']=='mixed-parity-unrounded-1064921','whole tuple variant')
    raw_values={}
    for port,sha in EXPECTED.items():
        raw=(args.coefficients_dir/(port+'.bin')).read_bytes()
        require(hashlib.sha256(raw).hexdigest()==sha,'literal tuple hash '+port)
        require(binding['payloads'][port]['sha256']==sha,'binding hash '+port)
        require(gzip.decompress((args.coefficients_dir/(port+'.bin.gz')).read_bytes())==raw,'compressed payload '+port)
        raw_values[port]=int.from_bytes(raw,'little')
    require(raw_values['beta']==(1<<1064921)-1,'literal beta')
    ports={a:raw_values[b] for a,b in ALIASES.items()}
    primary=json.loads((HERE/'pell14_degree34.json').read_text())
    certificate=json.loads((HERE/'pell14_degree34_degree_certificate.json').read_text())
    unshifted=json.loads((HERE/'pell14_degree34_unshifted.json').read_text())
    natural=json.loads((HERE/'pell14_natural_degree34.json').read_text())
    require(primary==build.build(),'exact primary regeneration')
    require(certificate==build.build(True),'exact certificate regeneration')
    require(unshifted==build.build(False,False),'exact unshifted regeneration')
    graph_check(primary,87);degree=graph_check(certificate,99)
    graph_check(unshifted,88);graph_check(natural,101)
    require([degree[r] for r in certificate['residuals']]==[12,17,2,16,15],'residual degree bounds')
    require(degree[certificate['output']]==34,'universal degree upper bound')
    ids=exact_identities();trials=0;rays=[];rng=random.Random(20261023)
    for mod in (1000003,1000033,1000037):
        reduced_ports={a:n%mod for a,n in ports.items()}
        rp,up=univar(primary,reduced_ports,mod);rc,uc=univar(certificate,reduced_ports,mod)
        require(rp==rc and up==uc,'exact finite-field ray comparison')
        require([len(v)-1 for v in rp]==[12,17,2,16,15],'ray residual exact degrees')
        expected=pow(2,16,mod)*pow(reduced_ports['beta'],20,mod)%mod
        require(len(up)-1==34 and up[-1]==expected and expected!=0,'attained degree and leader')
        rays.append({'prime':mod,'degree':34,'leading_coefficient':expected})
        for _ in range(32):
            values={v:rng.randrange(-1000,1001) for v in build.VARIABLES}
            require(numeric(primary,values,reduced_ports,mod)==direct(values,reduced_ports,mod),'direct formula')
            require(numeric(certificate,values,reduced_ports,mod)==direct(values,reduced_ports,mod),'cancellation graph')
            require(numeric(unshifted,values,reduced_ports,mod)==direct(values,reduced_ports,mod,False),'unshifted formula')
            shifted_values={v:n+1 for v,n in values.items()}
            require(numeric(natural,values,reduced_ports,mod)==direct(shifted_values,reduced_ports,mod),'natural translation')
            old_values=dict(values);old_values['z']+=1
            require(numeric(primary,values,reduced_ports,mod)==numeric(unshifted,old_values,reduced_ports,mod),'transport coordinate map')
            trials+=1
    receipt={'status':'PASS','variables':14,'domain':'strictly positive integers','exact_degree':34,
      'operations':87,'operation_breakdown':primary['operation_breakdown'],'system_operations':78,
      'system_maximum_degree':17,'natural_operations':101,'unshifted_operations':88,
      'fixed_tuple':'mixed-parity-unrounded-1064921','actual_payload_hashes':EXPECTED,
      'exact_symbolic_identities':ids,'universal_upper_certificate_residual_degrees':[12,17,2,16,15],
      'finite_field_exact_rays':rays,'modular_assignments':trials,
      'leading_form':'16384*(beta*J)^20*w^4*Y^6*(eta+zeta)^2*t^2',
      'boundary':'Finite checks certify identities, degree, transcription, counts and actual fixed data. The existence equivalence is the ordinary proof in PROOF.md with inherited compiler/Pell/calibration inputs.'}
    (HERE/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
