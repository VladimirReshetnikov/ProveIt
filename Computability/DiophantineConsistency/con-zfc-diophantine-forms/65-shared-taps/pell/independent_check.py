#!/usr/bin/env python3
"""Independent finite checks. The universal proof is in proof.md.

Uses only the Python standard library. All requirements remain active under -O.
The circuit builder is deliberately not imported.
"""
from pathlib import Path
import copy
import gzip
import hashlib
import json
import math
import random

HERE=Path(__file__).resolve().parent

def need(ok,label):
    if not ok: raise ValueError(label)

def constants():
    base=HERE/'coefficients'
    binding=json.loads((base/'COEFFICIENT_BINDING.json').read_text())
    out={}
    for rec in binding['materialization']['files']:
        packed=(base/rec['file']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(raw).hexdigest()==rec['sha256'],'coefficient raw hash')
        need(hashlib.sha256(packed).hexdigest()==rec['gzip_sha256'],'coefficient gzip hash')
        v=int.from_bytes(raw,'little');need(v.bit_length()==rec['bits'],'coefficient bit length')
        out[{'K':'K0','MF_source':'MF'}.get(rec['port'],rec['port'])]=v
    beta=out['beta']; B=beta+1; native=out['MF']-beta
    need(beta==(1<<590069)-1,'literal beta')
    need(beta%3==1 and 0<out['MC']<beta and 0<native<beta,'mask ranges')
    need(out['MC']%4==2 and native%8==4,'mask residues')
    need(out['MC'].bit_count()+native.bit_count()==590069,'mask population')
    return out

def evaluate(d,inputs,ports,mod):
    env={**inputs,**ports}
    def val(a):return a%mod if isinstance(a,int) else env[a]
    for g in d['gates']:
        a,b=map(val,g['args']);op=g['op']
        env[g['id']]=(a+b if op=='add' else a-b if op=='sub' else a*b)%mod
    return env[d['output']],{k:val(v) for k,v in d['registers'].items()}

def direct(name,v,ports,mod):
    # This transcription follows the displayed mathematical formula, not the DAG.
    beta,K,MC,MF=[ports[k] for k in ['beta','K0','MC','MF']]
    F,alpha,z,f,i,T,Y,r,eta,zeta,u,gamma=[v[k] for k in
      ['F','alpha','z','f','i','T','Y','r','eta','zeta','u','gamma']]
    J=3*v['j']+1 if name=='p14_degree26' else v['J']
    q=beta*J+1;C=q-F-alpha
    X=v['x']+q if name=='p14_degree26' else v['w']*q
    E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    vv=k-R-1;S=4*q*Y;M=q*S if name=='p14_degree26' else S
    D=M*(X+a*c)+H*(M*gamma-vv+(S*X if name=='p14_degree26' else 0))
    U=Delta*(f*f-1);I=i*c*c;V=f*f*(c*T-R)-c
    A0=(q**3*(ell+r)+Y)**2-q**6*(ell*(ell+k)+1)
    Nm=D*D-M*M*(Delta*c*c+1)
    At=q*(K*C-F-z*(q-1))+X*C if name=='p14_degree26' else (K+v['w'])*C-F-z*(q-1)
    Aa=(V+u)**2-U*u*(2*V+u)-1;As=I*I-U
    residuals={'A0':A0,'Nm':Nm,'At':At,'Aa':Aa,'As':As}
    return sum(t*t for t in residuals.values())%mod,{k:t%mod for k,t in residuals.items()}

def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a

def padd(a,b,p,sgn=1):
    return trim([((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%p
                 for i in range(max(len(a),len(b)))])

def pmul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%p
    return trim(c)

def ray(d,inputs,ports,p):
    env={k:[0,v%p] for k,v in inputs.items()};env.update({k:[v%p] for k,v in ports.items()})
    def val(a):return [a%p] if isinstance(a,int) else env[a]
    for g in d['gates']:
        a,b=map(val,g['args']);op=g['op']
        env[g['id']]=pmul(a,b,p) if op=='mul' else padd(a,b,p,1 if op=='add' else -1)
    return env[d['output']],{k:val(t) for k,t in d['registers'].items()}

def expected_leader(name,v,beta,p):
    if name=='p14_degree26':
        q=3*beta*v['j'];X=v['x']+q
    else:q=beta*v['J'];X=v['w']*q
    Y=v['Y'];R=q**3*(q-v['F']);k=v['eta']+v['zeta']
    la=2*X**2*Y**2*v['f']**4*v['u']*R
    lm=32*q*q*X**2*k*Y**4*(4*q*q*Y*v['gamma']+R)
    return ((lm*lm+la*la) if name=='p14_degree26' else la*la)%p

class Formal:
    """Tiny sparse commutative polynomial ring for universal local identities."""
    def __init__(self,x=0):
        if isinstance(x,Formal):self.d=x.d
        elif isinstance(x,str):self.d={(x,):1}
        elif isinstance(x,dict):self.d={m:c for m,c in x.items() if c}
        else:self.d={():x} if x else {}
    def __add__(self,o):
        o=Formal(o);r=self.d.copy()
        for m,c in o.d.items():r[m]=r.get(m,0)+c
        return Formal(r)
    __radd__=__add__
    def __neg__(self):return Formal({m:-c for m,c in self.d.items()})
    def __sub__(self,o):return self+-Formal(o)
    def __rsub__(self,o):return Formal(o)+-self
    def __mul__(self,o):
        o=Formal(o);r={}
        for m,a in self.d.items():
            for n,b in o.d.items():
                key=tuple(sorted(m+n));r[key]=r.get(key,0)+a*b
        return Formal(r)
    __rmul__=__mul__
    def __pow__(self,n):
        z=Formal(1)
        for _ in range(n):z=z*self
        return z

def exact_identities():
    q,l,r,Y,M,X,a,c,H,g,v,S,U,V,u=map(Formal,
      ['q','ell','r','Y','M','X','a','c','H','gamma','v','S','U','V','u'])
    raw=(q**3*(l+r)+Y)**2-q**6*(l*(l+Formal('k'))+1)
    expanded=q**6*(r*r+l*(2*r-Formal('k'))-1)+2*q**3*(l+r)*Y+Y*Y
    need(not (raw-expanded).d,'universal first-root cancellation')
    Dold=X+a*c+g*H;L=-v+S*X
    raw=(M*(X+a*c)+H*(M*g-v+S*X))**2-M*M*((a*a+H)*c*c+1)
    expanded=M*M*((X+g*H)**2+2*a*c*(X+g*H)-H*c*c-1)+2*M*Dold*H*L+H*H*L*L
    need(not (raw-expanded).d,'universal main-root cancellation')
    raw=(V+u)**2-U*u*(2*V+u)
    expanded=U*(V*V-(V+u)**2)+(V+u)**2
    need(not (raw-expanded).d,'universal auxiliary gap identity')
    return 3

def main():
    fixed=constants();rng=random.Random(143026)
    receipt={'scope':'Finite verification of literal data and exact local identities; unbounded proof is in proof.md.',
             'universal_local_polynomial_identities':exact_identities(),'circuits':[]}
    for name,degree,ops,resdegrees in [('p14_degree26',26,92,[11,13,3,13,10]),
                                     ('p14_degree30',30,85,[12,14,2,15,10])]:
        d=json.loads((HERE/'circuits'/(name+'.json')).read_text());ports={k:v%1000003 for k,v in fixed.items()}
        known=set(d['variables'])|set(d['fixed_ports']);byid={}
        for g in d['gates']:
            need(g['op'] in ['add','sub','mul'] and len(g['args'])==2,'binary gate')
            need(g['id'] not in known,'unique gate id')
            need(all(isinstance(x,int) or x in known for x in g['args']),'acyclic well-formed gate')
            known.add(g['id']);byid[g['id']]=g
        used=set()
        def walk(t):
            if isinstance(t,str) and t not in used:
                used.add(t)
                if t in byid:
                    for x in byid[t]['args']:walk(x)
        walk(d['output'])
        need(len(d['variables'])==14 and all(x in used for x in d['variables']),'14 live input variables')
        need(len(d['gates'])==ops and all(x in used for x in byid),'live operation count')
        for _ in range(100):
            inp={x:rng.randrange(1,101) for x in d['variables']}
            got,regs=evaluate(d,inp,ports,1000003);want,rs=direct(name,inp,ports,1000003)
            need(got==want,'independent literal formula evaluation')
            need(all(regs[k]==v for k,v in rs.items()),'independent residual transcription')
        for p in [1000003,1000033]:
            pp={k:v%p for k,v in fixed.items()}
            for _ in range(12):
                inp={x:rng.randrange(1,101) for x in d['variables']}
                poly,regs=ray(d,inp,pp,p)
                leader=expected_leader(name,inp,pp['beta'],p)
                need(len(poly)-1==degree and poly[-1]==leader,'fixed-instance degree and analytic leader on ray')
                need([len(regs[k])-1 for k in ['A0','Nm','At','Aa','As']]==resdegrees,'residual degrees on ray')
        broken=copy.deepcopy(d);broken['gates'][0]['op']='add'
        inp={x:11 for x in d['variables']}
        got,_=evaluate(broken,inp,ports,1000003);want,_=direct(name,inp,ports,1000003)
        need(got!=want,'transcription negative control')
        receipt['circuits'].append({'name':name,'variables':14,'operations':ops,'degree':degree,
          'residual_degrees':resdegrees,'formula_evaluations':100,'exact_modular_polynomial_rays':24,
          'negative_controls':1,'status':'PASS'})
    count=0
    for q in range(2,100):
        for s in range(1,13):
            Y=s*q**3
            for X in range(q+1,q+10):
                H=4*Y*(X+1)+3;S=4*q*Y;M=q*S
                need(math.gcd(S,H)<=3,'finite absorber gcd check')
                need((4*X*Y*Y)%M==0,'finite full-modulus divisibility')
                need(S//math.gcd(S,H)>q**4-1,'finite bootstrap size')
                if q%3==2:need(math.gcd(q,H)==1,'finite main quotient coprimality')
                count+=1
    receipt['bounded_carrier_checks']=count
    receipt['coefficient_payloads']='all four authentic compact ports; raw/compressed hashes and mask invariants checked'
    receipt['status']='PASS'
    (HERE/'CHECK_RESULTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
