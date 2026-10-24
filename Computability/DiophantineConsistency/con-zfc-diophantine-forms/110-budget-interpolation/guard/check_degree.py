#!/usr/bin/env python3
from pathlib import Path
import json
from exact_polynomial import Ring
ROOT=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok:raise ValueError(msg)

def cut(centered):
    names=['U','s','V','d','A','L','k','e','delta']
    ring=Ring(names)
    U,s,V,d,A,L,k,e,D=[ring.var(n) for n in names]
    B=U*U*(L*L+L*k+1)
    Z=U*V+s+(U*L if centered else 0)
    Cn=U*U*((D+1)*V*V-1)
    J=[D*(Z*Z+d+e-A-B)-Cn,2*D*Z,2*D*Z,2*D]
    def multiply(left,right):
        out=[ring.scalar(0) for _ in range(4)]
        for i in range(4):
            for j in range(4):
                term=left[i]*right[j]
                if i&j&1:term=term*d
                if i&j&2:term=term*e
                out[i^j]=out[i^j]+term
        return out
    K=multiply(J,J);K[0]=K[0]-4*(D*D*A*B+D*Cn*(A+B))
    f=multiply(K,K)
    X2=[Z*Z+d+e,2*Z,2*Z,ring.scalar(2)]
    f=[value-64*D**3*A*B*Cn*X2[i] for i,value in enumerate(f)]
    weights=[6,7,19,14,26,11,5,28,22];offsets=[0,7,14,21]
    degrees=[[p.weighted_degree(weights)+offsets[i] for i,p in enumerate(parts)] for parts in (J,K,f)]
    fd=max(degrees[-1]);lead=f[0].homogeneous(weights,fd)
    require(fd==max(degrees[-1]),'scalar max')
    require(all(degrees[-1][i]<fd for i in range(1,4)),'strict scalar dominance')
    print('centered',centered,'degrees',degrees,'top',lead,'sizes',[len(v.terms) for v in f])
    return {'tau_centered':centered,'cut_names':names,'weights':weights,'root_offsets':offsets,'component_degrees':degrees,
            'F8_scalar_leading':[[list(m),v] for m,v in lead.items()],'exact_degree':4*fd,'cut_monomials':[len(v.terms) for v in f]}

def actual_leading(centered):
    lead=Ring(['j','w','v','h','r','c','z','C','beta'])
    j,w,v,h,r,c,z,C,beta=[lead.var(n) for n in lead.names]
    q0=6*beta*j; X0=12*w*q0; Y0=q0*v; a0=X0*Y0; i0=2*r
    R0=q0**4*z-12*q0**3*w*C; k0=R0+h*a0; eta0=-Y0*k0
    Q0=a0**4*i0**2*c**4; U0=8*q0**2*a0
    V0=-a0**2*i0**2*c**4*R0; L0=X0*Y0**2*k0
    e0=-4*U0**2*q0**2*eta0**2
    if centered:
        top=2**24*Q0**16*U0**24*V0**16*L0**8*e0**4
        monomial=(456,152,168,16,64,128,16,0,456)
        expected=2**952*3**608
    else:
        top=2**16*Q0**16*U0**32*V0**16*L0**16
        monomial=(464,160,176,16,64,128,16,0,464)
        expected=2**960*3**624
    require(top.terms.get(monomial)==expected,'actual-coefficient leading monomial')
    degree=top.weighted_degree((1,1,1,1,1,1,1,1,0))
    require(degree==(1000 if centered else 1024),'actual exact total degree')
    return {'degree':degree,'selected_exponents':dict(zip(lead.names,monomial)),
        'selected_coefficient_without_beta':str(expected),'leading_monomials':len(top.terms)}

def main():
    results=[cut(False),cut(True)]
    for result in results:
        result['actual_leading_certificate']=actual_leading(result['tau_centered'])
    (ROOT/'DEGREE_CHECK.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
