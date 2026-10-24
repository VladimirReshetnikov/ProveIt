#!/usr/bin/env python3
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.append(str(ROOT.parent/'guard'))
from exact_polynomial import Ring
from audit_support import require

def cut(variant):
    names=['S','Q','V','L','k','s','d','A','e'];ring=Ring(names)
    S,Q,V,L,k,s,d,A,e=[ring.var(n) for n in names]
    C=S*(2*Q-1)*V
    Z=s+(C if variant!='direct' else 0)+(4*S*L if variant=='both' else 0)
    B=16*S*S*(L*L+L*k+1);Cn=4*S*S*(Q-1)*(Q*V*V-1)
    J=[Z*Z+d+e-A-B-Cn,2*Z,2*Z,ring.scalar(2)]
    def mul(left,right):
        out=[ring.scalar(0) for _ in range(4)]
        for i in range(4):
            for j in range(4):
                t=left[i]*right[j]
                if i&j&1:t=t*d
                if i&j&2:t=t*e
                out[i^j]=out[i^j]+t
        return out
    K=mul(J,J);K[0]=K[0]-4*(A*B+Cn*(A+B))
    f=mul(K,K);X2=[Z*Z+d+e,2*Z,2*Z,ring.scalar(2)]
    f=[v-64*A*B*Cn*X2[i] for i,v in enumerate(f)]
    weights=[34,32,25,17,7,35,70,88,94];offset=[0,35,47,82]
    deg=[[p.weighted_degree(weights)+offset[i] for i,p in enumerate(parts)] for parts in (J,K,f)]
    fd=deg[-1][0];require(all(v<fd for v in deg[-1][1:]),'scalar dominates final norms')
    lead=f[0].homogeneous(weights,fd)
    degree=4*fd
    require(degree=={'direct':2912,'aux':2272,'both':2240}[variant],'claimed exact cut degree')
    print(variant,deg,lead)
    return {'variant':variant,'names':names,'weights':weights,'root_weights':offset,'component_degrees':deg,
      'F8_leading':[[list(m),v] for m,v in lead.items()],'degree':degree}

def actual(variant):
    ring=Ring(['j','w','v','h','s','r','c','T','beta'])
    j,w,v,h,s,r,c,T,beta=[ring.var(n) for n in ring.names]
    q0=6*beta*j;W0=12*w;Y0=2*v*q0**3;a0=q0*W0*Y0;I0=2*s*r*c*c
    Q0=a0**4*I0**2;S0=I0*(4*a0)**5
    # R's leading form includes C,z. For the selected monomial with maximum
    # T exponent, only 4I0*T in the degree-five bracket contributes.
    Vsel=a0*a0*I0*I0*(4*I0*T)
    L0=h*a0*a0*Y0
    Dg0=-48*q0*q0*Y0*Y0*h*h*a0*a0*s*s
    e0=64*S0*S0*Dg0
    C0=2*S0*Q0*Vsel
    if variant=='both':
        top=2**40*C0**16*S0**8*L0**8*e0**4
        m=(1176,280,296,16,120,112,224,16,1176);expected=2**2592*3**1460
    elif variant=='aux':
        top=2**16*C0**16*(16*S0*S0*L0*L0)**8
        m=None;expected=None
    else:
        top=(4*S0*S0*Q0*Q0*Vsel*Vsel)**16
        m=None;expected=None
    degree=top.weighted_degree((1,1,1,1,1,1,1,1,0))
    require(degree=={'direct':2912,'aux':2272,'both':2240}[variant],'actual leading degree')
    require(len(top.terms)==1,'selected slice a monomial')
    onlym,coef=next(iter(top.terms.items()))
    if m is not None:require(onlym==m and coef==expected,'selected coefficient closed form')
    return {'selected_exponents':dict(zip(ring.names,onlym)),
      'coefficient_without_beta':str(coef),'degree':degree,
      'selection':'T at its maximal degree selects 4I0*T uniquely from V0; all remaining factors are monomials.'}

def main():
    result=[]
    for variant in ('direct','aux','both'):
        x=cut(variant);x['actual_coefficient']=actual(variant);result.append(x)
    (ROOT/'DEGREE_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
    return result
if __name__=='__main__':main()
