#!/usr/bin/env python3
"""Independent norm arithmetic and exact finite-field polynomial degree checks.

No numerical interpolation is used.  A complete univariate polynomial is
computed modulo a prime.  Together with the paper's homogeneous upper bound,
a nonzero coefficient in degree 954 proves that exact degree for the literal
fixed polynomial.  Random point checks below are explicitly only diagnostics.
"""
import json
import random
from pathlib import Path
import numpy as np
from build import VARIABLES, PORTS, build, evaluate, load_ports

HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise ValueError(message)

def formal_product(e,modulus=None):
    # Z[g,tau,f]/(g^2-G,tau^2-A,f^2-D), with its free rank-eight basis.
    def mul(x,y):
        z=[0]*8
        for j in range(8):
            for k in range(8):
                z[j^k]+=x[j]*y[k]*(e['G'] if j&k&1 else 1)*(e['A'] if j&k&2 else 1)*(e['D'] if j&k&4 else 1)
        return [v%modulus for v in z] if modulus else z
    ans=[1]+[0]*7
    ee=e['Q']*(e['D']*e['v']**2+e['b']**2)-1
    bb=2*e['Q']*e['v']*e['b']
    for sg in (-1,1):
        for st in (-1,1):
            for sf in (-1,1):
                z=[e['W'],-sg*e['L'],-st*e['S'],0,0,0,0,0]
                row=[e['d']*x for x in mul(z,z)]
                row[0]-=e['S']**2*ee;row[4]+=sf*e['S']**2*bb
                ans=mul(ans,row)
    require(not any(ans[1:]),'formal product failed to be scalar')
    return ans[0]

def leading(p,r,prime):
    q=r['beta']*r['J'];X=r['w']*q;Y=r['s']*q**3;E=X*Y
    k=r['eta']+r['zeta'];c=k*Y;I=r['i']*c*c;H=4*E;ell=E*c
    d=E**4*I**2;B=q**3*(q-r['F'])*E**2*I**2;V=I*r['T']*ell;U=4*q**4
    invE=pow(E,-1,prime)
    if p['carrier']=='midpoint':
        norm=pow(U,16,prime)*pow(2,14,prime)*pow(H,15,prime)*pow(d,8,prime)*pow(B,8,prime)*pow(V,4,prime)*pow(ell,3,prime)*(2*r['t']-r['i']*r['T']*c*invE)
    else:
        norm=-pow(U,16,prime)*pow(2,14,prime)*pow(H,16,prime)*pow(d,8,prime)*pow(B,8,prime)*pow(V,4,prime)*pow(ell,2,prime)*k*Y**2*(2*r['t']+k-r['i']*r['T']*c*invE)
    Nt=r['w']*(q-r['F']-r['alpha'])-r['z']*q
    return norm*Nt%prime

def exact_ray(p,ports,prime,seed):
    rng=random.Random(seed)
    env={v:np.array([0,rng.randrange(1,prime)],dtype=np.int64) for v in VARIABLES}
    env.update({v:np.array([ports[v]%prime],dtype=np.int64) for v in PORTS})
    ray={v:int(a[-1]) for v,a in env.items()}
    def trim(x):
        x=x%prime
        while len(x)>1 and x[-1]==0:x=x[:-1]
        return x
    for n,op,x,y in p['source']:
        x=np.array([x],dtype=np.int64) if isinstance(x,int) else env[x]
        y=np.array([y],dtype=np.int64) if isinstance(y,int) else env[y]
        if op=='*':
            require(min(len(x),len(y))*(prime-1)**2 < 2**63,'int64 convolution overflow')
            z=np.convolve(x,y)
        else:
            z=np.zeros(max(len(x),len(y)),dtype=np.int64)
            z[:len(x)]+=x;z[:len(y)]+=y if op=='+' else -y
        env[n]=trim(z)
    out=env[p['output']];degree=len(out)-1;lc=int(out[-1]);predicted=leading(p,ray,prime)
    require(degree==p['exact_degree'],('wrong exact degree',p['name'],degree))
    require(lc==predicted and lc!=0,('wrong leading form',p['name'],lc,predicted))
    return {'prime':prime,'ray':ray,'exact_degree':degree,'leading_coefficient':lc,'analytic_leading_form':predicted,'method':'complete univariate polynomial arithmetic; no interpolation'}

def integer_gap_fixtures():
    # Check the refined inequality without floating point or any square roots.
    # Sufficient exact bounds used in the paper: c>96 and I>=c^2.
    tested=0;below_index=0
    for q in (16,17,31,64):
        for w in (1,2,7):
            for s in (1,2):
                for eta,zeta in ((1,1),(1,2),(2,3)):
                    X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta
                    a=E+Y;Delta=(a+2)**2-1;R=q**4-3;I=c*c
                    d=Delta*Delta*I*I-1
                    # d*(Ig-cf)>b+cf follows from these three strict bounds.
                    require(c>96 and I>96*c,'weak c bound')
                    require(2*d>E**4*I**2,'d bound')
                    require(I>96*c,'gap comparison')
                    require(R<E,'R bound')
                    tested+=1;below_index+=int(k<=E)
    return {'fixtures':tested,'fixtures_with_k_le_E':below_index,'scope':'diagnostic exact bounds, not the universal proof'}

def main():
    ports=load_ports();result={'fixed_tuple_hashes_verified':True,'norm_diagnostics':{},'exact_degree_certificates':{},'weak_gap_fixtures':integer_gap_fixtures()}
    for car in ('midpoint','full'):
        p=build('product',car);rng=random.Random(954)
        for _ in range(16):
            vals={v:rng.randrange(-2,3) for v in VARIABLES+PORTS}
            e=evaluate(p,vals)
            require(e['N']==formal_product(e),'integer formal norm identity')
            require(e['N']%4 in (0,1),'mod4 unit guard')
        for _ in range(32):
            prime=1000000007;vals={v:rng.randrange(prime) for v in VARIABLES+PORTS}
            e=evaluate(p,vals,prime)
            require(e['N']==formal_product(e,prime),'modular formal norm identity')
        result['norm_diagnostics'][car]={'exact_integer_formal_products':16,'modular_formal_products':32,'scope':'transcription diagnostics; universal identity proved in report'}
        result['exact_degree_certificates'][car]=[exact_ray(p,ports,10007,954),exact_ray(p,ports,10009,955)]
        a=build('system',car);b=build('shifted_system',car)
        for _ in range(16):
            vals={v:rng.randrange(-3,4) for v in VARIABLES+PORTS};old=dict(vals);old['z']+=1
            eo=evaluate(a,old);en=evaluate(b,vals)
            require(eo['Nt']-1==en['transport_left']-en['transport_right'],'positive transport shift')
            require(eo['term1']==en['term1'] and eo['term2']==en['term2'],'shift changed norm')
        result['norm_diagnostics'][car]['transport_shift_checks']=16
    out=HERE/'generated';out.mkdir(exist_ok=True)
    (out/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
