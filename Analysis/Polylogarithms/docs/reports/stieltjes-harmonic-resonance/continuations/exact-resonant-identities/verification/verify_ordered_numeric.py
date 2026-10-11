#!/usr/bin/env python3
"""Independent numerical continuation for the new depth-four formula.

Direct finite ordered sums are completed by Euler--Maclaurin tails. Laurent
coefficients are extracted by a Cauchy average. The depth-four evaluator does
not use the article's regular-germ recursion or its normal form. This extends
the independently useful EM approach of the pinned Ordered Hurwitz report;
the depth-four tail and all current checks are implemented here. Results are
floating-point diagnostics, never interval certificates.
"""
import argparse
import json
from functools import lru_cache
from pathlib import Path
import mpmath as mp

def add(target,key,value):
    target[key]=target.get(key,0)+value

def convolution(left,right):
    out={}
    for h,x in left.items():
        for k,y in right.items():
            add(out,h+k,x*y)
    return out

@lru_cache(None)
def bernoullis(order):
    return tuple(mp.bernoulli(2*k)/mp.factorial(2*k) for k in range(1,order+1))

def tail(s,order,plus=True):
    out={-1:1/(s-1),0:mp.mpf('0.5') if plus else -mp.mpf('0.5')}
    for k,b in enumerate(bernoullis(order),1):
        out[2*k-1]=b*mp.rf(s,2*k-1)
    return out

def zsum(base,coefficients,x):
    return mp.fsum(co*mp.zeta(base+j,x) for j,co in coefficients.items())

def z2(s,t,a,N,K):
    finite=mp.fsum(mp.zeta(s,n+a+1)/(n+a)**t for n in range(N))
    return finite+zsum(s+t,tail(s,K,False),N+a)

def z3(s,t,v,a,N,K):
    total=mp.mpc(0); h=mp.mpc(0)
    for n in range(N):
        x=n+a
        total+=mp.zeta(s,x+1)*h/x**t
        h+=x**(-v)
    outer=tail(s,K,False)
    total+=mp.zeta(v,a)*zsum(s+t,outer,N+a)
    total-=zsum(s+t+v,convolution(outer,tail(v,K,True)),N+a)
    return total

def z4(s,t,v,w,a,N,K):
    total=mp.mpc(0); h=mp.mpc(0); h2=mp.mpc(0)
    for n in range(N):
        x=n+a
        total+=mp.zeta(s,x+1)*h2/x**t
        h2+=x**(-v)*h
        h+=x**(-w)
    outer=tail(s,K,False)
    vp,wp=tail(v,K,True),tail(w,K,True)
    total+=z2(v,w,a,N,K)*zsum(s+t,outer,N+a)
    total-=mp.zeta(w,a)*zsum(s+t+v,convolution(outer,vp),N+a)
    inner_double={}
    for j,co in tail(v,K,False).items():
        for k,ck in tail(v+w+j,K,True).items():
            add(inner_double,j+k,co*ck)
    mixed=convolution(vp,wp)
    for j,co in inner_double.items():
        add(mixed,j,-co)
    total+=zsum(s+t+v+w,convolution(outer,mixed),N+a)
    return total

def cauchy(function,k,args):
    r=mp.mpf(args.radius)
    values=[]
    for j in range(args.points):
        eps=r*mp.exp(2j*mp.pi*(mp.mpf(j)+mp.mpf('0.5'))/args.points)
        with mp.extradps(args.guard):
            values.append(function(eps)/eps**k)
    return mp.fsum(values)/args.points

def coordinates(a,args):
    N,K=args.cutoff,args.order
    g=[mp.stieltjes(j,a) for j in range(4)]
    z=lambda n:mp.zeta(n,a)
    zd=lambda n,k:mp.diff(lambda s:mp.zeta(s,a),n,k)
    B2=(g[0]**2-z(2))/2
    B3=(g[0]**3-3*g[0]*z(2)+2*z(3))/6
    B4=(g[0]**4-6*g[0]**2*z(2)+3*z(2)**2+8*g[0]*z(3)-6*z(4))/24
    E=(g[0]*g[2]-zd(2,2))/2
    F=(g[1]**2-zd(2,2))/2
    S=-g[1]*B2-g[0]*zd(2,1)+zd(3,1)
    # The poles of this normal slice have no positive powers of eps.
    eta=cauchy(lambda e:z2(1+e,1,a,N,K),1,args)
    alpha=cauchy(lambda e:z2(1+e,1,a,N,K),2,args)
    rho=2*alpha-E
    delta=E-alpha
    T=cauchy(lambda e:z2(2+e,1-e,a,N,K),1,args)
    V=g[0]*eta+g[1]*(g[0]**2+z(2))/2+g[0]*zd(2,1)-T
    triple_coefficient=cauchy(lambda e:z3(1+e,1+2*e,1+e,a,N,K),1,args)
    regular_linear=triple_coefficient-4*alpha-2*F-delta+g[3]/18
    kap=4*S-3*regular_linear
    return dict(a=a,g=g,B2=B2,B3=B3,B4=B4,E=E,F=F,S=S,
                eta=eta,rho=rho,T=T,V=V,kappa=kap,zd21=zd(2,1),z2=z(2))

def fp_formula(cdata,ray):
    p,b,c,d=map(mp.mpf,ray)
    q=cdata
    return (q['B4']+(q['S']*(b+c+d)/3+q['kappa']*(b-2*c+d)/6
                     +q['V']*(b-d)/2)/p
            +(q['E']*(c*c+d*d)/2+q['F']*c*d+q['rho']*(c*c-d*d)/2)/(p*(p+b))
            -q['g'][3]*d**3/(6*p*(p+b)*(p+b+c)))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=55)
    parser.add_argument('--guard',type=int,default=35)
    parser.add_argument('--points',type=int,default=22)
    parser.add_argument('--radius',default='0.006')
    parser.add_argument('--cutoff',type=int,default=45)
    parser.add_argument('--order',type=int,default=16)
    parser.add_argument('--tolerance',default='1e-29')
    parser.add_argument('--quick',action='store_true')
    args=parser.parse_args()
    mp.mp.dps=args.dps
    results=[]; residuals=[]; datas=[]
    def record(name,lhs,rhs,**extra):
        error=abs(lhs-rhs);residuals.append(error)
        results.append(dict(name=name,lhs=mp.nstr(lhs,args.dps-8),
                            rhs=mp.nstr(rhs,args.dps-8),
                            absolute_residual=mp.nstr(error,8),**extra))
        print(name,mp.nstr(error,5),flush=True)
    for aa in ([1] if args.quick else [1,2]):
        a=mp.mpf(aa)
        q=coordinates(a,args);datas.append(q)
        print('Coordinates computed at a='+str(aa),flush=True)
        for ray in ([(1,1,2,1)] if args.quick else [(1,1,2,1),(1,2,1,1)]):
            value=cauchy(lambda e:z4(*(1+mp.mpf(t)*e for t in ray),a,
                                     args.cutoff,args.order),0,args)
            record('Depth-four ray '+str(ray),value,fp_formula(q,ray),a=aa)
    if len(datas)==2:
        q,r=datas
        record('eta shift',q['eta']-r['eta'],-r['g'][1])
        record('rho shift',q['rho']-r['rho'],r['g'][2]/2)
        record('T shift',q['T']-r['T'],r['zd21'])
        D1=-r['g'][0]*r['g'][1]-r['zd21']
        record('kappa shift',q['kappa']-r['kappa'],3*r['eta']-2*D1)
    payload={'kind':'floating-point diagnostics, not interval certificates',
             'parameters':vars(args),'checks':results,
             'maximum_absolute_residual':mp.nstr(max(residuals),12),
             'passed':bool(max(residuals)<mp.mpf(args.tolerance)),
             'coordinates':[{'a':str(q['a']),**{k:mp.nstr(q[k],args.dps-8)
                 for k in ['eta','rho','T','kappa']}} for q in datas]}
    output=Path(__file__).resolve().parents[1]/'results'/'ordered_numeric.json'
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps(payload,indent=2))
    if not payload['passed']:
        raise SystemExit('Residual exceeds the requested diagnostic tolerance')

if __name__=='__main__':
    main()
