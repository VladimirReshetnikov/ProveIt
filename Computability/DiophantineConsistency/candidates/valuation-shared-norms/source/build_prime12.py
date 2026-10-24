#!/usr/bin/env python3
"""Twelve-integer consistency polynomials using fixed-prime root separation.
The rational auxiliary radicand is cleared in a literal division-free norm.
"""
from pathlib import Path
import argparse,itertools,json
import circuit as base
from norm5 import cleared_norm5
VARIABLES=['j','C','z','h','r','v','w','T','c','n','t','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def build(variant='rational',order=(0,1,2,3),carrier='19'):
    d=base.DAG(VARIABLES)
    x={name:d.leaf('variable',name) for name in VARIABLES}
    p={name:d.leaf('coefficient',name) for name in PORTS}
    J=6*x['j']+1
    q=p['beta']*J+1
    W0=12*x['w']+4
    X=q*W0
    Y=(2*x['v']+1)*(q*q*q)
    E=X*Y
    a=E+Y
    H=4*a+3
    Delta=a*a+H
    C=x['C']
    F=(p['K0']+W0)*C-x['z']*(q-1)
    alpha=q-F-C
    R=(q*(q-F)-C)*(q*q-1)+(p['MC']+q*p['MF'])*J
    k=R+1+x['h']*E
    c=x['c']
    eta=c-Y*k
    zeta=k-eta
    U=p['cone_A']*F
    Zc=p['cone_B']*C
    G=U*Zc-(q-U-Zc)**2
    Peta=eta*zeta
    Pair=G*Peta-(x['t']*x['t']-G-Peta+1)**2
    Dg=(3*Pair-4)*(x['s']*x['s'])+1
    I=x['s']*x['r']*(c*c)
    I2=I*I
    Df=1+Delta*I2
    Q=(Delta*Delta)*I2
    delta=Q-1
    V=Df*(c-R+4*I*x['T'])-c
    Cy=Q*(V*V)-1
    Da=delta*Cy
    ell=E*Y
    Ltau=ell*k
    Dt=1+Ltau*(Ltau+k)
    Dm=1+Delta*(c*c)
    b0=X+a*c
    u=H*x['T']-b0
    # Compute the homogeneous quintic in the quadratic algebra d_main^2=Dm.
    # The default carrier is ((u+d_main)^2+3H^2)*((u+d_main)^3-19H^3).
    # Carrier31 is retained only as an explicit comparison build.
    u2=u*u
    H2=H*H
    H3=H2*H
    if carrier=='19':
        Q0=u2+Dm+3*H2
        C0=u*(u2+3*Dm)-19*H3
        C1=3*u2+Dm
    elif carrier=='31':
        Q0=u2+Dm+31*H2
        C0=u*(u2+3*Dm+H2)+H3
        C1=3*u2+Dm+H2
    else: raise ValueError('unknown carrier')
    u_twice=2*u
    A=Q0*C0+u_twice*Dm*C1
    B=Q0*C1+u_twice*C0
    H5=H3*H2
    S=I*H5
    S2=S*S
    A0=(B*B)*Dm
    center=S*x['n']-A
    integer_radicands=[A0,9*S2*Df,81*S2*Dt,729*S2*Dg]
    rs=[integer_radicands[i] for i in order]
    if variant=='rational':
        cn=S2*Cy
        output=cleared_norm5(center,*rs,cn,delta)
        degree=2400
        degree_certificate={
            'monomial':{'j':1152,'w':288,'v':288,'s':160,'r':160,'c':320,'T':32},
            'coefficient':{'2':2400,'3':1440,'beta':1152},
            'top_form':'2^320*a_top^288*I_top^128*(4*I_top*T-R_top)^32'}
    elif variant=='integral':
        cn=S2*Da
        output=cleared_norm5(center,*rs,cn,d.coerce(1))
        degree=2912
        degree_certificate={
            'monomial':{'j':1408,'w':352,'v':352,'s':192,'r':192,'c':384,'T':32},
            'coefficient':{'2':2848,'3':1760,'beta':1408},
            'top_form':'2^320*a_top^352*I_top^160*(4*I_top*T-R_top)^32'}
    else: raise ValueError(variant)
    registers={name:value for name,value in locals().copy().items() if isinstance(value,base.Expr)}
    packet=base.export('prime_separated12_degree'+str(degree),d,output,registers,
        dict(exact_degree=degree,norm_degree=32,variant=variant,carrier=carrier,
             norm_integer_order=list(order),degree_certificate=degree_certificate,
             semantic_proof='../proofs/PRIME_TWELVE.md'))
    packet['coefficient_binding']='../inherited/root_fusion/coefficients/BINDING.json'
    return packet

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--variant',choices=['rational','integral'],default='rational')
    ap.add_argument('--optimize-order',action='store_true');ap.add_argument('--carrier',choices=['19','31'],default='19');args=ap.parse_args()
    orders=itertools.permutations(range(4)) if args.optimize_order else [(0,1,2,3)]
    packets=[build(args.variant,o,args.carrier) for o in orders]
    p=min(packets,key=lambda p:(p['operations'],p['norm_integer_order']))
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(p,indent=2)+'\n')
    print(json.dumps({k:p[k] for k in ('name','variables','operations','operation_counts','exact_degree','norm_integer_order')},indent=2))
if __name__=='__main__': main()
