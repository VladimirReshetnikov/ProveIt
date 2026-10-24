#!/usr/bin/env python3
"""Build the literal twelve-integer monotone-intersective consistency circuit.

Only fixed integer exponents and +,-,* occur in the exported circuit.
The six fixed coefficient leaves use the inherited root-fusion binding.
Python standard library only. No consistency or halting search is run.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import sys

VARIABLES = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 't', 's']


def load_source(root):
    root = Path(root).resolve()
    sys.path.insert(0, str(root))
    spec = importlib.util.spec_from_file_location('root_fusion_builder', root/'build_equations.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def build(root,variant='product'):
    base = load_source(root)
    d = base.DAG(VARIABLES)
    x = {name:d.leaf('variable',name) for name in VARIABLES}
    p = {name:d.leaf('coefficient',name) for name in base.BASE_PORTS}
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
    # (u+d_main)^2+31H^2 has coefficients (Q0,2u).
    # (u+d_main)^3+H^2(u+d_main)+H^3 has coefficients (C0,C1).
    u2=u*u
    H2=H*H
    H3=H2*H
    Q0=u2+Dm+31*H2
    C0=u*(u2+3*Dm+H2)+H3
    C1=3*u2+Dm+H2
    u_twice=2*u
    A=Q0*C0+u_twice*Dm*C1
    B=Q0*C1+u_twice*C0
    H5=H3*H2
    S=I*H5
    S2=S*S
    A0=(B*B)*Dm
    if variant=='compact':
        L=1+A0+Dt+Df+Da+Dg*Dg
        degree=16000
        degree_proof='Unique highest radicand A4 has degree1000; its16th power is the unique degree16000 part. Explicit nonzero coefficient: 2^13056*3^8640*beta^6912 at j^6912*w^1728*v^1728*s^1344*r^1344*c^2688*T^256.'
    elif variant=='product':
        # Once the imaginary guard is extracted, P>0 and G>0 imply R>0.
        # The bounds determine successive nonzero separating weights.
        c2=c*c
        s2=x['s']*x['s']
        r2=x['r']*x['r']
        T2=x['T']*x['T']
        b_bound=1+c2+R+c2*(s2+r2)*(T2+1)
        ba=Q*(Df*b_bound+c2+1)
        bf=Delta+I2+3
        bt=2+ell*ell+k*k
        bound_K=T2+c2+1
        w1=512*(bound_K*bound_K)+1
        w2=w1*(2*ba+1)
        w3=w2*(2*bf+1)
        w4=w3*(2*bt+1)
        degree=4832
        degree_proof='Unique highest radicand A4 has degree302; its16th power is the unique degree4832 part. Explicit nonzero coefficient: 2^5024*3^3120*beta^2560 at j^2560*w^544*v^672*h^64*s^256*r^160*c^384*T^192.'
    else:
        raise ValueError('unknown weight-bound variant')
    if variant=='product':
        A1=S2*(w1*w1)*Da
        A2=S2*(w2*w2)*Df
        A3=S2*(w3*w3)*Dt
        A4=S2*(w4*w4)*Dg
    else:
        W=2*L+1
        W2=W*W
        W4=W2*W2
        W6=W4*W2
        W8=W4*W4
        A1=S2*W2*Da
        A2=S2*W4*Dg
        A3=S2*W6*Dt
        A4=S2*W8*Df
    center=S*x['n']-A
    # cleared_norm5(x,A,B,D,Bg,Cn,delta) is the symmetric five-root norm.
    # Here delta=1 because every radicand is an integer polynomial.
    output=base.cleared_norm5(center,A1,A2,A0,A3,A4,d.coerce(1))
    registers={name:value for name,value in locals().copy().items()
               if isinstance(value,base.Expr)}
    packet=base.export('monotone_intersective12_degree'+str(degree),d,output,registers,
        dict(exact_degree=degree,norm_degree=32,weight_bound_variant=variant,
             degree_proof=degree_proof,
             semantic_proof='../proofs/INTERPOLATION12.md',
             coordinate_note='Every coordinate is an unrestricted integer. T is the interpolated auxiliary coordinate, n is the final norm coordinate.'))
    packet['coefficient_binding']='../inherited/root_fusion/coefficients/BINDING.json'
    return packet


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',type=Path,
        default=Path(__file__).resolve().parent/'inherited'/'root_fusion')
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--variant',choices=['product','compact'],default='product',
        help='product: degree4832; compact: degree16000 with fewer arithmetic operations')
    args=parser.parse_args()
    packet=build(args.source_root,args.variant)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(packet,indent=2)+'\n')
    print(json.dumps({k:packet[k] for k in
        ('name','variable_count','exact_degree','operations','operation_counts')},indent=2))


if __name__=='__main__':
    main()
