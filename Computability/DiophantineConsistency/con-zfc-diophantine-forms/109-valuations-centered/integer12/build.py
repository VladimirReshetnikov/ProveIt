#!/usr/bin/env python3
"""Build the literal twelve-integer prime-three intersective consistency circuit.

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


def build(root=None,variant='integer',carrier='pure19'):
    import dag as base
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
    # The selected factored quintic is evaluated in two quadratic-algebra pairs.
    # All resulting registers are integer polynomials.
    u2=u*u
    H2=H*H
    H3=H2*H
    if carrier == 'pure19':
        Q0=u2+Dm+3*H2
        C0=u*(u2+3*Dm)-19*H3
        C1=3*u2+Dm
    elif carrier == 'monotone31':
        Q0=u2+Dm+31*H2
        C0=u*(u2+3*Dm+H2)+H3
        C1=3*u2+Dm+H2
    else:
        raise ValueError('unknown carrier')
    u_twice=2*u
    A=Q0*C0+u_twice*Dm*C1
    B=Q0*C1+u_twice*C0
    H5=H3*H2
    S=(x['s']*x['r'])*H5
    S2=S*S
    A0=(B*B)*Dm
    # Prime-three separation.  Main B*sqrt(Dm)/S has strictly negative
    # even 3-adic order, whereas Da,Df,Dt are units modulo 3.
    A2=9*S2*Df
    A3=81*S2*Dt
    A4=729*S2*Dg
    if variant == 'integer':
        A1=S2*Da
        center=S*x['n']-A
        output=base.cleared_norm5(center,A1,A2,A0,A3,A4,d.coerce(1))
        degree=2848
        degree_proof='Unique highest radicand A1 has degree178. Leading form A1_top^16; see PROOF.md.'
    elif variant in ('rational','centered'):
        A1=S2*Cy
        center=S*x['n']-A if variant == 'rational' else S*(x['n']+V)-A
        output=base.cleared_norm5(center,A2,A3,A0,A4,A1,delta)
        degree=2336 if variant == 'rational' else 2304
        degree_proof=('Unique highest cleared numerator A1 has degree146; leading form A1_top^16.' if variant == 'rational' else 'Pairing the auxiliary radical leaves leading form 2^16*delta_top^16*S_top^16*V_top^16*A4_top^8.')
    else:
        raise ValueError('unknown variant')
    registers={name:value for name,value in locals().copy().items()
               if isinstance(value,base.Expr)}
    packet=base.export('prime_three_'+carrier+'_'+variant+'_12_degree'+str(degree),d,output,registers,
        dict(exact_degree=degree,norm_degree=2848,weight_bound_variant=variant, carrier=carrier,
             degree_proof=degree_proof,
             semantic_proof='PROOF.md',
             coordinate_note='Every coordinate is an unrestricted integer. T is the interpolated auxiliary coordinate, n is the final norm coordinate.'))
    packet['coefficient_binding']='coefficients/BINDING.json'
    return packet



def main():
    root=Path(__file__).resolve().parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir',type=Path,default=root/'equations')
    args=parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    for carrier in ('pure19','monotone31'):
        for variant in ('integer','rational','centered'):
            packet=build(variant=variant,carrier=carrier)
            path=args.output_dir/(packet['name']+'.json')
            path.write_text(json.dumps(packet,indent=2)+'\n')
            print(json.dumps({key:packet[key] for key in ('name','variable_count','operations','exact_degree')}))

if __name__=='__main__':
    main()
