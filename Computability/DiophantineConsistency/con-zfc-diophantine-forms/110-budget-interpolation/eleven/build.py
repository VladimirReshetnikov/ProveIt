#!/usr/bin/env python3
"""Eleven-variable centered-budget/intersective synthesis; no external writes."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.append(str(ROOT.parent/'guard'))
import circuit
from five_square_norm import cleared_norm5_compact2
VARIABLES=['j','C','z','h','r','v','w','T','c','n','s']
def build(root=None,variant='both'):
    base = circuit
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
    Derr=(U-q)**2+(Zc-q)**2
    Budget=k*k*(q*q-Derr)-4*q*q*eta*eta
    Dg=4*(3*Budget-4)*(x['s']*x['s'])+1
    I=2*x['s']*x['r']*(c*c)
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
    A1=4*S2*Da
    A2=S2*Df
    A3=16*S2*Dt
    A4=64*S2*Dg
    aux_shift=(2*Q-1)*V
    tau_shift=4*Ltau
    if variant=='direct':
        center=S*x['n']-A
        degree=2912
    elif variant=='aux':
        center=S*(x['n']+aux_shift)-A
        degree=2272
    elif variant=='both':
        center=S*(x['n']+aux_shift+tau_shift)-A
        degree=2240
    else:raise ValueError('variant')
    degree_proof='See DEGREE_PROOF.md and exact degree certificates.'
    # cleared_norm5(x,A,B,D,Bg,Cn,delta) is the symmetric five-root norm.
    # Here delta=1 because every radicand is an integer polynomial.
    output=cleared_norm5_compact2(center,A2,A3,A0,A4,A1,d.coerce(1))
    registers={name:value for name,value in locals().copy().items()
               if isinstance(value,base.Expr)}
    packet=base.export('budget_intersective11_degree'+str(degree),d,output,registers,
        dict(exact_degree=degree,norm_degree=32,centering_variant=variant,
             degree_proof=degree_proof,
             semantic_proof='PROOF.md',
             coordinate_note='Every coordinate is an unrestricted integer. T is the interpolated auxiliary coordinate, n is the final norm coordinate.'))
    packet['coefficient_binding']='../guard/coefficients/BINDING.json'
    return packet


def main():
    metrics=[]
    for variant in ('direct','aux','both'):
        packet=build(None,variant)
        path=ROOT/(packet['name']+'.json');path.write_text(json.dumps(packet,indent=2)+'\n')
        metrics.append({k:packet[k] for k in ('name','variable_count','exact_degree','operations','operation_counts')})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
