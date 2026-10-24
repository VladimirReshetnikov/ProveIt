#!/usr/bin/env python3
"""A five-root CRT polynomial in 13 unrestricted integers, degree 1072."""
from pathlib import Path
import json
from dag_support import DAG, Expr, export, BASE_PORTS, VARS13
from five_square_norm import cleared_norm5

ROOT=Path(__file__).resolve().parent

def cleared_norm4(x,A,B,D,Cn,delta):
    q0=delta*(x*x+D-A-B)-Cn; q1=-2*delta*x
    Tn=delta*delta*A*B; Rn=delta*Cn
    t0=q0*q0+D*q1*q1-4*(Tn+Rn*(A+B)); t1=2*q0*q1
    z64=64*Tn*Rn
    f0=t0*t0+D*t1*t1-z64*(x*x+D)
    f1=2*t0*t1+2*z64*x
    return f0*f0-D*f1*f1

def cleared_norm3(x,A,B,Cn,delta):
    Jn=delta*(x*x-A-B)-Cn
    Tn=delta*delta*A*B; Rn=delta*Cn
    Kn=Jn*Jn-4*(Tn+Rn*(A+B))
    return Kn*Kn-64*Tn*Rn*x*x

def cleared_norm2(x,A,Cn,delta):
    Jn=delta*(x*x-A)-Cn
    return Jn*Jn-4*delta*A*Cn

def build(keep_f=False,keep_guard=False,keep_tau=False):
    variables=VARS13+(['f'] if keep_f else [])+(['g'] if keep_guard else [])+(['tau'] if keep_tau else [])
    d=DAG(variables)
    x={name:d.leaf('variable',name) for name in variables}
    p={name:d.leaf('coefficient',name) for name in BASE_PORTS}
    J=6*x['j']+1; q=p['beta']*J+1; q2=q*q; W=12*x['w']+4
    X=q*W; Y=q*x['v']; E=X*Y; a=E+Y; H=4*a+3; Delta=a*a+H
    C=x['C']; F=(p['K0']+W)*C-x['z']*(q-1); alpha=q-F-C
    R=(q*(q-F)-C)*(q2-1)+(p['MC']+q*p['MF'])*J
    k=R+1+x['h']*E; c=x['c']; eta=c-Y*k; zeta=k-eta
    c2=c*c; I=(2*x['r']+1)*c2; I2=I*I; Bstrong=Delta*I2
    Df=1+Bstrong
    if keep_f:
        f2=x['f']*x['f'];Q=Delta*(f2-1);V=f2*(c*x['T']-R)-c
    else:
        Q=Delta*Bstrong;V=Df*(c*x['T']-R)-c
    delta=Q-1; Cy=Q*V*V-1
    ell0=E*Y; Dtau=ell0*(ell0+1)*(k*k)+1
    Dmain=1+Delta*c2; b0=X+a*c
    coneU=p['cone_A']*F; coneZ=p['cone_B']*C
    G=coneU*coneZ-(q-coneU-coneZ)**2; Peta=eta*zeta
    Pair=G*Peta-(x['t']**2-G-Peta+1)**2
    S=24*Pair-21-(6*x['p2']-1)**2-(6*x['p3']-1)**2
    M=2*q2; U=M*H; U2=U*U
    center=U*(x['n']+V)+M*b0+H*(x['v']-q2)
    scaled_Df=9*U2*Df; scaled_Dtau=(9 if keep_f else 81)*U2*Dtau
    scaled_Dmain=M*M*Dmain; scaled_S=(81 if keep_f else 729)*U2*S; scaled_Cy=U2*Cy
    if keep_f:
        Ef=f2-Df
        Ff=f2-Bstrong
        if keep_tau:
            Etau=x['tau']**2-Dtau
            Ft=x['tau']**2-ell0*(ell0+1)*(k*k)
            Nret=cleared_norm2(center,scaled_Dmain,scaled_Cy,delta)
        elif keep_guard:
            Nret=cleared_norm3(center,scaled_Dtau,scaled_Dmain,scaled_Cy,delta)
        else:
            Nret=cleared_norm4(center,scaled_Dtau,scaled_S,scaled_Dmain,scaled_Cy,delta)
        unit=(1+Nret)*Ff
        if keep_guard:
            Eg=x['g']**2-S
            Fg=x['g']**2+22+(6*x['p2']-1)**2+(6*x['p3']-1)**2-24*Pair
            unit=unit*Fg
        if keep_tau:unit=unit*Ft
        output=unit-1
    else:
        output=cleared_norm5(center,scaled_Df,scaled_Dtau,scaled_Dmain,
                            scaled_S,scaled_Cy,delta)
    registers={name:value for name,value in locals().copy().items() if isinstance(value,Expr)}
    if keep_tau:
        degree=124;normdegree=4
        leader={'monomial':{'j':58,'w':18,'v':24,'r':2,'h':6,'f':8,'z':2,'n':2,'c':4},'coefficient':'2^113 * 3^77 * beta^58'}
    elif keep_guard:
        degree=218;normdegree=8
        leader={'monomial':{'j':104,'w':38,'v':50,'r':2,'f':8,'h':12,'c':4},'coefficient':'-2^209 * 3^151 * beta^104'}
    elif keep_f:
        degree=414;normdegree=16
        leader={'monomial':{'j':196,'w':66,'v':98,'h':32,'r':2,'f':16,'c':4},'coefficient':'-2^402 * 3^302 * beta^196'}
    else:
        degree=1072;normdegree=32
        leader={'monomial':{'j':480,'w':160,'v':192,'h':32,'r':64,'c':128,'z':16},'coefficient':'2^1000 * 3^696 * beta^480'}
    name='integer'+str(len(variables))+'_crt_valuation_degree'+str(degree)
    return export(name,d,output,registers,
      dict(exact_degree=degree,norm_degree=normdegree,crt_carrier=True,
           degree_proof='PROOF.md and FAMILY.md: exact centered norm degrees and unit products.',
           exact_leading_coefficient=leader,
           semantic_proof='../PROOF.md'))

def main():
    out=ROOT/'equations';out.mkdir(exist_ok=True)
    for packet in [build(),build(True),build(True,True),build(True,True,True)]:
        (out/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        print(json.dumps({k:packet[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']},indent=2))

if __name__=='__main__':main()
