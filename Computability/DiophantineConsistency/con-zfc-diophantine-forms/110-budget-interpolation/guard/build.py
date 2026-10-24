#!/usr/bin/env python3
from pathlib import Path
import json
from circuit import DAG,Expr,BASE_PORTS,VARS12,export
from five_square_norm import cleared_norm5_compact2 as cleared_norm5
ROOT=Path(__file__).resolve().parent

def build(tau_centered=True):
    d=DAG(VARS12)
    x={name:d.leaf('variable',name) for name in VARS12}
    p={name:d.leaf('coefficient',name) for name in BASE_PORTS}
    J=6*x['j']+1;q=p['beta']*J+1;W=12*x['w']+4
    X=q*W;Y=q*x['v'];E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H
    C=x['C'];F=(p['K0']+W)*C-x['z']*(q-1);alpha=q-F-C
    R=(q*(q-F)-C)*(q*q-1)+(p['MC']+q*p['MF'])*J
    k=R+1+x['h']*E;c=x['c'];eta=c-Y*k
    c2=c*c;I=(2*x['r']+1)*c2;I2=I*I;Bstrong=Delta*I2
    Df=1+Bstrong;Q=Delta*Bstrong;delta=Q-1
    V=Df*(c*x['T']-R)-c;Cy=Q*V*V-1
    ell0=E*Y;L=ell0*k;Dtau=L*(L+k)+1
    Dmain=1+Delta*c2;b0=X+a*c
    coneU=p['cone_A']*F;coneZ=p['cone_B']*C
    Derr=(coneU-q)**2+(coneZ-q)**2
    budget=k*k*(q*q-Derr)-4*(q*q)*eta*eta
    Ag=budget-1-x['p2']**2-x['p3']*(x['p3']+1)
    M=2*(q*q);U=M*H;ML=M;U2=U*U
    s=U*(x['n']+L)+ML*b0+H*(x['v']-q*q) if tau_centered else U*x['n']+ML*b0+H*(x['v']-q*q)
    center=s+U*V
    scaled_Df=U2*Df;scaled_Dtau=U2*Dtau;scaled_Dmain=ML*ML*Dmain
    scaled_Ag=U2*Ag;scaled_Cy=U2*Cy
    output=cleared_norm5(center,scaled_Df,scaled_Dtau,scaled_Dmain,scaled_Ag,scaled_Cy,delta)
    r={n:v for n,v in locals().copy().items() if isinstance(v,Expr)}
    name='budget12_tau_centered' if tau_centered else 'budget12_aux_centered'
    packet=export(name,d,output,r,dict(exact_degree=1000 if tau_centered else 1024,norm_degree=32,
       crt_carrier=True,semantic_proof='PROOF.md',degree_proof='DEGREE_PROOF.md'))
    packet['coefficient_binding']='coefficients/BINDING.json'
    return packet

def main():
    metrics=[]
    for centered in (False,True):
        packet=build(centered)
        (ROOT/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
        metrics.append({k:packet[k] for k in ('name','variable_count','exact_degree','operations','operation_counts')})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
