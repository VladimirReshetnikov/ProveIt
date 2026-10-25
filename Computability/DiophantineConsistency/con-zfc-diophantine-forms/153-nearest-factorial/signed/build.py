#!/usr/bin/env python3
"""Build the index-modulus rebasing candidates, using fixed finite formulas."""
from pathlib import Path
import argparse
import json
from circuit import DAG, Expr, export, BASE_PORTS

ROOT=Path(__file__).resolve().parent

def root_variant(parent, tag, degree):
    spec=json.loads((ROOT/(parent+'_modified_spec.json')).read_text())
    d=DAG(spec['variables'])
    env={v:d.leaf('variable',v) for v in spec['variables']}
    env.update({v:d.leaf('coefficient',v) for v in BASE_PORTS})
    for name,formula in spec['registers']:
        env[name]=eval(formula,{'__builtins__':{}},env)
    packet=export(tag,d,env['P'],{n:env[n] for n,f in spec['registers']},
                  {'exact_degree':degree,'proof':'PROOF.md','parent':parent,
                   'index_modulus':'X*Y^2','budget_q_exponent':6})
    packet['coefficient_binding']='coefficients/BINDING.json'
    return packet

def scalar_variant():
    variables=['j','C','z','h','r','v','w','T','c','n','s']
    d=DAG(variables)
    x={v:d.leaf('variable',v) for v in variables}
    p={v:d.leaf('coefficient',v) for v in BASE_PORTS}
    j,C,z,h,r,v,w,T,c,n,s=[x[v] for v in variables]
    J=6*j+1;qm=p['beta']*J;q=qm+1;q2=q*q
    W=12*w+4;X=q*W;Y=v;E=X*Y;ell=E*Y
    a=E+Y;H=4*a+3;Delta=a*a+H;A=a+2
    F=(p['K0']+W)*C-z*qm
    R=(q*(q-F)-C)*(q2-1)+(p['MC']+q*p['MF'])*J
    k=R+1+h*ell;c2=c*c;Yk=Y*k;eta=c-Yk
    Derr=(p['cone_A']*F-q)**2+(p['cone_B']*C-q)**2
    q3=q2*q;Yeta=Y*eta;kq2=k*q2
    Budget=Yk*Yk*(q2-Derr)-q2*(4*Yeta*Yeta+kq2*kq2)
    L=ell*k;Dt=1+L*(L+k);Dguard=Budget-4;Pg=Dt*s
    P=Dt+Dguard*Pg*Pg
    Dm=1+Delta*c2;rDm=r*Dm;B=A*rDm;U=c2*rDm;AU=A*U
    strong=(Delta*c2)*AU;Df=strong+1;Q=Delta*strong;delta=Q-1
    b=c-R+4*AU*T;V=Df*b-c;Cy=Q*V*V-1
    K=X*(3*c-2*X)+2;M=2*q3;Dc=M*H;M2=M*M;M4=M2*M2
    Dc2=Dc*Dc;Dc3=Dc2*Dc;S=s*r*Dc*M4;S2=S*S
    zc=Dc*T+M*K+H*(v-q3);zc2=zc*zc
    Ac=(zc2+3*Dc2)*(zc2*zc-19*Dc3)
    c4=c2*c2;rc4=r*c4;U2=U*U;UT=U2*T;cm2=c2-2
    A2=Delta+1;A3=A*A2
    lam=(32*Delta+16)*U-4*rc4
    corr=8*U*cm2+64*A3+rc4*(3*c2-16)
    Psi=lam*V+UT*corr
    Z=S*(n+Psi)-Ac;Z2=Z*Z
    pa=delta*Z2;pb=delta*S2*P;pc=1024*S2*B*Df*Cy
    inner=pa+pb-pc;output=inner*inner-4*pa*pb
    regs={k:v for k,v in locals().copy().items() if isinstance(v,Expr)}
    packet=export('integer11_degree298',d,output,regs,
                  {'exact_degree':298,'proof':'PROOF.md',
                   'index_modulus':'X*Y^2','budget_q_exponent':6,
                   'radical_weight':32,
                   'parent':'free_whole_center11_c300'})
    packet['coefficient_binding']='coefficients/BINDING.json'
    return packet

def build_all():
    return [
        root_variant('integer14_degree86_ops112','integer14_degree82',82),
        root_variant('integer14_degree94_ops110','integer14_degree90',90),
        root_variant('integer13_degree156_ops125','integer13_degree152',152),
        scalar_variant(),
    ]

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
    summaries=[]
    for packet in build_all():
        path=ROOT/(packet['name']+'.json');payload=json.dumps(packet,indent=2)+'\n'
        if args.check:
            if path.read_text()!=payload:raise ValueError('DAG reconstruction differs: '+path.name)
        else:path.write_text(payload)
        summaries.append({k:packet[k] for k in ['name','variable_count','exact_degree','operations','operation_counts']})
    path=ROOT/'METRICS.json';payload=json.dumps(summaries,indent=2)+'\n'
    if args.check:
        if path.read_text()!=payload:raise ValueError('Metric reconstruction differs')
    else:path.write_text(payload)
    print(json.dumps(summaries,indent=2))

if __name__=='__main__': main()
