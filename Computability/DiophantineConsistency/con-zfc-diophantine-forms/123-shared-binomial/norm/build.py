#!/usr/bin/env python3
"""Rebuild the delivered eleven-integer polynomial circuits, offline.

The common fixed tuple is authenticated and reconstructed by check.py.
All ordinary correctness arguments are in PROOF.md and the retained sources.
"""
import json
from pathlib import Path
from circuit import DAG, Expr, BASE_PORTS, export

ROOT=Path(__file__).resolve().parent
VARIABLES=['j','C','z','h','r','v','w','T','c','n','s']

def build(modulus='original', center=True, reduced=False):
    d=DAG(VARIABLES)
    x={v:d.leaf('variable',v) for v in VARIABLES}
    p={v:d.leaf('coefficient',v) for v in BASE_PORTS}
    J=6*x['j']+1; qm=p['beta']*J; q=qm+1; q2=q*q; q3=q2*q; q2four=4*q2
    W=12*x['w']+4; X=q*W; Y=(2*x['v']+1)*q3
    E=X*Y; a=E+Y; H=4*a+3; Delta=a*a+H
    F=(p['K0']+W)*x['C']-x['z']*qm
    R=(q*(q-F)-x['C'])*(q2-1)+(p['MC']+q*p['MF'])*J
    k=R+1+x['h']*(E if modulus=='original' else q2four*q2)
    c=x['c']; c2=c*c; eta=c-Y*k
    Derr=(p['cone_A']*F-q)**2+(p['cone_B']*x['C']-q)**2
    Budget=k*k*(q2-Derr)-4*q2*eta*eta
    ell=E*Y; L=ell*k; Dt=1+L*(L+k)
    D=3*Budget-4; Dg=1+4*D*Dt*x['s']*x['s']
    tguard=2*Dt*x['s']; P=Dt+D*tguard*tguard
    I=2*x['r']*c2; I2=I*I; strong=Delta*I2
    Df=strong+1; Q=Delta*strong; delta=Q-1
    b=c-R+4*I*x['T']; V=Df*b-c; Cy=Q*V*V-1; Da=delta*Cy
    K=X*(3*c-2*X)+2
    H2=H*H; H3=H2*H
    zc=H*x['T']+K; zc2=zc*zc
    Ac=(zc2+3*H2)*(zc2*zc-19*H3)
    S=x['s']*x['r']*H; S2=S*S
    B=S*x['n']-Ac
    shift=(2*Q-1)*V if center else d.coerce(0)
    center_part=S*shift
    Z=S*(x['n']+shift)-Ac
    u=S2*Df; bnorm=4*S2*Da; e=16*S2*P
    if reduced and center:
        omega=B*B+2*B*center_part+S2*(V*V+4*Q-4)
        z2=omega+bnorm
        ub=u*bnorm; ab=u+bnorm
        inner=(omega-u-e)**2-4*(ub+e*ab)
        out=inner*inner-64*ub*e*z2
    else:
        z2=Z*Z
        ub=u*bnorm; ab=u+bnorm
        inner=(z2-ab-e)**2-4*(ub+e*ab)
        out=inner*inner-64*ub*e*z2
    regs={key:value for key,value in locals().copy().items() if isinstance(value,Expr)}
    name='scalar11_'+modulus+('_center' if center else '_direct')+('_reduced' if reduced else '')
    result=export(name,d,out,regs,{'modulus':modulus,'centered':center,'reduced':reduced})
    deg=[]
    for row in result['nodes']:
        op=row[0]
        deg.append(deg[row[1]]+deg[row[2]] if op=='mul' else max(deg[row[1]],deg[row[2]]) if op in ('add','sub') else int(op=='variable'))
    result['syntactic_degree_bound']=deg[result['output']]
    result['exact_degree']=488 if not center else (464 if modulus=='original' else 440)
    result['coefficient_binding']='coefficients/BINDING.json'
    result['register_degree_bounds']={k:deg[i] for k,i in result['named_registers'].items()}
    return result

if __name__=='__main__':
    metrics=[]
    for m in ['original','q4']:
        for cen,red in ([(False,False),(True,False),(True,True)] if m=='original' else [(True,False),(True,True)]):
            p=build(m,cen,red)
            (ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            metrics.append({k:p[k] for k in ['name','variable_count','operations','operation_counts','exact_degree','syntactic_degree_bound']})
    (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))
