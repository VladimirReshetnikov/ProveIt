#!/usr/bin/env python3
import json
from pathlib import Path
import circuit as base
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s']
def norm4(x,a,b,e,c):
    # F3(x-u;a,b,c), in u²=e, followed by its quadratic norm.
    x2=x*x;t20=x2+e;t21=-2*x
    ab=a+b;q0=t20-ab-c;q1=t21
    tn=a*b;rn=c
    v0=q0*q0+e*q1*q1-4*(tn+rn*ab);v1=2*q0*q1
    z64=64*tn*rn
    n0=v0*v0+e*v1*v1-z64*t20;n1=2*v0*v1-z64*t21
    return n0*n0-e*n1*n1

def build(fused=False,rational=False,center='both',guard_fused=False):
    d=base.DAG(VARS);x={v:d.leaf('variable',v) for v in VARS};p={v:d.leaf('coefficient',v) for v in base.BASE_PORTS}
    J=6*x['j']+1;qm=p['beta']*J;q=qm+1;q2=q*q;q3=q2*q
    W=12*x['w']+4;X=q*W;Y=(2*x['v']+1)*q3;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H
    F=(p['K0']+W)*x['C']-x['z']*qm
    R=(q*(q-F)-x['C'])*(q2-1)+(p['MC']+q*p['MF'])*J;k=R+1+x['h']*E;c=x['c'];c2=c*c
    eta=c-Y*k;U=p['cone_A']*F;Vc=p['cone_B']*x['C'];Derr=(U-q)**2+(Vc-q)**2
    Budget=k*k*(q2-Derr)-4*q2*eta*eta
    ell=E*Y;L=ell*k;Dt=1+L*(L+k)
    D=3*Budget-4
    s2=2*x['s']
    Pg=Dt*s2;P=Dt+D*Pg*Pg
    Dg=1+D*s2*s2 if not(fused or guard_fused) else None
    Amain=a+2;Dm=1+Delta*c2
    I=s2*x['r']*c2
    if fused:I=I*P*Dm*Amain
    I2=I*I;strong=Delta*I2;Df=strong+1;Q=Delta*strong;delta=Q-1
    b=c-R+4*I*x['T'];V=Df*b-c;Cy=Q*V*V-1;Da=delta*Cy
    # Short congruence carrier, equivalent to Kquad modulo odd H.
    K=X*(3*c-2*X)+2
    H2=H*H;H3=H2*H;H5=H2*H3;S=I*H5;S2=S*S
    zc=H*x['T']+K;zc2=zc*zc;Ac=(zc2+3*H2)*(zc2*zc-19*H3)
    if fused:
        Z=S*x['n']-Ac
        product=Df*P
        output=(delta if rational else 1)*(Z*Z)-S2*product*(Cy if rational else Da)
        name='optimized_fused11_'+('rational' if rational else 'integral')
    elif guard_fused:
        shift=0 if center=='direct' else (2*Q-1)*V
        Z=S*(x['n']+shift)-Ac
        ra=S2*Df;rb=4*S2*Da;rc=16*S2*P
        Z2=Z*Z;zp=Z2*rb;ue=ra*rc
        vnorm=Z2+rb-ra-rc
        ynorm=vnorm*vnorm-4*(zp+ue)
        output=ynorm*ynorm-64*zp*ue
        name='optimized_guard_fused11_'+center
    else:
        shift=0 if center=='direct' else (2*Q-1)*V
        if center=='both':shift=shift+4*L
        Z=S*(x['n']+shift)-Ac
        ra=S2*Df;rb=16*S2*Dt;re=64*S2*Dg;rc=4*S2*Da
        output=norm4(Z,ra,rb,re,rc)
        name='scalar11_'+center
    regs={k:v for k,v in locals().copy().items() if isinstance(v,base.Expr)}
    packet=base.export(name,d,output,regs,dict(semantic_proof='PROOF.md',fused=fused,rational=rational,center=center,guard_fused=guard_fused))
    packet['coefficient_binding']='coefficients/BINDING.json'
    packet['exact_degree']=(1632 if rational else 1892) if fused else ((728 if center=='direct' else 688) if guard_fused else {'direct':1456,'aux':1136,'both':1120}[center])
    degrees=[]
    for row in packet['nodes']:
        if row[0] in ('add','sub','mul'):degrees.append(degrees[row[1]]+degrees[row[2]] if row[0]=='mul' else max(degrees[row[1]],degrees[row[2]]))
        else:degrees.append(int(row[0]=='variable'))
    packet['syntactic_degree_bound']=degrees[packet['output']]
    packet['register_degree_bounds']={k:degrees[i] for k,i in packet['named_registers'].items()}
    return packet

def main():
    packets=[build(guard_fused=True,center=c) for c in ['direct','aux']]+[build(fused=True,rational=r,center='direct') for r in [False,True]]
    for p in packets:(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    metrics=[{k:p[k] for k in ['name','variable_count','operations','operation_counts','exact_degree','syntactic_degree_bound']} for p in packets]
    (ROOT/'METRICS_OPTIMIZED.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
