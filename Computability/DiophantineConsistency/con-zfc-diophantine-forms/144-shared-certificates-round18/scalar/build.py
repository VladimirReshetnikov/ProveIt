#!/usr/bin/env python3
import json
from pathlib import Path
import circuit as base
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s']
def build(center='c300', free_y=True):
 d=base.DAG(VARS);x={v:d.leaf('variable',v) for v in VARS};p={v:d.leaf('coefficient',v) for v in base.BASE_PORTS}
 j,C,z,h,r,v,w,T,c,n,s=[x[v] for v in VARS]
 J=6*j+1;qm=p['beta']*J;q=qm+1;q2=q*q
 W=12*w+4;X=q*W;Y=v if free_y else q*v;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H;A=a+2
 F=(p['K0']+W)*C-z*qm
 R=(q*(q-F)-C)*(q2-1)+(p['MC']+q*p['MF'])*J;k=R+1+h*E;c2=c*c
 Yk=Y*k;eta=c-Yk;Derr=(p['cone_A']*F-q)**2+(p['cone_B']*C-q)**2
 base_budget=k*k*(q2-Derr)-4*q2*eta*eta
 if free_y:
  q3=q2*q;Yeta=Y*eta;kq3=k*q3;Budget=Yk*Yk*(q2-Derr)-q2*(4*Yeta*Yeta+kq3*kq3)
 else:Budget=base_budget
 ell=E*Y;L=E*Yk;Dt=1+L*(L+k);Dguard=Budget-4;Pg=Dt*s;P=Dt+Dguard*Pg*Pg
 Dm=1+Delta*c2;rDm=r*Dm;B=A*rDm;U=c2*rDm;AU=A*U
 strong=(Delta*c2)*AU;Df=strong+1;Q=Delta*strong;delta=Q-1
 b=c-R+4*AU*T;V=Df*b-c;Cy=Q*V*V-1
 K=X*(3*c-2*X)+2;qscale=q2*q if free_y else q2;M=2*qscale;Dcar=M*H;M2=M*M;M4=M2*M2
 Dcar2=Dcar*Dcar;Dcar3=Dcar2*Dcar;S=s*r*Dcar*M4;S2=S*S
 zc=Dcar*T+M*K+H*(v-qscale);zc2=zc*zc;Ac=(zc2+3*Dcar2)*(zc2*zc-19*Dcar3)
 weight=8
 c4=c2*c2;rc4=r*c4
 lam=(8*Delta+4)*U-rc4;shift=lam*V
 if center in ('c308','c304','c300'):
  U2=U*U;UT=U2*T;cm2=c2-2
  if center=='c308':corr=2*U*cm2;shift=shift+UT*corr
  elif center=='c304':
   A2=Delta+1;A3=A*A2;corr=2*U*cm2+16*A3;shift=shift+UT*corr
  else:
   weight=32;A2=Delta+1;A3=A*A2;rc6=rc4*c2
   lam=(32*Delta+16)*U-4*rc4
   corr=8*U*cm2+64*A3+3*rc6;shift=lam*V+UT*corr
 Z=S*(n+shift)-Ac;Z2=Z*Z
 pa=delta*Z2;pb=delta*S2*P;pc=(weight*weight)*S2*B*Df*Cy
 inner=pa+pb-pc;output=inner*inner-4*pa*pb
 regs={k:v for k,v in locals().copy().items() if isinstance(v,base.Expr)}
 packet=base.export(('free_whole_center11_' if free_y else 'weak_whole_center11_')+center,d,output,regs,dict(semantic_proof='PROOF.md',center=center,free_y=free_y,radical_weight=weight))
 packet['coefficient_binding']='coefficients/BINDING.json'
 deg=[]
 for row in packet['nodes']:
  if row[0] in ('add','sub','mul'):deg.append(deg[row[1]]+deg[row[2]] if row[0]=='mul' else max(deg[row[1]],deg[row[2]]))
  else:deg.append(int(row[0]=='variable'))
 packet['syntactic_degree_bound']=deg[packet['output']];packet['register_degree_bounds']={k:deg[i] for k,i in packet['named_registers'].items()}
 packet['exact_degree']={'c316':316,'c308':308,'c304':304,'c300':300}[center]
 return packet
if __name__=='__main__':
 ps=[build(c,True) for c in ['c316','c308','c304','c300']]
 for p in ps:(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
 metrics=[{k:p[k] for k in ['name','variable_count','operations','operation_counts','exact_degree','syntactic_degree_bound']} for p in ps]
 (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
