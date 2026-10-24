#!/usr/bin/env python3
import json
from pathlib import Path
import circuit as base
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','s']
def build(rational=True, center='none'):
 d=base.DAG(VARS);x={v:d.leaf('variable',v) for v in VARS};p={v:d.leaf('coefficient',v) for v in base.BASE_PORTS}
 J=6*x['j']+1;qm=p['beta']*J;q=qm+1;q2=q*q;q3=q2*q
 W=12*x['w']+4;X=q*W;Y=(2*x['v']+1)*q3;E=X*Y;a=E+Y;H=4*a+3;Delta=a*a+H
 F=(p['K0']+W)*x['C']-x['z']*qm
 R=(q*(q-F)-x['C'])*(q2-1)+(p['MC']+q*p['MF'])*J;k=R+1+x['h']*E;c=x['c'];c2=c*c
 eta=c-Y*k;U=p['cone_A']*F;Vc=p['cone_B']*x['C'];Derr=(U-q)**2+(Vc-q)**2
 Budget=k*k*(q2-Derr)-4*q2*eta*eta
 ell=E*Y;L=ell*k;Dt=1+L*(L+k);D=3*Budget-4;s2=2*x['s'];Pg=Dt*s2;P=Dt+D*Pg*Pg
 A=a+2;Dm=1+Delta*c2;Ib=x['s']*x['r']*c2*Dm;I=2*A*Ib
 I2=I*I;strong=Delta*I2;Df=strong+1;Q=Delta*strong;delta=Q-1
 b=c-R+4*I*x['T'];V=Df*b-c;Cy=Q*V*V-1
 K=X*(3*c-2*X)+2
 H2=H*H;H3=H2*H;H5=H2*H3;S=I*H5;S2=S*S
 zc=H*x['T']+K;zc2=zc*zc;Ac=(zc2+3*H2)*(zc2*zc-19*H3)
 shift=0
 if center=='strong':shift=A*I*V
 elif center=='sharp':lam=(2*Delta+1)*Ib;shift=lam*V
 Z=S*(x['n']+shift)-Ac;Z2=Z*Z
 if rational:
  pa=delta*Z2;pb=4*delta*S2*P;pc=S2*Df*Cy
  rnorm=pa+pb-pc
  output=rnorm*rnorm-4*pa*pb
 else:
  Da=delta*Cy;ra=S2*Df*Da;rb=4*S2*P;rnorm=Z2-ra-rb;output=rnorm*rnorm-4*ra*rb
 name='pair_fused11_'+('rational' if rational else 'integral')+('_'+center if center!='none' else '')
 regs={k:v for k,v in locals().copy().items() if isinstance(v,base.Expr)}
 packet=base.export(name,d,output,regs,dict(semantic_proof='PROOF.md',rational=rational,center=center))
 packet['coefficient_binding']='coefficients/BINDING.json'
 degrees=[]
 for row in packet['nodes']:
  if row[0] in ('add','sub','mul'):degrees.append(degrees[row[1]]+degrees[row[2]] if row[0]=='mul' else max(degrees[row[1]],degrees[row[2]]))
  else:degrees.append(int(row[0]=='variable'))
 packet['syntactic_degree_bound']=degrees[packet['output']]
 packet['register_degree_bounds']={k:degrees[i] for k,i in packet['named_registers'].items()}
 packet['exact_degree']={'none':820,'strong':796,'sharp':772}[center] if rational else 964
 return packet
if __name__=='__main__':
 packets=[build(True,c) for c in ['none','strong','sharp']]+[build(False)]
 for p in packets:(ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
 metrics=[{k:p[k] for k in ['name','variable_count','operations','operation_counts','exact_degree','syntactic_degree_bound']} for p in packets]
 (ROOT/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2))
