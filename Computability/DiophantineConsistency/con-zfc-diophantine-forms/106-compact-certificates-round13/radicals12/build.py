#!/usr/bin/env python3
"""Twelve-coordinate coprime-quintic / fixed-prime / centered-auxiliary synthesis."""
import json
from pathlib import Path
from circuit import DAG,PORTS,norm5
ROOT=Path(__file__).resolve().parent
VARS=['j','C','z','h','r','v','w','T','c','n','t','s0']
def build():
 d=DAG(VARS);v={n:d.leaf(n) for n in VARS+PORTS};tag=d.tag
 j,C,z,h,r,vs,w,T,c,n,t,s0=[v[x] for x in VARS];beta,K0,MC,MF,cone_A,cone_B=[v[x] for x in PORTS]
 J=tag('J',6*j+1);q=tag('q',beta*J+1);q2=q*q;W=tag('W',12*w+4);X=tag('X',q*W);Y=tag('Y',q*vs);E=tag('E',X*Y);a=tag('a',E+Y);H=tag('H',4*a+3);Delta=tag('Delta',a*a+H)
 F=tag('F',(K0+W)*C-z*(q-1));R=tag('R',(q*(q-F)-C)*(q2-1)+(MC+q*MF)*J);k=tag('k',R+1+h*E);eta=tag('eta',c-Y*k);Zeta=tag('Zeta',eta*(k-eta));dc=cone_A*F;cc=cone_B*C;det=tag('det',dc*cc-(q-dc-cc)**2)
 P=tag('P',det*Zeta-(t*t-det-Zeta+1)**2);s=tag('s',3*s0);Dg=tag('Dg',(3*P-4)*s*s+1);c2=c*c;I=tag('I',s*r*c2);I2=I*I;core=Delta*I2;Df=tag('Df',1+core);Q=tag('Q',Delta*core);delta=tag('delta',Q-1)
 V=tag('V',Df*(c-R+4*I*T)-c);Cy=tag('Cy',Q*V*V-1);Da=tag('Da',delta*Cy);ell=tag('ell',E*Y*k);Dt=tag('Dt',1+ell*(ell+k));Dm=tag('Dm',1+Delta*c2);b0=tag('b0',X+a*c)
 M=tag('M',2*q2);L=tag('L',M*H);defect=tag('defect',vs-q2);btilde=tag('btilde',M*b0+H*defect);u=tag('u',L*T-btilde);Dtild=tag('Dtilde',M*M*Dm)
 u2=u*u;u4=u2*u2;L2=L*L;L3=L2*L;L4=L2*L2;L5=tag('L5',L4*L);D2=Dtild*Dtild;ten=10*u2*Dtild;thirtyone=31*L4;thirtytwo=32*L2
 A=tag('A',u*(u4+ten+5*D2)+thirtytwo*u*(u2+3*Dtild)+L3*(u2+Dtild)+thirtyone*u+31*L5)
 B=tag('B',5*u4+ten+D2+thirtytwo*(3*u2+Dtild)+2*L3*u+thirtyone)
 S=tag('S',I*L5);S2=S*S;Ca=tag('Caux',(2*Q-1)*V);Z=tag('norm_z',S*(n+Ca)-A)
 # Integer radicands. Group aux/strong/first internally; main and guard outside.
 ra=tag('rad_aux',4*S2*Da);rb=tag('rad_strong',36*S2*Df);rc=tag('rad_main',B*B*Dtild);rg=tag('rad_guard',2916*S2*Dg);rn=tag('rad_first',324*S2*Dt)
 out=tag('norm',norm5(Z,ra,rb,rc,rg,rn,1))
 p=d.finish(out,'integer12_degree2048',2048);p['source_interfaces']={'late_interpolation':'inherited/INTERPOLATION12.md','ordinary_calibration':'same coherent source34/source71 native/compiler/K215 family','new_steps':'coprime quintic scale carrier, guard s=3s0, fixed-prime weights, doubled auxiliary centering'}
 return p
if __name__=='__main__':
 p=build();(ROOT/'integer12_degree2048.json').write_text(json.dumps(p,indent=2)+'\n');m={k:p[k] for k in ['name','variable_count','exact_degree','live_binary_operations','operation_counts']};(ROOT/'METRICS.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m,indent=2))
