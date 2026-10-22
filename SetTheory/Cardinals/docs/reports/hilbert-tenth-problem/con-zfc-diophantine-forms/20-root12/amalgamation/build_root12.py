#!/usr/bin/env python3
"""Explicit twelve-positive-variable main-root amalgamation.
Algebra/circuit diagnostics only, not a formal verification of the compiler.
"""
import json, random
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from instance_binding import binding
from collections import Counter
from fractions import Fraction
ROOT=Path(__file__).resolve().parent
WITNESSES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
FIXED=['Bm1','Kconstant','MC','MF']
class Circuit:
 def __init__(self): self.source=[]
 def g(self,n,op,a,b): self.source.append([n,op,a,b]); return n

def build():
 c=Circuit();g=c.g
 qm1=g('qm1','*','Bm1','J'); q=g('q','+',qm1,1)
 q2=g('q2','*',q,q);q3=g('q3','*',q2,q)
 qF=g('qF','-',q,'F');Cw=g('Cw','-',qF,'alpha')
 X=g('X','*','w',q);Y=g('Y','*','s',q3);E=g('E','*',X,Y)
 k=g('k','+','eta','zeta');kY=g('kY','*',k,Y);cc=g('c','+',kY,'eta')
 a=g('a','+',E,Y);a2=g('a2','*',a,a);foura=g('foura','*',4,a)
 H=g('H','+',foura,3);Delta=g('Delta','+',a2,H)
 pack0=g('pack0','*',qm1,qF);pack1=g('pack1','+',pack0,'alpha')
 q2m1=g('q2m1','-',q2,1);pack2=g('pack2','*',pack1,q2m1)
 port0=g('port0','*',q,'MF');port1=g('port1','+','MC',port0)
 port2=g('port2','*',port1,'J');R=g('R','+',pack2,port2)
 hE=g('hE','*','h',E);nk0=g('nk0','-',k,hE);Nk=g('Nk','-',nk0,R)
 Kw=g('Kw','+','Kconstant','w');tc0=g('tc0','*',Kw,Cw)
 tc1=g('tc1','+',tc0,qF);zqm1=g('zqm1','*','z',qm1);Nt=g('Nt','-',tc1,zqm1)
 lf=g('Lfirst','*',E,kY);lfk=g('lfk','+',lf,k);ap=g('ap','*',lf,lfk);A=g('A','+',ap,1)
 c2=g('c2','*',cc,cc);I=g('I','*','i',c2);I2=g('I2','*',I,I)
 Dm1=g('Dm1','*',Delta,I2);D=g('D','+',Dm1,1);Q=g('Q','*',Delta,Dm1);d=g('d','-',Q,1)
 v=g('v','*',cc,'T');T2=g('T2','*','T','T');v2=g('v2','*',c2,T2);RD=g('RD','*',R,D);z0=g('z0','+',cc,RD)
 z02=g('z02','*',z0,z0);Dv2=g('Dv2','*',D,v2);P=g('P','+',Dv2,z02)
 QP=g('QP','*',Q,P);e=g('e','-',QP,1)
 kI2=g('kI2','*',k,I2);m0=g('m0','+',kI2,T2);M=g('M','*',2,m0);M2=g('M2','*',M,M)
 ms=g('ms','*',M,lfk);S=g('S','*',2,ms)
 HS=g('HS','*',H,S);L=g('L','+',HS,1)
 ac=g('ac','*',a,cc);b0=g('b0','+',X,ac);Lb0=g('Lb0','*',L,b0)
 Ht=g('Ht','*',H,'t');W=g('W','+',Ht,Lb0)
 Deltac2=g('Deltac2','*',Delta,c2);G=g('G','+',Deltac2,1)
 vz=g('vz','*',v,z0);Qvz=g('Qvz','*',Q,vz);B=g('B','*',2,Qvz)
 H2=g('H2','*',H,H);H4=g('H4','*',H2,H2)
 W2=g('W2','*',W,W);L2=g('L2','*',L,L);L2G=g('L2G','*',L2,G)
 Z0=g('Z0','+',W2,L2G);WL=g('WL','*',W,L);Z1=g('Z1','*',-2,WL)
 M2A=g('M2A','*',M2,A);n=g('n','*',H2,M2A)
 z0n=g('z0n','+',Z0,n);dz0n=g('dz0n','*',d,z0n);H2e=g('H2e','*',H2,e)
 C0=g('C0','-',dz0n,H2e);C1=g('C1','*',d,Z1)
 C02=g('C02','*',C0,C0);C12=g('C12','*',C1,C1);GC12=g('GC12','*',G,C12)
 q0=g('q0','+',C02,GC12);C0C1=g('C0C1','*',C0,C1);q1=g('q1','*',2,C0C1)
 B2=g('B2','*',B,B);DB2=g('DB2','*',D,B2);j=g('j','*',H4,DB2)
 d2=g('d2','*',d,d);d2n=g('d2n','*',d2,n);r=g('r','*',4,d2n)
 rz0=g('rz0','*',r,Z0);q0j=g('q0j','+',q0,j);U0=g('U0','-',q0j,rz0)
 rz1=g('rz1','*',r,Z1);U1=g('U1','-',q1,rz1)
 fourj=g('fourj','*',4,j);U02=g('U02','*',U0,U0);U12=g('U12','*',U1,U1)
 GU12=g('GU12','*',G,U12);e0=g('e0','+',U02,GU12);e1=g('e1','*',fourj,q0);Even=g('Even','-',e0,e1)
 u01=g('u01','*',U0,U1);twou01=g('twou01','*',2,u01);o1=g('o1','*',fourj,q1);Odd=g('Odd','-',twou01,o1)
 even2=g('even2','*',Even,Even);odd2=g('odd2','*',Odd,Odd);Godd2=g('Godd2','*',G,odd2)
 Res=g('Res12','-',even2,Godd2)
 system={'name':'main_root12_system','witnesses':WITNESSES,'fixed_numerals':FIXED,'coefficient_binding':binding(FIXED),'historical_source_provenance':{'repository_commit':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035','arithmetic_parent':'09-combined13; original shifted MF interface','role':'Provenance of the symbolic formulas, not the selected numeric tuple'},'source':list(c.source),'comparisons':[['Nk',1],['Nt',1],['Res12',0]],'residual_exact_degrees':[7,2,1136],'domain':'strictly positive integers'}
 guard=g('guard','+',Res,1);nknt=g('nknt','*',Nk,Nt);prod0=g('prod0','*',nknt,guard);out=g('polynomial','-',prod0,1)
 product={**system,'name':'main_root12_product','source':list(c.source),'output':out,'exact_degree':1145};product.pop('comparisons');product.pop('residual_exact_degrees')
 c.source=list(system['source']);g=c.g
 rk=g('rk','-',Nk,1);rt=g('rt','-',Nt,1);rk2=g('rk2','*',rk,rk);rt2=g('rt2','*',rt,rt);rr2=g('rr2','*',Res,Res);ss=g('ss','+',rk2,rt2);sos=g('sos','+',ss,rr2)
 squares={**system,'name':'main_root12_sos','source':list(c.source),'output':sos,'exact_degree':2272};squares.pop('comparisons');squares.pop('residual_exact_degrees')
 return system,product,squares

def evaluate(source,values):
 v=dict(values)
 for n,o,a,b in source:
  a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b]
  v[n]=a+b if o=='+' else a-b if o=='-' else a*b
 return v

def ledger(p):
 outputs=[p['output']] if 'output' in p else [a for a,b in p['comparisons']]
 need=set(outputs)
 for n,o,a,b in reversed(p['source']):
  if n in need:need.update(x for x in [a,b] if isinstance(x,str))
 assert all(n in need for n,o,a,b in p['source'])
 assert set(WITNESSES+FIXED)<=need
 counts=Counter(o for n,o,a,b in p['source'])
 return {'operations':len(p['source']),'multiplications':counts['*'],'additions_subtractions':counts['+']+counts['-'],'all_gates_live':True,'all_ports_live':True}

def independent_pair(v):
 # Independent quadratic-ring evaluation of H^8 F((W-L*b)/H).
 G=v['G']
 def add(x,y):return (x[0]+y[0],x[1]+y[1])
 def mul(x,y):return (x[0]*y[0]+G*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
 def sc(n,x):return (n*x[0],n*x[1])
 zz=mul((v['W'],-v['L']),(v['W'],-v['L']))
 C=add(sc(v['d'],zz),(v['H']**2*(v['d']*v['M']**2*v['A']-v['e']),0))
 U=add(add(mul(C,C),(v['H']**4*v['D']*v['B']**2,0)),sc(-4*v['d']**2*v['H']**2*v['M']**2*v['A'],zz))
 F=add(mul(U,U),sc(-4*v['D']*v['H']**4*v['B']**2,mul(C,C)))
 return F[0]**2-G*F[1]**2,F

def degree_check(p,seed,prime):
 rng=random.Random(seed)
 v={x:[rng.randrange(1,17),rng.randrange(1,17)] for x in WITNESSES}
 v.update({x:[z] for x,z in zip(FIXED,[31,127,10,45])})
 def add(a,b,sgn):
  z=[((a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
  while len(z)>1 and z[-1]==0:z.pop()
  return z
 for n,o,a,b in p['source']:
  a=[a] if isinstance(a,int) else v[a];b=[b] if isinstance(b,int) else v[b]
  if o=='*':
   z=[0]*(len(a)+len(b)-1)
   for i,x in enumerate(a):
    for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
   while len(z)>1 and not z[-1]:z.pop()
  else:z=add(a,b,1 if o=='+' else -1)
  v[n]=z
 if 'output' in p:actual=[len(v[p['output']])-1];expected=[p['exact_degree']]
 else:actual=[len(add(v[a],[b],-1))-1 for a,b in p['comparisons']];expected=p['residual_exact_degrees']
 assert actual==expected,(actual,expected)
 return {'seed':seed,'prime':prime,'degrees':actual}

def fixtures():
 results=[]
 for I in [2,3,5]:
  Q=I*I;d=Q-1
  chi,psi=1,0
  for idx in range(1,6):
   chi,psi=I*chi+(I*I-1)*psi,chi+I*psi
   if idx not in [3,5]:continue
   for f in [-3,2,4]:
    D=f*f;v=1;V=-chi//I;z0=v*f-V;P=D*v*v+z0*z0;e=Q*P-1;B=2*Q*v*z0
    tau=100*(z0+psi+1);A=tau*tau;M=2*(D+v*v)
    H=7;gamma=3;b0=5;b=b0+H*gamma;G=b*b
    S=2*M*(tau+1);L=H*S+1;t=L*gamma+M*tau+psi;W=H*t+L*b0
    vals={'Q':Q,'d':d,'D':D,'v':v,'z0':z0,'P':P,'e':e,'B':B,'A':A,'M':M,'H':H,'G':G,'L':L,'W':W}
    value,pair=independent_pair(vals);assert value==0
    x=Fraction(W-L*b,H);C=d*(x*x+M*M*A)-e;U=C*C+D*B*B-4*d*d*x*x*M*M*A
    fr=Fraction(-U,2*C*B);tr=(C+B*fr)/(2*d*x*M);yr=x-M*tr
    assert (fr,tr,yr)==(f,tau,psi)
    assert (b-b0)%H==0
    results.append({'I':I,'aux_index':idx,'f':f,'all_inverse_checks':True})
 return results

def main():
 packs=build();rng=random.Random(1212)
 for _ in range(100):
  values={x:rng.randrange(-3,5) for x in WITNESSES+FIXED}
  vv=evaluate(packs[0]['source'],values);norm,pair=independent_pair(vv)
  assert norm==vv['Res12'] and pair==(vv['Even'],vv['Odd'])
  assert evaluate(packs[1]['source'],values)['polynomial']==vv['Nk']*vv['Nt']*(1+norm)-1
  assert evaluate(packs[2]['source'],values)['sos']==(vv['Nk']-1)**2+(vv['Nt']-1)**2+norm*norm
 receipt={'source_pin':'f0ae4e0991ca44a7bb4e5671d42e33d775e48035','independent_signed_assignments':100,'component_fixtures':fixtures(),'packets':{},'verification_boundary':'Algebra and isolated root fixtures only. No full K215 witness, no kernel-checked compiler or logical endpoint proof.'}
 for p in packs:
  p['ledger']=ledger(p)
  p['degree_diagnostics']=[degree_check(p,12120,1000000007),degree_check(p,12121,1000000009)]
  (ROOT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
  receipt['packets'][p['name']]={'variables':len(WITNESSES),'ledger':p['ledger'],'degree_diagnostics':p['degree_diagnostics']}
 (ROOT/'ROOT12_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt['packets'],indent=2))
if __name__=='__main__':main()
