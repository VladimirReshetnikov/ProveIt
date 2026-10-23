"""Newly authored finite straight-line circuits; no executable upstream imports."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
class DAG:
 def __init__(self): self.rows=[]; self.memo={}
 def op(self,op,x,y,name=None):
  key=(op,*sorted((x,y),key=str)) if op in ('+','*') else (op,x,y)
  if key in self.memo:return self.memo[key]
  name=name or 'r'+str(len(self.rows));self.rows.append([name,op,x,y]);self.memo[key]=name;return name
 def add(self,x,y,n=None):return self.op('+',x,y,n)
 def sub(self,x,y,n=None):return self.op('-',x,y,n)
 def mul(self,x,y,n=None):return self.op('*',x,y,n)
 def sq(self,x,n=None):return self.mul(x,x,n)
def make(kind):
 d=DAG();a,s,m,q=d.add,d.sub,d.mul,d.sq
 qm=m('beta','J','qm');Qbase=a(qm,1,'q');q2=q(Qbase,'q2');q3=m(q2,Qbase,'q3')
 X=m('w',Qbase,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k');kY=m(k,Y,'kY');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
 c=a(kY,'eta','c');av=a(E,Y,'a');H=a(m(4,av),3,'H');delta=a(q(av),H,'Delta');c2=q(c,'c2');G=a(m(delta,c2),1,'G');ac=m(av,c,'ac');b0=a(X,ac,'b0')
 qF=s(Qbase,'F','qF');C=s(qF,'alpha','C');R=a(m(a(m(qm,qF),'alpha'),s(q2,1)),m(a('MC',m(Qbase,'MF')),'J'),'R')
 Nk=s(s(k,m('h',E)),R,'Nk');Nt=s(a(m(a('K0','w'),C),qF),m('z',qm),'Nt')
 I=m('i',c2,'I');S=m(delta,I,'S');Q=q(S,'Q');D=a(m(I,S),1,'D');dd=s(Q,1,'d');v=m(c,'T','v');b=a(c,m(R,D),'b');Dv2=m(D,q(v),'Dv2');b2=q(b,'b2')
 k2=q(k,'k2');k4=q(k2,'k4');u=m(k4,'i','u');M0=m(u,a(u,'T'),'M0')
 M=m(2,M0,'M') if kind in ['half_aux'] else M0
 HM=m(H,M,'HM');L=a(HM,1,'L');shift=0
 if kind!='base':shift=b
 if kind in ['ac_aux','ac2_aux','half_aux']:
  de=s(ac,ell,'de')
  if kind in ['ac2_aux','half_aux']:de=a(de,m(2,c),'de2')
  md=m(M0,s(m(2,de),k),'md') if kind=='half_aux' else m(M,de,'md')
  shift=a(shift,md,'shift')
 if kind.endswith('aux'):
  f0=m(a(av,2),I,'f0');shift=a(shift,m(v,f0),'shiftaux')
 ts='t' if shift==0 else a('t',shift,'ts');W=a(b0,m(H,ts),'W')
 H2=q(H,'H2');n=m(q(HM),A,'n');dn=m(dd,n,'dn');H2Q=m(H2,Q,'H2Q');HP=m(H2Q,Dv2,'HP');HU=m(H2Q,b2,'HU');He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
 W2=q(W,'W2');L2G=m(q(L),G,'L2G');Tr=m(2,m(dd,a(W2,L2G)),'Tr');Kn=q(m(dd,s(W2,L2G)),'Kn');AA=m(2,a(dn,He),'AA');cc=s(q(s(dn,He)),j,'cc');at=s(Tr,AA,'at');bt=s(cc,Kn,'bt');co=m(16,m(dn,j),'co');vr=s(m(at,a(m(at,Tr),m(2,bt))),co,'vr');ur=s(m(q(at),Kn),q(bt),'ur');left=m(ur,s(m(Tr,vr),ur),'norm_left');right=m(Kn,q(vr),'norm_right')
 common={'variant':kind,'domain':'positive integers','witnesses':['J','F','alpha','z','h','i','T','s','w','eta','zeta','t'],'fixed_numerals':['beta','K0','MC','MF'],'binding':'Complete package31 wang943-mixed-121x8801 tuple; never mix ports.','coefficient_binding_file':'COEFFICIENT_BINDING.json','proof':'WEIGHT10_PROOF.md'}
 sy={**common,'source':d.rows.copy(),'comparisons':[[Nk,1],[Nt,1],[left,right]]}
 N=s(right,left,'N');out=s(m(m(Nk,Nt),a(N,1)),1,'out');pr={**common,'source':d.rows.copy(),'output':out}
 degree={'base':1081,'b':961,'b_aux':949,'ac_aux':945,'ac2_aux':941,'half_aux':941}[kind]
 pr['exact_degree']=degree;sy['exact_maximum_residual_degree']=degree-9
 for obj in [sy,pr]:
  needed=set([obj['output']]) if 'output' in obj else set(v for p in obj['comparisons'] for v in p)
  for row in reversed(obj['source']):
   if row[0] in needed:needed.update(row[2:])
  obj['source']=[r for r in obj['source'] if r[0] in needed]
  obj['operations']=len(obj['source'])
 return sy,pr
if __name__=='__main__':
 for kind in ['base','b','b_aux','ac_aux','ac2_aux','half_aux']:
  for tag,obj in zip(['system','product'],make(kind)):
   (ROOT/('positive12_weight10_'+kind+'_'+tag+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
   print(kind,tag,obj['operations'])
