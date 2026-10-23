"""Locally authored polynomial emitter. No upstream executable imports."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
class Circuit:
 def __init__(self): self.rows=[];self.cache={}
 def op(self,o,x,y,n=None):
  key=(o,*sorted([x,y],key=str)) if o in '+*' else (o,x,y)
  if key in self.cache:return self.cache[key]
  n=n or 'r'+str(len(self.rows)+1);self.rows.append([n,o,x,y]);self.cache[key]=n;return n
 def m(self,x,y,n=None):return self.op('*',x,y,n)
 def a(self,x,y,n=None):return self.op('+',x,y,n)
 def s(self,x,y,n=None):return self.op('-',x,y,n)
 def q(self,x,n=None):return self.m(x,x,n)
def construct(kind):
 C=Circuit();m,a,s,q=C.m,C.a,C.s,C.q
 qm1=m('beta','J','qm1');qq=a(qm1,1,'q');q2=q(qq,'q2');q3=m(q2,qq,'q3')
 X=m('w',qq,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k')
 kY=m(k,Y,'kY');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
 c=a(kY,'eta','c');av=a(E,Y,'a');H=a(m(4,av),3,'H');Delta=a(q(av),H,'Delta');c2=q(c,'c2')
 G=a(m(Delta,c2),1,'G');ac=m(av,c,'ac');b0=a(X,ac,'b0');qF=s(qq,'F','qF');Cw=s(qF,'alpha','Cw')
 R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(qq,'MF')),'J'),'R')
 Nk=s(s(k,m('h',E)),R,'Nk');Nt=s(a(m(a('K0','w'),Cw),qF),m('z',qm1),'Nt')
 I=m('i',c2,'I');I2=q(I,'I2');Dm1=m(Delta,I2,'Dm1');D=a(Dm1,1,'D');Q=m(Delta,Dm1,'Q');d=s(Q,1,'d')
 T2=q('T','T2');v2=m(c2,T2,'v2');b=a(c,m(R,D),'b');P=m(Q,m(D,v2),'P');U=m(Q,q(b),'U')
 Mbase=m(k,a(I2,T2),'Mbase')
 M=m(2,Mbase,'M') if kind in ('half','half_aux') else Mbase
 HM=m(H,M,'HM');L=a(HM,1,'L')
 if kind=='base':shift=0
 elif kind=='b':shift=b
 else:
  delta=s(ac,ell,'delta')
  if kind in ('ac2','half','half_aux'):delta=a(delta,m(2,c),'delta2')
  md=m(Mbase,s(m(2,delta),k),'Mdelta') if kind in ('half','half_aux') else m(M,delta,'Mdelta')
  shift=a(b,md,'shift')
  if kind=='half_aux':shift=a(shift,m(m(c,'T'),m(a(av,2),I)),'shift_aux')
 ts='t' if kind=='base' else a('t',shift,'ts')
 W=a(b0,m(H,ts),'W')
 H2=q(H,'H2');n=m(q(HM),A,'n');dn=m(d,n,'dn');HP=m(H2,P,'HP');HU=m(H2,U,'HU');He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
 W2=q(W,'W2');L2G=m(q(L),G,'L2G');Trace=m(2,m(d,a(W2,L2G)),'Trace');Kroot=m(d,s(W2,L2G),'Kroot');Knorm=q(Kroot,'Knorm')
 AA=m(2,a(dn,He),'AA');constant=s(q(s(dn,He)),j,'constant');at=s(Trace,AA,'at');bt=s(constant,Knorm,'bt');coef=m(16,m(dn,j),'coef')
 vr=s(m(at,a(m(at,Trace),m(2,bt))),coef,'vr');ur=s(q(bt),m(q(at),Knorm),'ur');N=a(a(q(ur),m(Trace,m(ur,vr))),m(Knorm,q(vr)),'N')
 degree={'base':1081,'b':1041,'ac':1033,'ac2':1025,'half':1023,'half_aux':1022}[kind]
 common={'name':'positive12_shift_'+kind,'witnesses':['J','F','alpha','z','h','i','T','s','w','eta','zeta','t'],'fixed_numerals':['beta','K0','MC','MF'],'domain':'strictly positive integers','coefficient_binding':'One whole certified blank K215 tuple; MF is shifted. See ../COEFFICIENT_BINDING.json.','proof':'SHIFTED12_PROOF.md','variant':kind}
 def packet(rows,**kw):return dict(common,source=list(rows),ledger={'operations':len(rows),'multiplications':sum(r[1]=='*' for r in rows),'additions_subtractions':sum(r[1]!='*' for r in rows)},**kw)
 sy=packet(C.rows,comparisons=[[Nk,1],[Nt,1],[N,0]],exact_degrees=[7,2,degree-9]);out=s(m(m(Nk,Nt),a(N,1)),1,'polynomial');pr=packet(C.rows,output=out,exact_degree=degree)
 return pr,sy
if __name__=='__main__':
 for kind in ['base','b','ac','ac2','half','half_aux']:
  pr,sy=construct(kind)
  for typ,p in [('product',pr),('system',sy)]:
   (HERE/(p['name']+'_'+typ+'.json')).write_text(json.dumps(p,indent=2)+'\n')
  print(kind,pr['ledger'],pr['exact_degree'])
