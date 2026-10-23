"""Build a twelve-positive two-norm quotient equation, without imports of upstream code."""
import json
from pathlib import Path
OUT=Path(__file__).resolve().parent
class DAG:
 def __init__(self): self.rows=[]; self.cache={}
 def op(self,k,a,b,name=None):
  key=(k,*sorted((a,b),key=str)) if k in '+*' else (k,a,b)
  if key in self.cache:return self.cache[key]
  name=name or 'r'+str(len(self.rows));self.rows.append([name,k,a,b]);self.cache[key]=name;return name
 def add(self,a,b,n=None):return self.op('+',a,b,n)
 def sub(self,a,b,n=None):return self.op('-',a,b,n)
 def mul(self,a,b,n=None):return self.op('*',a,b,n)
 def sq(self,a,n=None):return self.mul(a,a,n)

def build():
 d=DAG();ad,su,mu,sq=d.add,d.sub,d.mul,d.sq
 qm=mu('beta','J','qm');q=ad(qm,1,'q');q2=sq(q,'q2');q3=mu(q2,q,'q3');q4=sq(q2,'q4')
 X=mu('w',q,'X');Y=mu('s',q3,'Y');E=mu(X,Y,'E')
 k=ad('eta','zeta','k');kY=mu(k,Y,'kY');c=ad(kY,'eta','c');c2=sq(c,'c2')
 a=ad(E,Y,'a');H=ad(mu(4,a),3,'H');Delta=ad(sq(a),H,'Delta')
 ell=mu(E,kY,'ell');A=ad(mu(ell,ad(ell,k)),1,'A');G=ad(mu(Delta,c2),1,'G');b0=ad(X,mu(a,c),'b0')
 qF=su(q,'F','qF');C=su(qF,'alpha','C')
 R=ad(mu(ad(mu(qm,qF),'alpha'),su(q2,1)),mu(ad('MC',mu(q,'MF')),'J'),'R')
 Nt=su(ad(mu(ad('K0','w'),C),qF),mu('z',qm),'Nt')
 U=mu(4,q4,'U');r=su(su(k,R),1,'r');S=mu(U,H,'S')
 W=ad(mu(U,b0),mu(H,ad(mu(U,ad('t',ell)),r)),'W')
 W2=sq(W,'W2');UG=mu(sq(U),G,'UG');SA=mu(sq(S),A,'SA')
 norm=su(sq(su(ad(W2,UG),SA)),mu(4,mu(W2,UG)),'N')
 I=mu('i',c2,'I');DI=mu(Delta,I,'DI');Q=sq(DI,'Q');D=ad(mu(DI,I),1,'D');daux=su(Q,1,'daux')
 v=mu(c,'T','v');baux=ad(c,mu(R,D),'baux');Dv2=mu(D,sq(v),'Dv2');b2=sq(baux,'b2')
 innerbase=ad(su(ad(Dv2,b2),1),mu(mu(daux,'y'),su(2,mu(Q,'y'))),'innerbase')
 inner=su(sq(innerbase),mu(4,mu(Dv2,b2)),'inner')
 out=su(mu(mu(Nt,ad(norm,1)),ad(inner,1)),1,'out')
 witness=['J','F','alpha','z','i','T','s','w','eta','zeta','y','t']
 blob={'domain':'strictly positive integers','witnesses':witness,'fixed_numerals':['beta','K0','MC','MF'],'source':d.rows,'output':out,'exact_degree':258,'operations':len(d.rows),'proof':'PROOF.md','coefficient_binding_file':'../coefficients/COEFFICIENT_BINDING.json','coefficient_payloads':{'beta':'../coefficients/coefficients/beta.bin.gz','K0':'../coefficients/coefficients/K.bin.gz','MC':'../coefficients/coefficients/MC.bin.gz','MF':'../coefficients/coefficients/MF_source.bin.gz'},'payload_encoding':'gzip-compressed unsigned little-endian integers; MF is already shifted'}
 (OUT/'twelve_positive_degree258.json').write_text(json.dumps(blob,indent=2)+'\n')
 return blob
if __name__=='__main__':
 b=build();print(json.dumps({k:v for k,v in b.items() if k!='source'},indent=2));print({x:sum(r[1]==x for r in b['source']) for x in '+-*'})
