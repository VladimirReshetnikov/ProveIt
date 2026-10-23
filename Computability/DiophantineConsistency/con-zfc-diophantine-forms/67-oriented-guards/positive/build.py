#!/usr/bin/env python3
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parent
class Circuit:
 def __init__(self):self.rows=[];self.cache={}
 def gate(self,op,x,y,name=None):
  pair=sorted((x,y),key=lambda a:(str(type(a)),str(a))) if op in ['+','*'] else (x,y);key=(op,*pair)
  if key in self.cache:return self.cache[key]
  name=name or 'g'+str(len(self.rows));self.rows.append([name,op,x,y]);self.cache[key]=name;return name
 def add(self,x,y,name=None):return self.gate('+',x,y,name)
 def sub(self,x,y,name=None):return self.gate('-',x,y,name)
 def mul(self,x,y,name=None):return self.gate('*',x,y,name)
 def sq(self,x,name=None):return self.mul(x,x,name)
 def live(self,outputs):
  need=set(outputs)
  for name,op,a,b in reversed(self.rows):
   if name in need:need.update((a,b))
  return [r for r in self.rows if r[0] in need],need

def build(certificate=False):
 d=Circuit();add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
 witnesses=['J','F','alpha','z','f','i','T','w','Y','r','eta','zeta','u','gamma']
 qm=mul('beta','J','qm');q=add(qm,1,'q');q2=sq(q,'q2');q3=mul(q2,q,'q3');q6=sq(q3,'q6');q4=sq(q2,'q4');qF=sub(q,'F','qF');C=sub(qF,'alpha','C')
 X=mul('w',q,'X');Y='Y';E=mul(X,Y,'E');k=add('eta','zeta','k');kY=mul(k,Y,'kY');c=add(kY,'eta','c');c2=sq(c,'c2');a=add(E,Y,'a');H=add(mul(4,a),3,'H');Delta=add(sq(a),H,'Delta');ac=mul(a,c,'ac');b0=add(X,ac,'b0');ell=mul(E,kY,'ell');ellr=add(ell,'r','ellr')
 if certificate:
  fg=add(sq('r'),mul(ell,sub(mul(2,'r'),k)),'fg')
  first=add(add(mul(q6,sub(fg,1)),mul(mul(2,q3),mul(ellr,Y))),sq(Y),'first')
 else:first=sub(sq(add(mul(q3,ellr),Y)),mul(q6,add(mul(ell,add(ell,k)),1)),'first')
 R=add(mul(add(mul(qm,qF),'alpha'),sub(q2,1)),mul(add('MC',mul(q,'MF')),'J'),'R')
 U=mul(4,mul(q,Y),'U');index=sub(sub(k,R),1,'index');zmain=add(mul(U,X),mul(H,sub(mul(U,'gamma'),index)),'zmain')
 if certificate:main=sub(add(mul(mul(2,mul(U,ac)),zmain),sq(zmain)),mul(sq(U),add(mul(H,c2),1)),'main')
 else:main=sub(sq(add(mul(U,ac),zmain)),mul(sq(U),add(mul(Delta,c2),1)),'main')
 f2=sq('f','f2');Q=mul(Delta,sub(f2,1),'Q');I=mul('i',c2,'I');strong=sub(sq(I),Q,'strong');V=sub(mul(f2,sub(mul(c,'T'),R)),c,'V');aux=sub(sub(sq(add(V,'u')),mul(Q,mul('u',add(mul(2,V),'u')))),1,'aux')
 Nt=sub(add(mul(add('K0','w'),C),qF),mul('z',qm),'Nt');transport=sub(Nt,1,'transport')
 residuals=[first,main,strong,aux,transport];out=sq(first)
 for res in residuals[1:]:out=add(out,sq(res))
 rows,needed=d.live([out])
 if not set(witnesses+['beta','K0','MC','MF'])<=needed:raise ValueError('missing input')
 return {'domain':'strictly positive integers','witnesses':witnesses,'fixed_numerals':['beta','K0','MC','MF'],'source':rows,'output':out,'residuals':residuals,'operations':len(rows),'operation_counts':dict(Counter(x[1] for x in rows)),'exact_degree':30,'residual_degrees':[12,14,10,15,2],'coefficient_binding_file':'coefficients/COEFFICIENT_BINDING.json','proof':'PROOF.md','certificate_only':certificate}
if __name__=='__main__':
 for cert in [False,True]:
  x=build(cert);name='fourteen_positive_degree30'+('_certificate' if cert else '')+'.json';(ROOT/name).write_text(json.dumps(x,indent=2)+'\n');print(name,x['operations'],x['operation_counts'])

 x=build(False);need=set(x['residuals'])
 for n,op,a,b in reversed(x['source']):
  if n in need:need.update((a,b))
 rows=[r for r in x['source'] if r[0] in need]
 system={'domain':x['domain'],'witnesses':x['witnesses'],'fixed_numerals':x['fixed_numerals'],'source':rows,'outputs':x['residuals'],'operations':len(rows),'operation_counts':dict(Counter(r[1] for r in rows)),'residual_degrees':x['residual_degrees'],'proof':'PROOF.md'}
 (ROOT/'fourteen_positive_system.json').write_text(json.dumps(system,indent=2)+'\n')
