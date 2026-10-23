#!/usr/bin/env python3
"""New independent evaluator for the wave-4 12-positive-variable norm.
All binary operations are charged. This file reads upstream JSON as data only.
"""
from collections import Counter
from pathlib import Path
import json, random, gzip, hashlib
HERE=Path(__file__).resolve().parent
WIT=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS=['beta','K0','MC','MF']
class Circuit:
 def __init__(self): self.rows=[];self.cache={}
 def op(self,op,a,b,name=None):
  key=(op, *sorted([a,b],key=str)) if op in ['+','*'] else (op,a,b)
  if key in self.cache:return self.cache[key]
  name=name or 'g'+str(len(self.rows)+1)
  self.rows.append([name,op,a,b]);self.cache[key]=name;return name
 def a(self,a,b,name=None):return self.op('+',a,b,name)
 def s(self,a,b,name=None):return self.op('-',a,b,name)
 def m(self,a,b,name=None):return self.op('*',a,b,name)
 def sq(self,a,name=None):return self.m(a,a,name)

def build(shift=False):
 cct=Circuit(); a,s,m,sq=cct.a,cct.s,cct.m,cct.sq
 qm1=m('beta','J','qm1');q=a(qm1,1,'q');q2=sq(q,'q2');q3=m(q,q2,'q3')
 X=m('w',q,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k');kY=m(k,Y,'kY')
 ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A');c=a(kY,'eta','c');aa=a(E,Y,'a');H=a(m(4,aa),3,'H')
 Delta=a(sq(aa),H,'Delta');c2=sq(c,'c2');G=a(m(Delta,c2),1,'G');b0=a(X,m(aa,c),'b0')
 qF=s(q,'F','qF');Cw=s(qF,'alpha','Cw')
 R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(q,'MF')),'J'),'R')
 Nk=s(s(k,m('h',E)),R,'Nk');trans=m(a('K0','w'),Cw,'trans');zq=m('z',qm1,'zq')
 if shift: Nt=a('F',zq,'transport_rhs')
 else: Nt=s(a(trans,qF),zq,'Nt')
 I=m('i',c2,'I');I2=sq(I,'I2');Dm1=m(Delta,I2,'Dm1');D=a(Dm1,1,'D');Q=m(Delta,Dm1,'Q');d=s(Q,1,'d')
 T2=sq('T','T2');v2=m(c2,T2,'v2');b=a(c,m(R,D),'b')
 M=m(k,a(I2,T2),'M');HM=m(H,M,'HM');L=a(HM,1,'L');W=a(b0,m(H,'t'),'W')
 H2=sq(H,'H2');HQ=m(H2,Q,'HQ');HP=m(HQ,m(D,v2),'HP');HU=m(HQ,sq(b),'HU')
 n=m(sq(HM),A,'n');dn=m(d,n,'dn');He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
 W2=sq(W,'W2');L2G=m(sq(L),G,'L2G');Trace=m(2,m(d,a(W2,L2G)),'Trace')
 Kroot=m(d,s(W2,L2G),'Kroot');Knorm=sq(Kroot,'Knorm')
 AA=m(2,a(dn,He),'AA');constant=s(sq(s(dn,He)),j,'constant')
 at=s(Trace,AA,'at');bt=s(constant,Knorm,'bt');coef=m(16,m(dn,j),'coef')
 vr=s(m(at,a(m(at,Trace),m(2,bt))),coef,'vr');ur=s(sq(bt),m(sq(at),Knorm),'ur')
 N=a(m(ur,a(ur,m(Trace,vr))),m(Knorm,sq(vr)),'N')
 comparisons=[[Nk,1],[trans,Nt] if shift else [Nt,1],[N,0]]
 result={'domain':'positive integers','witnesses':WIT,'fixed_numerals':PORTS,'source':list(cct.rows),'comparisons':comparisons,'coefficient_binding':'COEFFICIENT_BINDING.json','proof':'PROOF.md','residual_exact_degrees':[7,2,1072],'transport_shift':shift}
 if not shift:
  out=s(m(m(Nk,Nt),a(N,1)),1,'polynomial')
  prod={**result,'source':list(cct.rows),'output':out};prod.pop('comparisons');prod.pop('residual_exact_degrees');prod['exact_degree']=1081
  return result,prod
 return result,

def audit(c):
 known=set(WIT+PORTS);live=set();count=Counter();degrees={x:1 for x in WIT}|{x:0 for x in PORTS}
 for name,op,x,y in c['source']:
  if name in known or op not in ['+','-','*']:raise ValueError('Invalid gate')
  if any(not isinstance(z,int) and z not in known for z in [x,y]):raise ValueError('Unknown wire')
  known.add(name);count[op]+=1
  d1=0 if isinstance(x,int) else degrees[x];d2=0 if isinstance(y,int) else degrees[y]
  degrees[name]=d1+d2 if op=='*' else max(d1,d2)
 live=set([c['output']]) if 'output' in c else set(z for row in c['comparisons'] for z in row if isinstance(z,str))
 for name,op,x,y in reversed(c['source']):
  if name in live:live.update(z for z in [x,y] if isinstance(z,str))
 if live != known:raise ValueError(('Unused',known-live))
 c['ledger']={'operations':len(c['source']),'multiplications':count['*'],'additions_subtractions':count['+']+count['-'],'all_gates_and_ports_live':True}
 return c

def evaluate(c,vals,p=1000000007):
 env=dict(vals)
 for name,op,x,y in c['source']:
  x=x if isinstance(x,int) else env[x];y=y if isinstance(y,int) else env[y]
  env[name]=(x+y if op=='+' else x-y if op=='-' else x*y)%p
 return env

def norm8(e,p):
 G,A,D=e['G'],e['A'],e['D'];rad=[G,A,D]
 def mul(x,y):
  z=[0]*8
  for i,a in enumerate(x):
   for j,b in enumerate(y):
    coeff=a*b
    for h in range(3):
     if (i&j)&(1<<h):coeff=coeff*rad[h]%p
    z[i^j]=(z[i^j]+coeff)%p
  return z
 result=[1]+[0]*7
 Baux=2*e['Q']*e['c']*e['T']*e['b']%p
 ev=e['Q']*(e['D']*e['v2']+e['b']**2)-1
 for su in [-1,1]:
  for st in [-1,1]:
   for sf in [-1,1]:
    lin=[e['W'],-su*e['L'],-st*e['HM'],0,0,0,0,0]
    factor=[e['d']*z%p for z in mul(lin,lin)]
    factor[0]=(factor[0]-e['H2']*ev)%p;factor[4]=sf*e['H2']*Baux%p
    result=mul(result,factor)
 if result[1:]!=[0]*7:raise ValueError('Norm failed descent')
 return result[0]

def actual_ports(prime):
 binding=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text());values={};checked={}
 for variable,name in binding['port_aliases'].items():
  row=binding['coefficient_files'][name];raw=gzip.decompress((HERE/row['path']).read_bytes())
  digest=hashlib.sha256(raw).hexdigest()
  if digest!=row['sha256'] or len(raw)!=row['bytes']:raise ValueError('Coefficient bytes mismatch '+name)
  integer=int.from_bytes(raw,'little')
  if integer.bit_length()!=row['bit_length']:raise ValueError('Coefficient bit length mismatch '+name)
  values[variable]=integer%prime;checked[name]={'sha256':digest,'bytes':len(raw),'bit_length':integer.bit_length()}
 return values,checked

def main():
 system,product=build();shifted,=build(True)
 circuits={'positive12_system104':system,'positive12_product108':product,'positive12_shifted_system103':shifted}
 for name,c in circuits.items():
  audit(c);c['name']=name
  (HERE/(name+'.json')).write_text(json.dumps(c,indent=2)+'\n')
 if [len(c['source']) for c in [system,product,shifted]]!=[104,108,103]:raise ValueError('Operation ledger changed')
 pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
 for f in pins['files']:
  if hashlib.sha256((HERE/f['path']).read_bytes()).hexdigest()!=f['sha256']:raise ValueError('Source pin mismatch')
 old=json.loads((HERE/'upstream/positive12_product.json').read_text())
 if len(old['source'])!=111:raise ValueError('Unexpected source ledger')
 checks=[]
 for prime in [1000000007,1000000009]:
  ports,payloads=actual_ports(prime);rng=random.Random(20261022+prime)
  for fixture in range(120):
   vals={n:rng.randrange(-20,21) for n in WIT+PORTS}
   if fixture>=60:vals.update(ports)
   env=evaluate(product,vals,prime);oe=evaluate(old,vals,prime)
   if env[product['output']]!=oe[old['output']]:raise ValueError('Baseline identity failed')
   if env['N']!=norm8(env,prime):raise ValueError('Independent conjugate product failed')
   se=evaluate(shifted,vals,prime);ue=evaluate(system,{**vals,'z':vals['z']+1},prime)
   if (se['trans']-se['transport_rhs'])%prime!=(ue['Nt']-1)%prime:raise ValueError('Shift identity failed')
   if se['Nk']!=ue['Nk'] or se['N']!=ue['N']:raise ValueError('Shift changed other conditions')
  checks.append({'prime':prime,'signed_random_port_fixtures':60,'signed_actual_port_fixtures':60,'baseline_identity_checks':120,'independent_conjugate_product_checks':120,'transport_shift_checks':120})
 receipt={'schema':'positive12-arithmetic-audit-v1','circuits':{n:c['ledger'] for n,c in circuits.items()},'payloads':payloads,'checks':checks,'scope':'Finite arithmetic and payload checks. Universal identities and inherited semantic equivalence are proved in PROOF.md and upstream/POSITIVE12_PROOF.md; no new Lean or Rocq build.'}
 (HERE/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
