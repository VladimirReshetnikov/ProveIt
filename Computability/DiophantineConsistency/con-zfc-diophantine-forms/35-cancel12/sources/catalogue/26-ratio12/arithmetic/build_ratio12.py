#!/usr/bin/env python3
"""Ratio-separated 12-variable norm. Binary arithmetic circuit and audits."""
from collections import Counter
from pathlib import Path
from copy import deepcopy
import json, random
from fractions import Fraction
OUT=Path(__file__).resolve().parent
WITNESSES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','r']
FIXED=['beta','K0','MC','MF']

def require(condition,message):
 if not condition: raise ValueError(message)

def build():
 s=[]
 def g(n,o,a,b): s.append([n,o,a,b]); return n
 def add(n,a,b):return g(n,'+',a,b)
 def sub(n,a,b):return g(n,'-',a,b)
 def mul(n,a,b):return g(n,'*',a,b)
 def sq(n,a):return mul(n,a,a)
 mul('qm1','beta','J');add('q','qm1',1);sq('q2','q');mul('q3','q2','q')
 mul('X','w','q');mul('Y','s','q3');mul('E','X','Y')
 add('k','eta','zeta');mul('kY','k','Y');add('c','kY','eta')
 mul('ell','E','kY');add('ellk','ell','k');mul('ellprod','ell','ellk');add('A','ellprod',1)
 add('a','E','Y');mul('ac','a','c');add('b0','X','ac');mul('foura',4,'a');add('H','foura',3)
 sq('a2','a');add('Delta','a2','H');sq('c2','c');mul('Deltac2','Delta','c2');add('G','Deltac2',1)
 sub('qmF','q','F');sub('Cw','qmF','alpha');mul('hE','h','E');sub('index0','k','hE')
 mul('pack0','qm1','qmF');add('pack1','pack0','alpha');sub('q2m1','q2',1);mul('pack2','pack1','q2m1')
 mul('qMF','q','MF');add('mask0','MC','qMF');mul('mask1','mask0','J');add('R','pack2','mask1')
 sub('Nk','index0','R');add('Kplusw','K0','w');mul('trans0','Kplusw','Cw');add('trans1','trans0','qmF')
 mul('trans2','z','qm1');sub('Nt','trans1','trans2')
 mul('I','i','c2');sq('I2','I');mul('Dm1','Delta','I2');add('D','Dm1',1);mul('Q','Delta','Dm1');sub('d','Q',1)
 sq('T2','T');mul('v2','c2','T2');mul('RD','R','D');add('b','c','RD');mul('Dv2','D','v2');sq('b2','b')
 mul('P','Q','Dv2');mul('U','Q','b2');add('eplus1','P','U');sub('e','eplus1',1)
 mul('kI2','k','I2');add('M','kI2','T2');mul('HM','H','M');mul('twoHM',2,'HM');add('L','twoHM',1)
 mul('Hr','H','r');add('W','b0','Hr')
 sq('H2','H');sq('H2M2','HM');mul('n','H2M2','A');mul('H2e','H2','e')
 sq('W2','W');sq('L2','L');mul('L2G','L2','G');add('Z0','W2','L2G');mul('WL','W','L');mul('Z1',2,'WL')
 add('C00','Z0','n');mul('C01','d','C00');sub('C0','C01','H2e');mul('C1','d','Z1')
 sq('d2','d');mul('Kf0','d2','n');mul('Kf',4,'Kf0');mul('Kc0','Kf','Z0');mul('Kc1','Kf','Z1')
 sq('H4','H2');mul('PU','P','U');mul('j0','H4','PU');mul('j',4,'j0')
 def psq(prefix,x,y):
  sq(prefix+'xx',x);sq(prefix+'yy',y);mul(prefix+'Gyy','G',prefix+'yy');add(prefix+'0',prefix+'xx',prefix+'Gyy')
  mul(prefix+'xy',x,y);mul(prefix+'1',2,prefix+'xy');return prefix+'0',prefix+'1'
 cs0,cs1=psq('Cs','C0','C1');sub('V00',cs0,'Kc0');sub('V0','V00','j');sub('V1',cs1,'Kc1')
 vs0,vs1=psq('Vs','V0','V1');mul('fourj',4,'j');mul('fourjK0','fourj','Kc0');mul('fourjK1','fourj','Kc1')
 sub('N0',vs0,'fourjK0');sub('N1',vs1,'fourjK1');sq('N00','N0');sq('N11','N1');mul('GN11','G','N11');sub('N','N00','GN11')
 sys=dict(name='ratio12_system',witnesses=WITNESSES,fixed_numerals=FIXED,domain='strictly positive integers',source=deepcopy(s[:-1]),comparisons=[['Nk',1],['Nt',1],['N00','GN11']],residual_exact_degrees=[7,2,1072],coefficient_binding='../coefficients/COEFFICIENT_BINDING.json',source_provenance={'repository':'VladimirReshetnikov/ProveIt','commit':'a477d0fc8b6feda53796835564a988015e744d4d','bases':['20-root12/amalgamation/ROOT12_PROOF.md','21-norm12/arithmetic/build_norm12.py','22-monic12/proofs/RETAINED59_PROOF.md'],'new_reduction':'A<G ratio separation; L=1+2HM; M=kI^2+T^2'})
 add('guard',1,'N');mul('KN','Nk','Nt');mul('prod','KN','guard');sub('polynomial','prod',1)
 prod=dict(sys,name='ratio12_product',source=deepcopy(s),output='polynomial',exact_degree=1081);prod.pop('comparisons');prod.pop('residual_exact_degrees')
 shifted=deepcopy(sys); shifted['name']='ratio12_system_shifted'
 shifted['source']=[row for row in shifted['source'] if row[0] not in ['trans1','Nt']]
 pos=next(j for j,row in enumerate(shifted['source']) if row[0]=='trans2')+1
 shifted['source'].insert(pos,['transport_rhs','+','F','trans2'])
 shifted['comparisons']=[['Nk',1],['trans0','transport_rhs'],['N00','GN11']]
 shifted['coordinate_relation']='z_old=z+1; positive old compiler witnesses satisfy z_old>=2.'
 return sys,prod,shifted

def ledger(p):
 names=set(p['witnesses']+p['fixed_numerals']);ds={n:1 for n in p['witnesses']};ds.update({n:0 for n in p['fixed_numerals']})
 for n,o,a,b in p['source']:
  require(n not in names and o in ['+','-','*'] and all(isinstance(x,int) or x in names for x in [a,b]),'Invalid circuit row: '+repr([n,o,a,b]))
  da=0 if isinstance(a,int) else ds[a];db=0 if isinstance(b,int) else ds[b];ds[n]=da+db if o=='*' else max(da,db);names.add(n)
 live=set([p['output']] if 'output' in p else [x for a,b in p['comparisons'] for x in [a,b] if isinstance(x,str)])
 for n,o,a,b in reversed(p['source']):
  if n in live:live.update(x for x in [a,b] if isinstance(x,str))
 require(all(n in live for n,o,a,b in p['source']),'Dead gate');require(set(p['witnesses']+p['fixed_numerals'])<=live,'Unused port')
 ct=Counter(x[1] for x in p['source']);p['ledger']={'operations':len(p['source']),'multiplications':ct['*'],'additions_subtractions':ct['+']+ct['-'],'all_gates_live':True,'all_ports_live':True}
 p['degree_upper_by_register']=ds
 return ds

def evaluate(p,values):
 a=dict(values)
 for n,o,l,r in p['source']:
  l=l if isinstance(l,int) else a[l];r=r if isinstance(r,int) else a[r];a[n]=l+r if o=='+' else l-r if o=='-' else l*r
 return a

def norm_independent(a):
 G,A,D=a['G'],a['A'],a['D']
 def mul(x,y):
  z=[0]*8
  for i,v in enumerate(x):
   for k,w in enumerate(y):
    f=(G if i&k&1 else 1)*(A if i&k&2 else 1)*(D if i&k&4 else 1)
    z[i^k]+=f*v*w
  return z
 B=2*a['Q']*a['c']*a['T']*a['b'];out=[1]+[0]*7
 for su in [-1,1]:
  for st in [-1,1]:
   for sf in [-1,1]:
    root=[a['W'],-su*a['L'],-st*a['H']*a['M'],0,0,0,0,0]
    f=[a['d']*x for x in mul(root,root)];f[0]-=a['H2']*a['e'];f[4]+=sf*a['H2']*B;out=mul(out,f)
 require(not any(out[1:]),'Conjugate product did not descend');return out[0]

def leading_check(p,prime,seed):
 rng=random.Random(seed);v={n:(1,rng.randrange(1,31)) for n in WITNESSES}
 inp={n:c for n,(d,c) in v.items()};coeff=dict(zip(FIXED,[31,127,10,45]));v.update({n:(0,c) for n,c in coeff.items()})
 for n,o,l,r in p['source']:
  dl,cl=(0,l%prime) if isinstance(l,int) else v[l];dr,cr=(0,r%prime) if isinstance(r,int) else v[r]
  if o=='*':v[n]=(dl+dr,cl*cr%prime)
  else:
   degree=max(dl,dr);v[n]=(degree,((cl if dl==degree else 0)+(1 if o=='+' else -1)*(cr if dr==degree else 0))%prime)
 q0=31*inp['J'];k0=inp['eta']+inp['zeta']
 nlead=(2**32*inp['i']**48*k0**96*inp['w']**80*inp['s']**176*q0**656*(q0-inp['F'])**16)%prime
 plead=nlead*(-inp['h']*inp['w']*inp['s']*q0**4)*(inp['w']*(q0-inp['F']-inp['alpha'])-inp['z']*q0)%prime
 require(v['N']==(1072,nlead) and nlead!=0,'Norm leading form mismatch or zero fixture')
 require(v['polynomial']==(1081,plead) and plead!=0,'Product leading form mismatch or zero fixture')
 return {'prime':prime,'seed':seed,'N':list(v['N']),'product':list(v['polynomial'])}

def inverse_fixtures():
 out=[]
 for m in [2,3,5]:
  Q=m*m;d=Q-1;chi,psi=1,0
  for index in range(1,6):
   chi,psi=m*chi+d*psi,chi+m*psi
   if index not in [3,5]:continue
   for f in [-3,2,4]:
    D=f*f;v=1;offset=f+chi//m;tau=100*(offset+psi+1);A=tau*tau;M=2*(D+1)
    H=7;b0=5;gamma=100*tau;u=b0+H*gamma;G=u*u;L=1+2*H*M
    x=M*tau+psi;r=gamma+2*M*u+x;W=b0+H*r;B=2*Q*v*offset;e=Q*(D*v*v+offset*offset)-1
    data=dict(G=G,A=A,D=D,W=W,L=L,H=H,H2=H*H,M=M,Q=Q,d=d,c=1,T=1,b=offset,e=e)
    require(A<G and psi*psi<M*M*A,'Invalid synthetic separation fixture')
    require(norm_independent(data)==0,'Canonical norm fixture failed')
    xr=Fraction(W-L*u,H);C=d*(xr*xr+M*M*A)-e;V=C*C+D*B*B-4*d*d*xr*xr*M*M*A
    fr=Fraction(-V,2*C*B);tr=(C+B*fr)/(2*d*xr*M);yr=xr-M*tr
    require((fr,tr,yr)==(f,tau,psi),'Rational inverse fixture failed')
    out.append({'pell_m':m,'pell_index':index,'signed_f':f,'inverse_exact':True})
 return out

def main():
 ps=build();rng=random.Random(1081)
 for p in ps:ledger(p)
 for _ in range(40):
  vals={n:rng.randrange(-3,5) for n in WITNESSES+FIXED};a=evaluate(ps[1],vals)
  require(a['N']==norm_independent(a),'Norm identity failed');require(a['N1']%8==0,'Parity guard failed')
  require(evaluate(ps[1],vals)['polynomial']==a['Nk']*a['Nt']*(1+a['N'])-1,'Product finalizer failed')
  shifted=evaluate(ps[2],vals); old=evaluate(ps[1],dict(vals,z=vals['z']+1))
  require(old['Nt']-1==shifted['trans0']-shifted['transport_rhs'],'Shift identity failed')
 for p in ps:(OUT/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
 receipt={'packets':[{k:p[k] for k in ['name','ledger']} for p in ps],'exact_conjugate_product_signed_fixtures':40,'modular_leading_form_diagnostics':[leading_check(ps[1],1000000007,10810),leading_check(ps[1],1000000009,10811)],'isolated_rational_inverse_fixtures':inverse_fixtures(),'scope':'Circuit algebra, leading-form diagnostics, and isolated root fixtures only; mathematical proof is separate.'}
 (OUT/'ratio12_checks.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
