#!/usr/bin/env python3
"""Finite checks supporting the documented conditional 88 transport obstruction."""
from hashlib import sha256
from math import isqrt
import gzip,json
from pathlib import Path
import sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2]
G88=D/'research/ordinary12-absorb88-probe/graph-dag.json';G89=D/'research/ordinary12-absorb89-probe/graph-dag.json'
PAY=D/'candidates/free-j-polarized-positive/source/positive/coefficients/payloads'
PINS={G88:'84a9a529636d6cadcf0f0c673c0728aa7b6fcbc0e2f2ac562a377553de831b25',
 G89:'280b23e5be95692b9db0183affce4247d974320ded1e709f41b05cc7e32b2fdd',
 PAY/'beta.bin.gz':'466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c',
 PAY/'K.bin.gz':'b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
for p,h in PINS.items():need(sha(p)==h,'pin drift '+str(p))
g88=json.loads(G88.read_text());g89=json.loads(G89.read_text());rows={r[0]:r[1:] for r in g88['source']}
need(rows['qF']==['-','q','F'] and rows['G']==['+','alpha','g44'] and rows['g44']==['*','qF','qm'],'G definition')
need(rows['C']==['-','qF','alpha'] and rows['kw']==['+','K0','w'] and rows['g27']==['*','C','kw'] and rows['g28']==['-','g27','F'] and rows['Bt']==['*','q','g28'],'Bt definition')
need(rows['folded_kBt']==['*','k','Bt'] and rows['folded_g31']==['-','r','folded_kBt'] and rows['g33']==['*','qm','folded_g31'] and rows['Z']==['-','g33','Bt'],'first residual definition')
def dependencies(start,cut):
 seen=set();todo=[start]
 while todo:
  n=todo.pop()
  if n in seen or n in cut:continue
  seen.add(n)
  if n in rows:todo.extend(x for x in rows[n][1:] if isinstance(x,str))
 return seen
for n in ('A1','N'):
 need(not ({'F','alpha','Bt','r'}&dependencies(n,{'G'})),'other residual depends outside G: '+n)
beta=int.from_bytes(gzip.decompress((PAY/'beta.bin.gz').read_bytes()),'little')
K0=int.from_bytes(gzip.decompress((PAY/'K.bin.gz').read_bytes()),'little')
need(0<beta and 0<=K0<beta*beta,'fixed coefficient bound')
def evaluate(graph,values):
 v={i:i for i in range(5)};v.update(values)
 for name,op,x,y in graph['source']:
  a,b=v[x],v[y];v[name]=a+b if op=='+' else a-b if op=='-' else a*b
 return v
# Concrete first-factor test. Other residuals are deliberately not claimed to
# vanish; their exact preservation demonstrates the substitution on the DAG.
v={name:1 for name in g89['witnesses']+g89['fixed_numerals']}
v.update(beta=3,K0=1,MC=0,MF=0,r=27)
a=evaluate(g89,v);b=a['qm'];q=a['q'];ell=a['ell'];k=a['k'];Bt=a['Bt'];w=v['w'];s=v['s'];K=v['K0']
first=isqrt(1+ell*(ell+k));need(first*first==1+ell*(ell+k) and a['A0']==0 and Bt>0 and Bt%b==0,'starting first root')
step=q*(q*(K+w)+1);j=(Bt//b)//step+1;shift=b*j;Bnew=Bt-shift*step
need(Bnew<0 and Bnew%b==0,'crossing');t=(-Bnew)//b;need(1<=t<=step,'crossing bound')
Rnew=first-(k*b+1)*t
v2=dict(v);v2.update(F=v['F']+shift,alpha=v['alpha']+b*shift,r=Rnew)
z=evaluate(g88,v2)
need(Rnew>0 and z['Bt']==Bnew and z['Z']==b*first and z['A0']==0,'transformed first residual')
need(z['G']==a['G'] and z['A1']==a['A1'] and z['N']==a['N'] and z['P12']==a['P12'],'other factors/output')
need(a['P12']!=0,'example is unexpectedly a full zero')
for p,h in PINS.items():need(sha(p)==h,'input changed '+str(p))
print(json.dumps({'status':'PASS','fixed_beta_bits':beta.bit_length(),'fixed_K_bits':K0.bit_length(),
 'fixed_K_less_than_beta_squared':True,'sample':{'b':b,'q':q,'ell':ell,'k':k,'first':first,'Bt_before':Bt,
 'shift':shift,'Bt_after':Bnew,'new_absorbed_witness':Rnew,'first_residual':z['A0'],
 'other_residuals_preserved':True,'full_zero':False},
 'scope':'finite support for a conditional standard-natural argument; no full-zero construction, Lean model proof or existential inequivalence'},indent=2,sort_keys=True))
