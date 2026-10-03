#!/usr/bin/env python3
"""Independent literal-source audit; authenticates but never executes subjects."""
import argparse, hashlib, json
from collections import Counter
from pathlib import Path
AUTHOR={
 'native_pell_factored_first_coefficient.py':'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc',
 'native_pell_factored_first_coefficient.json':'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf',
 'native_pell_factored_first_coefficient.md':'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528'}
PARENTS={
 'native_binary_masked_selection63.py':'fcff972928d234450901021b2fce5acf41e0c917ab8174ac67fee0b60df7c985',
 'native_binary_masked_selection63.json':'18f0f6158aa1ef6da2a648f1eaef125d2cacbde7ed302be89044075ba875823d',
 'native_binary_masked_selection63.md':'c2e08f2d9fdaaf2e17880d7a131254492afd7ef21b035985714734cbc158c53e',
 'native_binary_positive_scale.py':'94842053d35207d73b4ac1890552b16d7576a017f957c0c97bd42ca5d5a5b81d',
 'native_binary_positive_scale.json':'ee373e17fdd038a0cf0278513c15c7fede80ae8f35ba64bf919859188b40c628',
 'native_binary_positive_scale.md':'d958feffa5d82ede3096d8c792fbf861385f2c7c011057c587663ead4ad2ce97',
 'three_mass_unbounded_interface.py':'cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a',
 'three_mass_unbounded_interface.json':'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e',
 'three_mass_unbounded_interface.md':'d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45'}
def need(x,m):
 if not x: raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a)is list:return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def add(a,b,sign=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+sign*c
 return {m:c for m,c in d.items() if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   p=tuple(x+y for x,y in zip(m,n));d[p]=d.get(p,0)+c*e
 return {m:c for m,c in d.items() if c}
def cone(rows,prefix):
 e={prefix+n:{power:1} for n,power in [('wn2',(1,0,0)),('sn2',(0,1,0)),('k',(0,0,1))]}
 for n,op,a,b in rows:
  if n in e:continue
  if all(type(v)is int or v in e for v in (a,b)):
   a={(0,0,0):a} if type(a)is int else e[a];b={(0,0,0):b} if type(b)is int else e[b]
   e[n]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return e[prefix+'L9']
def ledger(rows,ports,outputs):
 known=set(ports);deps={};cnt=Counter()
 for n,op,a,b in rows:
  need(type(n)is str and n not in known and op in ('*','+','-'),'fresh gate')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'closed exact operands')
  deps[n]=(a,b);known.add(n);cnt['M' if op=='*' else 'A']+=1
 todo=list(outputs);live=set()
 while todo:
  n=todo.pop()
  if n not in deps or n in live:continue
  live.add(n);todo.extend(deps[n])
 need(live==set(deps),'no dead source gates')
 need(({v for row in rows for v in row[2:] if type(v)is str and v not in deps} | {v for v in outputs if type(v)is str and v not in deps})==set(ports),'entire paid interface')
 return dict(operations=len(rows),M=cnt['M'],A=cnt['A'])
def sos(rows,pairs):
 out=list(rows)
 for i,(a,b) in enumerate(pairs):out.extend([[f'sos_res{i}','-',a,b],[f'sos_sq{i}','*',f'sos_res{i}',f'sos_res{i}']])
 terminal='sos_sq0'
 for i in range(1,len(pairs)):
  n=f'sos_sum{i}';out.append([n,'+',terminal,f'sos_sq{i}']);terminal=n
 return out,terminal
def verify(source_root,root):
 for p,h in AUTHOR.items():need(sha(source_root/p)==h,'author pin '+p)
 for p,h in PARENTS.items():need(sha(root/p)==h,'parent pin '+p)
 j=json.loads((source_root/'native_pell_factored_first_coefficient.json').read_text())
 read=lambda name:json.loads((root/(name+'.json')).read_text())
 originals={}
 p=read('native_binary_masked_selection63')['variants']['and64_prescribed'];originals['and_prescribed']=(p['source'],p['comparisons'],p['parameters'],p['strictly_positive_auxiliaries'])
 p=read('native_binary_positive_scale')['example'];originals['and_positive_scale']=(p['source'][:-(3*len(p['comparisons'])-1)],p['comparisons'],p['parameters'],p['auxiliaries'])
 for p in read('three_mass_unbounded_interface')['fixtures']:
  originals['clock_'+p['name']]=(p['source'][:-(3*len(p['comparisons'])-1)],p['comparisons'],p['parameters'],p['auxiliaries'])
 need(len(j['forms'])==len(originals)==6,'six distinct complete examples')
 results=[]
 for form in j['forms']:
  key=form['variant'];child=form['packet'];old,pairs,params,aux=originals[key];pref='native__' if key.startswith('clock_') else '';n=lambda x:pref+x
  need(exact(child['comparisons'],pairs) and exact(child['parameters'],params) and exact(child['auxiliaries'],aux),'unchanged full interface')
  need(exact(child['domains'],{'parameters':'natural' if pref else 'positive','auxiliaries':'positive'}),'mixed-domain contract')
  d={name:(op,a,b) for name,op,a,b in old}
  required={'UM':('*',n('wn2'),n('sn2')),'ksn2':('*',n('k'),n('sn2')),
   'UM2':('*',n('UM'),n('UM')),'scaled_norm_coefficient':('+',n('UM2'),n('wn2')),
   'ratio_product2':('*',n('ksn2'),n('ksn2')),'L9':('*',n('scaled_norm_coefficient'),n('ratio_product2'))}
  need(all(d[n(a)]==b for a,b in required.items()) and n('k') in aux,'literal independent supplied k cone')
  remove={n(x) for x in ('UM2','scaled_norm_coefficient','ratio_product2','L9')};expected=[]
  for row in old:
   if row[0]==n('L9'):expected.extend([[n('factored_first_base'),'*',n('UM'),n('ksn2')],[n('factored_first_next'),'+',n('factored_first_base'),n('k')],[n('L9'),'*',n('factored_first_base'),n('factored_first_next')]])
   elif row[0] not in remove:expected.append(row)
  need(exact(expected,child['source']),'entire source equals sole prescribed rewrite')
  target={(2,4,2):1,(1,2,2):1};need(cone(old,pref)==cone(expected,pref)==target,'independent literal cone coefficient proof')
  old_poly,out=sos(old,pairs);new_poly,new_out=sos(expected,pairs)
  need(exact(new_poly,child['polynomial_source']) and child['output']==new_out==out,'complete literal finalizer')
  # Proved coefficient becomes a shared abstract atom. Every downstream gate
  # is now independently matched by its ordered expression tree.
  atoms={}
  def intern(t):
   if t not in atoms:atoms[t]=len(atoms)
   return atoms[t]
  def expression(rows):
   e={v:intern(('port',v)) for v in params+aux}
   at=lambda v:intern(('constant',v)) if type(v)is int else e[v]
   for v,op,a,b in rows:e[v]=intern(('proved-L9',)) if v==n('L9') else intern((op,at(a),at(b)))
   return e
  a=expression(old_poly);b=expression(new_poly);common=set(a)&set(b)
  need(all(a[v]==b[v] for v in common),'all surviving complete register identities')
  need(a[out]==b[out] and all(a[f'sos_res{i}']==b[f'sos_res{i}'] for i in range(len(pairs))),'complete polynomial and all residual identities')
  old_l=ledger(old,params+aux,[v for pair in pairs for v in pair]);new_l=ledger(expected,params+aux,[v for pair in pairs for v in pair])
  old_s=ledger(old_poly,params+aux,[out]);new_s=ledger(new_poly,params+aux,[out])
  for before,after in [(old_l,new_l),(old_s,new_s)]:need(after=={'operations':before['operations']-1,'M':before['M']-1,'A':before['A']},'exact one multiplication saving')
  for reported,measured in [(child['certificate_ledger'],new_l),(child['polynomial_ledger'],new_s)]:need(all(reported[k]==v for k,v in measured.items()),'independent full paid ledger')
  # This native norm uses tau(tau+1); it is not the raw complete74 root.
  need(d[n('R9')]==('*',n('tau'),n('tauplus1')) and d[n('tauplus1')]==('+',n('tau'),1),'native first-root convention untouched')
  results.append({'variant':key,'old_certificate':old_l,'new_certificate':new_l,'old_polynomial':old_s,'new_polynomial':new_s,'positive_witnesses':len(aux),'comparisons':len(pairs),'shared_register_identities':len(common),'degree_claim_inherited':child['degree'],'domains':child['domains']})
 return {'status':'PASS_INDEPENDENT_NATIVE_FIRST_COEFFICIENT','review_source_sha256':sha(Path(__file__)),'author_pins':AUTHOR,'parent_pins':PARENTS,'forms':results,'identities':{'local_cones':6,'full_polynomials':6,'residuals':sum(r['comparisons'] for r in results),'shared_registers':sum(r['shared_register_identities'] for r in results)},'scope':'Exact complete polynomial equality over any commutative ring; parent semantics and degree claims inherited. No new universal-input claim, new degree expansion, parent theorem reproof, or astronomical witness construction.'}
def main():
 p=argparse.ArgumentParser();p.add_argument('--source-root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);v=p.parse_args();j=verify(v.source_root,v.root)
 if v.expect:need(exact(j,json.loads(v.expect.read_text())),'exact frozen review receipt')
 if v.output:v.output.write_text(json.dumps(j,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':j['status'],'identities':j['identities']}))
if __name__=='__main__':main()
