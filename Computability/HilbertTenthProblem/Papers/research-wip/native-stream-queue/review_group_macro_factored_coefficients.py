#!/usr/bin/env python3
"""Independent bounded five-source, two-coefficient delta review.
All predecessor and author files are data only. No Python imports/builders.
"""
import argparse,copy,hashlib,json
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('run without -O')
PARENT_PINS={
'group_macro_automaton_sharing.py':'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48',
'group_macro_automaton_sharing.json':'8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b',
'group_macro_automaton_sharing.md':'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585'}
INHERITED_PINS={'native_pell_factored_first_coefficient.py':'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc','native_pell_factored_first_coefficient.json':'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf','native_pell_factored_first_coefficient.md':'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528'}
AUTHOR_PINS={'group_macro_factored_coefficients.py':'d6d39080bc99d86a4dbe38233f2f84ae1ff47c9aea8003d61121e050039814fc','group_macro_factored_coefficients.json':'0cf1c28767cd55d0f3f14327741ca5bbd0c6ee8ddebd86466935cdc4dd4e1632','group_macro_factored_coefficients.md':'a22e42bf0055df78fdbfab69c92be16a0c538af31ac2ffe7ce8d14c324ff08d9'}
PREFIXES=('selection__','geometry__')
def need(x,m):
 if not x:raise ValueError(m)
def sha(x):return hashlib.sha256(x).hexdigest()
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':'))
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def local_proof():
 def add(a,b):
  r=dict(a)
  for k,v in b.items():r[k]=r.get(k,0)+v
  return {k:v for k,v in r.items()if v}
 def mul(a,b):
  r={}
  for m,c in a.items():
   for n,d in b.items():k=tuple(x+y for x,y in zip(m,n));r[k]=r.get(k,0)+c*d
  return {k:v for k,v in r.items()if v}
 X={(1,0,0):1};Y={(0,1,0):1};K={(0,0,1):1}
 E=mul(X,Y);V=mul(K,Y);L=mul(E,V)
 old=mul(add(mul(E,E),X),mul(V,V));new=mul(L,add(L,K))
 need(old==new=={(2,4,2):1,(1,2,2):1},'independent exact coefficient expansion')
 return [[list(m),c]for m,c in sorted(old.items())]

def finalize(source,comparisons):
 rows=copy.deepcopy(source)
 for i,(left,right)in enumerate(comparisons):rows.extend([[f'residual_{i}','-',left,right],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 current='square_0'
 for i in range(1,len(comparisons)):
  name=f'sum_{i}';rows.append([name,'+',current,f'square_{i}']);current=name
 return rows,current

def reconstruct(p):
 defs={n:(o,a,b)for n,o,a,b in p['source']};delete=set();blocks={};proofs=[]
 for prefix in PREFIXES:
  names=lambda n:prefix+n
  required={
   'UM':('*',names('wn2'),names('sn2')),
   'ksn2':('*',names('k'),names('sn2')),
   'UM2':('*',names('UM'),names('UM')),
   'scaled_norm_coefficient':('+',names('UM2'),names('wn2')),
   'ratio_product2':('*',names('ksn2'),names('ksn2')),
   'L9':('*',names('scaled_norm_coefficient'),names('ratio_product2')),
   'tauplus1':('+',names('tau'),1),
   'R9':('*',names('tau'),names('tauplus1'))}
  need(all(defs[names(n)]==v for n,v in required.items()),'entire actual native first coefficient and triangular root')
  need(names('k')in p['auxiliaries']and names('k')not in defs,'actual independent supplied k')
  need([names('L9'),names('R9')]in p['comparisons'],'first norm retained')
  for a,b in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
   consumers=[n for n,o,x,y in p['source']if names(a)in(x,y)]
   need(consumers==[names(b)],'private coefficient consumer closure')
   need(all(names(a)not in pair for pair in p['comparisons']),'no hidden comparison on deleted gate')
  for n in('UM2','scaled_norm_coefficient','ratio_product2','L9'):delete.add(names(n))
  base=names('factored_first_base');next_=names('factored_first_next');need(base not in defs and next_ not in defs,'fresh paid replacement names')
  blocks[names('L9')]=[[base,'*',names('UM'),names('ksn2')],[next_,'+',base,names('k')],[names('L9'),'*',base,next_]]
  proofs.append(dict(prefix=prefix,coefficient_polynomial=local_proof(),old_M=3,old_A=1,new_M=2,new_A=1,supplied_k=names('k')))
 result=[]
 for row in p['source']:
  if row[0]in blocks:result.extend(blocks[row[0]])
  elif row[0]not in delete:result.append(copy.deepcopy(row))
 return result,proofs

def ledger(rows,free,roots):
 degrees={n:1 for n in free};defs={};M=0
 for row in rows:
  need(type(row)is list and len(row)==4,'typed literal row');n,o,a,b=row
  need(type(n)is str and n not in degrees and o in('+','-','*'),'fresh scalar operation')
  need(all(type(v)is int or(type(v)is str and v in degrees)for v in(a,b)),'topological source closure')
  da=degrees[a]if type(a)is str else 0;db=degrees[b]if type(b)is str else 0
  degrees[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);M+=o=='*'
 reached=set();used=set();stack=list(roots)
 while stack:
  n=stack.pop()
  if type(n)is int:continue
  if n not in defs:need(n in free,'known scalar root');used.add(n)
  elif n not in reached:reached.add(n);stack.extend(defs[n])
 need(reached==set(defs)and used==set(free),'all supplied ports and all paid operations live')
 return dict(operations=len(rows),M=M,A=len(rows)-M,degree_upper=max(degrees[n]if type(n)is str else 0 for n in roots))

class Interner:
 def __init__(self):self.nodes={}
 def intern(self,key):
  if key not in self.nodes:self.nodes[key]=len(self.nodes)
  return self.nodes[key]
 def evaluate(self,rows,free):
  values={n:self.intern(('free',n))for n in free}
  def val(x):return self.intern(('constant',x))if type(x)is int else values[x]
  for n,o,a,b in rows:
   expr=self.intern((o,val(a),val(b)))
   if n in[p+'L9'for p in PREFIXES]:expr=self.intern(('independently_proved_coefficient',n))
   values[n]=expr
  return values

def evaluate(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  x=e[a]if type(a)is str else a;y=e[b]if type(b)is str else b;e[n]=x*y if o=='*'else x+y if o=='+'else x-y
 return e

def run(parent_root,author_root):
 for n,h in PARENT_PINS.items():need(sha((parent_root/n).read_bytes())==h,'parent pin '+n)
 for n,h in INHERITED_PINS.items():need(sha((parent_root/n).read_bytes())==h,'inherited coefficient pin '+n)
 for n,h in AUTHOR_PINS.items():need(sha((author_root/n).read_bytes())==h,'author pin '+n)
 old=json.loads((parent_root/'group_macro_automaton_sharing.json').read_text());new=json.loads((author_root/'group_macro_factored_coefficients.json').read_text())
 need(old['source_sha256']==PARENT_PINS['group_macro_automaton_sharing.py'],'parent source receipt link')
 need(new['source_sha256']==sha((author_root/'group_macro_factored_coefficients.py').read_bytes()),'author source receipt link')
 need(new['pins']==dict(PARENT_PINS,**INHERITED_PINS),'exact dependency manifest')
 expected=[('separate','dense'),('separate','generic'),('separate','path_sparse'),('shared','dense'),('shared','generic')]
 need([(f['graph'],f['flow'])for f in old['forms']]==expected==[(f['graph'],f['flow'])for f in new['forms']],'five exact source interfaces')
 result=[];counts=Counter()
 for parent,child in zip(old['forms'],new['forms']):
  p=parent['packet'];q=child['packet'];source,proofs=reconstruct(p);need(source==q['source'],'literal complete expected replacement schedule')
  free=p['parameters']+p['auxiliaries'];need(p['parameters']==['x'],'ordinary input interface');need(len(p['comparisons'])==47,'complete comparison count')
  unchanged=set(p)-{'source','polynomial_source','certificate_ledger','polynomial_ledger'}
  for key in unchanged:need(exact(p[key],q[key]),'every unrelated packet field unchanged: '+key)
  need(set(q)==set(p)|{'parent_ledgers','coefficient_transfer'},'honest current and historical metadata')
  need(q['parent_ledgers']=={k:p[k]for k in('certificate_ledger','polynomial_ledger')},'historical ledgers preserved as historical')
  expected_transfer=dict(prefixes=list(PREFIXES),same_supplied_tuple_polynomial=True,removed_multiplications=2,triangular_roots_unchanged=True,scope='Two literal private native first-coefficient cones only; no automaton or input change.')
  need(q['coefficient_transfer']==expected_transfer,'precise current transfer scope')
  for packet in(p,q):
   full,out=finalize(packet['source'],packet['comparisons']);need(full==packet['polynomial_source']and out==packet['output'],'complete literal finalizer')
   need(ledger(packet['source'],free,[x for pair in packet['comparisons']for x in pair])==packet['certificate_ledger'],'complete certificate ledger')
   need(ledger(full,free,[out])==packet['polynomial_ledger'],'complete polynomial ledger')
   counts['full_ledgers']+=2
  for field in('certificate_ledger','polynomial_ledger'):
   need(q[field]['M']==p[field]['M']-2 and q[field]['A']==p[field]['A']and q[field]['degree_upper']==p[field]['degree_upper'],'exact paid 2M delta and degree bound')
  interner=Interner();before=interner.evaluate(p['polynomial_source'],free);after=interner.evaluate(q['polynomial_source'],free);common=set(before)&set(after)
  for n in common:need(before[n]==after[n],'entire downstream DAG identity after the two independently proved coefficients')
  for i in range(47):need(before[f'residual_{i}']==after[f'residual_{i}'],'every complete residual identity')
  need(before[p['output']]==after[q['output']],'whole all-value polynomial identity')
  need(sha(stable(q['polynomial_source']).encode())==child['complete_source_sha256'],'saved complete source hash')
  # Four off-zero signed/rational evaluations corroborate but do not prove identity.
  for case in range(4):
   values={n:((i*7+case*3)%9)-4 for i,n in enumerate(free)}
   if case>=2:values={n:Fraction(v,case+1)for n,v in values.items()}
   a=evaluate(p['polynomial_source'],values);b=evaluate(q['polynomial_source'],values)
   need(all(a[n]==b[n]for n in common),'complete off-zero graph corroboration');counts['off_zero_whole_cases']+=1;counts['rational_cases']+=case>=2
  for prefix in PREFIXES:
   v={n:1 for n in free};v[prefix+'k']=5;e=evaluate(q['source'],v);L=e[prefix+'factored_first_base']
   need(e[prefix+'L9']-L*(L+e[prefix+'eta']+e[prefix+'zeta'])==3*L and L!=0,'actual supplied k cannot be replaced off zero');counts['supplied_k_boundary_cases']+=1
  counts.update(whole_sources=1,local_coefficient_proofs=len(proofs),common_computed_registers=len(common)-len(free),residual_identities=47,whole_polynomial_identities=1,paid_certificate_gates=len(q['source']),paid_polynomial_gates=len(q['polynomial_source']))
  result.append(dict(graph=child['graph'],flow=child['flow'],auxiliaries=len(q['auxiliaries']),comparisons=47,parent_certificate=p['certificate_ledger'],certificate=q['certificate_ledger'],parent_polynomial=p['polynomial_ledger'],polynomial=q['polynomial_ledger'],local_proofs=proofs,complete_source_sha256=child['complete_source_sha256']))
 need(counts['paid_polynomial_gates']==2217 and counts['residual_identities']==235 and counts['whole_sources']==5,'complete independent totals')
 return dict(status='PASS',review_source_sha256=sha(Path(__file__).read_bytes()),parent_pins=PARENT_PINS,inherited_pins=INHERITED_PINS,author_pins=AUTHOR_PINS,counts=dict(counts),forms=result,scope='Same supplied tuple entire-polynomial identity for each of five actual complete sources. Supplied k and triangular roots retained. Degree statements are propagated upper bounds only. No cross-graph polynomial identity, full native numerical witness, API guarantee, or new universal numerical bound is claimed.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--author-root',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=run(a.root,a.author_root or a.root)
 need(exact(r,json.loads(json.dumps(r))),'typed JSON serialization')
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact frozen receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'ledgers':[f['polynomial']for f in r['forms']]}))
if __name__=='__main__':main()
