#!/usr/bin/env python3
"""Exact two-multiplication saving in five complete macro-controller circuits.
Reads pinned saved sources only; no historical module or builder executes.
"""
import argparse,copy,hashlib,json,random
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'group_macro_automaton_sharing.py': 'f9d660c3309c030c98c8209f2b8a708a6731eedf62234d459ed4fa3f1db2af48', 'group_macro_automaton_sharing.json': '8e7044b66bebbacc0f89721807369607146b57bb67b14d1ddb9c4e05586a681b', 'group_macro_automaton_sharing.md': 'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585', 'native_pell_factored_first_coefficient.py': 'e20ea9a9ad7fe3c473bf5ec60df4143bae1020cb9836110de2c9c783f9248bfc', 'native_pell_factored_first_coefficient.json': 'bfb5889e9da52b0b4a3d40dd9fbfd99a3a8550d8b7b7cdbd185bfbd51524abdf', 'native_pell_factored_first_coefficient.md': 'b1ec2a04fc92fe41b3c84fb33c6b74931e7643259bdd570a0426ed9256c67528'}
PARENT='group_macro_automaton_sharing.json'
PREFIXES=('selection__','geometry__')
def need(c,m):
 if not c:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def stable(v):return json.dumps(v,sort_keys=True,separators=(',',':'))
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def finalize(rows,pairs):
 out=copy.deepcopy(rows)
 for i,(a,b)in enumerate(pairs):out.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 v='square_0'
 for i in range(1,len(pairs)):n=f'sum_{i}';out.append([n,'+',v,f'square_{i}']);v=n
 return out,v

def ledger(rows,free,roots):
 degree={n:1 for n in free};defs={};m=0
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in degree and o in('+','-','*'),'fresh gate')
  need(all(type(x)is int or type(x)is str and x in degree for x in(a,b)),'closed source')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);defs[n]=(a,b);m+=o=='*'
 seen=set();used=set();stack=list(roots)
 while stack:
  x=stack.pop()
  if type(x)is int:continue
  if x not in defs:used.add(x)
  elif x not in seen:seen.add(x);stack.extend(defs[x])
 need(seen==set(defs)and used==set(free),'all paid rows and supplied coordinates live')
 return dict(operations=len(rows),M=m,A=len(rows)-m,degree_upper=max(degree[x]if type(x)is str else 0 for x in roots))

def coefficient_identity():
 def add(a,b):
  z=dict(a)
  for m,c in b.items():z[m]=z.get(m,0)+c
  return {m:c for m,c in z.items()if c}
 def mul(a,b):
  z={}
  for m,c in a.items():
   for n,d in b.items():k=tuple(x+y for x,y in zip(m,n));z[k]=z.get(k,0)+c*d
  return {m:c for m,c in z.items()if c}
 X,Y,k=[{tuple(int(i==j)for i in range(3)):1}for j in range(3)]
 E=mul(X,Y);V=mul(k,Y);L=mul(E,V)
 old=mul(add(mul(E,E),X),mul(V,V));new=mul(L,add(L,k))
 need(old==new,'exact complete coefficient identity in independent X,Y,k')
 return [[list(m),c]for m,c in sorted(old.items())]

def rewrite(p):
 q=copy.deepcopy(p);rows=p['source'];defs={n:[o,a,b]for n,o,a,b in rows};replacements={};deleted=set()
 for prefix in PREFIXES:
  nm=lambda s:prefix+s
  want={nm('UM'):['*',nm('wn2'),nm('sn2')],nm('ksn2'):['*',nm('k'),nm('sn2')],nm('UM2'):['*',nm('UM'),nm('UM')],nm('scaled_norm_coefficient'):['+',nm('UM2'),nm('wn2')],nm('ratio_product2'):['*',nm('ksn2'),nm('ksn2')],nm('L9'):['*',nm('scaled_norm_coefficient'),nm('ratio_product2')],nm('tauplus1'):['+',nm('tau'),1],nm('R9'):['*',nm('tau'),nm('tauplus1')]}
  need(all(defs.get(n)==v for n,v in want.items()),'entire literal coefficient/root cone')
  need(nm('k')in p['auxiliaries']and [nm('L9'),nm('R9')]in p['comparisons'],'actual supplied k and unchanged triangular norm')
  for a,b in [('UM2','scaled_norm_coefficient'),('scaled_norm_coefficient','L9'),('ratio_product2','L9')]:
   need([n for n,o,x,y in rows if nm(a)in(x,y)]==[nm(b)]and all(nm(a)not in pair for pair in p['comparisons']),'private removed coefficient producer')
  block=[nm(s)for s in('UM2','scaled_norm_coefficient','ratio_product2','L9')];deleted.update(block)
  L=nm('factored_first_base');next_=nm('factored_first_next')
  need(L not in defs and next_ not in defs,'fresh coefficient names')
  replacements[nm('L9')]=[[L,'*',nm('UM'),nm('ksn2')],[next_,'+',L,nm('k')],[nm('L9'),'*',L,next_]]
 out=[]
 for row in rows:
  if row[0]in replacements:out.extend(replacements[row[0]])
  elif row[0]not in deleted:out.append(copy.deepcopy(row))
 q['source']=out;q['polynomial_source'],q['output']=finalize(out,p['comparisons'])
 q['parent_ledgers']={key:q.pop(key)for key in ('certificate_ledger','polynomial_ledger')}
 q['coefficient_transfer']=dict(prefixes=list(PREFIXES),same_supplied_tuple_polynomial=True,removed_multiplications=2,triangular_roots_unchanged=True,scope='Two literal private native first-coefficient cones only; no automaton or input change.')
 return q

class Ring:
 def __init__(self):self.ids={('one',):0}
 def atom(self,key):
  if key not in self.ids:self.ids[key]=len(self.ids)
  return self.ids[key]
 def val(self,x):return ((0,x),)if type(x)is int and x else()if type(x)is int else((self.atom(('variable',x)),1),)
 def add(self,a,b,s):
  z=dict(a)
  for n,c in b:z[n]=z.get(n,0)+s*c
  return tuple(sorted((n,c)for n,c in z.items()if c))
 def mul(self,a,b):
  if not a or not b:return()
  if len(a)==1 and a[0][0]==0:return tuple((n,c*a[0][1])for n,c in b)
  if len(b)==1 and b[0][0]==0:return tuple((n,c*b[0][1])for n,c in a)
  sign=1
  if a[0][1]<0:a=tuple((n,-c)for n,c in a);sign=-sign
  if b[0][1]<0:b=tuple((n,-c)for n,c in b);sign=-sign
  return ((self.atom(('product',)+tuple(sorted((a,b)))),sign),)
 def run(self,rows,free):
  e={n:self.val(n)for n in free}
  for n,o,a,b in rows:
   a=e[a]if type(a)is str else self.val(a);b=e[b]if type(b)is str else self.val(b)
   e[n]=self.mul(a,b)if o=='*'else self.add(a,b,1 if o=='+'else-1)
   if n in [p+'L9'for p in PREFIXES]:e[n]=self.val(('proved_coefficient',n))
  return e

def execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a*b if o=='*'else a+b if o=='+'else a-b
 return e

def verify(root):
 root=Path(root);need(len(PINS)==6,'six frozen dependencies')
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'source pin '+n)
 parent=json.loads((root/PARENT).read_text());forms=[];counts=Counter();rng=random.Random(2412);local=coefficient_identity()
 need([(f['graph'],f['flow'])for f in parent['forms']]==[('separate','dense'),('separate','generic'),('separate','path_sparse'),('shared','dense'),('shared','generic')],'exact five complete parents')
 for f in parent['forms']:
  p=f['packet'];q=rewrite(p);free=p['parameters']+p['auxiliaries']
  poly,out=finalize(p['source'],p['comparisons']);need(poly==p['polynomial_source']and out==p['output'],'whole literal parent finalizer')
  for key in ('comparisons','parameters','auxiliaries','codes','edges','m','alpha','beta','flow_plan'):need(exact(p[key],q[key]),'all unrelated source/interface data unchanged')
  for packet in (p,q):
   cl=ledger(packet['source'],free,[x for pair in packet['comparisons']for x in pair]);pl=ledger(packet['polynomial_source'],free,[packet['output']])
   if packet is p:need(exact(cl,p['certificate_ledger'])and exact(pl,p['polynomial_ledger']),'actual parent paid ledger')
   else:packet['certificate_ledger']=cl;packet['polynomial_ledger']=pl
  for field in ('certificate_ledger','polynomial_ledger'):
   need(q[field]['M']==p[field]['M']-2 and q[field]['A']==p[field]['A']and q[field]['degree_upper']==p[field]['degree_upper'],'two exact M savings with inherited degree upper')
  R=Ring();a=R.run(p['polynomial_source'],free);b=R.run(q['polynomial_source'],free)
  common=set(a)&set(b)
  for n in common:need(a[n]==b[n],'all common computed registers after proved coefficient cuts')
  need(a[p['output']]==b[q['output']],'whole polynomial identity from exact local coefficients')
  counts['common_register_identities']+=len(common)-len(free);counts['residual_identities']+=len(p['comparisons']);counts['whole_polynomial_identities']+=1;counts['live_paid_polynomial_gates']+=q['polynomial_ledger']['operations']
  for case in range(12):
   v={n:rng.randrange(1,5)if case<4 else rng.randrange(-3,4)for n in free}
   if case>=8:v={n:Fraction(x,3)for n,x in v.items()}
   x=execute(p['polynomial_source'],v);y=execute(q['polynomial_source'],v)
   for n in common:need(x[n]==y[n],'entire numerical graph after exact rewrite')
   counts['numeric_whole_identities']+=1;counts['rational_cases']+=case>=8
  for prefix in PREFIXES:
   # Deliberately violate k=eta+zeta: the supplied k is still required.
   v={n:1 for n in free};v[prefix+'k']=3;e=execute(q['source'],v);L=e[prefix+'factored_first_base'];wrong=L*(L+e[prefix+'eta']+e[prefix+'zeta'])
   need(e[prefix+'L9']!=wrong,'wrong computed-k substitution caught off zero');counts['wrong_k_diagnostics']+=1
  forms.append(dict(graph=f['graph'],flow=f['flow'],packet=q,complete_source_sha256=sha(stable(q['polynomial_source']).encode())))
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,local_coefficient_polynomial=local,counts=dict(counts),forms=forms,scope='Five complete fixed macro-matrix circuits, each saving exactly two multiplications with all-value polynomial identity. The fixed macro table is not an instantiated universal alphabet; no new universal arithmetic bound or exact degree claim. Native positive extension and ordinary affine input inherited unchanged.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],forms=[dict(graph=f['graph'],flow=f['flow'],polynomial=f['packet']['polynomial_ledger'])for f in r['forms']])))
if __name__=='__main__':main()
