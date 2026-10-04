#!/usr/bin/env python3
"""Independent two-order reconstruction of grouped/power composition; inert data only."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
PINS={
 'matrix193_grouped_power_composition.py':'3facf356824eb762575e1b90bc2ad24812187f675e02406041408686a58b8a7e',
 'matrix193_grouped_power_composition.json':'67ec3453bb211f3129f27d4194084007c0e1e74410745a11c4181c79ae707002',
 'matrix193_grouped_power_composition.md':'66b145ba5d2c87ff3ca5cadee3a1f27de626d11315809ec18a181a88815a0d14',
 'matrix193_grouped_population_reuse.py':'269b01191fb23bad7399bd7a95ecfa37dde1c47f987e86b69888755f57a6977e',
 'matrix193_grouped_population_reuse.json':'5144d0355e133bc056a848a27e8506eabf3314980d075b3e31403de258733dad',
 'matrix193_grouped_population_reuse.md':'acf84ac27f802ecdf0bcd50530bb0c1dfbc34d9db2b0c1716a6410253c87fc4a',
 'matrix193_coefficient_power_reuse.py':'127165e2644503e51072697d55154fd2a39fa7660f04724c604e5e4efd12377a',
 'matrix193_coefficient_power_reuse.json':'24d5786b3fe1c0d1dc34e324b7445d62eaac0362c3c169a710c2691b60716f17',
 'matrix193_coefficient_power_reuse.md':'c29442ece1f8291341fffef036cbd8db5c233914ff63fada2e133e0e9c97b741',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
RECIPES=[('cp42','r138','r139',54),('cp117','r142','r161',78),('cp119','r138','r143',30),('cp282','r161','r783',136),('cp317','r142','r200',150),('cp326','r142','r148',102),('cp344','r138','r200',162),('cp383','r138','r145',66),('cp526','r138','r552',186)]
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def poly(rows,q):
 env={q:{1:1}}
 for n,o,a,b in rows:
  if n==q or not all(type(v)is int or v in env for v in [a,b]):continue
  aa=({0:a} if a else {}) if type(a)is int else env[a];bb=({0:b} if b else {}) if type(b)is int else env[b]
  if o=='*':
   out={}
   for i,c in aa.items():
    for j,d in bb.items():out[i+j]=out.get(i+j,0)+c*d
  else:
   out=dict(aa)
   for i,c in bb.items():out[i]=out.get(i,0)+(c if o=='+' else -c)
  env[n]={i:c for i,c in out.items() if c}
 return env

def live(rows,out):
 by={r[0]:r for r in rows};seen=set();todo=[out]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in by:todo.extend(by[n][2:])
 return seen

def regroup(power,w):
 rows=power['source'];by={r[0]:r for r in rows};positions={r[0]:i for i,r in enumerate(rows)}
 hats=[w('edge_hat'+str(i)) for i in range(98)];basis={n:Counter({n:1}) for n in hats}
 def linear(n):
  if n not in basis:
   _,o,a,b=by[n];ck(o=='+','group uses only additions');basis[n]=linear(a)+linear(b)
  return basis[n]
 heads=[w('r'+str(i)) for i in [111,113,115,117,119,121,*range(122,131),133]]
 covered={};support=[]
 for h in heads:
  expansion=linear(h);ck(all(v==1 for v in expansion.values()),'unit group coefficients')
  ck(all(n not in covered for n in expansion),'disjoint heads');covered.update({n:h for n in expansion});support.append([h,sorted(expansion)])
 ck(len(covered)==40 and len(heads)==16,'group population')
 terms=[];used=set()
 for h in hats:
  term=covered.get(h,h)
  if term not in used:terms.append(term);used.add(term)
 ck(len(terms)==74,'74 terms')
 new=[];acc=terms[0]
 for i,b in enumerate(terms[1:]):
  n=w('r103') if i==72 else 'grouped_population_sum_'+str(i);new.append([n,'+',acc,b]);acc=n
 moving=[by[w('r'+str(i))] for i in range(110,134)];oldsum={w('r'+str(i)) for i in range(7,104)}
 ck(len(moving)==24 and sum(len(s)-1 for h,s in support)==24,'24 already-paid group operations')
 ck(linear(w('r103'))==Counter({h:1 for h in hats}),'old population full98 terms')
 newbasis=dict(basis)
 for n,o,a,b in new:newbasis[n]=newbasis[a]+newbasis[b]
 ck(newbasis[w('r103')]==Counter({h:1 for h in hats}),'new population full98 terms')
 dups=[w('r140'),w('r159')];dups.sort(key=positions.__getitem__);keep,drop=dups
 ck(by[keep][1]=='+' and by[drop][1]=='+' and sorted(by[keep][2:],key=str)==sorted(by[drop][2:],key=str)==sorted([w('r139'),1],key=str),'commutative duplicate')
 moved_names={r[0] for r in moving};result=[]
 for row in rows:
  if row[0]==w('r7'):result.extend(moving);result.extend(new)
  if row[0] in oldsum or row[0] in moved_names or row[0]==drop:continue
  result.append([row[0],row[1],keep if row[2]==drop else row[2],keep if row[3]==drop else row[3]])
 return result,{'heads':support,'sum_rows':len(new),'moved_rows':len(moving),'removed_duplicate':drop,'kept_duplicate':keep,'formal_population_coefficients':98}

def build(root,packets):
 for name,h in PINS.items():
  base=root if name=='matrix193_entry_controller_charts.json' else packets
  ck(sha((base/name).read_bytes())==h,'pin '+name)
 authored=read(packets/'matrix193_grouped_power_composition.json');grouped=read(packets/'matrix193_grouped_population_reuse.json');powers=read(packets/'matrix193_coefficient_power_reuse.json');maps=read(root/'matrix193_entry_controller_charts.json')
 results=[]
 for i,child in enumerate(authored['packets']):
  g=grouped['packets'][i];p=powers['packets'][i];mapping={} if not i else maps['packets'][i-1]['map'];w=lambda n:mapping.get(n,n)
  for key in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output','variant']:ck(child[key]==g[key]==p[key],'identical two-branch interface')
  # First route: local power changes on the grouped source, with fresh liveness.
  replacements={w(n):[w(n),'*',w(a),w(b)] for n,a,b,e in RECIPES}
  provisional=[replacements.get(r[0],r) for r in g['source']];alive=live(provisional,g['output']);expected=[r for r in provisional if r[0] in alive]
  ck(expected==child['source'],'power-after-group full array')
  deleted=[r for r in g['source'] if r[0] not in alive];ck(len(deleted)==24 and all(r[1]=='*' for r in deleted),'24 coefficient product deletion')
  ck(deleted==p['removed_private_rows'],'exact independent prior coefficient deletion set')
  # Reverse route: derive the grouping from98 formal hats, not author edits.
  opposite,group_proof=regroup(p,w);ck(opposite==child['source'],'group-after-power full array')
  known=set(child['free']);ct=Counter();degrees={n:0 if n in child['fixed_numerals'] else 1 for n in known}
  for n,o,a,b in child['source']:
   ck(n not in known and o in ['+','-','*'] and all(type(v)is int or v in known for v in [a,b]),'topological closure')
   da=degrees[a] if type(a)is str else 0;db=degrees[b] if type(b)is str else 0;degrees[n]=da+db if o=='*' else max(da,db);known.add(n);ct[o]+=1
  ck(known==live(child['source'],child['output']),'every row and port live')
  ledger={'total':len(child['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(child['witnesses']),'syntactic_degree_upper':degrees[child['output']]}
  ck(all(child['ledger'][k]==v for k,v in ledger.items()),'fresh ledger')
  Q=w('r108');a=poly(g['source'],Q);b=poly(child['source'],Q)
  for n,left,right,e in RECIPES:
   n,left,right=map(w,[n,left,right]);ck(a[n]==b[n]=={e:1},'entire power-cut polynomial')
   ck(len(a[left])==len(a[right])==1 and next(iter(a[left].values()))==next(iter(a[right].values()))==1,'unit operand powers')
   ck(next(iter(a[left]))+next(iter(a[right]))==e,'sum of paid exponents')
  coefficients=[]
  for rec in p['coefficient_certificates']:
   n=rec['wire'];expected={j:c for j,c in enumerate(rec['ascending_coefficients']) if c};ck(a[n]==b[n]==expected,'full16 coefficient polynomials')
   coefficients.append({'wire':n,'coefficient_entries':len(rec['ascending_coefficients']),'degree':max(expected),'digest':sha(enc(sorted(expected.items())))})
  ck(child['coefficient_component']==p['coefficient_component'] and len(child['coefficient_component'])==553,'all553 coefficient rows literal')
  newby={r[0]:r for r in child['source']};oldby={r[0]:r for r in g['source']}
  for r in child['source']:
   if r[0] not in replacements:ck(r==oldby[r[0]],'all other grouped definitions literal')
  native_base=[r[0] for r in grouped['packets'][0]['source']];native_base=native_base[native_base.index('selection__bs_even'):native_base.index('eight_units')+1]
  ck(len(native_base)==63 and all(newby[w(n)]==oldby[w(n)] for n in native_base),'native63 boundary')
  res=g['retained_residual_wires'];ck(child['retained_residual_wires']==res and all(newby[n]==oldby[n] for n in res),'all residuals')
  nf=3*len(res)+2;ck(child['source'][-nf:]==g['source'][-nf:],'complete finalizer')
  ck(child['ledger']['exact_degree']==g['ledger']['exact_degree']==p['ledger']['exact_degree'],'inherited exact degree')
  results.append({'variant':child['variant'],'ledger':ledger,'source_array_sha256':sha(enc(child['source'])),'literal_two_order_reconstruction':True,'group_proof':group_proof,'power_polynomials_verified':9,'coefficient_polynomials':coefficients,'removed_M':24,'component_rows_literal':553,'native_rows_literal':63,'residuals_literal':len(res),'finalizer_rows_literal':nf,'exact_degree_inherited_by_complete_identity':child['ledger']['exact_degree']})
 ck([r['ledger']['total'] for r in results]==[1568,1565,1565,1562],'final counts')
 return {'schema':'independent-grouped-power-composition-review-v1','review_source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'results':results,'full_rows_checked':sum(r['ledger']['total'] for r in results),'scope':'No frozen program executed/imported. Exact two-order literal reconstruction, cut coefficient identities and unchanged-row induction prove composition; no fresh native trajectory or giant-output expansion.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--packet-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root,a.packet_root or a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,read(a.expect)),'type-exact receipt')
 print('PASS:6260rows reconstructed in both orders;four98-hat sums;36powers;16coefficient words;native/finalizer/interface boundaries')
if __name__=='__main__':main()
