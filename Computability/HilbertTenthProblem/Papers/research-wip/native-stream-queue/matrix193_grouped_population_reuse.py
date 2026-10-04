#!/usr/bin/env python3
"""Fresh full-source grouped population sum reuse; frozen files are inert."""
import argparse, hashlib, json, random
from collections import Counter
from pathlib import Path
PINS={
 'matrix193_idle_affine_reuse.py':'a2dcb0e17ede95c182af4c1f4895b8551eb3786a376da3d081439baf8b896d72',
 'matrix193_idle_affine_reuse.json':'84a1d55889c8adff1c20b7c0e4bf3e69055ed6aefd9b0eea5065b3b082ba9dd5',
 'matrix193_idle_affine_reuse.md':'d8f63c7e3957564a0b2d2d39080cddc7a93f8920ed6c05bc25ce48e5cbd44f63',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
HEADS=[111,113,115,117,119,121,122,123,124,125,126,127,128,129,130,133]
def ck(x,m):
 if not x: raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate key');d[k]=v
  return d
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b
def add(a,b,s=1):
 d=dict(a)
 for k,v in b.items():
  d[k]=d.get(k,0)+s*v
  if d[k]==0:del d[k]
 return d
def mul(a,b):
 d={}
 for j,c in a.items():
  for k,e in b.items():d[j+k]=d.get(j+k,0)+c*e
 return {k:v for k,v in d.items() if v}
def univariate(rows,Q):
 e={Q:{1:1}}
 for n,o,a,b in rows:
  if n==Q or not all(type(v)is int or v in e for v in [a,b]):continue
  x=({0:a} if a else {}) if type(a)is int else e[a];y=({0:b} if b else {}) if type(b)is int else e[b]
  e[n]=mul(x,y) if o=='*' else add(x,y,1 if o=='+' else -1)
 return e
def linear(rows,hats):
 e={h:{h:1} for h in hats}
 for n,o,a,b in rows:
  if n in hats:continue
  if o not in ['+','-'] or not all(type(v)is int or v in e for v in [a,b]):continue
  x=({'constant':a} if a else {}) if type(a)is int else e[a];y=({'constant':b} if b else {}) if type(b)is int else e[b]
  e[n]=add(x,y,1 if o=='+' else -1)
 return e
def graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique ports');deps={};ct=Counter();deg={v:0 if v in p['fixed_numerals'] else 1 for v in p['free']}
 for n,o,a,b in p['source']:
  ck(type(n)is str and n not in known and o in ['+','-','*'],'producer')
  ck(all(type(v)is int or type(v)is str and v in known for v in [a,b]),'topology '+n)
  da=deg[a] if type(a)is str else 0;db=deg[b] if type(b)is str else 0
  deg[n]=da+db if o=='*' else max(da,db);known.add(n);deps[n]=(a,b);ct[o]+=1
 live=set();todo=[p['output']]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:live.add(n);todo.extend(deps.get(n,()))
 ck(live==known,'complete liveness')
 return {'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),'fixed_coefficient_ports':len(p['fixed_numerals']),'integer_literals':len({v for r in p['source'] for v in r[2:] if type(v)is int}),'syntactic_degree_upper':deg[p['output']],'all_live':True}
def identity(parent,child,hats,cut):
 cache={}
 def token(k):
  if k not in cache:cache[k]=len(cache)
  return cache[k]
 common={v:token(('port',v)) for v in parent['free']}
 def run(rows):
  e=dict(common)
  def val(v):return e[v] if type(v)is str else token(('integer',v))
  for n,o,a,b in rows:
   if n==cut:e[n]=token(('proved_sum98',tuple(e[h] for h in hats)))
   else:
    args=(val(a),val(b));args=tuple(sorted(args)) if o in ['+','*'] else args
    e[n]=token((o,)+args)
  return e
 old=run(parent['source']);new=run(child['source']);retained=sorted(set(old)&set(new))
 for n in retained:ck(old[n]==new[n],'whole-source value '+n)
 ck(old[parent['output']]==new[child['output']],'entire output')
 return {'all_common_registers_and_output_equal':True,'common_paid_registers':len(retained)-len(common),'sum_cut_binds_actual_98_input_values':True,'commutative_addition_used_for_duplicate':True}
def evaluate(p,values,q):
 e=dict(values)
 for n,o,a,b in p['source']:
  x=e[a] if type(a)is str else a;y=e[b] if type(b)is str else b
  e[n]=(x*y if o=='*' else x+y if o=='+' else x-y)%q
 return e
def make(parent,m,index,baseline):
 def w(n):return m.get(n,n) if type(n)is str else n
 rows=parent['source'];by={r[0]:r for r in rows};pos={r[0]:i for i,r in enumerate(rows)}
 hats=[w('edge_hat'+str(i)) for i in range(98)];cut=w('r103')
 oldchain=[w('r'+str(j)) for j in range(7,104)];oldset=set(oldchain)
 ck(by[oldchain[0]]==[oldchain[0],'+',hats[0],hats[1]],'old sum start')
 for j,n in enumerate(oldchain[1:],2):ck(by[n]==[n,'+',oldchain[j-2],hats[j]],'old sum chain')
 consumers=[(n,v) for n,o,a,b in rows if n not in oldset for v in [a,b] if type(v)is str and v in oldset]
 ck(consumers==[(w('r105'),cut)],'old sum private boundary')
 groupnames=[w('r'+str(j)) for j in range(110,134)]
 groups=[by[n] for n in groupnames];heads=[w('r'+str(j)) for j in HEADS]
 groupvalues=linear(groups,hats);seen=set();partition=[];head_for={}
 for head in heads:
  support=groupvalues[head];ck(all(c==1 and h in hats for h,c in support.items()),'unit hat group')
  ck(not seen.intersection(support),'disjoint group');seen.update(support)
  first=min(hats.index(h) for h in support);head_for[first]=head
  partition.append({'head':head,'members':sorted(support,key=hats.index)})
 ck(len(groups)==24 and len(heads)==16 and len(seen)==40,'group accounting')
 terms=[head_for[i] if i in head_for else h for i,h in enumerate(hats) if i in head_for or h not in seen]
 ck(len(terms)==74,'remaining population terms')
 newchain=[];acc=terms[0]
 for j,term in enumerate(terms[1:]):
  n=cut if j==72 else 'grouped_population_sum_'+str(j)
  ck(n==cut or n not in by and n not in parent['free'],'fresh row')
  newchain.append([n,'+',acc,term]);acc=n
 oldlinear=linear([by[n] for n in oldchain],hats)[cut];newlinear=linear(groups+newchain,hats)[cut]
 ck(oldlinear==newlinear=={h:1 for h in hats},'formal complete98-hat identity')
 dup=[w('r140'),w('r159')];early,late=sorted(dup,key=pos.get)
 ck(by[w('r140')]==[w('r140'),'+',1,w('r139')] and by[w('r159')]==[w('r159'),'+',w('r139'),1],'commutative duplicate')
 def alias(v):return early if v==late else v
 child={k:parent[k] for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']};child['variant']=parent['variant'];source=[]
 for n,o,a,b in rows:
  if n==oldchain[0]:source.extend([r[:] for r in groups]);source.extend(newchain)
  if n in oldset or n in groupnames or n==late:continue
  source.append([n,o,alias(a),alias(b)])
 child['source']=source;newby={r[0]:r for r in source}
 for n,o,a,b in rows:
  if n not in oldset and n!=late:ck(newby[n]==[n,o,alias(a),alias(b)],'all other definitions retained modulo proved alias')
 oldledger=graph(parent);ledger=graph(child)
 ck(ledger['total']==oldledger['total']-25 and ledger['A']==oldledger['A']-25 and ledger['M']==oldledger['M'],'25 paid additions saved')
 child['full_identity']=identity(parent,child,hats,cut)
 # Expand all four complete coefficient words from their actual paid Q.
 Q=w('r108');oldpoly=univariate(rows,Q);newpoly=univariate(source,Q);certs=[]
 for c in parent['coefficient_certificates']:
  n=c['wire'];expected={j:v for j,v in enumerate(c['ascending_coefficients']) if v}
  ck(oldpoly[n]==newpoly[n]==expected,'complete coefficient word')
  certs.append({'wire':n,'degree':max(expected),'ascending_coefficients':c['ascending_coefficients'],'polynomial_sha256':sha(enc(sorted(expected.items())))})
 child['coefficient_certificates']=certs
 component=parent['coefficient_component'];ck(all(newby[r[0]]==r for r in component),'577 component rows literal')
 child['coefficient_component']=component;ct=Counter(r[1] for r in component);ck((len(component),ct['*'],ct['+']+ct['-'])==(577,329,248),'component count')
 child['component_ledger']={'total':577,'M':329,'A':248}
 basepos={r[0]:j for j,r in enumerate(baseline['source'])};native=baseline['source'][basepos['selection__bs_even']:basepos['eight_units']+1]
 ck(len(native)==63,'native inventory')
 for r in native:
  n=w(r[0]);ck(newby[n]==by[n],'literal native row')
 residuals=parent['retained_residual_wires'];ck(all(newby[n]==by[n] for n in residuals),'residuals literal')
 finalcount=3*len(residuals)+2;ck(source[-finalcount:]==rows[-finalcount:],'full finalizer literal')
 ledger['outer_residuals']=len(residuals);ledger['exact_degree']=parent['ledger']['exact_degree'];child['ledger']=ledger;child['retained_residual_wires']=residuals
 child['source_boundary_checks']={'native_rows_literal':63,'residuals_literal':len(residuals),'finalizer_rows_literal':finalcount}
 child['edit']={'moved_existing_group_rows':groups,'disjoint_group_partition':partition,'old_sum_rows':[by[n] for n in oldchain],'new_sum_rows':newchain,'formal_hats':hats,'sum_cut':cut,'sum_additions_saved':24,'duplicate_earlier_row':by[early],'duplicate_deleted_row':by[late],'duplicate_consumers':[n for n,o,a,b in rows if late in [a,b]],'duplicate_additions_saved':1}
 child['parent_reference']={'receipt':'matrix193_idle_affine_reuse.json','packet_index':index,'source_array_sha256':sha(enc(rows)),'ledger_recounted':oldledger}
 child['degree_transfer']={'exact_degree':ledger['exact_degree'],'reason':'entire polynomial identity on unchanged variables to pinned immediate parent','new_leading_or_dense_degree_computation':False}
 checks=[];rng=random.Random(1586+index)
 for prime in [1000000007,1000000009]:
  for case in range(4):
   values={v:rng.randrange(-61,62) for v in child['free']}
   if case%2==0:values.update(child['fixture_fixed_bindings'])
   old=evaluate(parent,values,prime);new=evaluate(child,values,prime)
   for n in set(old)&set(new):ck(old[n]%prime==new[n]%prime,'supplemental common register '+n)
   checks.append({'prime':prime,'case':case,'illustrative_fixed_ports':case%2==0,'output':new[child['output']]})
 child['supplemental_modular_checks']=checks
 return child

def build(root):
 for n,h in PINS.items():ck(sha((root/n).read_bytes())==h,'pin '+n)
 parent=read(root/'matrix193_idle_affine_reuse.json');charts=read(root/'matrix193_entry_controller_charts.json')
 ck(parent['source_sha256']==PINS['matrix193_idle_affine_reuse.py'],'source binding')
 ck(len(parent['packets'])==4 and len(charts['packets'])==3,'inventory')
 packets=[make(p,{} if i==0 else charts['packets'][i-1]['map'],i,parent['packets'][0]) for i,p in enumerate(parent['packets'])]
 ck([p['ledger']['total'] for p in packets]==[1592,1589,1589,1586],'derived complete counts')
 ck([p['ledger']['positive_witnesses'] for p in packets]==[145,144,144,143],'unchanged witnesses')
 return {'schema':'matrix193-grouped-population-reuse-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source']) for p in packets),'formal_population_terms':98,'coefficient_polynomials':16,'coefficient_entries':sum(len(c['ascending_coefficients']) for p in packets for c in p['coefficient_certificates']),'signed_modular_comparisons':32,'all_ring_identities':True},'scope':{'frozen_code_executed':False,'identical_polynomial_and_supplied_coordinates_to_immediate_parent':True,'identical_positive_zeros_to_immediate_parent':True,'pre_IDLE_comparison':'ordinary input projection only; fresh histories/native witnesses may be needed','valid_fixed_program_recipe_unchanged':True,'exact_degrees_inherited_by_full_identity':True,'universal84_unchanged':True,'minimality_claim':False}}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True,type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(same(result,read(a.expect)),'type-exact receipt')
 print('PASS: four complete arrays1592/1589/1589/1586;25 additions saved each;full identities, graphs, coefficient words, domains/degrees')
if __name__=='__main__':main()
