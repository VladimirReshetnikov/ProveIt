#!/usr/bin/env python3
"""Fresh composition of grouped population and coefficient power reuse."""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={'matrix193_grouped_population_reuse.py': '269b01191fb23bad7399bd7a95ecfa37dde1c47f987e86b69888755f57a6977e', 'matrix193_grouped_population_reuse.json': '5144d0355e133bc056a848a27e8506eabf3314980d075b3e31403de258733dad', 'matrix193_grouped_population_reuse.md': 'acf84ac27f802ecdf0bcd50530bb0c1dfbc34d9db2b0c1716a6410253c87fc4a', 'matrix193_coefficient_power_reuse.py': '127165e2644503e51072697d55154fd2a39fa7660f04724c604e5e4efd12377a', 'matrix193_coefficient_power_reuse.json': '24d5786b3fe1c0d1dc34e324b7445d62eaac0362c3c169a710c2691b60716f17', 'matrix193_coefficient_power_reuse.md': 'c29442ece1f8291341fffef036cbd8db5c233914ff63fada2e133e0e9c97b741', 'matrix193_entry_controller_charts.json': 'd5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571'}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def encode(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(s):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def add(a,b,s=1):
 d=dict(a)
 for i,c in b.items():
  d[i]=d.get(i,0)+s*c
  if not d[i]:del d[i]
 return d
def mul(a,b):
 d={}
 for i,c in a.items():
  for j,h in b.items():d[i+j]=d.get(i+j,0)+c*h
 return {i:c for i,c in d.items() if c}
def polynomials(rows,Q):
 values={Q:{1:1}}
 for n,o,a,b in rows:
  if n==Q or not all(type(v)is int or v in values for v in [a,b]):continue
  aa=({0:a} if a else {}) if type(a)is int else values[a];bb=({0:b} if b else {}) if type(b)is int else values[b]
  values[n]=mul(aa,bb) if o=='*' else add(aa,bb,1 if o=='+' else -1)
 return values

def live_names(rows,output):
 by={r[0]:r for r in rows};live=set();todo=[output]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:
   live.add(v)
   if v in by:todo.extend(by[v][2:])
 return live

def audit(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique free ports');ct=Counter();degree={n:0 if n in p['fixed_numerals'] else 1 for n in p['free']}
 for n,o,a,b in p['source']:
  ck(type(n)is str and n not in known and o in ['+','-','*'],'unique arithmetic producer')
  ck(all(type(v)is int or (type(v)is str and v in known) for v in [a,b]),'complete topological order')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0;degree[n]=da+db if o=='*' else max(da,db);known.add(n);ct[o]+=1
 ck(live_names(p['source'],p['output'])==known,'all rows/ports live')
 return {'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),'fixed_coefficient_ports':len(p['fixed_numerals']),'integer_literals':len({v for r in p['source'] for v in r[2:] if type(v)is int}),'syntactic_degree_upper':degree[p['output']],'all_live':True}

def whole_identity(parent,child,Q,exponents):
 cache={}
 def token(key):
  if key not in cache:cache[key]=len(cache)
  return cache[key]
 common={n:token(('free',n)) for n in child['free']}
 def run(rows):
  env=dict(common)
  for n,o,a,b in rows:
   aa=env[a] if type(a)is str else token(('integer',a));bb=env[b] if type(b)is str else token(('integer',b))
   env[n]=token(('proved_Q_power',env[Q],exponents[n])) if n in exponents else token((o,aa,bb))
  return env
 old,new=run(parent['source']),run(child['source'])
 ck(old[Q]==new[Q],'same actual paid Q expression')
 for n,o,a,b in child['source']:ck(old[n]==new[n],'entire retained register '+n)
 ck(old[parent['output']]==new[child['output']],'entire final polynomial')
 return {'all_ring_identity':'F_child=F_immediate_grouped_parent on identical supplied coordinates','all_retained_paid_registers_checked':len(child['source']),'nine_proved_power_cut_tokens_include_actual_Q':True,'actual_Q_expression_equal':True,'entire_output_equal':True}

def evaluate(p,values,prime):
 env=dict(values)
 for n,o,a,b in p['source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%prime
 return env

def make(parent,recipe,m,index,native_labels):
 def w(n):return m.get(n,n) if type(n)is str else n
 ck(parent['variant']==recipe['variant'],'variant correspondence')
 for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']:ck(parent[k]==recipe[k],'same interface across both edit branches')
 rows=parent['source'];by={r[0]:r for r in rows};positions={r[0]:i for i,r in enumerate(rows)};component={r[0] for r in parent['coefficient_component']};Q=w('r108');oldpoly=polynomials(rows,Q);edits={};exponents={};certs=[]
 for cert in recipe['power_reuse_certificates']:
  n,a,b=cert['actual_labels'];e,ea,eb=cert['target_power'],cert['left_power'],cert['right_power']
  ck(n in component and a not in component and b not in component,'coefficient target/packing operand boundary')
  ck(by[n]==cert['old_target_row'] and cert['new_target_row']==[n,'*',a,b],'literal mapped power edit')
  ck(positions[a]<positions[n] and positions[b]<positions[n],'earlier paid operands')
  ck(ea+eb==e and oldpoly[n]=={e:1} and oldpoly[a]=={ea:1} and oldpoly[b]=={eb:1},'fresh exact input powers')
  edits[n]=[n,'*',a,b];exponents[n]=e;certs.append({'target':n,'left':a,'right':b,'old_row':by[n],'new_row':edits[n],'powers':[e,ea,eb]})
 ck(len(edits)==9,'nine distinct edits')
 provisional=[edits.get(r[0],r[:]) for r in rows];live=live_names(provisional,parent['output']);removed=[r for r in rows if r[0] not in live]
 ck(removed==recipe['removed_private_rows'],'exact same24 deleted coefficient rows')
 ck(len(removed)==24 and all(r[0] in component and r[1]=='*' for r in removed),'24M saving boundary')
 child={k:parent[k] for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']};child['variant']=parent['variant'];child['source']=[r for r in provisional if r[0] in live];newby={r[0]:r for r in child['source']}
 for r in rows:
  if r[0] in newby and r[0] not in edits:ck(newby[r[0]]==r,'every other retained definition literal')
 newpoly=polynomials(child['source'],Q)
 for n,e in exponents.items():ck(oldpoly[n]==newpoly[n]=={e:1},'fresh exact power output')
 coefficients=[]
 for rec in parent['coefficient_certificates']:
  n=rec['wire'];expected={i:c for i,c in enumerate(rec['ascending_coefficients']) if c}
  ck(oldpoly[n]==newpoly[n]==expected,'full coefficient expansion')
  coefficients.append({'wire':n,'degree':max(expected),'ascending_coefficients':rec['ascending_coefficients'],'polynomial_sha256':sha(encode(sorted(expected.items())))})
 child['coefficient_certificates']=coefficients
 child['coefficient_component']=[newby[r[0]] for r in parent['coefficient_component'] if r[0] in newby]
 ck(child['coefficient_component']==recipe['coefficient_component'],'all553 coefficient rows literally equal power recipe')
 ct=Counter(r[1] for r in child['coefficient_component']);ck((len(child['coefficient_component']),ct['*'],ct['+']+ct['-'])==(553,305,248),'component ledger')
 child['component_ledger']={'total':553,'M':305,'A':248};oldledger=audit(parent);ledger=audit(child)
 ck((ledger['total'],ledger['M'],ledger['A'])==(oldledger['total']-24,oldledger['M']-24,oldledger['A']),'full24M delta')
 child['whole_identity']=whole_identity(parent,child,Q,exponents)
 for n in native_labels:ck(newby[w(n)]==by[w(n)],'native row literal')
 res=parent['retained_residual_wires'];ck(all(newby[n]==by[n] for n in res),'every residual literal')
 nf=3*len(res)+2;ck(child['source'][-nf:]==rows[-nf:],'whole finalizer literal')
 ck(all(newby[r[0]]==r for r in parent['edit']['new_sum_rows']),'all73 new population rows retained literal')
 ck(all(newby[r[0]]==r for r in parent['edit']['moved_existing_group_rows']),'all24 rescheduled groups retained literal')
 ck(parent['edit']['duplicate_deleted_row'][0] not in newby,'packing duplicate remains absent')
 child['source_boundary_checks']={'native_rows_literal':len(native_labels),'residuals_literal':len(res),'finalizer_rows_literal':nf,'population_sum_rows_literal':73,'group_rows_literal':24,'packing_duplicate_still_absent':True}
 ledger['outer_residuals']=len(res);ledger['exact_degree']=parent['ledger']['exact_degree'];child['ledger']=ledger;child['retained_residual_wires']=res;child['power_edits']=certs;child['removed_private_rows']=removed
 child['parent_reference']={'receipt':'matrix193_grouped_population_reuse.json','packet_index':index,'source_array_sha256':sha(encode(rows)),'fresh_parent_ledger':oldledger}
 child['power_recipe_reference']={'receipt':'matrix193_coefficient_power_reuse.json','packet_index':index,'source_array_sha256':sha(encode(recipe['source']))}
 child['degree_transfer']={'exact_degree':ledger['exact_degree'],'reason':'full polynomial identity on unchanged variables to immediate grouped parent','new_degree_computation':False}
 tests=[];rng=random.Random(1562+index)
 for prime in [1000000007,1000000009]:
  for case in range(4):
   values={n:rng.randrange(-73,74) for n in child['free']}
   if case%2==0:values.update(child['fixture_fixed_bindings'])
   old=evaluate(parent,values,prime);new=evaluate(child,values,prime)
   for n in new:ck(old[n]%prime==new[n]%prime,'supplemental full register map')
   tests.append({'prime':prime,'case':case,'illustrative_fixed_bindings':case%2==0,'output':new[child['output']]})
 child['supplemental_modular_checks']=tests
 return child

def build(root,packet_root):
 for n,h in PINS.items():
  directory=root if n=='matrix193_entry_controller_charts.json' else packet_root
  ck(sha((directory/n).read_bytes())==h,'pin '+n)
 grouped=read(packet_root/'matrix193_grouped_population_reuse.json');power=read(packet_root/'matrix193_coefficient_power_reuse.json');charts=read(root/'matrix193_entry_controller_charts.json')
 for name,obj in [('matrix193_grouped_population_reuse',grouped),('matrix193_coefficient_power_reuse',power)]:ck(obj['source_sha256']==PINS[name+'.py'],'source binding')
 ck(len(grouped['packets'])==len(power['packets'])==4 and len(charts['packets'])==3,'complete inventory')
 labels=[r[0] for r in grouped['packets'][0]['source']];native=labels[labels.index('selection__bs_even'):labels.index('eight_units')+1];ck(len(native)==63,'native inventory')
 packets=[make(p,power['packets'][i],{} if i==0 else charts['packets'][i-1]['map'],i,native) for i,p in enumerate(grouped['packets'])]
 ck([p['ledger']['total'] for p in packets]==[1568,1565,1565,1562],'complete composed counts')
 ck([p['ledger']['positive_witnesses'] for p in packets]==[145,144,144,143],'unchanged witnesses')
 return {'schema':'matrix193-grouped-power-composition-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source']) for p in packets),'power_cut_identities':36,'coefficient_polynomials':16,'coefficient_entries':sum(len(c['ascending_coefficients']) for p in packets for c in p['coefficient_certificates']),'supplemental_modular_maps':32,'whole_source_identity':True},'scope':{'frozen_code_executed':False,'same_polynomial_and_coordinates_as_immediate_grouped_parent':True,'same_positive_zero_tuples_as_immediate_grouped_parent':True,'pre_IDLE_comparison':'ordinary input projection only','valid_fixed_program_recipe_unchanged':True,'exact_degrees_inherited':True,'new_native_fixture_or_diagnostic':False,'universal84_unchanged':True,'minimality_claim':False}}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--packet-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root,a.packet_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(exact(result,read(a.expect)),'type-exact receipt')
 print('PASS: complete grouped+power arrays1568/1565/1565/1562;full identities;553 coefficient rows;unchanged witnesses/degrees')
if __name__=='__main__':main()
