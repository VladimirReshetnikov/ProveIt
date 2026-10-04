#!/usr/bin/env python3
"""Fresh nine-power reuse in four complete IDLE-free matrix polynomials.
Frozen predecessor Python is pinned as inert bytes; none is executed/imported.
"""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={
 'matrix193_idle_affine_reuse.py':'a2dcb0e17ede95c182af4c1f4895b8551eb3786a376da3d081439baf8b896d72',
 'matrix193_idle_affine_reuse.json':'84a1d55889c8adff1c20b7c0e4bf3e69055ed6aefd9b0eea5065b3b082ba9dd5',
 'matrix193_idle_affine_reuse.md':'d8f63c7e3957564a0b2d2d39080cddc7a93f8920ed6c05bc25ce48e5cbd44f63',
 'matrix193_entry_controller_charts.py':'7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
 'matrix193_entry_controller_charts.md':'27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122'}
# target,left,right,target_exponent,left_exponent,right_exponent
REUSES=[['cp42','r138','r139',54,18,36],['cp117','r142','r161',78,6,72],['cp119','r138','r143',30,18,12],['cp282','r161','r783',136,72,64],['cp317','r142','r200',150,6,144],['cp326','r142','r148',102,6,96],['cp344','r138','r200',162,18,144],['cp383','r138','r145',66,18,48],['cp526','r138','r552',186,18,168]]
EXPECTED_REMOVED=['cp39','cp40','cp41','cp114','cp115','cp116','cp118','cp281','cp314','cp315','cp316','cp323','cp324','cp325','cp341','cp342','cp343','cp382','cp520','cp521','cp522','cp523','cp524','cp525']
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
 return {'all_ring_identity':'F_child=F_immediate_idle_affine_parent on identical supplied coordinates','all_retained_paid_registers_checked':len(child['source']),'nine_proved_power_cut_tokens_include_actual_Q':True,'actual_Q_expression_equal':True,'entire_output_equal':True}

def evaluate(p,values,prime):
 env=dict(values)
 for n,o,a,b in p['source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%prime
 return env

def make(parent,chart,index,native_labels):
 mapping={} if chart is None else chart['map']
 def w(v):return mapping.get(v,v) if type(v)is str else v
 variant='no_controller_chart' if chart is None else chart['chart'];ck(parent['variant']==variant,'parent/map correspondence')
 Q=w('r108');oldpol=polynomials(parent['source'],Q);by={r[0]:r for r in parent['source']};pos={r[0]:j for j,r in enumerate(parent['source'])};component_names={r[0] for r in parent['coefficient_component']}
 edits={};exponents={};cert=[]
 for name,a,b,e,ea,eb in REUSES:
  n,aa,bb=map(w,[name,a,b]);ck(ea+eb==e,'exponent sum')
  ck(oldpol[n]=={e:1} and oldpol[aa]=={ea:1} and oldpol[bb]=={eb:1},'exact paid operand/target powers')
  ck(n in component_names and aa not in component_names and bb not in component_names,'paid packing operands outside component')
  ck(pos[aa]<pos[n] and pos[bb]<pos[n],'earlier paid operands')
  edits[n]=[n,'*',aa,bb];exponents[n]=e
  cert.append({'baseline_labels':[name,a,b],'actual_labels':[n,aa,bb],'old_target_row':by[n],'new_target_row':edits[n],'target_power':e,'left_power':ea,'right_power':eb})
 provisional=[edits.get(r[0],r[:]) for r in parent['source']];live=live_names(provisional,parent['output']);removed=[r for r in parent['source'] if r[0] not in live]
 ck({r[0] for r in removed}=={w(n) for n in EXPECTED_REMOVED},'exact24 private removed rows')
 ck(len(removed)==24 and all(r[0] in component_names and r[1]=='*' for r in removed),'coefficient-only24M saving')
 child={key:parent[key] for key in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']};child['variant']=variant;child['source']=[r for r in provisional if r[0] in live]
 for key in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']:ck(child[key]==parent[key],'unchanged supplied interface '+key)
 newby={r[0]:r for r in child['source']}
 for r in parent['source']:
  if r[0] in newby and r[0] not in edits:ck(newby[r[0]]==r,'every other retained row literal')
 newpol=polynomials(child['source'],Q)
 for n,e in exponents.items():ck(newpol[n]==oldpol[n]=={e:1},'new target exact power')
 coeffs=[]
 for saved in parent['coefficient_certificates']:
  n=saved['wire'];expected={i:c for i,c in enumerate(saved['ascending_coefficients']) if c}
  ck(oldpol[n]==newpol[n]==expected,'all literal coefficient entries')
  coeffs.append({'side':saved['side'],'column':saved['column'],'wire':n,'degree':max(expected),'ascending_coefficients':[expected.get(i,0) for i in range(max(expected)+1)],'polynomial_sha256':sha(encode(sorted(expected.items())))})
 child['coefficient_certificates']=coeffs
 child['coefficient_component']=[edits.get(r[0],r[:]) for r in parent['coefficient_component'] if r[0] in live]
 ct=Counter(r[1] for r in child['coefficient_component']);ck((len(child['coefficient_component']),ct['*'],ct['+']+ct['-'])==(553,305,248),'553-row component ledger')
 child['component_ledger']={'total':553,'M':305,'A':248}
 oldledger=audit(parent);ledger=audit(child);ck((ledger['total'],ledger['M'],ledger['A'])==(oldledger['total']-24,oldledger['M']-24,oldledger['A']),'fresh full24M saving')
 native=[w(n) for n in native_labels];ck(len(native)==63 and all(newby[n]==by[n] for n in native),'entire native63 retained literal')
 residuals=parent['retained_residual_wires'];ck(all(newby[n]==by[n] for n in residuals),'all retained residuals literal')
 final_count=3*len(residuals)+2;ck(child['source'][-final_count:]==parent['source'][-final_count:],'full finalizer literal')
 ledger['outer_residuals']=len(residuals);ledger['exact_degree']=parent['ledger']['exact_degree'];ck(ledger['exact_degree']==[35587,53347,53347,71107][index],'inherited exact degree premise')
 child['ledger']=ledger;child['retained_residual_wires']=residuals
 child['power_reuse_certificates']=cert;child['removed_private_rows']=removed
 child['whole_identity']=whole_identity(parent,child,Q,exponents)
 child['source_boundary_checks']={'native_rows_literal':63,'outer_residual_rows_literal':len(residuals),'finalizer_rows_literal':final_count,'all_packing_rows_literal':True,'all_other_retained_rows_literal':True}
 child['degree_transfer']={'exact_degree':ledger['exact_degree'],'reason':'all-ring equality to immediate idle_affine parent on identical variables; pinned uniform valid-recipe degree transfers','new_degree_or_native_fixture_computation':False}
 child['parent_reference']={'receipt':'matrix193_idle_affine_reuse.json','packet_index':index,'source_array_sha256':sha(encode(parent['source'])),'fresh_parent_ledger':oldledger}
 cases=[];rng=random.Random(1587+index)
 for prime in [1000000007,1000000009]:
  for case in range(4):
   values={n:rng.randrange(-61,62) for n in child['free']}
   if case%2==0:values.update(child['fixture_fixed_bindings'])
   old=evaluate(parent,values,prime);new=evaluate(child,values,prime)
   for n in new:ck(old[n]%prime==new[n]%prime,'signed retained-register diagnostic')
   cases.append({'prime':prime,'case':case,'illustrative_fixed_bindings':case%2==0,'output':new[child['output']]})
 child['supplemental_modular_checks']=cases
 return child

def build(root,parent_root):
 for name,pin in PINS.items():
  directory=parent_root if name.startswith('matrix193_idle_affine_reuse.') else root
  ck(sha((directory/name).read_bytes())==pin,'pin '+name)
 parent=read(parent_root/'matrix193_idle_affine_reuse.json');charts=read(root/'matrix193_entry_controller_charts.json')
 for stem,receipt in [('matrix193_idle_affine_reuse',parent),('matrix193_entry_controller_charts',charts)]:ck(receipt['source_sha256']==PINS[stem+'.py'],'source/receipt provenance')
 ck(len(parent['packets'])==4 and len(charts['packets'])==3,'four-source inventory')
 baseline=parent['packets'][0]['source'];names=[r[0] for r in baseline];start=names.index('selection__bs_even');end=names.index('eight_units');native_labels=names[start:end+1];ck(len(native_labels)==63,'literal baseline native block')
 packets=[make(p,None if i==0 else charts['packets'][i-1],i,native_labels) for i,p in enumerate(parent['packets'])]
 ck([p['ledger']['total'] for p in packets]==[1593,1590,1590,1587],'four freshly counted arrays')
 ck([p['ledger']['positive_witnesses'] for p in packets]==[145,144,144,143],'retained witness counts')
 return {'schema':'matrix193-coefficient-power-reuse-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'baseline_reuses':REUSES,'packets':packets,'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source']) for p in packets),'exact_power_cut_identities':36,'complete_coefficient_polynomials':16,'coefficient_entries':sum(len(c['ascending_coefficients']) for p in packets for c in p['coefficient_certificates']),'signed_modular_register_comparisons':32,'full_expression_identities':4},'scope':{'frozen_predecessor_code_executed':False,'packing_changes_included':False,'same_polynomial_and_coordinates_as_immediate_parent':True,'same_positive_integer_zero_tuples_as_immediate_parent':True,'pre_IDLE_comparison':'ordinary-input projection inherited only','valid_fixed_program_recipe_unchanged':True,'diagnostic_array_or_giant_accepting_fixture':False,'exact_degree_inherited_by_full_identity':True,'universal84_unchanged':True,'minimality_or_exhaustive_search_claim':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--parent-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();r=build(a.root,a.parent_root or a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:ck(exact(r,read(a.expect)),'recursive type-exact receipt')
 print('PASS: four complete1593/1590/1590/1587 sources;24M saved each;553-row components;exact powers/coefficients/full outputs')
if __name__=='__main__':main()
