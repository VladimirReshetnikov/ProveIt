#!/usr/bin/env python3
"""Fresh composition of paid affine reuse with four frozen IDLE-free sources.
Predecessor Python is authenticated as bytes only, never imported or executed.
"""
import argparse,hashlib,json,random
from collections import Counter
from pathlib import Path
PINS={
 'matrix193_idle_free_scout.py':'33e6c22b35e6fd2c8735380f04433652686b0da20053c5446b139e8881f9ed94',
 'matrix193_idle_free_scout.json':'857f5af683abb1c27cba6335fd45cadbd0afc7f9c630bf312a27ea4c98aa23b7',
 'matrix193_idle_free_scout.md':'3502c8c69642ab3c90e5973a3668c896b34c23c0fdb88686338853573ac236d6',
 'matrix193_affine_reuse_scout.py':'930c44d7963a08ac96775eb328cafa1a9043d48dfa346b79c93c57f316043676',
 'matrix193_affine_reuse_scout.json':'c60870f886f26f21701f0a77ce02777d7d0258765dbb4f69d13e68926a6c9d4d',
 'matrix193_affine_reuse_scout.md':'85e15290465364db9d792c8dbcbc77914c1ef9ee78969b082154866a6dbc70ad',
 'matrix193_entry_controller_charts.py':'7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
 'matrix193_entry_controller_charts.md':'27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122'}
def ck(ok,msg):
 if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def enc(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def read(p):
 def pairs(items):
  result={}
  for key,value in items:ck(key not in result,'duplicate JSON key');result[key]=value
  return result
 def bad(x):raise ValueError('nonfinite JSON')
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def same(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(same(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(same(x,y) for x,y in zip(a,b))
 return a==b

def plus(a,b,s=1):
 out=dict(a)
 for n,c in b.items():
  out[n]=out.get(n,0)+s*c
  if not out[n]:del out[n]
 return out
def times(a,b):
 out={}
 for j,c in a.items():
  for k,d in b.items():out[j+k]=out.get(j+k,0)+c*d
 return {n:c for n,c in out.items() if c}
def polys(rows,cut):
 env={cut:{1:1}}
 for n,o,a,b in rows:
  if n==cut or not all(type(v)is int or v in env for v in [a,b]):continue
  aa=({0:a} if a else {}) if type(a)is int else env[a];bb=({0:b} if b else {}) if type(b)is int else env[b]
  env[n]=times(aa,bb) if o=='*' else plus(aa,bb,1 if o=='+' else -1)
 return env

def graph(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique free ports');deps={};ct=Counter();degree={v:0 if v in p['fixed_numerals'] else 1 for v in p['free']}
 for n,o,a,b in p['source']:
  ck(type(n)is str and n not in known and o in ['+','-','*'],'unique valid producer')
  ck(all(type(v)is int or (type(v)is str and v in known) for v in [a,b]),'topological closure')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0
  degree[n]=da+db if o=='*' else max(da,db);known.add(n);deps[n]=(a,b);ct[o]+=1
 live=set();todo=[p['output']]
 while todo:
  v=todo.pop()
  if type(v)is str and v not in live:live.add(v);todo.extend(deps.get(v,()))
 ck(live==known,'every row and supplied port live')
 return {'total':len(p['source']),'M':ct['*'],'A':ct['+']+ct['-'],'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),'fixed_coefficient_ports':len(p['fixed_numerals']),'integer_literals':len({v for row in p['source'] for v in row[2:] if type(v)is int}),'all_live':True,'syntactic_degree_upper':degree[p['output']]}

def identity(parent,child,names):
 cache={}
 def token(key):
  if key not in cache:cache[key]=len(cache)
  return cache[key]
 common={v:token(('port',v)) for v in child['free']};cut=names['cp374'];t=names['r144'];shared=names['r181']
 def interpret(rows):
  values=dict(common)
  def value(v):return values[v] if type(v)is str else token(('integer',v))
  for n,o,a,b in rows:
   if n==cut:
    ck(values[shared]==token(('+',values[t],token(('integer',1)))),'same paid affine input at cut')
    values[n]=token(('proved_affine_output',values[t],-25,-25))
   else:values[n]=token((o,value(a),value(b)))
  return values
 old=interpret(parent['source']);new=interpret(child['source'])
 for n,o,a,b in child['source']:ck(old[n]==new[n],'complete retained register '+n)
 ck(old[parent['output']]==new[child['output']],'entire polynomial identity')
 return {'all_ring_identity':'F_child=F_immediate_IDLE_parent on identical supplied coordinates','retained_paid_registers_checked':len(child['source']),'all_retained_registers_equal':True,'entire_output_equal':True,'normalized_cut_inputs_compared':True}

def coefficient_check(parent,child,affine,map_name):
 Q=map_name(affine['ports']['Q']);old=polys(parent['source'],Q);new=polys(child['source'],Q);out=[]
 for rec in affine['extraction']:
  for column,product in enumerate(rec['products']):
   n=map_name(product['polynomial']);coeffs=product['coefficients'];expected={len(coeffs)-1-i:c for i,c in enumerate(coeffs) if c}
   ck(len(coeffs)==rec['length'] and old[n]==new[n]==expected,'entire fixed matrix coefficient word')
   out.append({'side':rec['side'],'column':column,'wire':n,'degree':max(expected),'ascending_coefficients':[expected.get(k,0) for k in range(len(coeffs))],'nonzero_coefficients':len(expected),'polynomial_sha256':sha(enc(sorted(expected.items())))})
 return out

def evaluate(p,values,modulus):
 env=dict(values)
 for n,o,a,b in p['source']:
  aa=env[a] if type(a)is str else a;bb=env[b] if type(b)is str else b
  env[n]=(aa*bb if o=='*' else aa+bb if o=='+' else aa-bb)%modulus
 return env

def make(parent,chart,affine,index):
 mapping={} if chart is None else chart['map']
 def w(v):return mapping.get(v,v) if type(v)is str else v
 variant='no_controller_chart' if chart is None else chart['chart'];ck(parent['variant']==variant,'correct IDLE/chart correspondence')
 names={v:w(v) for v in ['cp373','cp374','r144','r181']};by={r[0]:r for r in parent['source']}
 patterns=[['r181','+','r144',1],['cp373','*',-25,'r144'],['cp374','+','cp373',-25]]
 for row in patterns:ck(by[w(row[0])]==[w(v) if j!=1 else v for j,v in enumerate(row)],'mapped literal affine pattern')
 dead=names['cp373'];cut=names['cp374'];users=[n for n,o,a,b in parent['source'] if dead in [a,b]];ck(users==[cut],'private single consumer')
 positions={r[0]:i for i,r in enumerate(parent['source'])};ck(positions[names['r181']]<positions[cut],'already-paid earlier affine register')
 replacement=[cut,'*',-25,names['r181']]
 # Build metadata afresh. Do not propagate stale parent row ledgers or tests.
 child={k:parent[k] for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']}
 child['source']=[replacement if row[0]==cut else row[:] for row in parent['source'] if row[0]!=dead];child['variant']=variant
 ck('edge_hat98' not in child['free'] and 'edge_hat98' not in child['witnesses'],'retained IDLE-free supplied interface')
 for k in ['free','witnesses','fixed_numerals','fixture_fixed_bindings','output']:ck(child[k]==parent[k],'unchanged supplied interface '+k)
 newby={r[0]:r for r in child['source']}
 for row in parent['source']:
  if row[0] not in [dead,cut]:ck(newby[row[0]]==row,'every other row literal')
 oldlocal=polys(parent['source'],names['r144']);newlocal=polys(child['source'],names['r144'])
 ck(oldlocal[cut]==newlocal[cut]=={0:-25,1:-25},'exact integer local identity')
 oldledger=graph(parent);ledger=graph(child)
 ck(ledger['total']==oldledger['total']-1 and ledger['A']==oldledger['A']-1 and ledger['M']==oldledger['M'],'derived one addition saving')
 # The affine packet supplies the effective matrix coefficient dataset and
 # its577-row component; map every row and authenticate it in the new arrays.
 mapped_component=[[w(v) if j!=1 else v for j,v in enumerate(row)] for row in affine['coefficient_component']]
 ck(len({r[0] for r in mapped_component})==len(mapped_component),'component map injective')
 for row in mapped_component:ck(newby[row[0]]==row,'entire mapped577-row coefficient component')
 component=Counter(r[1] for r in mapped_component)
 ck((len(mapped_component),component['*'],component['+']+component['-'])==(577,329,248),'complete component ledger')
 child['coefficient_component']=mapped_component
 child['component_ledger']={'total':577,'M':329,'A':248}
 child['coefficient_certificates']=coefficient_check(parent,child,affine,w)
 child['full_identity']=identity(parent,child,names)
 # Recheck literal native block and all current finalizer rows against IDLE.
 native_start=affine['stage_counts']['packing'];native_names=[w(row[0]) for row in affine['source'][native_start:native_start+63]]
 ck(len(native_names)==63 and all(n in newby and newby[n]==by[n] for n in native_names),'63 complete native rows literal')
 if chart is None:
  resids=[w(row[0]) for row in affine['source'][-62::2][:20]]
 else:resids=chart['retained_residual_wires']
 ck(len(resids)==[20,19,19,18][index] and all(type(n)is str and n in newby and newby[n]==by[n] for n in resids),'all retained residual positions literal')
 final_count=3*len(resids)+2;ck(child['source'][-final_count:]==parent['source'][-final_count:],'entire current finalizer literal')
 ledger['outer_residuals']=len(resids);ledger['exact_degree']=parent['ledger']['exact_degree']
 ck(ledger['exact_degree']==[35587,53347,53347,71107][index],'pinned IDLE exact degree premise')
 child['ledger']=ledger
 child['edit']={'label_map':names,'removed_row':by[dead],'old_output_row':by[cut],'new_output_row':replacement,'paid_shared_row':by[names['r181']],'private_consumers':users,'local_ascending_coefficients':[-25,-25],'all_other_rows_literal':True}
 child['retained_residual_wires']=resids
 child['source_boundary_checks']={'native_rows_literal':63,'current_residuals_literal':len(resids),'current_finalizer_rows_literal':final_count}
 child['degree_transfer']={'exact_degree':ledger['exact_degree'],'proof':'full polynomial equality on identical variables to pinned immediate IDLE parent; its uniform valid-recipe degree theorem transfers','new_dense_or_leading_degree_computation':False}
 child['parent_reference']={'receipt':'matrix193_idle_free_scout.json','packet_index':index,'variant':variant,'source_array_sha256':sha(enc(parent['source'])),'ledger_recounted':oldledger}
 checks=[];rng=random.Random(1611+index)
 for prime in [1000000007,1000000009]:
  for case in range(4):
   values={n:rng.randrange(-47,48) for n in child['free']}
   if case%2==0:values.update(child['fixture_fixed_bindings'])
   old=evaluate(parent,values,prime);new=evaluate(child,values,prime)
   for n in new:ck(old[n]%prime==new[n]%prime,'supplemental same-coordinate register '+n)
   checks.append({'prime':prime,'case':case,'illustrative_fixed_ports':case%2==0,'output':new[child['output']]})
 child['supplemental_modular_checks']=checks
 return child

def build(root,idle_root):
 for n,pin in PINS.items():
  directory=idle_root if n.startswith('matrix193_idle_free_scout.') else root
  ck(sha((directory/n).read_bytes())==pin,'pin '+n)
 idle=read(idle_root/'matrix193_idle_free_scout.json');affine_receipt=read(root/'matrix193_affine_reuse_scout.json');charts=read(root/'matrix193_entry_controller_charts.json')
 for stem,obj in [('matrix193_idle_free_scout',idle),('matrix193_affine_reuse_scout',affine_receipt),('matrix193_entry_controller_charts',charts)]:ck(obj['source_sha256']==PINS[stem+'.py'],'receipt/source binding')
 ck(len(idle['packets'])==4 and len(charts['packets'])==3,'parent inventory')
 affine=affine_receipt['packet'];packets=[make(parent,None if i==0 else charts['packets'][i-1],affine,i) for i,parent in enumerate(idle['packets'])]
 ck([p['ledger']['total'] for p in packets]==[1617,1614,1614,1611],'derived complete counts')
 ck([p['ledger']['positive_witnesses'] for p in packets]==[145,144,144,143],'unchanged positive witnesses')
 ck(sum(p['ledger']['total'] for p in packets)==6456,'all four arrays')
 return {'schema':'matrix193-idle-affine-reuse-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,'fresh_evidence':{'complete_arrays':4,'complete_rows':6456,'coefficient_polynomials':16,'coefficient_entries':sum(len(c['ascending_coefficients']) for p in packets for c in p['coefficient_certificates']),'signed_modular_comparisons':32,'local_and_whole_polynomial_identities':True,'all_live':True},'scope':{'predecessor_code_executed':False,'same_polynomial_and_supplied_interface_as_each_immediate_IDLE_parent':True,'same_positive_zero_tuples_as_immediate_IDLE_parent':True,'comparison_with_pre_IDLE_ancestors':'ordinary-input projection inherited only; no common-witness inverse claimed','valid_fixed_program_recipe_unchanged':True,'diagnostic_emitted_or_replayed':False,'new_outer_trajectory_or_native_Pell_tuple':False,'exact_degrees_inherited_by_full_identity':True,'universal84_unchanged':True,'minimality_claim':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--idle-root',type=Path);g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=ap.parse_args();result=build(a.root,a.idle_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(same(result,read(a.expect)),'recursive type-exact receipt mismatch')
 print('PASS: four complete affine+IDLE arrays1617/1614/1614/1611;6456rows;16full coefficient identities;unchanged positive domains/degrees')
if __name__=='__main__':main()
