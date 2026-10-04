#!/usr/bin/env python3
"""Fresh complete composition: terminal-carry parents plus exact paid power reuse."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

PINS = {
 'matrix193_terminal_carry_chart.py':'b6bd9bd02f5aa14e73f46804706c8ca155186be4610e10f5b5e1b518e6d9c7d3',
 'matrix193_terminal_carry_chart.json':'6afa10fee956f9e26167345300d886116374dafc6695e91bf5dd3d28679915f2',
 'matrix193_terminal_carry_chart.md':'a576e578d8dc80b174a60ca9bce28b1aa8dbd848a61c8c870ced4d9ab366fbd4',
 'matrix193_cross_stage_power_reuse.py':'8b2473737a06e5e4a2a03e2e8282c94f8c65ab0bfde6c15db454b6cd3f8a2668',
 'matrix193_cross_stage_power_reuse.json':'c3f525e806cfb3743ff99456b006f23f441091804e85db19cdcb5552859d4006',
 'matrix193_cross_stage_power_reuse.md':'d8e8768f07ece8f79b6698bd3729e7f48d846aa2d3abd07049efc046ddb50580',
 'matrix193_entry_controller_charts.py':'7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
 'matrix193_entry_controller_charts.md':'27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122',
}

def need(ok, message):
 if not ok: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def encoded(value): return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()
def load(path):
 def pairs(items):
  result={}
  for k,v in items:
   need(k not in result,'duplicate JSON key');result[k]=v
  return result
 def bad(text): raise ValueError('nonfinite JSON '+text)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def equal(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(equal(a[k],b[k]) for k in a)
 if type(a) is list:return len(a)==len(b) and all(equal(x,y) for x,y in zip(a,b))
 return a==b

def add(a,b,sign=1):
 out=dict(a)
 for i,c in b.items():
  out[i]=out.get(i,0)+sign*c
  if not out[i]:del out[i]
 return out

def mul(a,b):
 out={}
 for i,c in a.items():
  for j,d in b.items():out[i+j]=out.get(i+j,0)+c*d
 return {i:c for i,c in out.items() if c}

def expand(rows,Q):
 env={Q:{1:1}}
 for n,op,a,b in rows:
  if n==Q or not all(type(v)is int or v in env for v in (a,b)):continue
  def get(v):return ({0:v} if v else {}) if type(v)is int else env[v]
  x,y=get(a),get(b);env[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
 return env

def liveness(rows,output):
 by={r[0]:r for r in rows};live=set();todo=[output]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in live:
   live.add(n)
   if n in by:todo.extend(by[n][2:])
 return live

def reorder(rows,output):
 live=liveness(rows,output);by={r[0]:r for r in rows if r[0]in live}
 done=set();active=set();result=[]
 def emit(n):
  if n not in by or n in done:return
  need(n not in active,'acyclic dependency graph');active.add(n)
  for v in by[n][2:]:
   if type(v)is str:emit(v)
  active.remove(n);done.add(n);result.append(by[n])
 for r in rows:
  if r[0]in live:emit(r[0])
 return result,live

def audit(p):
 known=set(p['free']);need(len(known)==len(p['free']),'unique ports')
 degrees={n:0 if n in p['fixed_numerals'] else 1 for n in known};count=Counter()
 for n,op,a,b in p['source']:
  need(type(n)is str and n not in known and op in ('+','-','*'),'unique binary producer')
  need(all(type(v)is int or (type(v)is str and v in known)for v in (a,b)),'paid prior operands')
  da,db=(degrees[v] if type(v)is str else 0 for v in (a,b))
  degrees[n]=da+db if op=='*' else max(da,db);known.add(n);count[op]+=1
 need(liveness(p['source'],p['output'])==known,'all supplied ports and producers live')
 return {'total':len(p['source']),'M':count['*'],'A':count['+']+count['-'],
         'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),
         'fixed_coefficient_ports':len(p['fixed_numerals']),
         'integer_literals':len({v for r in p['source']for v in r[2:]if type(v)is int}),
         'syntactic_degree_upper':degrees[p['output']],'all_live':True}

def trace_finalizer(p,N):
 """Trace the algebraic finalizer, without assuming any contiguous source suffix."""
 rows=p['source'];by={r[0]:r for r in rows};res=p['retained_residual_wires']
 squares=[]
 for n in res:
  found=[r[0]for r in rows if r[1:]==['*',n,n]]
  need(len(found)==1,'unique square of each current residual');squares.append(found[0])
 out=by[p['output']];need(out[1]=='-' and out[3]==1,'final subtract one')
 product=by[out[2]];need(product[1:3]==['*',N],'final native-product multiplier')
 plusone=by[product[3]];need(plusone[1]=='+' and plusone[3]==1,'one plus SOS')
 sums=set();active=set()
 def leaves(n):
  if n in squares:return Counter({n:1})
  need(n not in active,'acyclic SOS');active.add(n)
  r=by[n];need(r[1]=='+' and type(r[2])is str and type(r[3])is str,'binary sum of squares')
  sums.add(n);answer=leaves(r[2])+leaves(r[3]);active.remove(n);return answer
 need(leaves(plusone[2])==Counter(squares),'each residual square exactly once')
 names=set(res)|set(squares)|sums|{plusone[0],product[0],out[0]}
 need(len(names)==3*len(res)+2,'full finalizer count')
 need(all(not any(v in names for v in r[2:]) for r in rows if r[0]not in names),'private finalizer consumer boundary')
 return [r for r in rows if r[0]in names]

def identity(parent,child,Q,proved):
 pool={}
 def token(key):
  if key not in pool:pool[key]=len(pool)
  return pool[key]
 inputs={n:token(('port',n))for n in parent['free']}
 def run(rows):
  env=dict(inputs)
  for n,op,a,b in rows:
   x,y=(env[v]if type(v)is str else token(('integer',v))for v in (a,b))
   env[n]=token(('proved_cut',env[Q],tuple(sorted(proved[n].items()))))if n in proved else token(('binary',op,x,y))
  return env
 before,after=run(parent['source']),run(child['source'])
 need(before[Q]==after[Q],'same complete paid scale expression')
 need(all(before[n]==v for n,v in after.items()),'all retained-register input-bound identities')
 need(before[parent['output']]==after[child['output']],'entire output identity')
 return {'exact_local_polynomial_cuts':len(proved),'cuts_bound_to_actual_input_bearing_Q':True,
         'retained_registers_compared':len(child['source']),'same_complete_polynomial':True,
         'contract':'F_composition=F_immediate_terminal_carry_parent over every commutative ring, on identical supplied coordinates'}

def evaluate(p,values,prime):
 env={n:v%prime for n,v in values.items()}
 for n,op,a,b in p['source']:
  x=env[a]if type(a)is str else a;y=env[b]if type(b)is str else b
  env[n]=(x*y if op=='*' else x+y if op=='+' else x-y)%prime
 return env

def compose(parent,recipe,baseline_recipe,mapping,index,native,protected):
 def w(n):return mapping.get(n,n)if type(n)is str else n
 def mapped(row):return [w(row[0]),row[1],w(row[2]),w(row[3])]
 need(parent['variant']==recipe['variant'],'variant correspondence')
 old_rows=parent['source'];by={r[0]:r for r in old_rows};Q=w('r108');oldpoly=expand(old_rows,Q)
 need(len(recipe['local_identities'])==len(baseline_recipe['local_identities'])==13,'exact13-edit inventory')
 changes={};proved={};certificates=[]
 for base,cert in zip(baseline_recipe['local_identities'],recipe['local_identities']):
  need(cert['old_row']==mapped(base['old_row']) and cert['new_row']==mapped(base['new_row']),'frozen controller-map correspondence')
  n,op,a,b=cert['new_row'];need(op=='*' and by[n]==cert['old_row'],'actual old terminal-chart row')
  expected={i:c for i,c in cert['target_polynomial']}
  need(oldpoly[n]==expected==mul(oldpoly[a],oldpoly[b]),'exact13 local identities from actual parent')
  need(sorted(oldpoly[a].items())==[tuple(t)for t in cert['left_polynomial']] and sorted(oldpoly[b].items())==[tuple(t)for t in cert['right_polynomial']],'exact paid operand polynomials')
  changes[n]=cert['new_row'];proved[n]=expected
  certificates.append({'old_row':by[n],'new_row':cert['new_row'],'target_polynomial':cert['target_polynomial'],
                       'left_polynomial':cert['left_polynomial'],'right_polynomial':cert['right_polynomial']})
 provisional=[changes.get(r[0],r[:])for r in old_rows];rows,live=reorder(provisional,parent['output'])
 removed=[r for r in old_rows if r[0]not in live]
 need(removed==recipe['removed_rows'],'exact34 actual deleted rows in their parent order')
 need({r[0]:r for r in removed}=={w(r[0]):mapped(r)for r in baseline_recipe['removed_rows']},'full deleted rows agree under controller map')
 need(Counter(r[1]for r in removed)==Counter({'*':30,'+':4}),'exact30M4A saving')
 child={k:parent[k]for k in ('variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output')}
 child['source']=rows;newby={r[0]:r for r in rows};newpoly=expand(rows,Q)
 need(all(row==changes.get(n,by[n])for n,row in newby.items()),'every retained non-edit row literal')
 need([r[0]for r in old_rows if r[0]in newby and r[0]not in oldpoly]==[r[0]for r in rows if r[0]not in oldpoly],'non-pure chronology unchanged')
 need(all(oldpoly[n]==poly for n,poly in newpoly.items()),'every retained pure-Q polynomial')
 need(all(newpoly[n]==poly for n,poly in proved.items()),'all13 rescheduled targets re-expanded')
 coefficients=[]
 for cert in parent['coefficient_certificates']:
  n=cert['wire'];expected={i:c for i,c in enumerate(cert['ascending_coefficients'])if c}
  need(oldpoly[n]==newpoly[n]==expected,'complete coefficient polynomial')
  coefficients.append({'wire':n,'ascending_coefficients':cert['ascending_coefficients'],'degree':max(expected),
                       'polynomial_sha256':sha(encoded(sorted(expected.items())))})
 compnames={r[0]for r in parent['coefficient_component']};component=[r for r in rows if r[0]in compnames]
 need(compnames<=set(newby) and len(component)==553,'all553 coefficient definitions remain')
 need(component==recipe['coefficient_component'],'complete scheduled coefficient array equals frozen power recipe')
 need({n for n in compnames if by[n]!=newby[n]}=={w('cp526')},'only cp526 changes inside component')
 cc=Counter(r[1]for r in component);need((cc['*'],cc['+']+cc['-'])==(305,248),'component ledger')
 child['coefficient_component']=component;child['component_ledger']={'total':553,'M':305,'A':248};child['coefficient_certificates']=coefficients
 for n in native+protected:need(newby[w(n)]==by[w(n)],'literal protected row '+n)
 child['retained_residual_wires']=parent['retained_residual_wires']
 oldfinal=trace_finalizer(parent,w('eight_units'));newfinal=trace_finalizer(child,w('eight_units'))
 need(oldfinal==newfinal,'complete explicitly traced finalizer literal')
 before=audit(parent);ledger=audit(child)
 need((ledger['total'],ledger['M'],ledger['A'])==(before['total']-34,before['M']-30,before['A']-4),'fresh complete ledger difference')
 ledger.update(exact_degree=parent['ledger']['exact_degree'],outer_residuals=len(child['retained_residual_wires']))
 child['ledger']=ledger;child['whole_identity']=identity(parent,child,Q,proved)
 child['local_identities']=certificates;child['removed_rows']=removed
 child['source_boundary_checks']={'native_rows_literal':len(native),'group_population_rows_literal':len(protected),
    'coefficient_rows':len(component),'changed_coefficient_rows':1,'residuals_literal':len(child['retained_residual_wires']),
    'finalizer_rows_literal':len(oldfinal),'finalizers_explicitly_traced_without_suffix_assumption':True,
    'nonpure_relative_order_retained':True,'other_retained_definitions_literal':len(rows)-len(changes)}
 child['parent_reference']={'receipt':'matrix193_terminal_carry_chart.json','packet_index':index,
   'source_array_sha256':sha(encoded(old_rows)),'fresh_ledger':before}
 child['power_recipe_reference']={'receipt':'matrix193_cross_stage_power_reuse.json','packet_index':index,
   'source_array_sha256':sha(encoded(recipe['source']))}
 child['degree_transfer']={'exact_degree':ledger['exact_degree'],'reason':'whole polynomial identity on identical coordinates to terminal-carry parent',
   'parent_degree_proof_sha256':sha(encoded(parent['degree_proof'])),'no_new_leading_degree_computation':True}
 checks=[];rng=random.Random(1504+index)
 for prime in (1000000007,1000000009):
  for case in range(4):
   values={n:rng.randrange(-127,128)for n in child['free']}
   if case%2==0:values.update(child['fixture_fixed_bindings'])
   a,b=evaluate(parent,values,prime),evaluate(child,values,prime)
   need(all(a[n]==v for n,v in b.items()),'signed modular entire register identity')
   checks.append({'prime':prime,'case':case,'illustrative_fixed_bindings':case%2==0,'output':b[child['output']]})
 child['supplemental_modular_checks']=checks
 return child

def build(root,packet_root):
 for name,pin in PINS.items():
  folder=root if name.startswith('matrix193_entry_controller_charts.')else packet_root
  need(sha((folder/name).read_bytes())==pin,'frozen byte pin '+name)
 parents=load(packet_root/'matrix193_terminal_carry_chart.json');recipe=load(packet_root/'matrix193_cross_stage_power_reuse.json');charts=load(root/'matrix193_entry_controller_charts.json')
 for name,data in [('matrix193_terminal_carry_chart',parents),('matrix193_cross_stage_power_reuse',recipe),('matrix193_entry_controller_charts',charts)]:
  need(data['source_sha256']==PINS[name+'.py'],'receipt/source binding')
 need(len(parents['packets'])==len(recipe['packets'])==4 and len(charts['packets'])==3,'complete inventory')
 names=[r[0]for r in parents['packets'][0]['source']];native=names[names.index('selection__bs_even'):names.index('eight_units')+1]
 protected=['r'+str(i)for i in range(110,134)]+[n for n in names if n.startswith('grouped_population_sum_')]+['r103']
 need(len(native)==63 and len(protected)==97,'native and group/population inventories')
 packets=[compose(p,recipe['packets'][i],recipe['packets'][0],{}if i==0 else charts['packets'][i-1]['map'],i,native,protected)for i,p in enumerate(parents['packets'])]
 need([p['ledger']['total']for p in packets]==[1510,1507,1507,1504],'all full operation counts')
 need([p['ledger']['positive_witnesses']for p in packets]==[141,140,140,139],'all witness counts')
 need([p['ledger']['exact_degree']for p in packets]==[35587,53345,53347,71105],'terminal-parent exact degree inheritance')
 return {'schema':'matrix193-terminal-power-composition-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,
   'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source'])for p in packets),'local_polynomial_identities':52,
     'complete_coefficient_words':16,'coefficient_entries':sum(len(c['ascending_coefficients'])for p in packets for c in p['coefficient_certificates']),
     'whole_source_identities':4,'explicit_finalizer_traces':8,'signed_modular_entire_register_maps':32},
   'scope':{'frozen_code_executed_or_imported':False,'same_polynomial_and_coordinates_as_immediate_terminal_parent':True,
     'same_positive_zero_tuples_as_immediate_terminal_parent':True,'earlier_bounded_extraction_parent_comparison':'ordinary input projection only',
     'pre_IDLE_comparison':'ordinary input projection only','valid_fixed_program_recipe_unchanged':True,
     'exact_degrees_inherited_from_terminal_chart':True,'new_giant_fixture_or_native_Pell_tuple':False,
     'universal84_unchanged':True,'minimality_claim':False}}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--packet-root',type=Path)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
 result=build(a.root,a.packet_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:need(equal(result,load(a.expect)),'type-exact complete receipt')
 print('PASS: full1510/1507/1507/1504;52 exact cuts;full identities;traced finalizers;inherited terminal degrees')
if __name__=='__main__':main()
