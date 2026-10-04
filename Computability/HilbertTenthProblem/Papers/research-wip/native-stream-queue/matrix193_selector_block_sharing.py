#!/usr/bin/env python3
"""Fresh complete sharing of identical contiguous positive-hat selector words."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

PINS={
 'matrix193_terminal_power_composition.py':'2dc0fb36f50da402cc479673bb2c23a4354f9a80e23fb6f17857168fc1ad9cd1',
 'matrix193_terminal_power_composition.json':'c6456750337b4f87f55918d03760b5759606b772e298d37c0c5df9c92b87b623',
 'matrix193_terminal_power_composition.md':'7ea837d4def42b7b97577c3e5f4c421f73a8256ac1858890bdbcc2ad0a6948a3',
 'matrix193_entry_controller_charts.py':'7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf',
 'matrix193_entry_controller_charts.json':'d5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
 'matrix193_entry_controller_charts.md':'27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122',
}
# Zero-based low-degree indices: X start, Y start, common length.
MATCHES=[(0,0,7),(10,10,3),(13,16,12),(28,40,3),(34,46,3),
         (37,52,12),(52,67,3),(58,73,3),(61,79,9)]
POWERS={1:'r134',3:'r142',7:'r166',9:'r138',12:'r144'}

def ck(value,message):
 if not value:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def canonical(obj):return json.dumps(obj,sort_keys=True,separators=(',',':')).encode()
def read(path):
 def pairs(items):
  d={}
  for k,v in items:ck(k not in d,'duplicate JSON key');d[k]=v
  return d
 def bad(text):raise ValueError('nonfinite JSON '+text)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_constant=bad)
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b

def add(a,b,sign=1):
 d=dict(a)
 for k,v in b.items():
  d[k]=d.get(k,0)+sign*v
  if not d[k]:del d[k]
 return d

def univariate_product(a,b):
 d={}
 for i,c in a.items():
  for j,e in b.items():d[i+j]=d.get(i+j,0)+c*e
 return {i:c for i,c in d.items()if c}

def q_polynomials(rows,Q):
 env={Q:{1:1}}
 for n,op,a,b in rows:
  if n==Q or not all(type(v)is int or v in env for v in (a,b)):continue
  def get(v):return ({0:v}if v else {})if type(v)is int else env[v]
  x,y=get(a),get(b);env[n]=univariate_product(x,y)if op=='*'else add(x,y,1 if op=='+'else -1)
 return env

def extract_word(rows,root,base):
 by={r[0]:r for r in rows};word=[];names=[];n=root
 while n in by and by[n][1]=='+':
  _,op,a,b=by[n];product=by.get(a)
  if product is None or product[1]!='*'or product[3]!=base:break
  word.append(b);names.extend((n,a));n=product[2]
 word.append(n)
 ck(all(type(v)is str for v in word),'word coefficients are paid named ports')
 ck(len(names)==len(set(names))==2*(len(word)-1),'literal Horner cone')
 ck(not(set(word)&set(names)),'word leaves outside private cone')
 return word,set(names)

def pieces(word,which):
 starts={m[which]:m[2]for m in MATCHES};out=[];i=0
 while i<len(word):
  length=starts.get(i,1);out.append(word[i:i+length]);i+=length
 ck(i==len(word),'complete word partition')
 return out

def emit_component(words,powers,targets,reserved):
 rows=[];memo={}
 def binary(op,a,b):
  name='selector_shared_'+str(len(rows));ck(name not in reserved,'new local namespace')
  rows.append([name,op,a,b]);return name
 def block(word):
  key=tuple(word)
  if key in memo:return memo[key]
  acc=word[-1]
  for coefficient in reversed(word[:-1]):acc=binary('+',binary('*',acc,powers[1]),coefficient)
  memo[key]=acc;return acc
 def assemble(word,which):
  blocks=pieces(word,which);acc=block(blocks[-1])
  for chunk in reversed(blocks[:-1]):
   acc=binary('+',binary('*',acc,powers[len(chunk)]),block(chunk))
  return acc
 outputs=[assemble(word,i)for i,word in enumerate(words)]
 ck(len(set(outputs))==2,'distinct output producers')
 renames=dict(zip(outputs,targets))
 component=[[renames.get(n,n),op,renames.get(a,a),renames.get(b,b)]for n,op,a,b in rows]
 ck(len(component)==242 and Counter(r[1]for r in component)==Counter({'*':121,'+':121}),'242 component ledger')
 return component

def linear_product(a,b):
 # Keys are (Q exponent, independent named selector atom or None).
 d={}
 for (i,u),c in a.items():
  for (j,v),e in b.items():
   ck(u is None or v is None,'selection component stays linear in its atoms')
   key=(i+j,v if u is None else u);d[key]=d.get(key,0)+c*e
 return {k:v for k,v in d.items()if v}

def linear_expansion(rows,atoms,powers):
 env={name:{(0,name):1}for name in atoms}
 ck(not(set(atoms)&set(powers)),'selector and scale seed separation')
 env.update({name:{(exponent,None):1}for name,exponent in powers.items()})
 for n,op,a,b in rows:
  ck(n not in env,'new linear component producer')
  ck(all(type(v)is int or v in env for v in (a,b)),'linear component paid boundaries')
  def get(v):return ({(0,None):v}if v else {})if type(v)is int else env[v]
  x,y=get(a),get(b);env[n]=linear_product(x,y)if op=='*'else add(x,y,1 if op=='+'else -1)
 return env

def live(rows,output):
 by={r[0]:r for r in rows};seen=set();todo=[output]
 while todo:
  n=todo.pop()
  if type(n)is str and n not in seen:
   seen.add(n)
   if n in by:todo.extend(by[n][2:])
 return seen

def audit(p):
 known=set(p['free']);ck(len(known)==len(p['free']),'unique free ports')
 degree={n:0 if n in p['fixed_numerals']else 1 for n in known};count=Counter()
 for n,op,a,b in p['source']:
  ck(type(n)is str and n not in known and op in ('+','-','*'),'fresh binary producer')
  ck(all(type(v)is int or(type(v)is str and v in known)for v in (a,b)),'complete paid source order')
  da,db=(degree[v]if type(v)is str else 0 for v in (a,b));degree[n]=da+db if op=='*'else max(da,db)
  count[op]+=1;known.add(n)
 ck(live(p['source'],p['output'])==known,'all source rows and ports live')
 return {'total':len(p['source']),'M':count['*'],'A':count['+']+count['-'],
         'positive_witnesses':len(p['witnesses']),'supplied_ports':len(p['free']),
         'fixed_coefficient_ports':len(p['fixed_numerals']),
         'integer_literals':len({v for r in p['source']for v in r[2:]if type(v)is int}),
         'syntactic_degree_upper':degree[p['output']],'all_live':True}

def finalizer(p,N):
 rows=p['source'];by={r[0]:r for r in rows};res=p['retained_residual_wires'];squares=[]
 for n in res:
  candidates=[r[0]for r in rows if r[1:]==['*',n,n]];ck(len(candidates)==1,'one residual square');squares.append(candidates[0])
 out=by[p['output']];ck(out[1]=='-'and out[3]==1,'final subtraction')
 product=by[out[2]];ck(product[1:3]==['*',N],'native multiplier')
 one=by[product[3]];ck(one[1]=='+'and one[3]==1,'one plus SOS');sums=set()
 def leaves(n):
  if n in squares:return Counter({n:1})
  r=by[n];ck(r[1]=='+'and type(r[2])is str and type(r[3])is str,'SOS sum tree')
  sums.add(n);return leaves(r[2])+leaves(r[3])
 ck(leaves(one[2])==Counter(squares),'all residuals exactly once')
 names=set(res)|set(squares)|sums|{out[0],product[0],one[0]}
 ck(len(names)==3*len(res)+2,'complete finalizer inventory')
 ck(all(not any(v in names for v in r[2:])for r in rows if r[0]not in names),'private finalizer')
 return [r for r in rows if r[0]in names]

def whole_identity(parent,child,Q,cuts):
 pool={}
 def token(key):
  if key not in pool:pool[key]=len(pool)
  return pool[key]
 inputs={n:token(('input',n))for n in parent['free']}
 def run(rows):
  env=dict(inputs)
  for n,op,a,b in rows:
   aa,bb=(env[v]if type(v)is str else token(('integer',v))for v in (a,b))
   if n in cuts:
    binding=tuple(sorted((exponent,env[atom],coefficient)for(exponent,atom),coefficient in cuts[n].items()))
    env[n]=token(('proved_linear_selector_word',env[Q],binding))
   else:env[n]=token(('binary',op,aa,bb))
  return env
 old,new=run(parent['source']),run(child['source']);common=set(old)&set(new)
 ck(old[Q]==new[Q],'actual paid Q is unchanged')
 ck(all(old[n]==new[n]for n in common),'all retained old registers identical')
 ck(old[parent['output']]==new[child['output']],'entire output identity')
 return {'selector_cut_identities':len(cuts),'scale_and_selector_atoms_bound_to_actual_input_expressions':True,
         'retained_parent_paid_registers_compared':len(common)-len(parent['free']),
         'entire_polynomial_identity':'F_shared=F_immediate_terminal_power_parent over every commutative ring on identical supplied coordinates'}

def evaluate(p,values,prime):
 env={n:v%prime for n,v in values.items()}
 for n,op,a,b in p['source']:
  x=env[a]if type(a)is str else a;y=env[b]if type(b)is str else b
  env[n]=(x*y if op=='*'else x+y if op=='+'else x-y)%prime
 return env

def make(parent,mapping,index,native,protected):
 def w(n):return mapping.get(n,n)if type(n)is str else n
 rows=parent['source'];by={r[0]:r for r in rows};Q=w('r108');base=w('r134');targets=[w('r346'),w('r540')]
 extracted=[extract_word(rows,n,base)for n in targets];words=[x[0]for x in extracted];cones=[x[1]for x in extracted]
 ck([len(word)for word in words]==[72,97]and[len(cone)for cone in cones]==[142,192],'two full literal word inventories')
 ck(not(cones[0]&cones[1]),'disjoint old Horner cones')
 oldnames=cones[0]|cones[1];oldcomponent=[r for r in rows if r[0]in oldnames]
 ck(all(v not in oldnames or v in targets for r in rows if r[0]not in oldnames for v in r[2:]),'only two output consumers cross old cone boundary')
 matching=[];used=[set(),set()]
 for a,b,length in MATCHES:
  ck(words[0][a:a+length]==words[1][b:b+length]and len(words[0][a:a+length])==length,'literal identical common run')
  for which,start in ((0,a),(1,b)):
   interval=set(range(start,start+length));ck(not(used[which]&interval),'disjoint shared intervals');used[which]|=interval
  matching.append({'X_start':a,'Y_start':b,'length':length,'actual_coefficients':words[0][a:a+length]})
 ck(sum(c['length']for c in matching)==55,'55 shared selector coefficients')
 powers={length:w(name)for length,name in POWERS.items()};qp=q_polynomials(rows,Q)
 for length,name in powers.items():ck(qp[name]=={2*length:1},'existing paid block-concatenation power')
 component=emit_component(words,powers,targets,set(by)|set(parent['free']))
 atoms=set(words[0])|set(words[1]);power_seeds={n:2*k for k,n in powers.items()}
 oldlin=linear_expansion(oldcomponent,atoms,{base:2});newlin=linear_expansion(component,atoms,power_seeds)
 cuts={};certs=[]
 for n,word in zip(targets,words):
  expected={(2*j,atom):1 for j,atom in enumerate(word)}
  ck(oldlin[n]==newlin[n]==expected,'complete exact selector polynomial')
  cuts[n]=expected;certs.append({'wire':n,'ascending_selector_coefficients':word,'Q_degree':2*(len(word)-1),
    'expanded_terms':[[e,a,c]for(e,a),c in sorted(expected.items())]})
 # Insert the complete shared component at the first old cone position.
 newrows=[];inserted=False
 for r in rows:
  if r[0]in oldnames:
   if not inserted:newrows.extend(component);inserted=True
  else:newrows.append(r)
 child={k:parent[k]for k in ('variant','free','witnesses','fixed_numerals','fixture_fixed_bindings','output')}
 child['source']=newrows;child['retained_residual_wires']=parent['retained_residual_wires'];newby={r[0]:r for r in newrows}
 ck([r for r in newrows if r[0]not in {x[0]for x in component}]==[r for r in rows if r[0]not in oldnames],'all surrounding rows literal and ordered')
 before,ledger=audit(parent),audit(child)
 ck((ledger['total'],ledger['M'],ledger['A'])==(before['total']-92,before['M']-46,before['A']-46),'full92-gate saving')
 child['whole_identity']=whole_identity(parent,child,Q,cuts)
 newqp=q_polynomials(newrows,Q);coeffs=[]
 for c in parent['coefficient_certificates']:
  n=c['wire'];expected={i:v for i,v in enumerate(c['ascending_coefficients'])if v}
  ck(qp[n]==newqp[n]==expected,'entire fixed coefficient word')
  coeffs.append({'wire':n,'ascending_coefficients':c['ascending_coefficients'],'degree':max(expected),
                 'polynomial_sha256':sha(canonical(sorted(expected.items())))})
 ck(all(newby[r[0]]==r for r in parent['coefficient_component']),'coefficient553 literal')
 child['coefficient_component']=parent['coefficient_component'];child['component_ledger']={'total':553,'M':305,'A':248};child['coefficient_certificates']=coeffs
 for n in native+protected:ck(newby[w(n)]==by[w(n)],'literal retained protected producer')
 oldfinal,newfinal=finalizer(parent,w('eight_units')),finalizer(child,w('eight_units'));ck(oldfinal==newfinal,'complete traced finalizer literal')
 ledger.update(exact_degree=parent['ledger']['exact_degree'],outer_residuals=len(child['retained_residual_wires']));child['ledger']=ledger
 child['selector_words']=certs;child['matching_runs']=matching;child['word_partitions']=[pieces(word,i)for i,word in enumerate(words)]
 child['old_selector_component']=oldcomponent;child['shared_selector_component']=component
 child['selector_ledger']={'old_rows':334,'old_M':167,'old_A':167,'new_rows':242,'new_M':121,'new_A':121,
   'shared_runs':9,'shared_coefficients':55,'X_partition_blocks':len(pieces(words[0],0)),'Y_partition_blocks':len(pieces(words[1],1)),
   'new_power_gates':0,'paid_power_bindings':[{'length':k,'wire':n,'Q_exponent':2*k}for k,n in powers.items()]}
 child['source_boundary_checks']={'old_cone_external_outputs':targets,'all_surrounding_definitions_literal':True,
   'native_rows_literal':63,'group_population_rows_literal':97,'fixed_coefficient_rows_literal':553,
   'residual_producers_literal':len(child['retained_residual_wires']),'explicitly_traced_finalizer_rows_literal':len(oldfinal)}
 child['parent_reference']={'receipt':'matrix193_terminal_power_composition.json','packet_index':index,
   'source_array_sha256':sha(canonical(rows)),'fresh_ledger':before}
 child['degree_transfer']={'exact_degree':ledger['exact_degree'],'reason':'complete polynomial identity on identical variables to immediate terminal-power parent','new_degree_computation':False}
 tests=[];rng=random.Random(1412+index)
 for prime in (1000000007,1000000009):
  for case in range(4):
   values={n:rng.randrange(-139,140)for n in child['free']}
   if case%2==0:values.update(child['fixture_fixed_bindings'])
   a,b=evaluate(parent,values,prime),evaluate(child,values,prime)
   ck(all(a[n]==b[n]for n in set(a)&set(b)),'supplemental entire retained-register equality')
   tests.append({'prime':prime,'case':case,'illustrative_fixed_bindings':case%2==0,'output':b[child['output']]})
 child['supplemental_modular_checks']=tests
 return child

def build(root,parent_root):
 for n,pin in PINS.items():
  directory=parent_root if n.startswith('matrix193_terminal_power_composition.')else root
  ck(sha((directory/n).read_bytes())==pin,'frozen pin '+n)
 parent=read(parent_root/'matrix193_terminal_power_composition.json');charts=read(root/'matrix193_entry_controller_charts.json')
 ck(parent['source_sha256']==PINS['matrix193_terminal_power_composition.py']and charts['source_sha256']==PINS['matrix193_entry_controller_charts.py'],'source bindings')
 ck(len(parent['packets'])==4 and len(charts['packets'])==3,'full variant inventory')
 names=[r[0]for r in parent['packets'][0]['source']];native=names[names.index('selection__bs_even'):names.index('eight_units')+1]
 protected=['r'+str(i)for i in range(110,134)]+[n for n in names if n.startswith('grouped_population_sum_')]+['r103']
 ck(len(native)==63 and len(protected)==97,'protected source inventory')
 packets=[make(p,{}if i==0 else charts['packets'][i-1]['map'],i,native,protected)for i,p in enumerate(parent['packets'])]
 ck([p['ledger']['total']for p in packets]==[1418,1415,1415,1412],'complete counts')
 ck([p['ledger']['positive_witnesses']for p in packets]==[141,140,140,139],'witness counts')
 return {'schema':'matrix193-selector-block-sharing-v1','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,'packets':packets,
  'fresh_evidence':{'complete_arrays':4,'complete_rows':sum(len(p['source'])for p in packets),'selector_polynomial_identities':8,
   'individually_authenticated_shared_runs':36,'complete_coefficient_words':16,'coefficient_entries':sum(len(c['ascending_coefficients'])for p in packets for c in p['coefficient_certificates']),
   'whole_source_identities':4,'explicit_finalizer_traces':8,'signed_modular_retained_register_checks':32},
  'scope':{'frozen_code_executed_or_imported':False,'same_polynomial_and_supplied_coordinates_as_immediate_parent':True,
   'same_positive_integer_zero_tuples_as_immediate_parent':True,'valid_fixed_program_recipe_unchanged':True,
   'earlier_terminal_carry_and_IDLE_comparisons':'ordinary input projection only','exact_degrees_inherited':True,
   'new_native_tuple_or_accepting_fixture':False,'universal84_unchanged':True,'optimality_claim':False}}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--parent-root',type=Path)
 g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path);a=p.parse_args()
 result=build(a.root,a.parent_root or a.root)
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 else:ck(same(result,read(a.expect)),'type-exact full receipt')
 print('PASS: full1418/1415/1415/1412;334->242 selector rows;exact all-ring identities;unchanged domains/degrees')
if __name__=='__main__':main()
