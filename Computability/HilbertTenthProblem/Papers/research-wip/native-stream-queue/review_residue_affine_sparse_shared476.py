#!/usr/bin/env python3
"""Independent all-row reconstruction and local-polynomial/DAG audit."""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

AUTHOR = {
 'residue_affine_sparse_shared476.py':'52e09d2b3474e37c6116e16b7a1ee59395a337a5ff381b4881ae616ecbaafddf',
 'residue_affine_sparse_shared476.json':'90e6e265ae1eb9a1cd1239255c14da3d3c6e5841f330f7a6220536d182778ba8',
 'residue_affine_sparse_shared476.md':'cbd4d632b813f0ad34a9e5b35894d187ca229c14f1d4cf3af269a518ab57fcd4',
}
PARENT = {
 'residue_affine_sparse_program_radix504.py':'d85b7985fb54b23950070515514e4e88a3d942c17aa7531320c306e1fe46f073',
 'residue_affine_sparse_program_radix504.json':'d089b8477f28b154e04fa149231e19c333dacd35f995829ac09395fb3a70c0eb',
 'residue_affine_sparse_program_radix504.md':'4c3e0545b8f7f025096a30170a1785d33da35b625e3aa8dacb1362a461d0a549',
}
GROUPS = [
 ('prime_selector_93',[2,3,13]),('prime_selector_95',[32,33,34]),
 ('prime_selector_97',[26,27,35]),('prime_selector_101',[16,17,28,30,31]),
 ('prime_selector_109',[6,7,10,18,19,20,21,24,25]),
 ('prime_selector_113',[5,8,9,14,15]),('prime_selector_115',[4,11,12]),
 ('selectors_36',[0,1]),('control_codes__duplicate_state_6',[22,23]),('edge_29',[29]),
]

def check(ok,msg):
 if not ok:raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def encode(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def load(path):
 def pairs(xs):
  out={}
  for k,v in xs:
   check(k not in out,'duplicate key');out[k]=v
  return out
 def bad(x):raise ValueError('noninteger numeric JSON '+x)
 return json.loads(path.read_text(),object_pairs_hook=pairs,parse_float=bad,parse_constant=bad)
def definitions(rows):
 out={}
 for row in rows:
  check(type(row)is list and len(row)==4,'row shape')
  n,o,a,b=row
  check(type(n)is str and n not in out and o in ['+','-','*'],'SSA')
  check(all(type(v) in [str,int] for v in [a,b]),'operand')
  out[n]=row
 return out
def ports(rows):
 names=set(definitions(rows))
 return sorted({v for r in rows for v in r[2:] if type(v)is str and v not in names})
def audit(rows):
 by=definitions(rows);free=ports(rows);known=set(free)
 for n,o,a,b in rows:
  check(n not in known and all(type(v)is int or v in known for v in [a,b]),'topology')
  known.add(n)
 live=set();todo=['norm_output']
 while todo:
  n=todo.pop()
  if type(n)is not str or n in live:continue
  live.add(n)
  if n in by:todo.extend(by[n][2:])
 check(live==known,'full row and port liveness')
 ops=Counter(r[1] for r in rows)
 return {'rows':len(rows),'M':ops['*'],'A':ops['+']+ops['-'],'ports':len(free),'all_live':True}

def plus(a,b,sign=1):
 out=dict(a)
 for k,c in b.items():
  out[k]=out.get(k,0)+sign*c
  if not out[k]:del out[k]
 return out
def times(a,b):
 out={}
 for k,c in a.items():
  for j,d in b.items():
   key=tuple(sorted(k+j));out[key]=out.get(key,0)+c*d
 return {k:c for k,c in out.items() if c}
def expand(rows,target,boundaries):
 by=definitions(rows);env={v:{(v,):1} for v in boundaries}
 def visit(v):
  if type(v)is int:return {():v} if v else {}
  if v not in env:
   check(v in by,'uncut polynomial leaf '+v)
   _,o,a,b=by[v];a=visit(a);b=visit(b)
   env[v]=times(a,b) if o=='*' else plus(a,b,1 if o=='+' else -1)
  return env[v]
 return visit(target)
def records(poly):return [[list(m),c] for m,c in sorted(poly.items())]

def reconstruct(old):
 out=definitions(old)
 deleted=[f'selectors_{k}' for k in range(37,70)]+[
  'range_repeat_shift_407','three_range_repeat_408',
  'non_increment_149','non_decrement_150','zero_complement_151']
 for n in deleted:del out[n]
 acc=GROUPS[0][0]
 for j,(group,_) in enumerate(GROUPS[1:]):
  n=f'u21_grouped_J_{j}' if j<8 else 'selectors_70'
  out[n]=[n,'+',acc,group];acc=n
 replacements=[
  ['common_quotient_152','+','quotient_71','difference_word_148'],
  ['u21_nonzero_actions','+','action_selector_123','action_selector_134'],
  ['u21_nonzero_or_test','+','u21_nonzero_actions','edge_14'],
  ['common_payload_154','+','common_remainder_153','u21_nonzero_or_test'],
  ['all_ranges_427','*','range_mask_91','repeat_odd_318']]
 for row in replacements:out[row[0]]=row
 return out,deleted

def exact_identity(old,new):
 free=ports(old);edges={f'edge_{k}' for k in range(36)}
 for name,indices in GROUPS:
  check(expand(old,name,edges)=={(f'edge_{k}',):1 for k in indices},'group '+name)
 check(sorted(k for _,xs in GROUPS for k in xs)==list(range(36)),'disjoint36 partition')
 j={():-36,**{(f'edge{k}_hat',):1 for k in range(36)}}
 for rows in [old,new]:check(expand(rows,'selectors_70',free)==j,'whole population polynomial')
 r3={():1,('scale_89',):1,('scale_89','scale_89'):1}
 for rows,wire in [(old,'three_range_repeat_408'),(old,'repeat_odd_318'),(new,'repeat_odd_318')]:
  check(expand(rows,wire,{'scale_89'})==r3,'range cubic repunit')
 bd={'quotient_71','selectors_70','difference_word_148','complement_73','action_selector_123','action_selector_134','edge_14'}
 payload={(n,):(-1 if n=='complement_73' else 1) for n in bd-{'selectors_70'}}
 for rows in [old,new]:check(expand(rows,'common_payload_154',bd)==payload,'exact payload cancellation')
 # Intern normal expression nodes, but interpret every authorized local cut
 # as its proved sparse polynomial in the ACTUAL reached boundary values.
 table={}
 def intern(key):
  if key not in table:table[key]=len(table)+1
  return table[key]
 def interpret(rows):
  env={n:intern(('port',n)) for n in free}
  for n,o,a,b in rows:
   x=env[a] if type(a)is str else intern(('integer',a))
   y=env[b] if type(b)is str else intern(('integer',b))
   poly=j if n=='selectors_70' else r3 if n in ['repeat_odd_318','three_range_repeat_408'] else payload if n=='common_payload_154' else None
   if poly is not None:
    terms={}
    for mon,coef in poly.items():
     key=tuple(sorted(env[v] for v in mon));terms[key]=terms.get(key,0)+coef
    env[n]=intern(('polynomial',tuple(sorted((m,c) for m,c in terms.items() if c))))
   else:
    if o in ['+','*'] and y<x:x,y=y,x
    env[n]=intern((o,x,y))
  return env
 a,b=interpret(old),interpret(new)
 common=set(definitions(old))&set(definitions(new));changed={'common_quotient_152','common_remainder_153'}
 check(all(a[n]==b[n] for n in common-changed),'all common downstream expression values')
 check(all(a[n]!=b[n] for n in changed),'two values really change')
 check(a['norm_output']==b['norm_output'],'full polynomial identity')
 native=[n for n in common if n.startswith('native__')]
 check(len(native)==72 and all(a[n]==b[n] for n in native),'native72 values')
 return {'population_polynomial':records(j),'range_polynomial':records(r3),'payload_polynomial':records(payload),
  'groups':[[n,v] for n,v in GROUPS],'same_value_retained_rows':len(common-changed),
  'different_intermediate_rows':sorted(changed),'native_values':len(native),'whole_output_equal':True,
  'cut_values_bound_to_reached_source_expressions':True,'expression_nodes':len(table)}

def run(rows,v,p):
 env=dict(v)
 for n,o,a,b in rows:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b
  env[n]=(a*b if o=='*' else a+b if o=='+' else a-b)%p
 return env
def build(root,author):
 for n,h in AUTHOR.items():check(sha((author/n).read_bytes())==h,'author pin '+n)
 for n,h in PARENT.items():check(sha((root/n).read_bytes())==h,'parent pin '+n)
 receipt=load(author/'residue_affine_sparse_shared476.json')
 check(receipt['source_sha256']==AUTHOR['residue_affine_sparse_shared476.py'],'receipt helper binding')
 for n,h in receipt['dependencies'].items():check(sha((root/n).read_bytes())==h,'additional dependency '+n)
 parent=load(root/'residue_affine_sparse_program_radix504.json');child=receipt['packet'];old=parent['source'];new=child['source']
 parent_before=encode(old)
 expected,deleted=reconstruct(old);check(definitions(new)==expected,'all476 literal row definitions')
 check(encode(old)==parent_before,'independent reconstruction preserves untouched parent')
 check(child['source_sha256']==sha(encode(new)),'author emitted array binding')
 a,b=audit(old),audit(new)
 check((a['rows'],a['M'],a['A'])==(504,177,327),'parent ledger')
 check((b['rows'],b['M'],b['A'],b['ports'])==(476,176,300,70),'child ledger')
 check(ports(old)==ports(new),'identical free interface')
 check(child['parameters']==parent['parameters']==['program','radix_program','input'],'ordinary input parameters')
 check(child['fixed_program_parameters']==parent['fixed_program_parameters']==['program','radix_program'],'fixed2 parameters')
 check(child['witnesses']==sorted(set(ports(old))-set(parent['parameters'])) and len(child['witnesses'])==67,'all67 positive witnesses')
 check(child['valid_recipe']==parent['valid_recipe'],'same recipe')
 check(new[-20:]==old[-20:],'literal full20 finalizer')
 finalops=Counter(r[1] for r in new[-20:])
 check((finalops['*'],finalops['+']+finalops['-'])==(7,13),'finalizer7M13A')
 check(all(definitions(new)[r[0]]==r for r in old if r[0].startswith('native__')),'literal native72')
 identity=exact_identity(old,new)
 check(encode(old)==parent_before,'whole identity comparison preserves untouched parent')
 modular=[]
 for p in [1000000007,1000000009]:
  for sample in range(4):
   v={n:((j+3)*(sample+7)%29)-14 for j,n in enumerate(ports(old))}
   before,after=run(old,v,p),run(new,v,p)
   check(before['norm_output']==after['norm_output'],'fresh modular output')
   modular.append([p,sample,after['norm_output']])
 return {'schema':'review-residue-affine-sparse-shared476-v1','source_sha256':sha(Path(__file__).read_bytes()),
  'author_pins':AUTHOR,'parent_pins':PARENT,'authenticated_dependency_count':len(receipt['dependencies']),
  'untouched_parent_source_sha256':sha(parent_before),'parent_array_immutable':True,
  'author_receipt_helper_binding':True,'author_array_binding':True,
  'parent_ledger':a,'child_ledger':b,'witnesses':67,'literal_native_rows':72,'literal_finalizer_rows':20,
  'certificate_ledger':{'rows':456,'M':169,'A':287},'finalizer_ledger':{'rows':20,'M':7,'A':13},
  'deleted_rows':deleted,'new_rows':sorted(set(expected)-set(definitions(old))),
  'complete_source_array_sha256':sha(encode(new)),'exact_identity':identity,'fresh_modular_checks':modular,
  'scope':{'all476_rows_independently_reconstructed':True,'predecessor_execution':False,
           'degree_bound_inherited_by_identity':5160,'exact_degree_claim':False,
           'full_native_tuple_or_new_history_claim':False,'new_universality_proof_claim':False}}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();out=build(a.root,a.author_root or a.root)
 if a.output:
  with a.output.open('x') as f:f.write(json.dumps(out,sort_keys=True,indent=2)+'\n')
 else:check(encode(out)==encode(load(a.expect)),'exact review receipt')
 print('PASS independent476: all rows reconstructed; three exact cuts; whole output;67 witnesses/72 native/20 finalizer')
if __name__=='__main__':main()
