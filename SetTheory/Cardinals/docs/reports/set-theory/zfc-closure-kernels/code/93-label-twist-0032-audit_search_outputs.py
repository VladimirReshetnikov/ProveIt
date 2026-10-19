#!/usr/bin/env python3
"""Independent finite grammar audits for the recorded discovery outputs.

This does not execute a Turing machine, establish initialization, or certify
all instruction contracts. Trace-domain audits use the stated independence
relation, whose register-program proof is supplied separately.
"""
from pathlib import Path
from functools import cache
import argparse,json
from fine_semantic_domain import Domain,trace_normal

def audit(package,path,domain,lock_path=None,affine_pairs_path=None):
 d=Domain(package);s=d.source;data=json.loads(Path(path).read_text())
 independence=d.disjoint_pairs
 if domain=='affine_trace':
  lines=Path(affine_pairs_path).read_text().splitlines();count=int(lines[0]);pairs={tuple(sorted(row.split()))for row in lines[1:]if row.strip()}
  assert len(pairs)==count==178 and d.disjoint_pairs<=pairs
  independence=pairs
 @cache
 def norm(w):return trace_normal(w,independence)if domain in('disjoint_trace','affine_trace')else w
 convert=lambda w:w if domain=='ordered'else d.expand(w)
 encode={name:c for c,name in d.symbols.items()}
 names={int(q):norm(convert(''.join(encode[c]for c in w)))for q,w in s['flattened_semantic_words'].items()}
 atom_ast={norm(convert(c)):s['atoms'][name]['ast']for c,name in d.symbols.items()};assert len(atom_ast)==44
 lines=(Path(package)/'inputs/semantic.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split())
 old={}
 for row in lines[1:n+1]:
  k,w,q=row.split();old[norm(convert(w))]=(norm(convert(w[:int(k)])),norm(convert(w[int(k):])))
 masks={}
 for row in lines[n+nr+1:]:
  if row.strip():c,m=row.split();masks[norm(convert(c))]=int(m)
 rules={norm(w):(norm(a),norm(b))for w,a,b in data['rules']}
 assert len(rules)==len(data['rules'])==data['rules_count']
 for w,a,b in data['rules']:
  assert norm(w)==norm(a+b),('invalid semantic concatenation',w,a,b)
 for w,(a,b)in rules.items():
  assert w not in atom_ast
  for bit,child in enumerate((a,b)):
   assert child in rules or child in atom_ast
   if child in atom_ast:assert masks[child]&(1<<bit)
 routes={(r['source'],r['read']):norm(r['word'])for r in data['routes']}
 assert len(routes)==len(data['routes'])==11
 def project(w,bits):
  for bit in bits:
   assert w in rules;w=rules[w][int(bit)]
  return w
 checked_routes=0
 for c in s['left_entry_projection_constraints']:
  reason=c['reason'];key=(reason['source'],reason['read']);bits=c['prefix']
  if 'via'in reason:assert reason['via']==177;bits=str(reason['previous'])+bits
  target=norm(convert(''.join(encode[t]for t in c['word'])))
  assert project(routes[key],bits)==target
  checked_routes+=1
 released={24,89,107,152,154,175,188,207,213,245}
 for q in s['required_entry_roots']:
  if q not in released:assert names[q]in rules
 for w in data['roots']:assert norm(w)in rules
 locks_checked=0
 if lock_path:
  lines=Path(lock_path).read_text().splitlines();count=int(lines[0])
  for row in lines[1:]:
   if row.strip():w,b,t=row.split();assert project(norm(convert(w)),b)==norm(convert(t));locks_checked+=1
  assert locks_checked==count
 byast={int(ast):names[int(q)]for q,ast in s['sequence_ast_roots'].items()};visiting=set()
 def join(a,b):return(1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2]),a[3]+b[3]+int(a[0]>=5))
 @cache
 def astprop(i):
  key=('A',i);assert key not in visiting;visiting.add(key)
  if i in byast:result=wordprop(byast[i])
  else:
   row=s['ast_dag'][i];result=(0,0,0,0)if row[0]=='L'else join(astprop(row[1]),astprop(row[2]))
  visiting.remove(key);return result
 @cache
 def wordprop(w):
  key=('W',w);assert key not in visiting;visiting.add(key)
  if w in atom_ast:result=astprop(atom_ast[w])
  else:
   a,b=rules[w]if w in rules else old[w];result=join(wordprop(a),wordprop(b))
  visiting.remove(key);return result
 props=astprop(s['original_ast'])
 if data.get('properties'):assert list(props[:3])==data['properties'][:3]
 return dict(status='PASS_FINITE_GRAMMAR_AUDIT',domain=domain,rules=len(rules),route_cases=checked_routes,bootstrap_projection_equations=locks_checked,leading_zero_depth=props[0],maximum_zero_run=props[1],maximum_leaf_depth=props[2],six_zero_chains=props[3],semantic_premise=('The independently proved 178-pair commutation relation.'if domain=='affine_trace'else 'Closed no-HALT blocks with disjoint register supports commute.'if domain=='disjoint_trace'else 'Exact ordered expansion into closed atoms.'),scope='Finite grammar, orientations, source-path statistics, route projections, and supplied bootstrap equations only. No new exact binary table, blank-start theorem, or complete runtime simulation is certified.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--package',type=Path,required=True);p.add_argument('--grammar',type=Path,required=True);p.add_argument('--domain',choices=['ordered','fine','disjoint_trace','affine_trace'],required=True);p.add_argument('--locks',type=Path);p.add_argument('--affine-pairs',type=Path);p.add_argument('--output',type=Path);a=p.parse_args();assert __debug__
 result=audit(a.package,a.grammar,a.domain,a.locks,a.affine_pairs);text=json.dumps(result,indent=2)+'\n'
 if a.output:a.output.write_text(text)
 print(text,end='')
