#!/usr/bin/env python3
"""Independent word, projection, orientation, reachability and AST-property audit.

This is an abstract grammar audit, not a binary TM correctness certificate.
"""
import argparse,json
from pathlib import Path
from functools import lru_cache
P=argparse.ArgumentParser();P.add_argument('grammar',type=Path);P.add_argument('--inputs',type=Path,required=True);P.add_argument('--bootstrap-lock',type=Path);P.add_argument('--output',type=Path);a=P.parse_args()
s=json.loads((a.inputs/'closed-sequence-grammar-next22.json').read_text());symbols=json.loads((a.inputs/'semantic-symbols.json').read_text());enc={v:k for k,v in symbols.items()}
lines=(a.inputs/'semantic.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split());names={int(q):w for k,w,q in map(str.split,lines[1:n+1])};old={w:(w[:int(k)],w[int(k):]) for k,w,q in map(str.split,lines[1:n+1])};allowed={c:int(m) for c,m in map(str.split,lines[n+1+nr:])}
d=json.loads(a.grammar.read_text());g={w:(left,right) for w,left,right in d['rules']};assert len(g)==len(d['rules'])==d['rules_count']
for w,(l,r) in g.items():
 assert w==l+r and l and r
 for i,child in enumerate((l,r)):
  assert child in g or child in symbols
  if len(child)==1:assert allowed[child]&(1<<i)
routes={(r['source'],r['read']):r['word'] for r in d['routes']}
def project(w,prefix):
 for bit in prefix:w=g[w][int(bit)]
 return w
constraints=0
for c in s['left_entry_projection_constraints']:
 r=c['reason'];pre=c['prefix']
 if r.get('via')==177:pre=str(r['previous'])+pre
 assert project(routes[r['source'],r['read']],pre)==''.join(enc[t] for t in c['word'])
 constraints+=1
released={24,89,107,152,154,175,188,207,213,245}
mandatory={names[q] for q in s['required_entry_roots'] if q not in released};assert mandatory<=g.keys()
lockcount=0
if a.bootstrap_lock:
 ls=a.bootstrap_lock.read_text().splitlines();lockcount=int(ls[0]);assert len(ls)==lockcount+1
 for row in ls[1:]:
  w,b,t=row.split();assert project(w,b)==t;mandatory.add(w)
seen=set()
def visit(w):
 if len(w)==1 or w in seen:return
 seen.add(w)
 for child in g[w]:visit(child)
for w in mandatory|set(routes.values()):visit(w)
assert seen==g.keys(),set(g)-seen
ast_to_word={int(v):names[int(q)] for q,v in s['sequence_ast_roots'].items()}
def join(l,r):return (l[0]+1,max(l[0]+1,l[1],r[1]),max(l[2],r[2])+1)
@lru_cache(None)
def wp(w):
 if len(w)==1:return ep(s['atoms'][symbols[w]]['ast'])
 return join(*(wp(x) for x in g.get(w,old.get(w))))
@lru_cache(None)
def ep(i):
 if i in ast_to_word:return wp(ast_to_word[i])
 row=s['ast_dag'][i]
 if row[0]=='L':return(0,0,0)
 return join(ep(row[1]),ep(row[2]))
props=ep(s['original_ast']);assert props[1]<=7 and props[2]<=64
out=dict(status='PASS_ABSTRACT_ONLY',grammar_file=str(a.grammar),rules_count=len(g),framework_states=118,working_states_if_realized=118+len(g),folded_projection_checks=constraints,bootstrap_lock_checks=lockcount,source_properties=dict(lead=props[0],maximum_zero_run=props[1],maximum_leaf_depth=props[2]),all_rules_reachable=True,scope='Exact finite word and AST checks. This does not prove literal TM realization, bootstrap unless separately certified, or ZFC consistency equivalence.')
print(json.dumps(out,indent=2))
if a.output:a.output.write_text(json.dumps(out,indent=2)+'\n')
