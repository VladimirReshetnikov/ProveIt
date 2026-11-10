#!/usr/bin/env python3
"""Independently render JSON nodes into the restricted pinned Lean source format."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-seed33-jones-json-lean-structural-check';j=root/'research/nine-seed33-jones-compact-macro-prototype/recipe.json';l=root/'research/nine-seed33-jones-compact-recipe-scoped-check/src/DiophantineConsistency/Sign33MacroRecipe.lean';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(j)=='06154f18e49d5ac3ca49add3a9b8bb03717f14590d2ef14f892d04b7dc3a75b3' and sha(l)=='6da2e67714b495c92c79dd89ac4a5c89bb0d613a00d626c53b6ac7b479190b32' and sha(p/'check.py')=='77b632028e61876caa2c955d274d1e3173e70fa509bd6602ad3afef43fb04ec8'
d=json.loads(j.read_text());assert d['inputs']==9 and d['output']=='output' and d['schema']=='named-ring-dag-with-finite-sum-macros-v1' and d['seed']=='SharingSeed33.seed CurrentWindowCarry2011.ports' and d['seed_type']=='Expr (Fin 34)' and d['coefficient_definitions']=={'z':'ExecutableJones.indexZ seed 0','y':'ExecutableJones.indexY seed 0','pcoef':'ExecutableJones.pCoefficient seed k','expo':'ExecutableJones.codingExpo 33 4 k','star':'ExecutableJones.codingStar 33 4'}
# Produce canonical Lean terms from the JSON tree; references must point backward and binders must match their local finite sum.
def render(x,names,binder=None):
 assert isinstance(x,list) and x and isinstance(x[0],str);op=x[0]
 if op in ('const','lit','var'):
  assert len(x)==2 and type(x[1]) is int and x[1]>=0
  if op=='var':assert x[1]<9;return f'(.input ⟨{x[1]}, by decide⟩)'
  return f'(.constant ({x[1]} : Int))' if op=='const' else f'(.lit {x[1]})'
 if op=='ref':assert len(x)==2 and x[1] in names;return f'(.ref ⟨{names[x[1]]}, by decide⟩)'
 if op=='fixed':assert len(x)==2 and x[1] in ('y','z');return f'(.fixed{x[1].upper()})'
 if op in ('pcoef','expo','index'):
  assert len(x)==2 and binder==(x[1],'range' if op=='index' else 'star');return f'(.{op})'
 if op in ('add','sub','mul','pow'):assert len(x)==3;return f'(.{op} {render(x[1],names,binder)} {render(x[2],names,binder)})'
 if op=='sum_range':assert len(x)==4 and binder is None and isinstance(x[1],str);return f'(.sumRange {render(x[2],names)} {render(x[3],names,(x[1],"range"))})'
 if op=='sum_star':assert len(x)==3 and binder is None and isinstance(x[1],str);return f'(.sumStar {render(x[2],names,(x[1],"star"))})'
 raise AssertionError(('unsupported JSON',op))
text=l.read_text();m=re.search(r'^def recipe : Dag 45 := by\n(.*?)\n\n/--',text,re.M|re.S);assert m;body=m[1].splitlines();assert len(body)==47 and body[0]=='  let d0 : Dag 0 := .nil' and body[-1]=='  exact d45' and len(d['nodes'])==45
names={}
for i,row in enumerate(d['nodes']):
 assert isinstance(row['name'],str) and row['name'] not in names
 expected=f"  let d{i+1} : Dag {i+1} := .snoc d{i} {render(row['expr'],names)}";assert body[i+1]==expected,(i,row['name']);names[row['name']]=i
assert names[d['output']]==44
# The checked recipe source is the exact source in the independently audited scoped recipe attempt.
c=root/'reviews/nine-seed33-jones-compact-recipe-scoped-terminal-frontier-independent/check.py';assert sha(c)=='d803a3f9c28d7882e8e7c01c82c3de7a9fca3a6bb492b4bee967e13b56f07ebf';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,text=True,timeout=120);assert x.returncode==0 and not x.stderr;v=json.loads(x.stdout);assert v['status']=='PASS_EXTERNAL_STRUCTURAL_COMPARISON' and v['nodes']==v['rejected_single_node_mutations']==45 and v['rejected_metadata_and_lean_mutations']==4
print(json.dumps({'status':'PASS_EXTERNAL_COMPARISON','nodes':45,'scope':'independent canonical rendering of pinned JSON AST against audited Lean recipe source; no Lean JSON parser/PDF theorem'},indent=2))
