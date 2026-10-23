#!/usr/bin/env python3
"""Independent source-only parsing and physical-shape check of inert native AX literal."""
import collections,hashlib,json,re
from pathlib import Path
D=Path('/tmp/k215-phase21-actual-peer');p=Path('/tmp/k215-phase21-native-literal-fallback/candidate/L2Axioms254.lean')
dag=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Dag254.lean')
common=Path('/tmp/k215-phase21-repairs/AXWord-v2.lean');out=D/'literal-review-v1.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
pin=lambda p:{'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
assert not out.exists() and sha(p)=='25e48307ed165cd6a920a0e104101f9b1197c06d3f40ecf32eedc32b156ef477'
s=p.read_text();body=s.split('def axExpr : AXExpr :=',1)[1].split('theorem axExpr_checked',1)[0].strip()
tokens=re.findall(r'\.[A-Za-z][A-Za-z0-9]*|[()]',body);assert re.sub(r'\.[A-Za-z][A-Za-z0-9]*|[()]|\s+','',body)==''
i=0
def take():
 global i
 t=tokens[i];i+=1;return t
counts=collections.Counter()
def expr():
 t=take()
 if t=='(':
  a=expr();assert take()==')';return a
 assert t in ['.atom','.prefix','.seq','.gate'];kind=t[1:];counts[kind]+=1
 if kind=='atom':return (kind,take()[1:])
 if kind=='prefix':return (kind,take()[1:],expr())
 if kind=='seq':return (kind,expr(),expr())
 return (kind,)
tree=expr();assert i==len(tokens)
assert dict(counts)=={'seq':66,'prefix':114,'atom':66,'gate':1}
nodes={int(n):(int(a),int(b)) for n,a,b in re.findall(r'^\s*\|\s*(\d+)\s*=>\s*\(\(\.node\s+(\d+)\),\s*\(\.node\s+(\d+)\)\)',dag.read_text(),re.M)}
node_body=common.read_text().split('def AXAtom.node',1)[1].split('def AXAtom.effect',1)[0]
atoms={a:int(n) for a,n in re.findall(r'\|\s*\.([A-Za-z0-9]+)\s*=>\s*(\d+)',node_body)}
assert len(atoms)==14 and atoms['readwff']==158
checks=[];macro_effects=[]
def check(n,e):
 kind=e[0];checks.append((n,kind))
 if kind=='gate':assert n==71;return
 if kind=='atom':assert e[1]!='readwff' and n==atoms[e[1]];macro_effects.append(e[1]);return
 if kind=='prefix':
  a=e[1];car,nxt=nodes[n];assert car==atoms[a]
  if a=='readwff':car,nxt=nodes[nxt];assert car==208
  macro_effects.append(a);check(nxt,e[2]);return
 a,b=nodes[n];check(a,e[1]);check(b,e[2])
check(1,tree);assert len(checks)==247 and len(macro_effects)==180 and macro_effects.count('readwff')==1
# The object below is data, not a proof; Lean's axExpr_checked remains mandatory.
report={'status':'PASS_INDEPENDENT_SOURCE_ONLY_LITERAL_SHAPE','reader':pin(__file__),'candidate':pin(p),'DAG_source':pin(dag),'shared_checker_source':pin(common),'constructor_counts':dict(counts),'expression_constructors':len(checks),'semantic_macros_before_final_gate':len(macro_effects),'final_gate_count':1,'root_node':1,'gate_node':71,'two_node_literal_read_count':1,'AST_sha256':hashlib.sha256(json.dumps(tree,separators=(',',':')).encode()).hexdigest(),'all_tokens_consumed':True,'physical_node_shape_checked':True,'owned_parser_independent_of_author_generator':True,'compiler_invocations':0,'canonical_edits':0,'scope':'Independent parser accepts only the four AXExpr constructors and known AXAtom names; each branch follows the pinned native literal DAG at root 1, including the 158/208 fused read and gate 71. This source-only check does not replace Lean axExpr_checked, the generic run proof, ax_eval, final warning checks, or supervisor limits.'}
with out.open('x') as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps({'status':report['status'],'report':pin(out)},indent=2))
