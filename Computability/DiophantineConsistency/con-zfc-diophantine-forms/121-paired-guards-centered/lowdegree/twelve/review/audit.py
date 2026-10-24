#!/usr/bin/env python3
"""Exact independent DAG-tail identity and prefix-equivalence audit. No builder import."""
import copy,hashlib,json
from collections import Counter
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent
D=HERE.parent
PARENT=D.parents[1]/'prior/ZFC_Diophantine_Coprime_Projection/lowdegree/twelve'
new=json.loads((D/'equation.json').read_text())
old=json.loads((PARENT/'equation.json').read_text())
CUTS=['sroot','uroot','vroot','wroot','eroot']
SYMS=s.symbols('z a b c d')

def require(ok,msg):
 if not ok: raise ValueError(msg)

def validate(g):
 nodes=g['nodes'];seen=set()
 def visit(i):
  if i in seen:return
  require(isinstance(i,int) and 0<=i<len(nodes),'bad index')
  seen.add(i); n=nodes[i]
  require(n[0] in ['integer','variable','coefficient','add','sub','mul'],'opcode')
  if n[0] in ['add','sub','mul']:
   require(len(n)==3 and all(0<=j<i for j in n[1:]),'acyclic')
   visit(n[1]);visit(n[2])
 visit(g['output']); require(len(seen)==len(nodes),'dead node')
 require({n[1] for n in nodes if n[0]=='variable'}==set(g['variables']),'liveness')
 counts=Counter(n[0] for n in nodes if n[0] in ['add','sub','mul'])
 require(dict(counts)==g['operation_counts'] and sum(counts.values())==g['operations'],'counts')
 return counts

def fingerprints(g):
 out=[]; trees=[]
 for n in g['nodes'][:1+max(g['named_registers'][c] for c in CUTS)]:
  if n[0] in ['add','sub','mul']:
   args=[]
   for ix in n[1:]:
    child=trees[ix]
    if n[0] in ['add','mul'] and child[0]==n[0]:args.extend(child[1:])
    else:args.append(child)
   if n[0] in ['add','mul']:args.sort(key=repr)
   payload=(n[0],*args)
  else:payload=tuple(n)
  trees.append(payload)
  out.append(hashlib.sha256(repr(payload).encode()).hexdigest())
 return out

def tail(g):
 nodes=g['nodes'];cuts={g['named_registers'][n]:v for n,v in zip(CUTS,SYMS)};memo={}
 def ev(i):
  if i in cuts:return cuts[i]
  if i in memo:return memo[i]
  n=nodes[i]
  if n[0]=='integer':ans=s.Integer(n[1])
  elif n[0] in ['variable','coefficient']:raise ValueError('tail escaped its verified prefix')
  else:
   a,b=ev(n[1]),ev(n[2]);ans=a+b if n[0]=='add' else a-b if n[0]=='sub' else a*b
  memo[i]=ans;return ans
 return s.Poly(s.expand(ev(g['output'])),*SYMS)

counts=validate(new);validate(old)
require(new['variables']==old['variables'],'variable mismatch')
require(new['fixed_numerals']==old['fixed_numerals'],'fixed numeral mismatch')
fn,fo=fingerprints(new),fingerprints(old)
for cut in CUTS:
 require(fn[new['named_registers'][cut]]==fo[old['named_registers'][cut]],'prefix changed at '+cut)
nt,ot=tail(new),tail(old)
require(nt==ot,'complete norm tails differ')
require(counts=={'mul':84,'add':32,'sub':23},'claimed count')
require(new['exact_degree']==old['exact_degree']==500,'exact-degree transfer')
# Deliberately corrupt every live norm-tail operation; all must be rejected.
# Prefix mutations are caught through exact canonical fingerprints.
mutated=[]
for i,n in enumerate(new['nodes']):
 if n[0] not in ['add','sub','mul']:continue
 g=copy.deepcopy(new);g['nodes'][i][0]='sub' if n[0]=='add' else 'add'
 ff=fingerprints(g)
 prefix_changed=any(ff[g['named_registers'][c]]!=fo[old['named_registers'][c]] for c in CUTS)
 if prefix_changed:mutated.append(i);continue
 require(tail(g)!=ot,'undetected arithmetic mutation '+str(i));mutated.append(i)
result={'status':'pass','scope':'Exact universal tail identity and live prefixes identical modulo associative/commutative add/mul, not a new semantic compiler theorem.',
 'new_sha256':hashlib.sha256((D/'equation.json').read_bytes()).hexdigest(),
 'parent_sha256':hashlib.sha256((PARENT/'equation.json').read_bytes()).hexdigest(),
 'variables':len(new['variables']),'exact_degree_by_pointwise_equality':500,
 'operations':sum(counts.values()),'operation_counts':dict(counts),'universal_tail_monomials':len(nt.terms()),
 'identical_prefix_cuts':CUTS,'rejected_live_opcode_mutations':len(mutated),
 'parent_degree_coefficient':'[j^228 w^76 v^84 h^8 z^8 r^32 c^64] = 2^488 * 3^332 * beta^228 > 0'}
(HERE/'CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
