#!/usr/bin/env python3
"""Recognize exact additive loops in the frozen AST and prove commuting matrices."""
from pathlib import Path
import json,hashlib,itertools
from audit_negation_peephole import Machine,leaves
HERE=Path(__file__).resolve().parent
SRC=HERE/'fine_source_ast.json'
data=json.loads(SRC.read_text());ast=data['ast_dag']
def tree(i):
 r=ast[i];return r if r[0]=='L' else ['N',tree(r[1]),tree(r[2])]
vocab={'tokens':{c:{'ast':i,'leaves':list(leaves(tree(i)).values())} for c,i in data['token_ast'].items()}}
def identity():return [[int(i==j) for j in range(10)] for i in range(10)]
def multiply(a,b):return [[sum(a[i][k]*b[k][j] for k in range(10)) for j in range(10)] for i in range(10)]
def segment(m,start):
 p=start;seen=set();incs=[0]*9;path=[]
 while m.ops[p][0] not in ('dec','halt'):
  if p in seen:raise ValueError('unconditional loop')
  seen.add(p);path.append(p);op,*args=m.ops[p]
  if op=='inc':incs[args[0]]+=1
  p=m.next[p]
 return p,incs,path
summaries={}
for c,x in vocab['tokens'].items():
 m=Machine(tree(x['ast']));p,pre,prepath=segment(m,m.start)
 if m.ops[p][0]=='halt':
  a=identity()
  for i,k in enumerate(pre):a[i][9]+=k
  summaries[c]=dict(kind='increments',matrix=a,initial_path=prepath,increments=pre)
  continue
 if any(pre):continue
 guard=m.ops[p][1];q0,n0,path0=segment(m,m.next[p][0]);q1,n1,path1=segment(m,m.next[p][1])
 if m.ops[q0][0]!='halt' or any(n0) or q1!=p or n1[guard]:continue
 a=identity();a[guard][guard]=0
 for i,k in enumerate(n1):a[i][guard]+=k
 summaries[c]=dict(kind='finite_transfer_loop',guard_register=guard,positive_increments=n1,guard_pc=p,zero_path=path0,positive_path=path1,matrix=a)
# Exact homogeneous matrices over integers, no random/finite-field inference.
pairs=set();disjoint=set();overlap=[]
for c,d in itertools.combinations(sorted(vocab['tokens']),2):
 a,b=vocab['tokens'][c]['leaves'],vocab['tokens'][d]['leaves']
 sa={x[1] for x in a if x[0] in ('inc','dec')};sb={x[1] for x in b if x[0] in ('inc','dec')}
 if not sa&sb and not any(x[0]=='halt' for x in a+b):pairs.add((c,d));disjoint.add((c,d))
 if c in summaries and d in summaries and multiply(summaries[c]['matrix'],summaries[d]['matrix'])==multiply(summaries[d]['matrix'],summaries[c]['matrix']):
  pairs.add((c,d))
  if (c,d) not in disjoint:overlap.append((c,d))
result=dict(status='PASS_EXACT_INTEGER_AFFINE_IDENTITIES',source_sha256=hashlib.sha256(SRC.read_bytes()).hexdigest(),summaries=summaries,disjoint_pairs=len(disjoint),extra_overlapping_pairs=overlap,total_pairs=len(pairs),soundness='Each recognized loop has one decrement guard, a zero exit, and an increment-only back edge that does not increment its guard. Induction on initial guard gives the exact transfer matrix; matrix multiplication proves commutation for every natural register vector.')
(HERE/'affine_commutation.json').write_text(json.dumps(result,indent=2)+'\n')
(HERE/'affine_pairs.txt').write_text(str(len(pairs))+'\n'+''.join(f'{a} {b}\n' for a,b in sorted(pairs)))
print('Recognized affine tokens',len(summaries),''.join(summaries));print('Disjoint',len(disjoint),'Extra',len(overlap),'Total',len(pairs));print(overlap)
