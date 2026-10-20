#!/usr/bin/env python3
"""Independent instruction-ordinal bisimulation for reassociated binary sources.

Standard library only, no optimizer imports. The arithmetic-PC and tree-interval
resolvers use separate computations and must agree on every guarded successor.
The candidate is not accepted by hash: semantic and structural checks decide.
"""
from pathlib import Path
import argparse,hashlib,json,copy
BASE_SHA='cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def validate(rows):
 need(isinstance(rows,list)and rows,'nonempty source list');leaves={};prefixes=set()
 for row in rows:
  need(isinstance(row,list)and len(row)==3,'source row shape');p,op,a=row
  need(type(p)is str and p and set(p)<=set('01') and p not in leaves,'invalid/duplicate path')
  need(op in ('CI','CD','CB','CC','CH'),'unknown opcode')
  if op in ('CI','CD'):need(type(a)is int and 0<=a<9,'register operand')
  elif op in ('CB','CC'):need(type(a)is int and a>=1,'control operand')
  else:need(a is None,'halt operand')
  leaves[p]=(op,a);prefixes.update(p[:i] for i in range(len(p)))
 need(rows==sorted(rows),'source leaf ordering')
 need(not(set(leaves)&prefixes),'prefix code overlaps');nodes=prefixes|set(leaves)
 need(all(p+'0'in nodes and p+'1'in nodes for p in prefixes),'incomplete binary tree')
 def tree(p):return leaves[p] if p in leaves else (tree(p+'0'),tree(p+'1'))
 return leaves,prefixes,tree('')
def arithmetic(rows):
 leaves,prefixes,_=validate(rows);index={p:i for i,(p,_,_)in enumerate(rows)};depth=max(map(len,leaves))
 def resolve(bits):
  p='';i=0
  while p not in leaves:
   need(i<=depth,'unresolved PC');p+=bits[i]if i<len(bits)else'0';i+=1
  need('1'not in bits[i:],'nonzero unread PC suffix');return index[p]
 def inc(bits):return format((int(bits,2)+1)%(1<<len(bits)),f'0{len(bits)}b')if bits else''
 def strip(bits,b,n):
  for k in range(len(bits)-1,-1,-1):
   if bits[k]==b:
    n-=1
    if not n:return bits[:k]
  return ''
 graph=[]
 for p,op,a in rows:
  if op=='CH':succ=[]
  elif op=='CI':succ=[resolve(inc(p))]
  elif op=='CD':succ=[resolve(inc(p)),resolve(inc(strip(p,'0',1)))]
  elif op=='CB':succ=[resolve(inc(strip(p,'0',a)))]
  else:succ=[resolve(strip(p,'1',a))]
  graph.append([op,a,succ])
 return graph,resolve('')
def intervals(rows):
 # Build nested records directly, independently of the binary integer resolver.
 root={};n=len(rows)
 for i,(p,op,a)in enumerate(rows):
  at=root
  for bit in p:at=at.setdefault(bit,{})
  at['leaf']=i
 ranges={}
 def visit(at,path):
  if 'leaf'in at:lo=hi=at['leaf']
  else:
   a,b=visit(at['0'],path+'0'),visit(at['1'],path+'1');need(a[1]+1==b[0],'disordered subtree ranges');lo,hi=a[0],b[1]
  ranges[path]=(lo,hi);return lo,hi
 visit(root,'')
 def ancestor(p,bit,k):
  count=0
  for j in reversed(range(len(p))):
   count+=p[j]==bit
   if count==k:return p[:j]
  return ''
 graph=[]
 for i,(p,op,a)in enumerate(rows):
  if op=='CI':succ=[(i+1)%n]
  elif op=='CD':succ=[(i+1)%n,(ranges[ancestor(p,'0',1)][1]+1)%n]
  elif op=='CB':succ=[(ranges[ancestor(p,'0',a)][1]+1)%n]
  elif op=='CC':succ=[ranges[ancestor(p,'1',a)][0]]
  else:need(op=='CH','interval opcode');succ=[]
  graph.append([op,a,succ])
 return graph,ranges[''][0]
def stats(rows,tree):
 seen=set()
 def visit(t):
  if t in seen:return
  seen.add(t)
  if not isinstance(t[0],str):visit(t[0]);visit(t[1])
 visit(tree);primitives={t for t in seen if isinstance(t[0],str)}
 return dict(primitive_occurrences=len(rows),distinct_subtrees=len(seen),distinct_primitive_leaves=len(primitives),internal_subtrees=len(seen)-len(primitives),maximum_depth=max(len(p)for p,_,_ in rows),maximum_zero_run=max(len(z)for p,_,_ in rows for z in p.split('1')))
def compare(before,after):
 _,_,bt=validate(before);_,_,at=validate(after)
 need([(op,a)for p,op,a in before]==[(op,a)for p,op,a in after],'primitive sequence differs')
 ba,be=arithmetic(before);bi,bie=intervals(before);aa,ae=arithmetic(after);ai,aie=intervals(after)
 need(ba==bi and be==bie,'baseline independent resolvers disagree')
 need(aa==ai and ae==aie,'candidate independent resolvers disagree')
 need(ba==aa and be==ae==0,'instruction-ordinal transition system differs')
 need([i for i,(p,o,a)in enumerate(before)if o=='CH']==[i for i,(p,o,a)in enumerate(after)if o=='CH'],'halting ordinals differ')
 count=sum(2 if op=='CD'else 1 for _,op,_ in before)
 return dict(status='INDEPENDENT_EXACT_SOURCE_BISIMULATION_PASS',before_metrics=stats(before,bt),after_metrics=stats(after,at),guarded_cases=count,entry_ordinal=be,halt_ordinals=[i for i,(p,o,a)in enumerate(after)if o=='CH'],graph_sha256=sha(json.dumps(aa,separators=(',',':')).encode()),relation='Equal instruction ordinals and equal nine natural register values; each guarded source step has exactly the same register update and successor ordinal.',scope='All source executions, not merely reachable or bounded-register executions. The logical calculus is unchanged because the exact primitive stream and complete guarded CFG are unchanged. Binary runtime and blank startup are separate obligations.')
def render(tree,p=''):
 if isinstance(tree[0],str):return [[p,*tree]]
 return render(tree[0],p+'0')+render(tree[1],p+'1')
def regroup(tree):
 # Deliberately rotate each occurrence, including nonclosed ones; seek one that
 # preserves the instruction sequence but changes a control target.
 if isinstance(tree[0],str):return
 if not isinstance(tree[0][0],str):
  a,b=tree[0];yield a,(b,tree[1])
 if not isinstance(tree[1][0],str):
  b,c=tree[1];yield (tree[0],b),c
 for u in regroup(tree[0]):yield u,tree[1]
 for v in regroup(tree[1]):yield tree[0],v
def controls(before,after):
 results=[]
 def reject(name,bad):
  try:compare(before,bad)
  except (ValueError,KeyError,IndexError,TypeError)as e:results.append(dict(name=name,status='REJECTED',reason=str(e)));return True
  raise ValueError('Negative control accepted: '+name)
 bad=copy.deepcopy(after);i=next(i for i,r in enumerate(bad)if r[1]=='CI');bad[i][2]=(bad[i][2]+1)%9;reject('changed_register_instruction',bad)
 bad=copy.deepcopy(after);i=next(i for i,r in enumerate(bad)if r[1]in ('CB','CC'));bad[i][2]+=1;reject('changed_control_depth',bad)
 _,_,t=validate(after)
 for rt in regroup(t):
  bad=render(rt)
  try:compare(before,bad)
  except ValueError as e:
   results.append(dict(name='nonclosed_reassociation_preserving_primitive_stream',status='REJECTED',reason=str(e)));break
 else:raise ValueError('No nonclosed grouping negative control found')
 return results
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--baseline',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 raw=a.baseline.read_bytes();need(sha(raw)==BASE_SHA,'baseline identity differs');cr=a.candidate.read_bytes();before=json.loads(raw);after=json.loads(cr);r=compare(before,after);r.update(baseline_sha256=sha(raw),candidate_sha256=sha(cr),negative_controls=controls(before,after),checker_sha256=sha(Path(__file__).read_bytes()))
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
