"""Circuit utilities adapted from ProveIt package 30 optimize_nine_circuit.py.
Pinned source: 8c6eec9d19ef80538c8e61ff6e0180040583446a.
Original license retained in source/LICENSE.ProveIt. No upstream code executes.
"""
from collections import Counter
class Circuit:
 def __init__(self): self.nodes=[];self.index={};self.values={}
 def leaf(self,kind,**kw): return self.intern(dict(kind=kind,**kw))
 def intern(self,node):
  key=tuple(sorted(node.items()))
  if key not in self.index: self.index[key]=len(self.nodes);self.nodes.append(node)
  i=self.index[key]
  if node['kind']=='literal':self.values[i]=node['value']
  return i
 def const(self,n): return self.leaf('literal',value=n)
 def op(self,k,a,b):
  av=self.values.get(a);bv=self.values.get(b)
  if av is not None and bv is not None:return self.const({'add':lambda:av+bv,'sub':lambda:av-bv,'mul':lambda:av*bv}[k]())
  if k=='add' and av==0:return b
  if k=='add' and bv==0:return a
  if k=='sub' and bv==0:return a
  if k=='mul' and (av==0 or bv==0):return self.const(0)
  if k=='mul' and av==1:return b
  if k=='mul' and bv==1:return a
  if k in ('add','mul') and a>b:a,b=b,a
  return self.intern(dict(kind=k,left=a,right=b))
 def add(self,a,b):return self.op('add',a,b)
 def mul(self,a,b):return self.op('mul',a,b)
 def pack(self,root,names):
  alive=set();todo=[root]
  while todo:
   i=todo.pop()
   if i in alive:continue
   alive.add(i);n=self.nodes[i]
   if n['kind'] in ('add','sub','mul'):todo.extend([n['left'],n['right']])
  ids={j:i for i,j in enumerate(sorted(alive))};nodes=[]
  for j in sorted(alive):
   n=self.nodes[j].copy()
   if n['kind'] in ('add','sub','mul'):n['left']=ids[n['left']];n['right']=ids[n['right']]
   nodes.append(n)
  count=Counter(n['kind'] for n in nodes)
  return dict(nodes=nodes,output=ids[root],named_nodes={k:ids[v] for k,v in names.items() if v in ids},operation_counts={k:count[k] for k in ('add','sub','mul')},variables=[n['name'] for n in nodes if n['kind']=='variable'])

def evaluate(body,fixed,variables,p):
 out=[]
 for n in body['nodes']:
  k=n['kind']
  if k=='fixed':v=fixed[n['name']]
  elif k=='variable':v=variables[n['name']]
  elif k=='literal':v=n['value']
  elif k=='add':v=out[n['left']]+out[n['right']]
  elif k=='sub':v=out[n['left']]-out[n['right']]
  elif k=='mul':v=out[n['left']]*out[n['right']]
  else:raise ValueError(k)
  out.append(v%p)
 return out

def audit_body(body):
 nodes=body['nodes'];alive=set();todo=[body['output']]
 while todo:
  i=todo.pop()
  if i in alive:continue
  alive.add(i);n=nodes[i]
  if n['kind'] in ('add','sub','mul'):
   assert 0<=n['left']<i and 0<=n['right']<i
   todo.extend([n['left'],n['right']])
 assert len(alive)==len(nodes)
 counts=Counter(n['kind'] for n in nodes)
 return dict(node_count=len(nodes),live_operations=sum(counts[k] for k in ('add','sub','mul')),operations={k:counts[k] for k in ('add','sub','mul')},fixed_leaves=counts['fixed'],variable_leaves=counts['variable'])
