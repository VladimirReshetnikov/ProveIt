"""New, independent data-only Jones9 circuit rewriter/auditor.
No received Python module is imported or executed. Input DAG and recipes are inert JSON.
The rewrite replaces the digit polynomial by sparse Horner evaluation and constructs
its complete-homogeneous baseline using shared radix-five powers.
"""
from pathlib import Path
from collections import Counter
from functools import lru_cache
import json, random, hashlib, sys
BASE=Path(__file__).resolve().parent
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
  if k=='add':
   for x,y in ((a,b),(b,a)):
    nd=self.nodes[x]
    if nd['kind']=='sub' and nd['right']==y:return nd['left']
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
def rewrite(old,constants,strategy='binary'):
 d=Circuit();oldnodes=old['nodes'];B_old=old['named_nodes']['B'];nu=constants['nu'];L=constants['L'];mapping={};special={};names={}
 def rawclone(i):
  if i in mapping:return mapping[i]
  n=oldnodes[i]
  if n['kind'] in ('add','sub','mul'):j=d.op(n['kind'],clone(n['left']),clone(n['right']))
  else:j=d.intern(n.copy())
  mapping[i]=j;return j
 def clone(i):
  if i in special:return special[i]
  return rawclone(i)
 B=rawclone(B_old);one=d.const(1);zero=d.const(0)
 p5=[B]
 for j in range(nu+5):
  v=p5[-1];v2=d.mul(v,v);v4=d.mul(v2,v2);p5.append(d.mul(v4,v))
 @lru_cache(None)
 def power(n):
  if n==0:return one
  if n==1:return B
  if n in five:return p5[five[n]]
  if strategy=='binary':
   x=power(n//2);y=d.mul(x,x)
   return d.mul(y,B) if n%2 else y
  digits=[];q=n;j=0
  if strategy=='runs':
   ds=[]
   while q:ds.append(q%5);q//=5
   while j<len(ds):
    a=ds[j]
    if not a:j+=1;continue
    end=j+1
    while end<len(ds) and ds[end]==a:end+=1
    digits.append(runpower(j,end,a));j=end
   v=one
   for a in digits:v=d.mul(v,a)
   return v
  while q:
   a=q%5;q//=5
   if a:
    u=p5[j];u2=d.mul(u,u)
    digits.append({1:lambda:u,2:lambda:u2,3:lambda:d.mul(u2,u),4:lambda:d.mul(u2,u2)}[a]())
   j+=1
  v=one
  for a in digits:v=d.mul(v,a)
  return v
 @lru_cache(None)
 def runpower(j,end,a):
  u=p5[j]
  if a==2:u=d.mul(u,u)
  elif a==3:u=d.mul(d.mul(u,u),u)
  elif a==4:u=d.mul(d.mul(u,u),d.mul(u,u))
  return u if end==j+1 else d.mul(u,runpower(j+1,end,a))
 five={5**j:j for j in range(len(p5))}
 # Shared suffix products: v_j=B^(5^nu-5^j), with v_nu=1.
 gap=[one]*(nu+1)
 for j in range(nu-1,-1,-1):
  p2=d.mul(p5[j],p5[j]);p4=d.mul(p2,p2);gap[j]=d.mul(gap[j+1],p4)
 weights=[p5[nu]]+gap
 hs=[one,zero,zero,zero,zero]
 for v in weights:
  for r in range(1,5):hs[r]=d.add(hs[r],d.mul(v,hs[r-1]))
 baseline=d.mul(p5[nu],hs[4]);z=rawclone(next(i for i,n in enumerate(oldnodes) if n.get('name')=='z_index'))
 sparse=sorted([(L-rec['expo'],rec['name']) for rec in constants['coefficient_records']],reverse=True)
 prev=sparse[0][0];acc=d.leaf('fixed',name=sparse[0][1])
 for exponent,name in sparse[1:]:
  acc=d.add(d.mul(acc,power(prev-exponent)),d.leaf('fixed',name=name));prev=exponent
 corr=d.mul(acc,power(prev));e=d.add(d.mul(z,baseline),corr)
 special[old['named_nodes']['e']]=e
 special[old['named_nodes']['q']]=p5[nu+1]
 ell=zero
 for j in range(1,nu+1):ell=d.add(ell,p5[j])
 special[old['named_nodes']['ell']]=ell
 # Retain original geometric-sum circuit and every downstream gate. Rewrite pure
 # power subtrees to share the same power table, without executing their source.
 pure={B_old:1}
 for i,node in enumerate(oldnodes):
  if i==B_old:continue
  if node['kind']=='literal' and node['value']==1:pure[i]=0
  elif node['kind']=='mul' and node['left'] in pure and node['right'] in pure:pure[i]=pure[node['left']]+pure[node['right']]
 # Power occurrences excluding the construction of B can now use new shared table.
 for i,exponent in pure.items():
  if i>B_old and i not in special:special[i]=power(exponent)
 root=clone(old['output'])
 for name,i in old['named_nodes'].items():names[name]=clone(i)
 result=d.pack(root,names)
 result.update(nu=nu,L=L,weights=old['weights'],model=old['model'],rewrite='Independent sparse Horner plus shared radix-five complete-homogeneous baseline',power_strategy=strategy)
 return result

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

def main():
 old=json.loads((BASE/'18-jones9/nine/generated/nine_majorant_dag.json').read_text());constants=json.loads((BASE/'18-jones9/nine/generated/constants.json').read_text());outdir=BASE/'nine_optimized';outdir.mkdir(exist_ok=True)
 results={};rng=random.Random(202610230049)
 for strategy in ('binary','radix5','runs'):
  new=rewrite(old,constants,strategy);check=audit_body(new);checks=0
  for p in (101,1009,65537,1000000007):
   for trial in range(16):
    fixed={n['name']:rng.randrange(p) for n in old['nodes'] if n['kind']=='fixed'};variables={x:rng.randrange(p) for x in old['variables']}
    a=evaluate(old,fixed,variables,p);b=evaluate(new,fixed,variables,p)
    for name in old['named_nodes']:
     assert a[old['named_nodes'][name]]==b[new['named_nodes'][name]],(strategy,p,trial,name)
     checks+=1
  check.update(named_node_residue_comparisons=checks,polynomial_identity_basis='Sparse Horner telescoping; gap_j=product_{k=j}^{nu-1} B^(4*5^k); complete-homogeneous recurrence unchanged; downstream gates unchanged.',source_sha256=hashlib.sha256((BASE/'18-jones9/nine/generated/nine_majorant_dag.json').read_bytes()).hexdigest())
  (outdir/f'nine_majorant_{strategy}.json').write_text(json.dumps(new,separators=(',',':'))+'\n');results[strategy]=check
 results['baseline']=audit_body(old)
 (outdir/'AUDIT.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
