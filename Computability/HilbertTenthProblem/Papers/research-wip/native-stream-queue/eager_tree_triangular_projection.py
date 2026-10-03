"""Strictly forward pointers replace all ranks in the finite eager Tree certificate.

All supplied coordinates are natural (including zero); external N is retained.
"""
import argparse,copy,hashlib,json,random,types
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PARENT_FILE='eager_tree_occurrence_flow.py'
PARENT_SHA='0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c'
RECEIPT_SHA='10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d'
NOTE_SHA='ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9'

def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def parent(root=None):
 root=Path(__file__).resolve().parent if root is None else Path(root)
 path=root/PARENT_FILE;data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==PARENT_SHA,'Parent source pin')
 m=types.ModuleType('_eager_tree_flow_for_projection');m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m

def constants(N):return {f'r{i}_p{s}_{j}':0 for i in range(N)for s in range(3)for j in range(i+1)}
def fold(op,a,b):
 if type(a)is int and type(b)is int:return a+b if op=='+'else a-b if op=='-'else a*b
 if op=='*'and(a==0 or b==0):return 0
 if op=='*'and a==1:return b
 if op=='*'and b==1:return a
 if op=='+'and a==0:return b
 if op in('+','-')and b==0:return a
 return None

def _rewrite(p,m,cleanup):
 need(type(cleanup)is bool,'Exact cleanup Boolean')
 N=p['N'];fixed=constants(N);aliases=dict(fixed);changed=set(fixed);rows=[];local=[]
 deleted={23*i+22 for i in range(N)};kept=[r for i,r in enumerate(p['residuals'])if i not in deleted]
 deps={n:(a,b)for n,op,a,b in p['source']};live=set();todo=list(kept)
 while todo:
  n=todo.pop()
  if n in deps and n not in live:live.add(n);todo.extend(deps[n])
 for n,op,a,b in p['source']:
  if n not in live:continue
  aa=aliases.get(a,a);bb=aliases.get(b,b);affected=a in changed or b in changed
  out=fold(op,aa,bb)if cleanup or affected else None
  if out is not None:
   aliases[n]=out;changed.add(n);local.append([n,op,aa,bb,out])
  else:
   rows.append([n,op,aa,bb])
   if affected:changed.add(n)
 residuals=[aliases.get(r,r)for r in kept]
 live={x for x in residuals if type(x)is str}
 for n,op,a,b in reversed(rows):
  if n in live:live.update(x for x in(a,b)if type(x)is str)
 rows=[r for r in rows if r[0]in live]
 free=[x for x in p['free']if x not in fixed and not x.endswith('_mu')]
 poly,output=m.finalizer(rows,residuals)
 cert=m.inspect(rows,free,residuals);ledger=m.inspect(poly,free,[output]);witnesses=len(free)-3
 expectedM=(9*N*N+101*N+6)//2;expectedA=6*N*N+(61-int(cleanup))*N+17
 need(ledger['M']==expectedM and ledger['A']==expectedA,'Complete paid formula')
 need(witnesses==(3*N*N+33*N)//2 and len(residuals)==22*N+3,'Projected interface counts')
 return dict(N=N,cleanup=cleanup,free=free,source=rows,residuals=residuals,polynomial_source=poly,output=output,certificate_ledger=cert,polynomial_ledger=ledger,witnesses=witnesses,residual_count=len(residuals),exact_degree=4,fixed_parent_pointers=fixed,parent_sha256=PARENT_SHA,removed_parent_residual_indices=sorted(deleted),local_constant_identities=local,scope='Strictly forward natural pointers. Same represented triples at each external N; unique restored flow or height on the triangular parent slice. No all-parent-zero bijection or fixed-arity universality claim.')

def build(N,*,cleanup=False,root=None,repo):
 need(type(N)is int and N>=1,'Exact positive N');m=parent(root);return _rewrite(m.build(N,repo=repo),m,cleanup)
def checked(p,*,root=None,repo):
 need(type(p)is dict,'Packet');q=build(p.get('N'),cleanup=p.get('cleanup'),root=root,repo=repo);need(exact(p,q),'Complete canonical packet');return q

def values_for(p,values,signed):
 need(type(signed)is bool and type(values)is dict and set(values)==set(p['free']),'Complete assignment/mode')
 need(all(type(k)is str and type(v)is int for k,v in values.items()),'Exact integer fields')
 if not signed:need(all(v>=0 for v in values.values()),'Natural coordinates')
 return dict(values)
def run(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  x=d[a]if type(a)is str else a;y=d[b]if type(b)is str else b;d[n]=x+y if op=='+'else x-y if op=='-'else x*y
 return d

def evaluate(p,values,*,signed=False,root=None,repo):
 p=checked(p,root=root,repo=repo);v=values_for(p,values,signed);return run(p['polynomial_source'],v)[p['output']]
def restore_flow(p,values,*,signed=False,root=None,repo):
 p=checked(p,root=root,repo=repo);v=dict(values_for(p,values,signed),**p['fixed_parent_pointers']);N=p['N']
 for i in range(N):v[f'r{i}_mu']=int(i==0)+sum(v[f'r{j}_mu']*v[f'r{j}_p{s}_{i}']for j in range(i)for s in range(3))
 return v

def restore_height(p,values,*,signed=False,root=None,repo):
 p=checked(p,root=root,repo=repo);v=dict(values_for(p,values,signed),**p['fixed_parent_pointers']);N=p['N']
 for i in reversed(range(N)):v[f'r{i}_h']=1+sum(v[f'r{i}_p{s}_{j}']*v[f'r{j}_h']for j in range(i+1,N)for s in range(3))
 return v

def project_triangular_zero(p,values,*,root=None,repo):
 p=checked(p,root=root,repo=repo);m=parent(root);old=m.build(p['N'],repo=repo);v=values_for(old,values,False)
 need(all(v[k]==0 for k in p['fixed_parent_pointers']),'Triangular parent slice')
 need(run(old['polynomial_source'],v)[old['output']]==0,'Parent zero required')
 out={k:v[k]for k in p['free']};need(restore_flow(p,out,root=root,repo=repo)==v,'Unique triangular flow');return out

def normalize_parent_zero(p,values,*,root=None,repo):
 p=checked(p,root=root,repo=repo);m=parent(root);old=m.build(p['N'],repo=repo);v=values_for(old,values,False);N=p['N']
 need(run(old['polynomial_source'],v)[old['output']]==0,'Parent zero required')
 A=[[sum(v[f'r{i}_p{s}_{j}']for s in range(3))for j in range(N)]for i in range(N)]
 reach={0}
 while True:
  nxt=reach|{j for i in reach for j in range(N)if A[i][j]}
  if nxt==reach:break
  reach=nxt
 indeg={j:sum(bool(A[i][j])for i in reach)for j in reach};order=[]
 while len(order)<len(reach):
  choices=[i for i in reach if i not in order and indeg[i]==0];need(bool(choices),'Reachable cycle contradicts natural flow')
  i=min(choices);order.append(i)
  for j in reach:indeg[j]-=bool(A[i][j])
 need(order[0]==0,'Root first topological order')
 order += [i for i in range(N)if i not in reach]
 dummy=dict(x=0,y=0,z=1,a=0,b=0,c=0,u=0,v=0,d=2,e=2,q=2,j=4,k=8)
 for i in range(N):
  if i not in reach:
   v.update({f'r{i}_{k}':x for k,x in dummy.items()});v.update({f'r{i}_t{j}':int(j==0)for j in range(5)});v.update({f'r{i}_p{s}_{j}':0 for s in range(3)for j in range(N)})
 scalars=list(dummy)+['t'+str(j)for j in range(5)];permuted={k:v[k]for k in('program','argument','output')}
 for i,oldi in enumerate(order):
  permuted.update({f'r{i}_{field}':v[f'r{oldi}_{field}']for field in scalars})
  for j,oldj in enumerate(order):
   permuted.update({f'r{i}_p{s}_{j}':v[f'r{oldi}_p{s}_{oldj}']for s in range(3)})
 need(all(permuted[k]==0 for k in constants(N)),'Strict forward pointers after permutation')
 out={k:permuted[k]for k in p['free']};need(run(p['polynomial_source'],out)[p['output']]==0,'Constructed child zero');return out

def restore_polynomials(p,m,kind):
 env={x:m.atom(x)for x in p['free']};env.update({x:{}for x in p['fixed_parent_pointers']});N=p['N']
 for i in range(N)if kind=='flow'else reversed(range(N)):
  name=f'r{i}_mu'if kind=='flow'else f'r{i}_h';value=m.atom(int(i==0)if kind=='flow'else 1)
  for j in range(i)if kind=='flow'else range(i+1,N):
   for slot in range(3):
    pointer=f'r{j}_p{slot}_{i}'if kind=='flow'else f'r{i}_p{slot}_{j}';field=f'r{j}_mu'if kind=='flow'else f'r{j}_h'
    value=m.plus(value,m.times(env[pointer],env[field]))
  env[name]=value
 return env

def polynomial(rows,env,m):
 env=dict(env)
 for n,op,a,b in rows:
  aa=env[a]if type(a)is str else m.atom(a);bb=env[b]if type(b)is str else m.atom(b)
  env[n]=m.times(aa,bb)if op=='*'else m.plus(aa,bb,-1 if op=='-'else 1)
 return env

def verify(root,repo):
 root=Path(root);m=parent(root)
 for name,h in(('eager_tree_occurrence_flow.json',RECEIPT_SHA),('eager_tree_occurrence_flow.md',NOTE_SHA)):
  need(hashlib.sha256((root/name).read_bytes()).hexdigest()==h,'Parent companion pin')
 saved=json.loads((root/'eager_tree_occurrence_flow.json').read_text());rng=random.Random(2032);forms=[];counts=dict(full_graph_identities=0,retained_residual_identities=0,restored_zero_rows=0,signed_numeric_identities=0,genuine_zero_projections=0,cycle_normalizations=0,necessary_permutation_cases=0,guards=0,copies=0)
 for N in range(1,9):
  parents={'flow':m.build(N,repo=repo),'height':m.canonical_parent(N,repo=repo)}
  for cleanup in(False,True):
   p=build(N,cleanup=cleanup,root=root,repo=repo);newpoly=polynomial(p['polynomial_source'],{x:m.atom(x)for x in p['free']},m)
   for kind,old in parents.items():
    restored=restore_polynomials(p,m,kind);oldpoly=polynomial(old['polynomial_source'],restored,m)
    need(oldpoly[old['output']]==newpoly[p['output']],'Complete polynomial graph identity to '+kind)
    index=0
    for j,r in enumerate(old['residuals']):
     if j<23*N and j%23==22:need(oldpoly[r]=={},'Restored rank/flow row zero');counts['restored_zero_rows']+=1
     else:need(oldpoly[r]==newpoly[p['residuals'][index]],'Literal retained residual identity');index+=1;counts['retained_residual_identities']+=1
    counts['full_graph_identities']+=1
   need(max(map(len,newpoly[p['output']]),default=0)==4,'Exact quartic')
   for case in range(4):
    v={x:rng.randint(-2,3)for x in p['free']};value=run(p['polynomial_source'],v)[p['output']]
    for kind,old in parents.items():
     restored=(restore_flow if kind=='flow'else restore_height)(p,v,signed=True,root=root,repo=repo);need(value==run(old['polynomial_source'],restored)[old['output']],'Signed complete graph identity');counts['signed_numeric_identities']+=1
   forms.append(dict(packet=p,parent_ledger=parents['flow']['polynomial_ledger'],height_parent_ledger=parents['height']['polynomial_ledger'],saved_from_flow={k:parents['flow']['polynomial_ledger'][k]-p['polynomial_ledger'][k]for k in('M','A','operations')}))
 kernel=m.parent(repo)
 for x,y in [(x,y)for x in range(8)for y in range(3)]+[(154,1)]:
  ev=kernel.Evaluation(budget=100,max_bits=256)
  try:z=ev.app(x,y)
  except(kernel.Exhausted,kernel.RepeatedActiveCall,RecursionError):continue
  for pad in(0,1):
   rows=kernel.certificate(ev,(x,y),pad=pad);N=len(rows);p=build(N,root=root,repo=repo);v=m.flatten(rows,x,y,z,m.root_flow(rows));child=normalize_parent_zero(p,v,root=root,repo=repo);back=restore_flow(p,child,root=root,repo=repo)
   need(project_triangular_zero(p,back,root=root,repo=repo)==child,'Exact triangular inverse');need(evaluate(p,child,root=root,repo=repo)==0,'Genuine projected zero');counts['genuine_zero_projections']+=1
   if x==154:
    need(sum(v[k]for k in p['fixed_parent_pointers'])>0,'Fixture needs topological reordering')
    naive={k:v[k]for k in p['free']};need(run(p['polynomial_source'],naive)[p['output']]>0,'Deleting backward pointers without permutation fails');counts['necessary_permutation_cases']+=1
 for fixture in saved['unreachable_cycle_examples']:
  p=build(fixture['row_count'],root=root,repo=repo);v=normalize_parent_zero(p,fixture['values'],root=root,repo=repo);need(evaluate(p,v,root=root,repo=repo)==0,'Disconnected cycle normalized');counts['cycle_normalizations']+=1
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('Malformed accepted')
 for N in(True,False,0,-1,1.0,'1',None):reject(lambda N=N:build(N,root=root,repo=repo))
 p=build(2,root=root,repo=repo)
 for bad in(0,1,None,'false'):reject(lambda bad=bad:build(2,cleanup=bad,root=root,repo=repo))
 for key in p:
  bad=copy.deepcopy(p);bad.pop(key);reject(lambda bad=bad:checked(bad,root=root,repo=repo))
 for key in('source','polynomial_source','free','residuals'):
  bad=build(2,root=root,repo=repo);bad[key].clear();need(exact(build(2,root=root,repo=repo),p),'Independent packet copies');counts['copies']+=1
 v={x:0 for x in p['free']}
 for bad in(True,0.0,-1):
  w=dict(v);w[p['free'][0]]=bad;reject(lambda w=w:evaluate(p,w,root=root,repo=repo))
 reject(lambda:evaluate(p,v,signed=1,root=root,repo=repo))
 reject(lambda:normalize_parent_zero(p,{x:0 for x in m.build(2,repo=repo)['free']},root=root,repo=repo))
 return dict(status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_sha256=PARENT_SHA,parent_receipt_sha256=RECEIPT_SHA,parent_note_sha256=NOTE_SHA,counts=counts,forms=forms,scope='Complete finite strict-forward pointer family. Full polynomial graph identities to uniquely restored triangular flow/height slices; same represented natural triples at external N via dummying/permutation. No all-parent-zero bijection or fixed-arity bound.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True);ap.add_argument('--repo',required=True);ap.add_argument('--output',required=True);ap.add_argument('--expect');a=ap.parse_args();out=verify(a.root,a.repo)
 if a.expect:need(exact(out,json.loads(Path(a.expect).read_text())),'Exact saved receipt')
 Path(a.output).write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out['counts'],sort_keys=True))
if __name__=='__main__':main()
