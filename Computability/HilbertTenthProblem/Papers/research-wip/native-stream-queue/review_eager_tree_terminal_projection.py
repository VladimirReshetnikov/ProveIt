#!/usr/bin/env python3
"""Independent review of the frozen maintained last-row Tree projection."""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'eager_tree_pointer_product_scout.py':'35fab9c363c38421a2d4b569bfd56f1cddf95717f9dfaa37ada4ce7dc6fe49bd',
'eager_tree_pointer_product_scout.json':'9d0eaa72ffee7c900f8e348c305293193a8b4ebaa066c534902795f6b87ba4cc',
'eager_tree_pointer_product_scout.md':'c0c5991e451ae74fc9a6b9c15e996a4e2f80dd04b33d2bb2a433d03142bf47b3',
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def read(root,name):
 b=(Path(root)/name).read_bytes();need(hashlib.sha256(b).hexdigest()==PINS[name],'pin '+name);return b
def hashjson(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def fold(op,a,b):
 if type(a)is int and type(b)is int:return a+b if op=='+'else a-b if op=='-'else a*b
 if op=='*':
  if a==0 or b==0:return 0
  if a==1:return b
  if b==1:return a
 if op=='+'and a==0:return b
 if op in('+','-')and b==0:return a
 return None

def literal_projection(old):
 last=old['N']-1;fixed={f'r{last}_{x}':0 for x in('t3','t4','c')};aliases=dict(fixed);affected=set(fixed);rows=[]
 for n,op,a,b in old['source']:
  aa=aliases.get(a,a);bb=aliases.get(b,b);hit=a in affected or b in affected;v=fold(op,aa,bb)if hit else None
  if v is None:rows.append([n,op,aa,bb])
  else:aliases[n]=v
  if hit:affected.add(n)
 need(all(aliases.get(x,x)==0 for x in old['residuals'][-3:]),'three forced-zero residuals')
 residuals=[aliases.get(x,x)for x in old['residuals'][:-3]];live=set(residuals)
 for n,o,a,b in rows[::-1]:
  if n in live:live.update(x for x in(a,b)if type(x)is str)
 rows=[r for r in rows if r[0]in live];free=[x for x in old['free']if x not in fixed]
 need(set(free)<=live and not(set(fixed)&live),'remaining coordinates and deleted privacy')
 return rows,residuals,free,fixed

class Expressions:
 def __init__(self):self.ids={};self.nodes=[]
 def get(self,key):
  if key not in self.ids:self.ids[key]=len(self.nodes);self.nodes.append(key)
  return self.ids[key]
 def leaf(self,x):return self.get(('i'if type(x)is int else'v',x))
 def op(self,o,a,b):
  A=self.nodes[a];B=self.nodes[b]
  if A[0]=='i'and B[0]=='i':return self.leaf(fold(o,A[1],B[1]))
  zero=self.leaf(0);one=self.leaf(1)
  if o=='*':
   if a==zero or b==zero:return zero
   if a==one:return b
   if b==one:return a
  if o=='+':
   if a==zero:return b
   if b==zero:return a
  if o=='-'and b==zero:return a
  if o in('+','*')and a>b:a,b=b,a
  return self.get((o,a,b))
 def run(self,rows,free,fixed=None):
  e={x:self.leaf((fixed or{}).get(x,x))for x in free}
  for n,o,a,b in rows:e[n]=self.op(o,e[a]if type(a)is str else self.leaf(a),e[b]if type(b)is str else self.leaf(b))
  return e

def numeric(rows,v):
 e=dict(v)
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else a;b=e[b]if type(b)is str else b;e[n]=a+b if o=='+'else a-b if o=='-'else a*b
 return e

def ledger(rows,free,outputs):
 known=set(free);defs={};degree={x:1 for x in free}
 for row in rows:
  need(type(row)is list and len(row)==4,'literal row');n,o,a,b=row
  need(type(n)is str and n not in known and o in('+','-','*'),'fresh exact gate')
  need(all(type(x)is int or type(x)is str and x in known for x in(a,b)),'source closure')
  da=degree[a]if type(a)is str else 0;db=degree[b]if type(b)is str else 0
  degree[n]=da+db if o=='*'else max(da,db);known.add(n);defs[n]=(a,b)
 live=set();stack=list(outputs)
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x);stack.extend(defs.get(x,()))
 need(set(defs)|set(free)<=live,'all paid rows/coordinates live')
 M=sum(r[1]=='*'for r in rows)
 return M,len(rows)-M,max(degree[x]if type(x)is str else 0 for x in outputs)
def diagonal(rows,free):
 def add(a,b,s=1):
  c=[0]*max(len(a),len(b))
  for i,x in enumerate(a):c[i]+=x
  for i,x in enumerate(b):c[i]+=s*x
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def mul(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e={x:[0,1]for x in free}
 for n,o,a,b in rows:
  a=e[a]if type(a)is str else[a];b=e[b]if type(b)is str else[b];e[n]=mul(a,b)if o=='*'else add(a,b,1 if o=='+'else -1)
 return e

def simple_zero(old,tag=0):
 N=old['N'];v={n:0 for n in old['free']}
 for i in range(N):v[f'r{i}_t0']=1;v[f'r{i}_z']=1
 if tag==0:v.update(program=0,argument=0,output=1)
 elif N==1:
  v['r0_t0']=0;v[f'r0_t{tag}']=1
  if tag==1:
   a,y=2,3;z=(a+y)*(a+y+1)+2*y+2
   v.update(r0_a=a,r0_x=2*a+1,r0_y=y,r0_z=z,program=2*a+1,argument=y,output=z)
  else:
   b,y=2,3;x=b*(b+1)+2*b+2
   v.update(r0_b=b,r0_x=x,r0_y=y,r0_z=b,program=x,argument=y,output=b)
 else:raise ValueError('only last leaf alternatives at N1')
 need(numeric(old['polynomial_source'],v)[old['output']]==0,'handwritten complete parent zero')
 return v

AUTHOR={
'eager_tree_terminal_projection.py':'edee37e68cde72e65ecc6e903ab6d2aa359f01182fb3d4a5e744a49ab92e46bd',
'eager_tree_terminal_projection.json':'25f02a91b38b23f798a10d8c1fc88e014fa277a392281ea93aaa146a5bcade95',
'eager_tree_terminal_projection.md':'ad8439465f5def857e917b2e4df3d42f36f2e8ad5e4f740b5ca74cbf036a3e0b',
}
def author_load(root):
 blobs={}
 for name,pin in AUTHOR.items():
  b=(Path(root)/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'author pin '+name);blobs[name]=b
 path=Path(root)/'eager_tree_terminal_projection.py';m=types.ModuleType('_independently_authenticated_terminal');m.__file__=str(path)
 exec(compile(blobs[path.name],str(path),'exec'),m.__dict__)
 return m,json.loads(blobs['eager_tree_terminal_projection.json'])

def verify(root,artifacts):
 blobs={n:read(root,n)for n in PINS};parent=json.loads(blobs['eager_tree_pointer_product_scout.json'])
 need(parent['source_sha256']==PINS['eager_tree_pointer_product_scout.py'],'source/parent receipt link')
 oldforms={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in parent['forms']}
 expected={(n,c)for n in range(1,9)for c in(False,True)}
 need(len(parent['forms'])==16 and set(oldforms)==expected,'exact complete parent family')
 mod,saved=author_load(artifacts);need(saved['source_sha256']==AUTHOR['eager_tree_terminal_projection.py'],'source/child receipt link')
 savedforms={(f['packet']['N'],f['packet']['cleanup']):f['packet']for f in saved['forms']}
 need(len(saved['forms'])==16 and set(savedforms)==expected,'exact complete child family')
 counts=dict(literal_complete_sources=0,whole_graphs=0,arbitrary_c_graphs=0,retained_residuals=0,deleted_zero_residuals=0,paid_live_gates=0,exact_degrees=0,numeric_graphs=0,rational_graphs=0,natural_restorations=0,zero_maps=0,nonunique_c_fibers=0,guards=0,copies=0,warm_pins=0)
 results=[];rng=random.Random(381072)
 for N,cleanup in sorted(expected):
  old=oldforms[N,cleanup];p=mod.build(N,cleanup=cleanup,root=root)
  need(exact(p,savedforms[N,cleanup]),'canonical packet versus saved full source')
  need(exact(mod.canonical_parent(N,cleanup=cleanup,root=root),old),'canonical entire parent')
  need(exact(mod.rewrite(copy.deepcopy(old),root=root),p),'rewrite canonical packet')
  need(exact(mod.checked(p,root=root),p)and exact(mod.polynomial_source(p,root=root),p['polynomial_source']),'public canonical accessors')
  rows,res,free,fixed=literal_projection(old)
  need(exact(rows,p['source'])and exact(res,p['residuals'])and exact(free,p['free'])and exact(fixed,p['fixed_parent_coordinates']),'independent literal projected source')
  poly=copy.deepcopy(rows)
  for i,r in enumerate(res):poly.append([f'terminal_square_{i}','*',r,r])
  out='terminal_square_0'
  for i in range(1,len(res)):
   nxt=f'terminal_sum_{i}';poly.append([nxt,'+',out,f'terminal_square_{i}']);out=nxt
  need(exact(poly,p['polynomial_source'])and out==p['output'],'one square per occurrence and literal full paid finalizer')
  expected_map=[dict(parent_index=i,parent_port=r,child_port=res[i])for i,r in enumerate(old['residuals'][:-3])]
  need(exact(p['residual_map'],expected_map)and p['removed_parent_residual_indices']==list(range(len(res),len(res)+3)),'current residual mapping')
  last=N-1;lastslots=old['slot_map'][-3:]
  need([x['row']for x in lastslots]==[last]*3 and [x['child_port']for x in lastslots]==old['residuals'][-3:],'actual last membership schema')
  inter=Expressions();ee=inter.run(old['source'],old['free']);active=inter.op('+',inter.leaf(f'r{last}_t3'),inter.leaf(f'r{last}_t4'))
  need([ee[r]for r in old['residuals'][-3:]]==[active,active,inter.leaf(f'r{last}_t3')],'literal empty products and repeated residual')
  before=inter.run(old['polynomial_source'],old['free'],fixed);after=inter.run(poly,free)
  need(before[old['output']]==after[out],'complete graph identity');counts['whole_graphs']+=1
  arbitrary=inter.run(old['polynomial_source'],old['free'],{f'r{last}_t3':0,f'r{last}_t4':0})
  need(arbitrary[old['output']]==after[out],'complete polynomial independent of arbitrary terminal c');counts['arbitrary_c_graphs']+=1
  for i,r in enumerate(res):need(before[old['residuals'][i]]==after[r],'retained residual polynomial');counts['retained_residuals']+=1
  for r in old['residuals'][-3:]:need(before[r]==inter.leaf(0),'deleted residual zero');counts['deleted_zero_residuals']+=1
  M,A,degree=ledger(poly,free,[out]);cm,ca,cd=ledger(rows,free,res)
  oldM,oldA,_=ledger(old['polynomial_source'],old['free'],[old['output']]);oldcm,oldca,_=ledger(old['source'],old['free'],old['residuals'])
  need((oldM-M,oldA-A,oldcm-cm,oldca-ca)==(11,20,8,17),'full versus certificate delta')
  need(M==(3*N*N+81*N-46)//2 and A==(3*N*N+(131-2*int(cleanup))*N-78)//2,'general paid formula')
  need(len(free)-3==p['witnesses']==13*N-5 and len(res)==p['residual_count']==8*N,'full interface formula')
  need(p['polynomial_ledger']==dict(M=M,A=A,operations=M+A,degree_upper_bound=degree,all_live=True),'current full ledger')
  need(p['certificate_ledger']==dict(M=cm,A=ca,operations=cm+ca,degree_upper_bound=cd,all_live=True),'current certificate ledger')
  coefficients=diagonal(poly,free)[out];d=6 if N==1 else 10*N-8;lead=17 if N==1 else 8*2**(10*(N-1))+2**(8*(N-1))
  need(degree==p['exact_degree']==len(coefficients)-1==d and coefficients[-1]==lead,'exact whole-polynomial degree and coefficient')
  need(p['degree_certificate']['diagonal_leading_coefficient']==lead,'degree metadata')
  need(p['full_polynomial_graph_identity']is True and p['natural_existential_projection']is True and p['full_parent_zero_bijection']is False and exact(p['parent_pins'],PINS),'scope/provenance metadata')
  counts['literal_complete_sources']+=1;counts['paid_live_gates']+=M+A;counts['exact_degrees']+=1
  for k in range(8):
   v={n:rng.randint(0,3)if k<3 else rng.randint(-3,3)for n in free}
   rational=k==7
   if rational:v={n:Fraction(x,2)for n,x in v.items()}
   extension=dict(v,**fixed);result=numeric(poly,v)[out]
   need(numeric(old['polynomial_source'],extension)[old['output']]==result,'entire numeric graph')
   extension[f'r{last}_c']=Fraction(-17,3)if rational else 11
   need(numeric(old['polynomial_source'],extension)[old['output']]==result,'entire arbitrary c graph')
   counts['numeric_graphs']+=1;counts['rational_graphs']+=rational
   if not rational:
    need(mod.evaluate(p,v,signed=k>=3,root=root)==result,'public integer evaluator')
    restored=mod.restore_assignment(p,v,signed=k>=3,root=root);need(exact(restored,dict(v,**fixed)),'unconditional public graph restoration')
    if k<3:need(min(restored.values())>=0,'natural restoration');counts['natural_restorations']+=1
  cases=[simple_zero(old)]+([simple_zero(old,1),simple_zero(old,2)]if N==1 else[])
  if N==5:cases.append(copy.deepcopy(parent['nonunique_zero_fixture']['child']))
  for v in cases:
   need(set(v)==set(old['free'])and numeric(old['polynomial_source'],v)[old['output']]==0,'independent complete zero fixture')
   child={n:v[n]for n in free};need(exact(mod.project_parent_zero(p,v,root=root),child)and mod.evaluate(p,child,root=root)==0,'natural projection')
   restored=mod.restore_assignment(p,child,root=root);need(numeric(old['polynomial_source'],restored)[old['output']]==0,'restored parent zero')
   need(exact(mod.project_parent_zero(p,restored,root=root),child),'normalized slice inverse');counts['zero_maps']+=1
   for c in(1,7,100):
    ambiguous=dict(restored);ambiguous[f'r{last}_c']=c
    need(numeric(old['polynomial_source'],ambiguous)[old['output']]==0 and exact(mod.project_parent_zero(p,ambiguous,root=root),child)and ambiguous!=restored,'full zero fiber is not bijective');counts['nonunique_c_fibers']+=1
  results.append(dict(N=N,cleanup=cleanup,M=M,A=A,operations=M+A,witnesses=p['witnesses'],residuals=len(res),exact_degree=d,diagonal_leading_coefficient=lead,coefficient_sha256=hashjson(coefficients),source_sha256=hashjson(poly)))
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise ValueError('Malformed API accepted')
 for n in(True,False,0,-1,9,1.0,'1',None):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,n=n:fn(n,root=root))
 for c in(0,1,None,'true'):
  for fn in(mod.build,mod.canonical_parent):reject(lambda fn=fn,c=c:fn(2,cleanup=c,root=root))
 p=mod.build(2,root=root);old=oldforms[2,True];v={n:0 for n in p['free']}
 for key in p:
  q=copy.deepcopy(p);del q[key];reject(lambda q=q:mod.checked(q,root=root))
 for key in('N','witnesses','residual_count','exact_degree'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('full_polynomial_graph_identity','natural_existential_projection','full_parent_zero_bijection','cleanup'):
  q=copy.deepcopy(p);q[key]=int(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in('source','polynomial_source','free','residual_map','residuals'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:mod.checked(q,root=root))
 for key in old:
  q=copy.deepcopy(old);del q[key];reject(lambda q=q:mod.rewrite(q,root=root))
 for rowkind in('source','polynomial_source'):
  q=copy.deepcopy(p);q[rowkind][-1][1]='+'if q[rowkind][-1][1]=='*'else'*';reject(lambda q=q:mod.checked(q,root=root))
 for val in(True,1.0,Fraction(1),-1):
  bad=dict(v,program=val)
  for fn in(mod.evaluate,mod.restore_assignment):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for bad in({},dict(v,surplus=0),list(v)):
  for fn in(mod.evaluate,mod.restore_assignment):reject(lambda fn=fn,bad=bad:fn(p,bad,root=root))
 for mode in(0,1,None):
  for fn in(mod.evaluate,mod.restore_assignment):reject(lambda fn=fn,mode=mode:fn(p,v,signed=mode,root=root))
 oldzero=simple_zero(old)
 for bad in({n:0 for n in old['free']},dict(oldzero,program=True),dict(oldzero,program=0.0),dict(oldzero,r1_c=-1),dict(oldzero,extra=0)):
  reject(lambda bad=bad:mod.project_parent_zero(p,bad,root=root))
 for key,val in p.items():
  if type(val)in(dict,list):
   q=mod.build(2,root=root);q[key].clear();need(exact(mod.build(2,root=root),p),'build mutable field copy');counts['copies']+=1
 for fn in(lambda:mod.canonical_parent(2,root=root),lambda:mod.rewrite(old,root=root),lambda:mod.checked(p,root=root)):
  q=fn();q['source'].clear();need(exact(mod.checked(p,root=root),p)and exact(mod.canonical_parent(2,root=root),old),'canonical accessor isolated');counts['copies']+=1
 q=mod.polynomial_source(p,root=root);q.clear();need(exact(mod.polynomial_source(p,root=root),p['polynomial_source']),'source copy');counts['copies']+=1
 q=mod.restore_assignment(p,v,root=root);q['program']=1;need(v['program']==0,'restore assignment copy');counts['copies']+=1
 q=mod.project_parent_zero(p,oldzero,root=root);q['program']=1;need(oldzero['program']==0,'projection assignment copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='terminal_independent_pins_')as tmp:
  tmp=Path(tmp)
  for n,b in blobs.items():(tmp/n).write_bytes(b)
  need(exact(mod.build(2,root=tmp),p),'warm initial pinned call')
  for n,b in blobs.items():
   (tmp/n).write_bytes(b+b'\n')
   calls=[lambda:mod.build(2,root=tmp),lambda:mod.canonical_parent(2,root=tmp),lambda:mod.rewrite(old,root=tmp),lambda:mod.checked(p,root=tmp),lambda:mod.polynomial_source(p,root=tmp),lambda:mod.evaluate(p,v,root=tmp),lambda:mod.restore_assignment(p,v,root=tmp),lambda:mod.project_parent_zero(p,oldzero,root=tmp)]
   for fn in calls:reject(fn);counts['warm_pins']+=1
   (tmp/n).write_bytes(b)
 proc=subprocess.run([sys.executable,'-O',str(Path(artifacts)/'eager_tree_terminal_projection.py')],capture_output=True,text=True,timeout=30)
 need(proc.returncode!=0 and'Run without -O'in proc.stderr,'explicit optimized rejection');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_EAGER_TREE_TERMINAL_PROJECTION',review_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=PINS,author_pins=AUTHOR,counts=counts,forms=results,scope='Independent complete-source/API/degree review of all16 saved forms. Natural existential projection; full zero bijection only on terminal c0 slice. No historical suite or general fixed-arity bound.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.artifacts)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact saved independent receipt')
 if a.output:a.output.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
 print(out['status'],out['counts'])
if __name__=='__main__':main()
