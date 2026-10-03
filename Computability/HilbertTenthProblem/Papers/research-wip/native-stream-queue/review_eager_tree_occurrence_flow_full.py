#!/usr/bin/env python3
"""Independent complete-source and existential graph audit; no historical main."""
import argparse,copy,hashlib,itertools,json,math,random,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
AUTHOR='eager_tree_occurrence_flow.py'
PINS={'eager_tree_occurrence_flow.py':'0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c','eager_tree_occurrence_flow.json':'10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d','eager_tree_occurrence_flow.md':'ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9'}
KERNEL='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py'
KERNEL_SHA='636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52'
SCALARS=['x','y','z','h','a','b','c','u','v','d','e','q','j','k']

def require(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def digest(data):return hashlib.sha256(data).hexdigest()
def load(path,pin,name):
 data=path.read_bytes();require(digest(data)==pin,'source pin '+str(path));m=types.ModuleType(name);m.__file__=str(path)
 saved=sys.modules.get(name);sys.modules[name]=m
 try:exec(compile(data,str(path),'exec'),m.__dict__)
 finally:
  if saved is None:sys.modules.pop(name,None)
  else:sys.modules[name]=saved
 return m

def fields(N,flow):
 return [n for i in range(N)for n in([f'r{i}_{"mu"if f=="h"and flow else f}'for f in SCALARS]+[f'r{i}_t{j}'for j in range(5)]+[f'r{i}_p{s}_{j}'for s in range(3)for j in range(N)])]+['program','argument','output']
class Writer:
 def __init__(self):self.rows=[]
 def op(self,o,a,b):
  n='manual_'+str(len(self.rows));self.rows.append([n,o,a,b]);return n
 def add(self,a,b):return self.op('+',a,b)
 def sub(self,a,b):return self.op('-',a,b)
 def mul(self,a,b):return self.op('*',a,b)
 def sum(self,values):
  vs=list(values)
  if not vs:return 0
  n=vs[0]
  for v in vs[1:]:n=self.add(n,v)
  return n
 def stem(self,a):return self.add(self.mul(a,2),1)
 def pair(self,a,b):
  s=self.add(a,b);return self.add(self.add(self.mul(s,self.add(s,1)),self.mul(b,2)),2)

def manual(N,flow):
 w=Writer();res=[]
 for row in range(N):
  r={f:f'r{row}_{"mu"if f=="h"and flow else f}'for f in SCALARS};t=[f'r{row}_t{j}'for j in range(5)];ptr=[[f'r{row}_p{s}_{j}'for j in range(N)]for s in range(3)]
  x,y,z,h,a,b,c,u,v,d,e,q,j,k=[r[f]for f in SCALARS];t0,t1,t2,t3,t4=t
  sa,sy=w.stem(a),w.stem(y);active=w.add(t3,t4)
  res.extend([w.sub(w.sum(t),1),w.sub(d,w.pair(a,b)),w.sub(e,w.pair(a,y)),w.sub(q,w.pair(0,b)),w.sub(j,w.pair(sa,b)),w.sub(k,w.pair(d,c)),
   w.sub(x,w.sum([w.mul(t1,sa),w.mul(t2,q),w.mul(t3,j),w.mul(t4,k)])),w.mul(t0,w.sub(z,sy)),w.mul(t1,w.sub(z,e)),w.mul(t2,w.sub(z,b))])
  sums=[w.sum(p)for p in ptr];res.extend([w.sub(sums[0],active),w.sub(sums[1],active),w.sub(sums[2],t3)])
  targets=[[w.add(w.mul(t3,b),w.mul(t4,y)),w.add(w.mul(t3,y),w.mul(t4,a)),w.mul(active,u)],
   [w.add(w.mul(t3,a),w.mul(t4,u)),w.add(w.mul(t3,y),w.mul(t4,b)),w.add(w.mul(t3,v),w.mul(t4,z))],
   [w.mul(t3,u),w.mul(t3,v),w.mul(t3,z)]]
  for slot in range(3):
   for col,f in enumerate(['x','y','z']):res.append(w.sub(w.sum(w.mul(ptr[slot][jj],f'r{jj}_{f}')for jj in range(N)),targets[slot][col]))
  if flow:res.append(None)
  else:
   hm1=w.sub(h,1);products=[w.mul(ptr[slot][jj],f'r{jj}_h')for slot in range(3)for jj in range(N)];res.append(w.sub(hm1,w.sum(products)))
 res += [w.sub('r0_x','program'),w.sub('r0_y','argument'),w.sub('r0_z','output')]
 if flow:
  for i in range(N):
   incoming=w.sum(w.mul(f'r{j}_mu',f'r{j}_p{s}_{i}')for j in range(N)for s in range(3));r=w.sub(f'r{i}_mu',incoming)
   if i==0:r=w.sub(r,1)
   res[23*i+22]=r
 cert=copy.deepcopy(w.rows);squares=[w.mul(r,r)for r in res];out=w.sum(squares)
 return {'source':cert,'residuals':res,'polynomial_source':w.rows,'output':out,'free':fields(N,flow)}

class Intern:
 def __init__(self):self.nodes={}
 def node(self,k):
  if k not in self.nodes:self.nodes[k]=len(self.nodes)
  return self.nodes[k]
 def execute(self,rows,free):
  d={n:self.node(('var',n))for n in free}
  for n,op,a,b in rows:
   av=self.node(('const',a))if type(a)is int else d[a];bv=self.node(('const',b))if type(b)is int else d[b]
   d[n]=self.node((op,av,bv))
  return d

def count(rows,free,outputs):
 ready=set(free);deps={};degree={v:1 for v in free};M=0
 for n,o,a,b in rows:
  require(n not in ready and type(n)is str and type(o)is str and o in('+','-','*'),'closed typed gate')
  require(all(type(v)is int or type(v)is str and v in ready for v in(a,b)),'closed operands')
  da=0 if type(a)is int else degree[a];db=0 if type(b)is int else degree[b];degree[n]=da+db if o=='*'else max(da,db);ready.add(n);deps[n]=(a,b);M+=o=='*'
 live=set();todo=list(outputs)
 while todo:
  n=todo.pop()
  if type(n)is int or n in live:continue
  live.add(n);todo.extend(deps.get(n,()))
 require(set(deps)<=live and set(free)<=live,'all paid gates and supplied coordinates live')
 return [len(rows),M,len(rows)-M,max(degree[v]for v in outputs)]

def run(p,values):
 d=dict(values)
 for n,op,a,b in p['polynomial_source']:
  a=a if type(a)is int else d[a];b=b if type(b)is int else d[b];d[n]=a*b if op=='*'else a+b if op=='+'else a-b
 return d

def edges(N,values):return [[sum(values[f'r{i}_p{s}_{j}']for s in range(3))for j in range(N)]for i in range(N)]
def reachable(A):
 seen={0};todo=[0]
 while todo:
  i=todo.pop()
  for j,a in enumerate(A[i]):
   if a and j not in seen:seen.add(j);todo.append(j)
 return seen

def topo(A,vertices):
 seen=set();active=set();order=[]
 def visit(i):
  require(i not in active,'reachable cycle')
  if i in seen:return
  active.add(i)
  for j,a in enumerate(A[i]):
   if a:require(j in vertices,'edge leaves reachable set');visit(j)
  active.remove(i);seen.add(i);order.append(i)
 for i in sorted(vertices):visit(i)
 return order

def inverse(N,values):
 A=edges(N,values);R=reachable(A);order=topo(A,R);old={k:v for k,v in values.items()if not k.endswith('_mu')};heights={}
 for i in order:heights[i]=1+sum(a*heights[j]for j,a in enumerate(A[i])if a)
 for i in range(N):
  if i in R:old[f'r{i}_h']=heights[i];continue
  dummy=dict(x=0,y=0,z=1,h=1,a=0,b=0,c=0,u=0,v=0,d=2,e=2,q=2,j=4,k=8)
  for name,v in dummy.items():old[f'r{i}_{name}']=v
  for t in range(5):old[f'r{i}_t{t}']=int(t==0)
  for s in range(3):
   for j in range(N):old[f'r{i}_p{s}_{j}']=0
 return old,len(R)

def forward(N,old):
 A=edges(N,old);order=topo(A,set(range(N)));mu=[0]*N;mu[0]=1
 for i in reversed(order):
  for j,a in enumerate(A[i]):mu[j]+=mu[i]*a
 new={k:v for k,v in old.items()if not k.endswith('_h')};new.update({f'r{i}_mu':mu[i]for i in range(N)})
 return new

def graph_checks():
 counts={'finite_flow_trials':0,'finite_natural_flows':0,'unreachable_cycle_flows':0,'signed_cycle_example':1}
 for N,coeff in [(2,range(4)),(3,range(2))]:
  for es in itertools.product(coeff,repeat=N*N):
   A=[list(es[i*N:(i+1)*N])for i in range(N)]
   for mu in itertools.product(range(5),repeat=N):
    counts['finite_flow_trials']+=1
    if any(mu[i]!=int(i==0)+sum(mu[j]*A[j][i]for j in range(N))for i in range(N)):continue
    R=reachable(A);topo(A,R);require(all(mu[i]>0 for i in R),'reachable positivity');counts['finite_natural_flows']+=1
    try:topo(A,set(range(N)))
    except ValueError:counts['unreachable_cycle_flows']+=1
 # Naturalness is essential even for the bare graph theorem: A=[2],mu=[-1].
 require(-1==1+2*(-1),'signed root-cycle flow exists')
 return counts

def verify(repo,artifacts):
 for name,pin in PINS.items():require(digest((artifacts/name).read_bytes())==pin,'author artifact pin '+name)
 m=load(artifacts/AUTHOR,PINS[AUTHOR],'_review_eager_flow_author');kernel=load(repo/KERNEL,KERNEL_SHA,'_review_eager_flow_kernel');receipt=json.loads((artifacts/'eager_tree_occurrence_flow.json').read_text())
 counts={'complete_manual_sources':0,'residual_DAG_identities':0,'full_output_DAG_identities':0,'full_corrections':0,'signed_cases':0,'rational_cases':0,'actual_zero_roundtrips':0,'unreachable_cycle_restorations':0,'guards':0,'copies':0};forms=[];rng=random.Random(3102026)
 for N in(1,2,3,4,5,8):
  parent=m.canonical_parent(N,repo=repo);child=m.build(N,repo=repo);counts['complete_manual_sources']+=2;quartic=[]
  for supplied,flow in[(parent,False),(child,True)]:
   expected=manual(N,flow);I=Intern();a=I.execute(supplied['polynomial_source'],supplied['free']);b=I.execute(expected['polynomial_source'],expected['free']);require(exact(supplied['free'],expected['free']),'exact supplied coordinates')
   for x,y in zip(supplied['residuals'],expected['residuals']):require(a[x]==b[y],'independent literal residual DAG');counts['residual_DAG_identities']+=1
   require(a[supplied['output']]==b[expected['output']],'independent entire finalizer DAG');counts['full_output_DAG_identities']+=1
   got=count(supplied['polynomial_source'],supplied['free'],[supplied['output']]);A=15*N*N+(68 if flow else 69)*N+(6 if flow else 5);M=12*N*N+56*N+3
   require(got==[M+A,M,A,4],'complete paid formula');require(count(expected['polynomial_source'],expected['free'],[expected['output']])==got,'independent paid count')
   # All residuals quadratic and SOS: this exact line has a nonzero t^4
   # coefficient. It certifies attainment rather than a syntactic bound alone.
   outputs=[]
   for t in range(5):
    vals={n:0 for n in supplied['free']};vals['r0_a']=t;outputs.append(run(supplied,vals)[supplied['output']])
   lead=sum((-1)**(4-i)*math.comb(4,i)*v for i,v in enumerate(outputs));require(lead>0 and lead%24==0,'actual exact quartic source certificate');quartic.append({'mode':'flow'if flow else'height','coefficient_of_t4':lead//24})
  for case in range(16):
   old={n:rng.randint(-3,4)if case<8 else rng.randint(0,4)for n in parent['free']}
   if case>=14:old={n:Fraction(v,2)for n,v in old.items()}
   new={n[:-2]+'_mu'if n.endswith('_h')else n:v for n,v in old.items()}
   for i in range(N):
    mass=rng.randint(-3,4)if case<8 else rng.randint(0,4);new[f'r{i}_mu']=Fraction(mass,2)if case>=14 else mass
   a=run(parent,old);b=run(child,new)
   correction=sum(b[child['residuals'][23*i+22]]**2-a[parent['residuals'][23*i+22]]**2 for i in range(N));require(b[child['output']]-a[parent['output']]==correction,'whole square-replacement correction')
   counts['full_corrections']+=1;counts['signed_cases']+=case<8;counts['rational_cases']+=case>=14
  forms.append({'N':N,'parent_count':count(parent['polynomial_source'],parent['free'],[parent['output']]),'child_count':count(child['polynomial_source'],child['free'],[child['output']]),'residuals':len(child['residuals']),'witnesses':len(child['free'])-3,'exact_degree_line_certificates':quartic})
  bad=[]
  for field in child:
   q=copy.deepcopy(child);del q[field];bad.append(q)
  for field in('source','polynomial_source','free','residuals'):
   q=copy.deepcopy(child);q[field]=tuple(q[field]);bad.append(q)
  for i,row in enumerate(child['source']):
   for j in(2,3):
    if type(row[j])is int:
     for value in(float(row[j]),bool(row[j])):
      q=copy.deepcopy(child);q['source'][i][j]=value;bad.append(q)
  q=copy.deepcopy(child);q['source'].append(['dead','+',1,0]);bad.append(q)
  q=copy.deepcopy(child);q['exact_degree']=4.0;bad.append(q)
  for q in bad:
   try:m.checked(q,repo=repo)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('malformed packet accepted')
  vals={n:0 for n in child['free']}
  for name,value in[('r0_mu',-1),('r0_t0',True),('program',0.0)]:
   vv=dict(vals);vv[name]=value
   try:m.evaluate(child,vv,repo=repo)
   except ValueError:counts['guards']+=1
   else:raise AssertionError('invalid natural value accepted')
  for field in('source','polynomial_source','free','residuals'):
   q=m.build(N,repo=repo);q[field].clear();require(exact(m.build(N,repo=repo),child),'defensive packet copies');counts['copies']+=1
 # Bounded actual evaluator fixtures, never the historical author main suite.
 for x,y in[(0,0),(0,3),(1,2),(2,4),(8,0),(8,1),(10,10),(10,2)]:
  ev=kernel.Evaluation(budget=100,max_bits=2048);z=ev.app(x,y)
  for pad in(0,1,3):
   rows=kernel.certificate(ev,(x,y),pad=pad);N=len(rows);old={}
   for i,row in enumerate(rows):
    for f in SCALARS:old[f'r{i}_{f}']=row[f]
    old.update({f'r{i}_t{j}':v for j,v in enumerate(row['t'])});old.update({f'r{i}_p{s}_{j}':v for s,ps in enumerate(row['pointers'])for j,v in enumerate(ps)})
   old.update(program=x,argument=y,output=z);new=forward(N,old);parent=manual(N,False);child=manual(N,True)
   require(run(parent,old)[parent['output']]==0 and run(child,new)[child['output']]==0,'complete genuine forward zero');back,_=inverse(N,new);require(run(parent,back)[parent['output']]==0,'complete same-N inverse zero');counts['actual_zero_roundtrips']+=1
 for example in receipt['unreachable_cycle_examples']:
  N=example['row_count'];new=example['values'];child=manual(N,True);parent=manual(N,False);require(run(child,new)[child['output']]==0,'actual disconnected-cycle flow zero');back,reachable_count=inverse(N,new);require(reachable_count<N and run(parent,back)[parent['output']]==0,'discard unreachable component and restore N-row old zero');counts['unreachable_cycle_restorations']+=1
 # An unreachable circulation can inflate even the reachable root mass.
 ev=kernel.Evaluation();I,omega=10,1014;z=ev.app(I,omega)
 ev.records[(omega,omega)]=dict(x=omega,y=omega,z=0,h=1,a=I,b=I,c=0,u=omega,v=omega,tag=3,premises=[(I,omega),(I,omega),(omega,omega)])
 rows=kernel.certificate(ev,(I,omega));N=len(rows);cyc=next(i for i,row in enumerate(rows)if(row['x'],row['y'])==(omega,omega));mu=[0]*N;mu[0]=1;mu[cyc]=2
 for ps in rows[cyc]['pointers']:
  for j,v in enumerate(ps):
   if j!=cyc:mu[j]+=2*v
 for i in sorted((i for i in range(N)if i!=cyc),key=lambda i:rows[i]['h'],reverse=True):
  for ps in rows[i]['pointers']:
   for j,v in enumerate(ps):mu[j]+=mu[i]*v
 new={}
 for i,row in enumerate(rows):
  for f in SCALARS:new[f'r{i}_{"mu"if f=="h"else f}']=mu[i]if f=='h'else row[f]
  new.update({f'r{i}_t{j}':v for j,v in enumerate(row['t'])});new.update({f'r{i}_p{s}_{j}':v for s,ps in enumerate(row['pointers'])for j,v in enumerate(ps)})
 new.update(program=I,argument=omega,output=z);require(mu[0]==5 and all(type(v)is int and v>=0 for v in new.values()),'root mass exceeds minimal occurrences')
 child=manual(N,True);old=manual(N,False);require(run(child,new)[child['output']]==0,'whole zero with circulation feeding root');back,_=inverse(N,new);require(run(old,back)[old['output']]==0,'same-N inverse for inflated root flow');counts['unreachable_cycle_feeds_root']=1
 counts.update(graph_checks())
 for N in(0,-1,True,1.0):
  try:m.build(N,repo=repo)
  except ValueError:counts['guards']+=1
  else:raise AssertionError('invalid external N accepted')
 saved=sys.modules.get('_authenticated_eager_tree_flow');fake=types.ModuleType('_authenticated_eager_tree_flow');fake.polynomial=lambda *args:None;sys.modules[fake.__name__]=fake
 try:require(exact(m.build(2,repo=repo),m.build(2,repo=repo))and sys.modules[fake.__name__]is fake,'cold stub isolation')
 finally:
  if saved is None:sys.modules.pop(fake.__name__,None)
  else:sys.modules[fake.__name__]=saved
 counts['cold_stub_isolation']=1
 with tempfile.TemporaryDirectory(prefix='review_eager_flow_')as tmp:
  dest=Path(tmp)/KERNEL;dest.parent.mkdir(parents=True);original=(repo/KERNEL).read_bytes();dest.write_bytes(original);m.build(2,repo=tmp);dest.write_bytes(original+b'\n')
  try:m.build(2,repo=tmp)
  except ValueError:counts['warm_source_pin_rejections']=1
  else:raise AssertionError('warm changed source accepted')
 return {'status':'PASS_INDEPENDENT_EAGER_TREE_OCCURRENCE_FLOW','review_source_sha256':digest(Path(__file__).read_bytes()),'author_pins':PINS,'kernel_pin':KERNEL_SHA,'counts':counts,'forms':forms,'scope':'Manual complete-source identities and full ledgers; natural reachable-DAG proof and existential same-N restoration. No witness bijection, uniqueness, fixed arity or replay of historical full suite.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo,a.artifacts)
 if a.expect:require(exact(r,json.loads(a.expect.read_text())),'saved independent receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
