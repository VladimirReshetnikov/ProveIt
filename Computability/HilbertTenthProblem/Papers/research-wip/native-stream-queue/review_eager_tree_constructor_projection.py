#!/usr/bin/env python3
"""Independent constructor graph, exact-degree, paid-ledger and API audit."""
import argparse,copy,hashlib,json,math,random,subprocess,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('review requires ordinary Python (no -O)')
SUBJECT={'eager_tree_constructor_projection.py':'a4c09cc720ac0d5b7f884e8636900a93ba6c17a7040a0f01c83b94f6f469bc81','eager_tree_constructor_projection.json':'26bf1f948751f94e77e5716fddc0668c8d8c910bcb2ac6237b50ece7a9090852','eager_tree_constructor_projection.md':'c5a65687c3756f220e11210525e9bc6ce7968ec2def7348a9dcf5d2cb69d8fc7'}
PARENT={'eager_tree_triangular_projection.py':'a3b528c0ed9434ab95cf1705146a6cc287a9cf9fceb7c14f0062f042219788e2','eager_tree_triangular_projection.json':'79abbc089bac5648e7dad0c1a41fd40572f9fd4ffad7433209cbd4a954bc9cc1','eager_tree_triangular_projection.md':'28e96fdcca087b4263cf88edfe19a9116b1842b2df792f0068659ec47c9028c3','eager_tree_occurrence_flow.py':'0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c','eager_tree_occurrence_flow.json':'10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d','eager_tree_occurrence_flow.md':'ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9'}
KERNEL='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py'
KERNEL_SHA='636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52'
def need(v,msg):
 if not v:raise AssertionError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def same(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(same(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(same(x,y)for x,y in zip(a,b))
 return a==b
def load(path):
 m=types.ModuleType('_independent_'+path.stem);m.__file__=str(path);exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__);return m
def add(a,b,sign=1):
 c=dict(a)
 for mon,n in b.items():c[mon]=c.get(mon,0)+sign*n
 return {m:n for m,n in c.items()if n}
def mul(a,b):
 c={}
 for m,n in a.items():
  for v,w in b.items():
   k=tuple(sorted(m+v));c[k]=c.get(k,0)+n*w
 return {m:n for m,n in c.items()if n}
def atom(v):return {():v}if type(v)is int and v else{}if type(v)is int else{(v,):1}
def expand(rows,free,fixed=None):
 d={n:atom(n)for n in free};d.update({n:atom(v)for n,v in(fixed or{}).items()})
 for n,op,a,b in rows:
  x=atom(a)if type(a)is int else d[a];y=atom(b)if type(b)is int else d[b];d[n]=mul(x,y)if op=='*'else add(x,y,1 if op=='+'else-1)
 return d
def run(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  x=a if type(a)is int else d[a];y=b if type(b)is int else d[b];d[n]=x*y if op=='*'else x+y if op=='+'else x-y
 return d
def inspect(rows,free,ports):
 seen=set(free);need(len(seen)==len(free),'no duplicate fields');deps={};count=Counter()
 for row in rows:
  need(type(row)is list and len(row)==4,'literal source row');n,op,a,b=row
  need(type(n)is str and n not in seen and op in('+','-','*'),'unique typed gate')
  need(all(type(v)is int or type(v)is str and v in seen for v in(a,b)),'acyclic closed source')
  seen.add(n);deps[n]=(a,b);count['M'if op=='*'else'A']+=1
 live=set();todo=list(ports)
 while todo:
  v=todo.pop()
  if type(v)is int or v in live:continue
  need(v in seen,'closed output');live.add(v);todo.extend(deps.get(v,()))
 need(set(deps)<=live and set(free)<=live,'all emitted gates and fields live')
 return dict(M=count['M'],A=count['A'],operations=len(rows))
def finalizer(p):
 rows=copy.deepcopy(p['source']);rs=p['residuals'];squares=[]
 for i,r in enumerate(rs):
  n='flow_square_'+str(i);rows.append([n,'*',r,r]);squares.append(n)
 out=squares[0]
 for i,n in enumerate(squares[1:],1):
  z='flow_sum_'+str(i);rows.append([z,'+',out,n]);out=z
 need(same(rows,p['polynomial_source'])and out==p['output'],'literal complete SOS tail')
def constants(N):return {'r0_mu':1,**{f'r{i}_p{s}_0':0 for i in range(N)for s in range(3)}}
def S(a):return 2*a+1
def F(a,b):return (a+b)*(a+b+1)+2*b+2
def split(x):
 if x==0:return(0,)
 if x%2:return(1,(x-1)//2)
 n=(x-2)//2;t=(math.isqrt(8*n+1)-1)//2;b=n-t*(t+1)//2;return(2,t-b,b)
def application(x,y,budget=100):
 records={};active=set();fuel=[budget]
 def rec(x,y):
  if(x,y)in records:return records[x,y]['z']
  if(x,y)in active or fuel[0]<=0 or max(x.bit_length(),y.bit_length())>96:raise ValueError('bounded evaluator limit')
  active.add((x,y));fuel[0]-=1;a=b=c=u=v=0;children=[];sx=split(x)
  if sx[0]==0:tag=0;z=S(y)
  elif sx[0]==1:tag=1;a=sx[1];z=F(a,y)
  else:
   first,b=sx[1:];sf=split(first)
   if sf[0]==0:tag=2;z=b
   elif sf[0]==1:
    tag=3;a=sf[1];u=rec(b,y);v=rec(a,y);z=rec(u,v);children=[(b,y),(a,y),(u,v)]
   else:
    tag=4;a,bb=sf[1:];c=b;b=bb;u=rec(y,a);z=rec(u,b);children=[(y,a),(u,b)]
  if z.bit_length()>96:raise ValueError('bounded code size')
  records[x,y]=dict(x=x,y=y,z=z,a=a,b=b,c=c,u=u,v=v,tag=tag,children=children)
  active.remove((x,y));return z
 z=rec(x,y);return z,records

def flatten_records(records,keys,external):
 N=len(keys);d={};index={key:i for i,key in enumerate(keys)if key is not None}
 for i,key in enumerate(keys):
  r=records[key]if key is not None else dict(x=0,y=0,z=1,a=0,b=0,c=0,u=0,v=0,tag=0,children=[])
  for f in('x','y','z','a','b','c','u','v'):d[f'r{i}_{f}']=r[f]
  a,b,c,y=[r[n]for n in('a','b','c','y')]
  for f,v in dict(d=F(a,b),e=F(a,y),q=F(0,b),j=F(S(a),b),k=F(F(a,b),c),mu=0).items():d[f'r{i}_{f}']=v
  for tag in range(5):d[f'r{i}_t{tag}']=int(r['tag']==tag)
  for s in range(3):
   for j in range(N):d[f'r{i}_p{s}_{j}']=int(s<len(r['children'])and index[r['children'][s]]==j)
 d.update(zip(('program','argument','output'),external));return d


def ppower(p,n):
 q=atom(1)
 for _ in range(n):q=mul(q,p)
 return q

def restore_poly(p):
 env={n:atom(n)for n in p['free']}
 def pair(a,b):
  s=add(a,b);return add(add(mul(s,add(s,atom(1))),mul(atom(2),b)),atom(2))
 for i in range(p['N']):
  a,b,c,y=[env[f'r{i}_{n}']for n in('a','b','c','y')];d=pair(a,b)
  vals=(d,pair(a,y),pair(atom(0),b),pair(add(mul(atom(2),a),atom(1)),b),pair(d,c))
  env.update({f'r{i}_{n}':v for n,v in zip(('d','e','q','j','k'),vals)})
 return env

def eval_polynomial_source(rows,initial):
 env=dict(initial)
 for n,op,a,b in rows:
  x=atom(a)if type(a)is int else env[a];y=atom(b)if type(b)is int else env[b];env[n]=mul(x,y)if op=='*'else add(x,y,1 if op=='+'else-1)
 return env

def restore_values(p,values):
 v=dict(values)
 for i in range(p['N']):
  a,b,c,y=[v[f'r{i}_{n}']for n in('a','b','c','y')];d=F(a,b)
  v.update({f'r{i}_{n}':x for n,x in zip(('d','e','q','j','k'),(d,F(a,y),F(0,b),F(S(a),b),F(d,c)))})
 return v

def verify(repo,root,subject):
 need(len(SUBJECT)==3,'author freeze must be installed before any load')
 for directory,pins in((subject,SUBJECT),(root,PARENT)):
  for n,h in pins.items():need(sha((directory/n).read_bytes())==h,'exact frozen pin '+n)
 need(sha((repo/KERNEL).read_bytes())==KERNEL_SHA,'corrected original kernel pin')
 author=load(subject/'eager_tree_constructor_projection.py');parent=load(root/'eager_tree_triangular_projection.py');saved=json.loads((subject/'eager_tree_constructor_projection.json').read_text());old_saved=json.loads((root/'eager_tree_triangular_projection.json').read_text())
 counts=Counter();forms=[];packets={};parents={};rng=random.Random(151010)
 for N in range(1,9):
  for cleanup in(False,True):
   p=parent.build(N,cleanup=cleanup,root=root,repo=repo);q=author.build(N,cleanup=cleanup,root=root,repo=repo);parents[N,cleanup]=p;packets[N,cleanup]=q
   need(same(p,next(f['packet']for f in old_saved['forms']if f['packet']['N']==N and f['packet']['cleanup']is cleanup)),'actual triangular parent matches pinned full source')
   need(same(q,next(f['packet']for f in saved['forms']if f['packet']['N']==N and f['packet']['cleanup']is cleanup)),'fresh child matches saved complete source')
   need(same(author.rewrite(p,root=root,repo=repo),q),'entire canonical public parent rewrite')
   removed={f'r{i}_{n}'for i in range(N)for n in('d','e','q','j','k')};indices={22*i+j for i in range(N)for j in range(1,6)}
   need(set(q['removed_parent_coordinates'])==removed and set(q['removed_parent_residual_indices'])==indices and q['free']==[n for n in p['free']if n not in removed],'literal five-field graph interface')
   oldenv=eval_polynomial_source(p['source'],restore_poly(q));new=expand(q['source'],q['free']);j=0;oldout={};newout={};ds=[]
   for i,r in enumerate(p['residuals']):
    if i in indices:need(oldenv[r]=={},'deleted unconditional constructor row identically zero');counts['zero_definition_rows']+=1
    else:need(oldenv[r]==new[q['residuals'][j]],'retained complete residual graph identity');j+=1;counts['retained_residual_identities']+=1
    oldout=add(oldout,mul(oldenv[r],oldenv[r]))
   for r in q['residuals']:
    ds.append(max(map(len,new[r]),default=0));newout=add(newout,mul(new[r],new[r]))
   need(oldout==newout,'entire SOS graph identity');finalizer(p);finalizer(q)
   leader={m:c for m,c in newout.items()if len(m)==10};want={}
   for i in range(N):want=add(want,mul(ppower(atom(f'r{i}_t4'),2),ppower(add(atom(f'r{i}_a'),atom(f'r{i}_b')),8)))
   need(max(ds)==5 and all(d<=3 for i,d in enumerate(ds)if i%17!=1 or i>=17*N),'all non-input-constructor residuals have degree at most3')
   need(leader==want and max(map(len,newout))==10 and leader.get(tuple(sorted(['r0_t4']*2+['r0_a']*8)))==1,'complete degree10 leader and constant nonzero monomial')
   c=inspect(q['source'],q['free'],q['residuals']);l=inspect(q['polynomial_source'],q['free'],[q['output']]);ol=inspect(p['polynomial_source'],p['free'],[p['output']])
   need(all(q['certificate_ledger'][k]==v for k,v in c.items())and all(q['polynomial_ledger'][k]==v for k,v in l.items()),'independently recounted paid ledgers')
   need(l['M']==(9*N*N+91*N+6)//2 and l['A']==6*N*N+(51-int(cleanup))*N+17,'general complete constructor ledger')
   need({k:ol[k]-l[k]for k in('M','A','operations')}==dict(M=5*N,A=10*N,operations=15*N),'exact full15N saving')
   need(len(q['free'])-3==(3*N*N+23*N)//2 and len(q['residuals'])==17*N+3,'full arity and residual formulas')
   # Constructor RHS computation is retained with aliases; exactly the5N
   # definition subtractions disappear before the separately rebuilt finalizer.
   need(len(p['source'])-len(q['source'])==5*N and c['M']==p['certificate_ledger']['M'],'no free constructor arithmetic or hidden M saving')
   counts['whole_graph_identities']+=1;counts['complete_degree_certificates']+=1;counts['complete_live_gates']+=l['operations']
   for case in range(6):
    values={n:Fraction(rng.randint(-3,4),rng.choice((1,2,3)))for n in q['free']};restored=restore_values(q,values)
    need(run(q['polynomial_source'],values)[q['output']]==run(p['polynomial_source'],restored)[p['output']],'full rational graph identity');counts['rational_graph_identities']+=1
   for _ in range(3):
    values={n:rng.randint(0,5)for n in q['free']};v=author.restore_constructors(q,values,root=root,repo=repo)
    need(v==restore_values(q,values)and all(v[n]>=2 for n in removed),'unconditional natural graph restoration, not requiring a zero');counts['unconditional_natural_restorations']+=1
   forms.append(dict(N=N,cleanup=cleanup,ledger=l,witnesses=len(q['free'])-3,residuals=len(q['residuals']),exact_degree=10,full_graph_identity=True,leading_monomial_coefficient=1))
 # Independent five-case evaluator supplies strict-forward parent zeros.
 fixtures=[];root_tags=set()
 for x,y in[(0,3),(1,4),(2,5),(4,0),(8,0),(10,2),(10,1014),(12,0),(18,1),(20,2),(154,1)]:
  try:z,records=application(x,y)
  except ValueError:continue
  post=[];seen=set()
  def dfs(key):
   if key in seen:return
   seen.add(key)
   for child in records[key]['children']:dfs(child)
   post.append(key)
  dfs((x,y));root_tags.add(records[x,y]['tag'])
  for pad in(0,1,2):
   keys=list(reversed(post))+[None]*pad;N=len(keys);v=flatten_records(records,keys,(x,y,z))
   for cleanup in(False,True):
    p=parents.get((N,cleanup))or parent.build(N,cleanup=cleanup,root=root,repo=repo);q=packets.get((N,cleanup))or author.build(N,cleanup=cleanup,root=root,repo=repo);old={n:v[n]for n in p['free']};child={n:old[n]for n in q['free']}
    need(run(p['polynomial_source'],old)[p['output']]==0,'independently generated triangular parent zero')
    need(author.restore_constructors(q,child,root=root,repo=repo)==old and author.project_parent_zero(q,old,root=root,repo=repo)==child,'both complete natural graph-zero inverse directions')
    need(author.evaluate(q,child,root=root,repo=repo)==0,'actual child accepts genuine application');counts['genuine_zero_bijections']+=1
   fixtures.append(dict(input=[x,y],output=z,N=N))
 need(root_tags==set(range(5)),'all five root rules exercised')
 kw=dict(root=root,repo=repo);p=parents[2,False];q=packets[2,False];zeros={n:0 for n in q['free']}
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['rejected_calls']+=1
  else:raise AssertionError('malformed public call accepted')
 for n in(True,False,None,0,-1,1.0,'1'):reject(lambda n=n:author.build(n,**kw))
 for cleanup in(None,1,0,'false'):reject(lambda cleanup=cleanup:author.build(2,cleanup=cleanup,**kw))
 for key in q:
  bad=copy.deepcopy(q);bad.pop(key);reject(lambda bad=bad:author.checked(bad,**kw))
 for key in('N','cleanup','witnesses','residual_count','exact_degree'):
  bad=copy.deepcopy(q);bad[key]=float(bad[key]);reject(lambda bad=bad:author.checked(bad,**kw))
 for key in('source','polynomial_source','free','residuals','constructor_definitions','removed_parent_coordinates'):
  bad=copy.deepcopy(q);bad[key]=tuple(bad[key]);reject(lambda bad=bad:author.checked(bad,**kw))
  fresh=author.build(2,**kw);fresh[key].clear();need(same(author.build(2,**kw),q),'fresh defensive copies');counts['copies']+=1
 bad=copy.deepcopy(q);bad['polynomial_source'][-1]=[q['output'],'-',0,0];reject(lambda:author.checked(bad,**kw))
 bad=copy.deepcopy(q);bad['constructor_definitions'][0]['computed_port']='program';reject(lambda:author.checked(bad,**kw))
 for key in('source','polynomial_source','free','residuals'):
  bad=copy.deepcopy(p);bad[key]=tuple(bad[key]);reject(lambda bad=bad:author.rewrite(bad,**kw))
 reject(lambda:author.rewrite(q,**kw));reject(lambda:author.project_parent_zero(q,restore_values(q,zeros),**kw))
 for value in(True,0.0,Fraction(0),-1):
  bad=dict(zeros);bad['program']=value;reject(lambda bad=bad:author.evaluate(q,bad,**kw));reject(lambda bad=bad:author.restore_constructors(q,bad,**kw))
 for bad in({},dict(zeros,extra=0)):
  reject(lambda bad=bad:author.evaluate(q,bad,**kw));reject(lambda bad=bad:author.restore_constructors(q,bad,**kw))
 for signed in(1,0,None):reject(lambda signed=signed:author.evaluate(q,zeros,signed=signed,**kw))
 negative={n:-3 for n in q['free']};need(author.restore_constructors(q,negative,signed=True,**kw)==restore_values(q,negative),'explicit signed graph values');need(author.evaluate(q,negative,signed=True,**kw)==run(q['polynomial_source'],negative)[q['output']],'signed polynomial API')
 with tempfile.TemporaryDirectory(prefix='review_constructor_pins_')as tmp:
  tmp=Path(tmp);pr=tmp/'parents';pr.mkdir();tr=tmp/'repo';k=tr/KERNEL;k.parent.mkdir(parents=True)
  for name in PARENT:(pr/name).write_bytes((root/name).read_bytes())
  k.write_bytes((repo/KERNEL).read_bytes());author.build(1,root=pr,repo=tr)
  for target in[pr/n for n in PARENT]+[k]:
   data=target.read_bytes();target.write_bytes(data+b'\n');reject(lambda:author.build(1,root=pr,repo=tr));target.write_bytes(data);counts['warm_pin_rejections']+=1
 sentinel=object();name='_authenticated_eager_tree_flow';prior=sys.modules.get(name,sentinel);poison=types.ModuleType(name);sys.modules[name]=poison
 try:need(same(author.build(1,**kw),packets[1,False])and sys.modules[name]is poison,'authenticated kernel source overrides/restores stub');counts['module_restoration_checks']=1
 finally:
  if prior is sentinel:sys.modules.pop(name,None)
  else:sys.modules[name]=prior
 proc=subprocess.run([sys.executable,'-O',str(subject/'eager_tree_constructor_projection.py')],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'optimized interpreter rejected');counts['optimized_rejections']=1
 return dict(status='PASS_INDEPENDENT_EAGER_TREE_CONSTRUCTOR_PROJECTION',review_source_sha256=sha(Path(__file__).read_bytes()),subject_pins=SUBJECT,parent_pins=PARENT,kernel_path=KERNEL,kernel_sha256=KERNEL_SHA,counts=dict(counts),forms=forms,genuine_fixtures=fixtures,scope='Entire polynomial graph identities and natural zero-fiber bijection to the triangular parent. All constructor RHS arithmetic paid; degree10 and15N operations saved. External N, no fixed-arity bound or unique computation fiber; signed/rational checks algebra only.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',required=True,type=Path);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--subject-root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo,a.root,a.subject_root)
 if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact saved review receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
