#!/usr/bin/env python3
"""Independent source, graph-normalization, paid-ledger and API audit."""
import argparse,copy,hashlib,json,math,random,subprocess,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('review requires ordinary Python (no -O)')
SUBJECT={
 'eager_tree_root_projection.py':'217b9c800fe7d91a258496e8346f37915aacf6deaaa79543d6fbdaf8fda692db',
 'eager_tree_root_projection.json':'7f2e91bf860eae69fb6213fb055ec9d2d6ecb444a8bb485ebceef02a58b9941e',
 'eager_tree_root_projection.md':'d35084b764d117f80712ea97e5d7491a9ae5f596af879e90cc7950c5d6721851'}
PARENT={
 'eager_tree_occurrence_flow.py':'0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c',
 'eager_tree_occurrence_flow.json':'10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d',
 'eager_tree_occurrence_flow.md':'ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9'}
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

def independent_normalize(v,N):
 # DFS gives a topological order of exactly the reachable graph; slots retain
 # their multiplicities when calculating path counts.
 adj=[[j for s in range(3)for j in range(N)if v[f'r{i}_p{s}_{j}']]for i in range(N)]
 state={};post=[]
 def dfs(i):
  need(state.get(i)!=1,'reachable directed cycle')
  if state.get(i)==2:return
  state[i]=1
  for j in adj[i]:dfs(j)
  state[i]=2;post.append(i)
 dfs(0);mu=[0]*N;mu[0]=1
 for i in reversed(post):
  for j in adj[i]:mu[j]+=mu[i]
 out=dict(v)
 dummy=dict(x=0,y=0,z=1,a=0,b=0,c=0,u=0,v=0,d=2,e=2,q=2,j=4,k=8)
 for i in range(N):
  out[f'r{i}_mu']=mu[i]
  if i not in state:
   out.update({f'r{i}_{f}':n for f,n in dummy.items()})
   out.update({f'r{i}_t{t}':int(t==0)for t in range(5)})
   out.update({f'r{i}_p{s}_{j}':0 for s in range(3)for j in range(N)})
 need(all(out[k]==n for k,n in constants(N).items()),'DFS normalization constants')
 return out,sorted(state),mu

def verify(repo,root,subject):
 for directory,pins in((subject,SUBJECT),(root,PARENT)):
  for name,h in pins.items():need(sha((directory/name).read_bytes())==h,'frozen pin '+name)
 need(sha((repo/KERNEL).read_bytes())==KERNEL_SHA,'actual corrected kernel pin')
 author=load(subject/'eager_tree_root_projection.py');parent=load(root/'eager_tree_occurrence_flow.py')
 saved=json.loads((subject/'eager_tree_root_projection.json').read_text());parent_saved=json.loads((root/'eager_tree_occurrence_flow.json').read_text())
 counts=Counter();forms=[];packets={};parents={};rng=random.Random(318771)
 for N in range(1,9):
  p=parent.build(N,repo=repo);parents[N]=p;fixed=constants(N)
  if N in(1,2,3,5,8):need(same(p,next(f['packet']for f in parent_saved['forms']if f['packet']['N']==N)),'fresh actual parent matches frozen full source')
  env=expand(p['source'],p['free'],fixed);need(env[p['residuals'][22]]=={},'root balance graph identity zero')
  ppoly={}
  for r in p['residuals']:ppoly=add(ppoly,mul(env[r],env[r]))
  finalizer(p);oldledger=inspect(p['polynomial_source'],p['free'],[p['output']])
  for cleanup in(False,True):
   q=author.build(N,cleanup=cleanup,root=root,repo=repo);packets[N,cleanup]=q
   need(same(q,next(f['packet']for f in saved['forms']if f['packet']['N']==N and f['packet']['cleanup']is cleanup)),'actual fresh child equals frozen packet')
   need(same(q['fixed_parent_coordinates'],fixed)and q['free']==[x for x in p['free']if x not in fixed],'exact removed coordinate set')
   finalizer(q);new=expand(q['source'],q['free']);newpoly={}
   for j,r in enumerate(p['residuals']):
    if j==22:continue
    nr=q['residuals'][j-(j>22)];need(env[r]==new[nr],'independent full retained polynomial identity');counts['retained_residual_identities']+=1
   for r in q['residuals']:
    need(max(map(len,new[r]),default=0)<=2,'every retained residual degree at most2');newpoly=add(newpoly,mul(new[r],new[r]))
   need(newpoly==ppoly,'independent complete polynomial graph identity')
   leader={mon:c for mon,c in new[q['residuals'][1]].items()if len(mon)==2}
   need(leader=={('r0_a','r0_a'):-1,('r0_a','r0_b'):-2,('r0_b','r0_b'):-1},'retained nonzero quadratic leader')
   need(max(map(len,newpoly),default=0)==4,'independent exact complete degree4')
   cert=inspect(q['source'],q['free'],q['residuals']);ledger=inspect(q['polynomial_source'],q['free'],[q['output']])
   need(all(q['certificate_ledger'][k]==v for k,v in cert.items())and all(q['polynomial_ledger'][k]==v for k,v in ledger.items()),'all actual ledgers')
   expectedM=12*N*N+41*N+5;expectedA=84-int(cleanup)if N==1 else 15*N*N+(53-int(cleanup))*N+4
   need(ledger==dict(M=expectedM,A=expectedA,operations=expectedM+expectedA),'closed ledger including N1 exception')
   need(len(q['free'])-3==3*N*N+16*N-1 and len(q['residuals'])==23*N+2,'full witness/residual formulas')
   need(oldledger['operations']-ledger['operations']==(18 if N==1 else 30*N)+cleanup*N,'literal-parent saving and separate static cleanup')
   # Any source instruction outside the original constant-dependency cone
   # must remain literally unchanged in the default schedule.
   affected=set(fixed);orig={r[0]:r for r in p['source']}
   for n,op,a,b in p['source']:
    if a in affected or b in affected:affected.add(n)
   if not cleanup:
    got={r[0]:r for r in q['source']}
    for n,row in orig.items():
     if n not in affected:need(n in got and same(row,got[n]),'unaffected source instructions not folded or shared')
   counts['full_polynomial_identities']+=1;counts['exact_degree_certificates']+=1;counts['complete_live_gates']+=ledger['operations']
   for case in range(5):
    values={x:Fraction(rng.randint(-5,5),rng.choice((1,2,3)))for x in q['free']};old=run(p['polynomial_source'],dict(values,**fixed));now=run(q['polynomial_source'],values)
    need(old[p['output']]==now[q['output']],'whole rational graph identity');counts['rational_graph_identities']+=1
   forms.append(dict(N=N,cleanup=cleanup,ledger=ledger,witnesses=len(q['free'])-3,residuals=len(q['residuals']),degree=4,whole_graph_identity=True))
  a,b=packets[N,False],packets[N,True];need(a['polynomial_ledger']['M']==b['polynomial_ledger']['M']and a['polynomial_ledger']['A']-b['polynomial_ledger']['A']==N,'static cleanup exactly N additions')
 # Fresh independently generated genuine applications and padded same-N rows.
 fixtures=[];root_tags=set()
 cases=[(0,3),(1,4),(2,5),(4,0),(8,0),(10,2),(10,1014),(12,0),(18,1),(20,2)]
 for x,y in cases:
  try:z,records=application(x,y)
  except ValueError:continue
  root_tags.add(records[x,y]['tag'])
  for pad in(0,1,2):
   keys=[(x,y)]+[key for key in records if key!=(x,y)]+[None]*pad;N=len(keys);v=flatten_records(records,keys,(x,y,z));normalized,reach,mu=independent_normalize(v,N);v=normalized
   p=parents.get(N)or parent.build(N,repo=repo)
   need(run(p['polynomial_source'],v)[p['output']]==0,'independently constructed genuine parent zero')
   for cleanup in(False,True):
    q=packets.get((N,cleanup))or author.build(N,cleanup=cleanup,root=root,repo=repo)
    child={k:v[k]for k in q['free']};need(author.normalize_parent_zero(q,v,root=root,repo=repo)==child,'public normalize equals independent rooted path counts')
    need(author.project_normalized_zero(q,v,root=root,repo=repo)==child and author.restore(q,child,root=root,repo=repo)==v,'both normalized-slice inverse directions')
    need(author.evaluate(q,child,root=root,repo=repo)==0,'actual child zero');counts['genuine_normalized_zero_maps']+=1
   fixtures.append(dict(input=[x,y],output=z,N=N,reachable=reach,mass=mu))
 need(root_tags==set(range(5)),'genuine fixture coverage of all five eager rules')
 # Independently build a disconnected counterfeit, with an actual application
 # as root. The cyclic row sends two selected slots into that root.
 z,records=application(10,1014);omega=1014
 records[omega,omega]=dict(x=omega,y=omega,z=0,a=10,b=10,c=0,u=omega,v=omega,tag=3,children=[(10,omega),(10,omega),(omega,omega)])
 keys=[(10,omega),(1,omega),(0,omega),(F(0,omega),S(omega)),None,(omega,omega)];N=6;incoming=[]
 for circulation in(1,2,5):
  v=flatten_records(records,keys,(10,omega,omega))
  for i in(0,1,2,3):v[f'r{i}_mu']=1+2*circulation
  v['r5_mu']=circulation;p=parents[N];need(run(p['polynomial_source'],v)[p['output']]==0,'explicit positive circulation into root is a parent zero')
  normal,reach,mu=independent_normalize(v,N);need(reach==[0,1,2,3]and mu==[1,1,1,1,0,0],'minimal rooted counts discard circulation')
  for cleanup in(False,True):
   q=packets[N,cleanup];naive={k:v[k]for k in q['free']};bad=run(q['polynomial_source'],naive)[q['output']]
   need(bad>0,'unrestricted coordinate projection false')
   child=author.normalize_parent_zero(q,v,root=root,repo=repo);need(child=={k:normal[k]for k in q['free']}and author.restore(q,child,root=root,repo=repo)==normal,'complete independent normal form')
   need(author.evaluate(q,child,root=root,repo=repo)==0,'incoming-root normalization actual zero');counts['incoming_root_normalizations']+=1
  incoming.append(dict(circulation=circulation,N=N,parent_root_mass=1+2*circulation,incoming_slots=2,naive_child_value=bad,normalized_value=0))
 need(incoming[0]['naive_child_value']==saved['incoming_root_fixture']['naive_projection_score']==4112998,'literal reported counterexample reproduced independently')
 def reject(call):
  try:call()
  except(ValueError,TypeError,KeyError):counts['rejected_calls']+=1
  else:raise AssertionError('malformed call accepted')
 kw=dict(root=root,repo=repo);q=packets[2,False];p=parents[2];zero={x:0 for x in q['free']}
 for n in(None,True,False,1.0,'2',0,-1):reject(lambda n=n:author.build(n,**kw))
 for c in(None,0,1,'false'):reject(lambda c=c:author.build(2,cleanup=c,**kw))
 for key in q:
  bad=copy.deepcopy(q);bad.pop(key);reject(lambda bad=bad:author.checked(bad,**kw))
 for key in('N','witnesses','residual_count','exact_degree'):
  bad=copy.deepcopy(q);bad[key]=float(bad[key]);reject(lambda bad=bad:author.checked(bad,**kw))
 for key in('free','source','residuals','polynomial_source'):
  bad=copy.deepcopy(q);bad[key]=tuple(bad[key]);reject(lambda bad=bad:author.checked(bad,**kw))
  fresh=author.build(2,**kw);fresh[key].clear();need(same(author.build(2,**kw),q),'defensive ownership');counts['copy_checks']+=1
 bad=copy.deepcopy(q);bad['fixed_parent_coordinates']['r0_mu']=True;reject(lambda:author.checked(bad,**kw))
 bad=copy.deepcopy(q);bad['polynomial_source'][-1]=[q['output'],'-',0,0];reject(lambda:author.checked(bad,**kw))
 for value in(True,0.0,Fraction(0),-1):
  v=dict(zero);v['program']=value
  reject(lambda v=v:author.evaluate(q,v,**kw));reject(lambda v=v:author.restore(q,v,**kw))
 for v in({},dict(zero,extra=0)):
  reject(lambda v=v:author.evaluate(q,v,**kw));reject(lambda v=v:author.restore(q,v,**kw))
 for s in(1,0,None):reject(lambda s=s:author.evaluate(q,zero,signed=s,**kw))
 negative={n:-2 for n in q['free']};need(author.evaluate(q,negative,signed=True,**kw)==run(q['polynomial_source'],negative)[q['output']],'explicit signed algebra only')
 need(author.restore(q,negative,signed=True,**kw)==dict(negative,**constants(2)),'signed affine graph restoration')
 reject(lambda:author.project_normalized_zero(q,dict(zero,**constants(2)),**kw));reject(lambda:author.normalize_parent_zero(q,{x:0 for x in p['free']},**kw))
 q6=packets[6,False]
 # The last incoming fixture is an actual parent zero outside the slice.
 unnormalized=flatten_records(records,keys,(10,omega,omega))
 for i in(0,1,2,3):unnormalized[f'r{i}_mu']=3
 unnormalized['r5_mu']=1;reject(lambda:author.project_normalized_zero(q6,unnormalized,**kw))
 for n in('r0_mu','r0_p0_0'):
  bad=dict(normal);bad[n]=float(bad[n]);reject(lambda bad=bad:author.normalize_parent_zero(q6,bad,**kw))
 # Public build authenticates executable source and kernel each call.
 # Companion proof/receipt pins are a verify-only boundary by design.
 with tempfile.TemporaryDirectory(prefix='review_tree_root_guards_')as tmp:
  tmp=Path(tmp);td=tmp/'parents';td.mkdir();tr=tmp/'repo';f=tr/KERNEL;f.parent.mkdir(parents=True)
  for name in PARENT:(td/name).write_bytes((root/name).read_bytes())
  f.write_bytes((repo/KERNEL).read_bytes());author.build(1,root=td,repo=tr)
  for target in(td/'eager_tree_occurrence_flow.py',f):
   data=target.read_bytes();target.write_bytes(data+b'\n');reject(lambda:author.build(1,root=td,repo=tr));target.write_bytes(data);counts['warm_executable_pin_rejections']+=1
  for name in('eager_tree_occurrence_flow.json','eager_tree_occurrence_flow.md'):
   target=td/name;data=target.read_bytes();target.write_bytes(data+b'\n');need(same(author.build(1,root=td,repo=tr),packets[1,False]),'build companion guard scope');reject(lambda:author.verify(td,tr));target.write_bytes(data);counts['verify_companion_pin_rejections']+=1
 sentinel=object();module_name='_authenticated_eager_tree_flow';prior=sys.modules.get(module_name,sentinel);poison=types.ModuleType(module_name);sys.modules[module_name]=poison
 try:need(same(author.build(1,**kw),packets[1,False])and sys.modules[module_name]is poison,'authenticated source overrides and restores warm stub');counts['cold_source_module_checks']=1
 finally:
  if prior is sentinel:sys.modules.pop(module_name,None)
  else:sys.modules[module_name]=prior
 proc=subprocess.run([sys.executable,'-O',str(subject/'eager_tree_root_projection.py')],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'assert-disabled mode rejected');counts['optimized_mode_rejections']=1
 return dict(status='PASS_INDEPENDENT_EAGER_TREE_ROOT_PROJECTION',review_source_sha256=sha(Path(__file__).read_bytes()),subject_pins=SUBJECT,parent_pins=PARENT,kernel_path=KERNEL,kernel_sha256=KERNEL_SHA,counts=dict(counts),forms=forms,genuine_fixtures=fixtures,incoming_root_fixtures=incoming,guard_scope='Public builds pin executable parent and actual kernel every call; parent JSON/MD pinned by verify only.',scope='All-value complete graph identity. Same-N represented natural triples and bijection only to normalized parent slice. External N, natural witnesses incl zero, exact degree4. No ordinary-input/fixed-arity bound or signed semantic claim.')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',required=True,type=Path);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--subject-root',required=True,type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo,a.root,a.subject_root)
 if a.expect:need(same(r,json.loads(a.expect.read_text())),'exact saved review receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],r['counts'])
if __name__=='__main__':main()
