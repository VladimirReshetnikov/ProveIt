#!/usr/bin/env python3
"""Independent literal source, graph, ledger and API review of finite Tree projection."""
import argparse,copy,hashlib,itertools,json,math,py_compile,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'eager_tree_triangular_projection.py':'a3b528c0ed9434ab95cf1705146a6cc287a9cf9fceb7c14f0062f042219788e2',
'eager_tree_triangular_projection.json':'79abbc089bac5648e7dad0c1a41fd40572f9fd4ffad7433209cbd4a954bc9cc1',
'eager_tree_triangular_projection.md':'28e96fdcca087b4263cf88edfe19a9116b1842b2df792f0068659ec47c9028c3',
'eager_tree_occurrence_flow.py':'0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c',
'eager_tree_occurrence_flow.json':'10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d',
'eager_tree_occurrence_flow.md':'ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9',
'review_eager_tree_occurrence_flow_full.py':'a7546d9c7a33a0c350bc6b27e87c06126d79380cf59466b7f3fe217dfca5c2ab'}
KERNEL='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py'
KERNEL_SHA='636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52'

def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def load(path,pin,name):
 data=path.read_bytes();need(sha(data)==pin,'authenticated source '+path.name)
 m=types.ModuleType(name);m.__file__=str(path);prior=sys.modules.get(name);sys.modules[name]=m
 try:exec(compile(data,str(path),'exec'),m.__dict__)
 finally:
  if prior is None:sys.modules.pop(name,None)
  else:sys.modules[name]=prior
 return m

def atom(x):return ({():x}if x else {})if type(x)is int else{(x,):1}
def add(a,b,s=1):
 d=dict(a)
 for mon,c in b.items():d[mon]=d.get(mon,0)+s*c
 return {mon:c for mon,c in d.items()if c}
def mul(a,b):
 d={}
 for ma,ca in a.items():
  for mb,cb in b.items():
   mon=tuple(sorted(ma+mb));d[mon]=d.get(mon,0)+ca*cb
 return {mon:c for mon,c in d.items()if c}
def expand(rows,env):
 d=dict(env)
 for n,op,a,b in rows:
  a=atom(a)if type(a)is int else d[a];b=atom(b)if type(b)is int else d[b]
  d[n]=mul(a,b)if op=='*'else add(a,b,-1 if op=='-'else 1)
 return d

def fixed(N):return {f'r{i}_p{s}_{j}':0 for i in range(N)for s in range(3)for j in range(i+1)}
def lift(N,v,kind):
 out=dict(v,**fixed(N))
 if kind=='flow':
  for i in range(N):out[f'r{i}_mu']=int(i==0)+sum(out[f'r{j}_mu']*out[f'r{j}_p{s}_{i}']for j in range(i)for s in range(3))
 else:
  for i in reversed(range(N)):out[f'r{i}_h']=1+sum(out[f'r{i}_p{s}_{j}']*out[f'r{j}_h']for j in range(i+1,N)for s in range(3))
 return out

def rank_schema(N,i,kind):
 r=add(atom(f'r{i}_mu'if kind=='flow'else f'r{i}_h'),atom(int(i==0)if kind=='flow'else 1),-1)
 for j in range(N):
  for s in range(3):
   a,b=(f'r{j}_mu',f'r{j}_p{s}_{i}')if kind=='flow'else(f'r{i}_p{s}_{j}',f'r{j}_h')
   r=add(r,mul(atom(a),atom(b)),-1)
 return r

def flat(rows,x,y,z,m):
 out=dict(program=x,argument=y,output=z)
 for i,row in enumerate(rows):
  out.update({f'r{i}_{f}':row[f]for f in m.SCALARS})
  out.update({f'r{i}_t{j}':v for j,v in enumerate(row['t'])})
  out.update({f'r{i}_p{s}_{j}':v for s,ps in enumerate(row['pointers'])for j,v in enumerate(ps)})
 return out

def permute(v,N,order):
 need(sorted(order)==list(range(N))and order[0]==0,'root-fixed row permutation')
 out={k:v[k]for k in('program','argument','output')}
 for i,j in enumerate(order):
  prefix=f'r{j}_'
  for k,value in v.items():
   if k.startswith(prefix)and not k[len(prefix):].startswith('p'):out[f'r{i}_'+k[len(prefix):]]=value
  for s in range(3):
   for k,l in enumerate(order):out[f'r{i}_p{s}_{k}']=v[f'r{j}_p{s}_{l}']
 return out

def subfold(packet,fixed,deleted,cleanup):
 aliases=dict(fixed);changed=set(fixed);rows=[]
 for n,op,a,b in packet['source']:
  aa=aliases.get(a,a);bb=aliases.get(b,b);dirty=a in changed or b in changed;replace=None
  if cleanup or dirty:
   if type(aa)is int and type(bb)is int:replace=aa*bb if op=='*'else aa+bb if op=='+'else aa-bb
   elif op=='*'and(aa==0 or bb==0):replace=0
   elif op=='*'and aa==1:replace=bb
   elif op=='*'and bb==1:replace=aa
   elif op=='+'and aa==0:replace=bb
   elif op in('+','-')and bb==0:replace=aa
  if replace is not None:aliases[n]=replace;changed.add(n)
  else:
   rows.append([n,op,aa,bb])
   if dirty:changed.add(n)
 res=[aliases.get(r,r)for i,r in enumerate(packet['residuals'])if i not in deleted];live={r for r in res if type(r)is str}
 for n,op,a,b in reversed(rows):
  if n in live:live.update(v for v in(a,b)if type(v)is str)
 rows=[row for row in rows if row[0]in live];free=[v for v in packet['free']if v not in fixed and v in live]
 poly=copy.deepcopy(rows);squares=[]
 for i,r in enumerate(res):n='square'+str(i);poly.append([n,'*',r,r]);squares.append(n)
 total=squares[0]
 for i,sq in enumerate(squares[1:]):n='total'+str(i);poly.append([n,'+',total,sq]);total=n
 return {'source':rows,'polynomial_source':poly,'residuals':res,'free':free,'output':total}

def verify(repo,artifacts):
 for name,pin in PINS.items():need(sha((artifacts/name).read_bytes())==pin,'artifact pin '+name)
 need(sha((repo/KERNEL).read_bytes())==KERNEL_SHA,'actual corrected kernel')
 author=load(artifacts/'eager_tree_triangular_projection.py',PINS['eager_tree_triangular_projection.py'],'_independent_triangular_author')
 manual=load(artifacts/'review_eager_tree_occurrence_flow_full.py',PINS['review_eager_tree_occurrence_flow_full.py'],'_independent_triangular_manual')
 kernel=load(repo/KERNEL,KERNEL_SHA,'_independent_triangular_kernel')
 saved=json.loads((artifacts/'eager_tree_triangular_projection.json').read_text());parents=json.loads((artifacts/'eager_tree_occurrence_flow.json').read_text())
 counts=dict(literal_complete_sources=0,residual_DAG_identities=0,full_finalizer_DAG_identities=0,paid_live_gates=0,retained_coefficient_identities=0,local_fold_identities=0,actual_rank_schemas=0,recursive_rank_cancellations=0,full_graph_proofs=0,whole_graph_values=0,signed_graph_values=0,rational_graph_values=0,public_restore_calls=0,genuine_normalizations=0,genuine_permutation_cases=0,unreachable_cycle_normalizations=0,root_inflation_normalizations=0,guards=0,copies=0,source_pin_guards=0)
 rng=random.Random(14102026);forms=[]
 for N in range(1,9):
  parentforms={kind:manual.manual(N,kind=='flow')for kind in('height','flow')}
  for cleanup in(False,True):
   p=author.build(N,cleanup=cleanup,root=artifacts,repo=repo)
   expected=subfold(parentforms['height'],fixed(N),{23*i+22 for i in range(N)},cleanup)
   need(exact(p['free'],expected['free']),'literal coordinate order')
   need(exact(p,saved['forms'][2*(N-1)+int(cleanup)]['packet']),'saved full source packet')
   need(exact(p['fixed_parent_pointers'],fixed(N)),'actual deleted pointers')
   need(p['removed_parent_residual_indices']==[23*i+22 for i in range(N)],'only rank rows removed')
   need(p['parent_sha256']==PINS['eager_tree_occurrence_flow.py'],'current parent provenance')
   I=manual.Intern();a=I.execute(p['polynomial_source'],p['free']);b=I.execute(expected['polynomial_source'],expected['free'])
   need(len(p['residuals'])==len(expected['residuals']),'residual multiplicity')
   for x,y in zip(p['residuals'],expected['residuals']):need(a[x]==b[y],'independent complete residual DAG');counts['residual_DAG_identities']+=1
   need(a[p['output']]==b[expected['output']],'independent entire paid finalizer');counts['full_finalizer_DAG_identities']+=1
   counts['literal_complete_sources']+=1
   M=(9*N*N+101*N+6)//2;A=6*N*N+(61-int(cleanup))*N+17;R=22*N+3;W=(3*N*N+33*N)//2
   got=manual.count(p['polynomial_source'],p['free'],[p['output']]);cert=manual.count(p['source'],p['free'],p['residuals'])
   need(got==[M+A,M,A,4]and cert==[M+A-2*R+1,M-R,A-R+1,2],'full literal gate counts')
   for key,v in [('operations',M+A),('M',M),('A',A),('degree_upper_bound',4),('all_live',True)]:need(exact(p['polynomial_ledger'][key],v),'current full metadata')
   for key,v in zip(('operations','M','A','degree_upper_bound'),cert):need(exact(p['certificate_ledger'][key],v),'current comparison metadata')
   for n,op,a,b,c in p['local_constant_identities']:
    aa=atom(a);bb=atom(b);value=mul(aa,bb)if op=='*'else add(aa,bb,-1 if op=='-'else 1)
    need(value==atom(c),'reported local fold is a literal polynomial identity');counts['local_fold_identities']+=1
   need(exact(p['witnesses'],W)and exact(p['residual_count'],R)and exact(p['exact_degree'],4),'witnesses, equations and exact degree')
   need(not any('_mu'in x or x.endswith('_h')for x in p['free']),'no hidden supplied ranks')
   counts['paid_live_gates']+=M+A
   # Independent sparse coefficient proof, without the author's expansion helper.
   new=expand(p['source'],{v:atom(v)for v in p['free']});quartic_leader=new[p['residuals'][1]]
   top={mon:c for mon,c in quartic_leader.items()if len(mon)==2}
   need(top=={('r0_a','r0_a'):-1,('r0_a','r0_b'):-2,('r0_b','r0_b'):-1},'uniform nonzero retained quadratic')
   for kind,par in parentforms.items():
    old=expand(par['source'],{v:atom(v)for v in par['free']})
    substituted=expand(par['source'],{v:atom(fixed(N).get(v,v))for v in par['free']});j=0
    # Rank variables are private: remaining cones contain none after expansion.
    for i,r in enumerate(par['residuals']):
     if i<23*N and i%23==22:
      row=i//23;need(old[r]==rank_schema(N,row,kind),'actual literal parent rank schema');counts['actual_rank_schemas']+=1
     else:
      need(substituted[r]==new[p['residuals'][j]],'all retained coefficient identities');j+=1;counts['retained_coefficient_identities']+=1
    # Formal recursive graph proof: process actual triangular schema, maintaining
    # sparse restored polynomials. This uses no zero or Boolean assumption.
    env={v:atom(v)for v in p['free']};env.update({v:{}for v in fixed(N)})
    for i in(range(N)if kind=='flow'else reversed(range(N))):
     name=f'r{i}_mu'if kind=='flow'else f'r{i}_h';rank=atom(int(i==0)if kind=='flow'else 1)
     for j in(range(i)if kind=='flow'else range(i+1,N)):
      for s in range(3):
       v,w=(f'r{j}_mu',f'r{j}_p{s}_{i}')if kind=='flow'else(f'r{i}_p{s}_{j}',f'r{j}_h')
       rank=add(rank,mul(env[v],env[w]))
     env[name]=rank
    for i in range(N):
     expr={}
     for mon,c in rank_schema(N,i,kind).items():
      term=atom(c)
      for v in mon:term=mul(term,env[v])
      expr=add(expr,term)
     need(not expr,'entire recursive rank row identically zero');counts['recursive_rank_cancellations']+=1
    counts['full_graph_proofs']+=1
   # Whole evaluations also cover signed integers and rational graph tuples.
   for case in range(10):
    val={v:rng.randint(-2,3)if case<6 else rng.randint(0,3)for v in p['free']}
    if case in(4,5):val={k:Fraction(v,3)for k,v in val.items()}
    out=manual.run(p,val)[p['output']]
    for kind,par in parentforms.items():
     restored=lift(N,val,kind);need(manual.run(par,restored)[par['output']]==out,'complete numeric graph identity');counts['whole_graph_values']+=1;counts['signed_graph_values']+=case<4;counts['rational_graph_values']+=case in(4,5)
     if case not in(4,5):
      got=(author.restore_flow if kind=='flow'else author.restore_height)(p,val,signed=case<4,root=artifacts,repo=repo);need(exact(got,restored),'public recursive restoration');counts['public_restore_calls']+=1
      if case>=6:need(all(v>=0 for v in got.values())and(kind=='flow'or all(got[f'r{i}_h']>=1 for i in range(N))),'natural restoration before zero equations')
   forms.append(dict(N=N,cleanup=cleanup,ledger=[M+A,M,A],certificate=cert,witnesses=W,residuals=R,exact_degree=4,uniform_quadratic_leader=[[list(k),v]for k,v in sorted(top.items())]))
 # Genuine evaluator fixtures; no historical main suite is executed.
 for x,y in[(0,0),(1,2),(2,4),(8,0),(8,1),(10,10),(10,2),(154,1)]:
  ev=kernel.Evaluation(budget=100,max_bits=2048);z=ev.app(x,y)
  for pad in(0,2):
   rows=kernel.certificate(ev,(x,y),pad=pad);N=len(rows);height=flat(rows,x,y,z,manual);flow=manual.forward(N,height)
   orders=[list(range(N))]
   if N>2:orders += [[0]+list(reversed(range(1,N)))]
   if N==6:orders+=[[0]+list(order)for order in list(itertools.permutations(range(1,N)))[:12]]
   for order in orders:
    old=permute(flow,N,order);par=manual.manual(N,True);need(manual.run(par,old)[par['output']]==0,'row/column permutation preserves complete parent zero')
    for cleanup in(False,True):
     p=author.build(N,cleanup=cleanup,root=artifacts,repo=repo);child=author.normalize_parent_zero(p,old,root=artifacts,repo=repo)
     need(tuple(child[k]for k in('program','argument','output'))==(x,y,z),'unchanged external scalar input/output binding')
     need(manual.run(p,child)[p['output']]==0,'complete normalized zero')
     back=author.restore_flow(p,child,root=artifacts,repo=repo);need(exact(author.project_triangular_zero(p,back,root=artifacts,repo=repo),child),'normalized slice zero bijection');counts['genuine_normalizations']+=1
     if any(old[v]for v in fixed(N)):
      naive={v:old[v]for v in p['free']};need(manual.run(p,naive)[p['output']]>0,'deletion really requires permutation');counts['genuine_permutation_cases']+=1
 for item in parents['unreachable_cycle_examples']:
  N=item['row_count'];old=item['values'];p=author.build(N,root=artifacts,repo=repo);child=author.normalize_parent_zero(p,old,root=artifacts,repo=repo)
  need(manual.run(p,child)[p['output']]==0,'actual unreachable cycle dummy normalization');counts['unreachable_cycle_normalizations']+=1
 # Independent complete flow zero with an unreachable circulation feeding root.
 ev=kernel.Evaluation();I,omega=10,1014;z=ev.app(I,omega)
 ev.records[(omega,omega)]=dict(x=omega,y=omega,z=0,h=1,a=I,b=I,c=0,u=omega,v=omega,tag=3,premises=[(I,omega),(I,omega),(omega,omega)])
 rows=kernel.certificate(ev,(I,omega));N=len(rows);cyc=next(i for i,row in enumerate(rows)if(row['x'],row['y'])==(omega,omega));mu=[0]*N;mu[0]=1;mu[cyc]=2
 for ps in rows[cyc]['pointers']:
  for j,v in enumerate(ps):
   if j!=cyc:mu[j]+=2*v
 for i in sorted((i for i in range(N)if i!=cyc),key=lambda i:rows[i]['h'],reverse=True):
  for ps in rows[i]['pointers']:
   for j,v in enumerate(ps):mu[j]+=mu[i]*v
 flow=flat(rows,I,omega,z,manual);flow={k:v for k,v in flow.items()if not k.endswith('_h')};flow.update({f'r{i}_mu':v for i,v in enumerate(mu)});par=manual.manual(N,True)
 need(mu[0]==5 and manual.run(par,flow)[par['output']]==0,'complete nonminimal root mass zero')
 for cleanup in(False,True):
  p=author.build(N,cleanup=cleanup,root=artifacts,repo=repo);v=author.normalize_parent_zero(p,flow,root=artifacts,repo=repo);back=author.restore_flow(p,v,root=artifacts,repo=repo)
  need(back['r0_mu']==1 and manual.run(p,v)[p['output']]==0,'circulation removed before projection');counts['root_inflation_normalizations']+=1
 # Public API failure modes and copies, without trusting Python numeric equality.
 def reject(call):
  try:call()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('invalid public input accepted')
 p=author.build(2,root=artifacts,repo=repo);vals={x:0 for x in p['free']}
 for N in(True,False,0,-1,1.,None,'2'):reject(lambda N=N:author.build(N,root=artifacts,repo=repo))
 for mode in(0,1,0.,None,'false'):reject(lambda mode=mode:author.build(2,cleanup=mode,root=artifacts,repo=repo))
 bads=[]
 for key in p:
  q=copy.deepcopy(p);del q[key];bads.append(q)
 for key in('source','polynomial_source','free','residuals','removed_parent_residual_indices','local_constant_identities'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);bads.append(q)
 for key in('N','exact_degree','witnesses','residual_count'):
  q=copy.deepcopy(p);q[key]=float(q[key]);bads.append(q)
 for idx,row in enumerate(p['source']):
  for col in(2,3):
   if type(row[col])is int:
    q=copy.deepcopy(p);q['source'][idx][col]=float(row[col]);bads.append(q)
 q=copy.deepcopy(p);q['polynomial_source'].append(['dead','+',0,1]);bads.append(q)
 q=copy.deepcopy(p);q['fixed_parent_pointers']['r0_p0_0']=False;bads.append(q)
 q=copy.deepcopy(p);q['polynomial_ledger']['all_live']=1;bads.append(q)
 q=copy.deepcopy(p);q['scope']='same witnesses everywhere';bads.append(q)
 for q in bads:reject(lambda q=q:author.checked(q,root=artifacts,repo=repo))
 for api in(author.evaluate,author.restore_flow,author.restore_height):
  for bad in(True,0.,Fraction(0,1),-1):
   v=dict(vals);v['program']=bad;reject(lambda v=v,api=api:api(p,v,root=artifacts,repo=repo))
  v=dict(vals);v.pop('program');reject(lambda api=api,v=v:api(p,v,root=artifacts,repo=repo))
  v=dict(vals,extra=0);reject(lambda api=api,v=v:api(p,v,root=artifacts,repo=repo))
  for signed in(0,1,None):reject(lambda api=api,signed=signed:api(p,vals,signed=signed,root=artifacts,repo=repo))
 old={x:0 for x in manual.manual(2,True)['free']}
 for api in(author.project_triangular_zero,author.normalize_parent_zero):
  reject(lambda api=api:api(p,old,root=artifacts,repo=repo))
  for value in(True,0.,-1):
   v=dict(old,program=value);reject(lambda api=api,v=v:api(p,v,root=artifacts,repo=repo))
 for key in('free','source','residuals','polynomial_source','fixed_parent_pointers','local_constant_identities','polynomial_ledger'):
  q=author.build(2,root=artifacts,repo=repo);q[key].clear();need(exact(author.build(2,root=artifacts,repo=repo),p),'independent public packet copies');counts['copies']+=1
 a=author.restore_flow(p,vals,root=artifacts,repo=repo);a['r0_mu']=99;need(author.restore_flow(p,vals,root=artifacts,repo=repo)['r0_mu']==1,'independent restored assignments');counts['copies']+=1
 # Reauthentication on warm calls; strict byte pins, no fallback on mismatch.
 with tempfile.TemporaryDirectory(prefix='review_tree_triangular_')as name:
  root=Path(name);(root/KERNEL).parent.mkdir(parents=True);(root/KERNEL).write_bytes((repo/KERNEL).read_bytes());pp=root/'eager_tree_occurrence_flow.py';data=(artifacts/pp.name).read_bytes();pp.write_bytes(data)
  need(exact(author.build(2,root=root,repo=root),p),'portable isolated inputs')
  pp.write_bytes(data+b'\n')
  for api in(lambda:author.build(2,root=root,repo=root),lambda:author.checked(p,root=root,repo=root),lambda:author.restore_height(p,vals,root=root,repo=root)):
   reject(api);counts['source_pin_guards']+=1
  pp.write_bytes(data);kp=root/KERNEL;kd=kp.read_bytes();kp.write_bytes(kd+b'\n')
  for api in(lambda:author.build(2,root=root,repo=root),lambda:author.evaluate(p,vals,root=root,repo=root),lambda:author.restore_flow(p,vals,root=root,repo=root)):
   reject(api);counts['source_pin_guards']+=1
  kp.write_bytes(kd)
  # Timestamp/size-compatible malicious .pyc must not substitute for pinned bytes.
  import os
  for path in(pp,kp):
   raw=path.read_bytes();st=path.stat();payload=b"raise RuntimeError('FORGED BYTECODE EXECUTED')\n";need(len(raw)>len(payload),'bytecode fixture size');path.write_bytes(payload+b' '*(len(raw)-len(payload)));os.utime(path,ns=(st.st_atime_ns,st.st_mtime_ns));py_compile.compile(str(path),doraise=True);path.write_bytes(raw);os.utime(path,ns=(st.st_atime_ns,st.st_mtime_ns))
  names=['_eager_tree_flow_for_projection','_authenticated_eager_tree_flow'];prior={n:sys.modules.get(n)for n in names};stubs={n:types.ModuleType(n)for n in names};sys.modules.update(stubs)
  try:need(exact(author.build(2,root=root,repo=root),p)and all(sys.modules[n]is stubs[n]for n in names),'cold bytecode and module-stub isolation')
  finally:
   for n,v in prior.items():
    if v is None:sys.modules.pop(n,None)
    else:sys.modules[n]=v
  counts['cold_poison_isolation']=1
 proc=subprocess.run([sys.executable,'-O',str(artifacts/'eager_tree_triangular_projection.py'),'--help'],capture_output=True,text=True)
 need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'explicit optimized-interpreter guard');counts['optimized_interpreter_guard']=1
 return dict(status='PASS_INDEPENDENT_TRIANGULAR_TREE',review_source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,kernel_sha256=KERNEL_SHA,counts=counts,forms=forms,scope='Independent complete manual source and full SOS checks for 16 forms, both exact ring graph restorations and natural same-N represented triples; no all-parent-zero bijection, unique fibers, fixed-arity claim or unchanged historical suite replay.')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.repo,a.artifacts)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'exact saved independent receipt')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(r['status'],json.dumps(r['counts'],sort_keys=True))
if __name__=='__main__':main()
