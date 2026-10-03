"""Eliminate five natural constructor coordinates from the finite Tree packet.

Complete graph projection of the pinned triangular source; external N remains.
"""
import argparse,copy,hashlib,json,random,subprocess,sys,tempfile,types
from fractions import Fraction
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'eager_tree_triangular_projection.py':'a3b528c0ed9434ab95cf1705146a6cc287a9cf9fceb7c14f0062f042219788e2','eager_tree_triangular_projection.json':'79abbc089bac5648e7dad0c1a41fd40572f9fd4ffad7433209cbd4a954bc9cc1','eager_tree_triangular_projection.md':'28e96fdcca087b4263cf88edfe19a9116b1842b2df792f0068659ec47c9028c3','eager_tree_occurrence_flow.py':'0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c','eager_tree_occurrence_flow.json':'10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d','eager_tree_occurrence_flow.md':'ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9'}
KERNEL='SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py'
KERNEL_SHA='636ce7feadd65198b59050a7ca799c185fd4845e6d7d3a741a2628e3e4684b52'
FIELDS=('d','e','q','j','k')
def need(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)in(list,tuple):return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b

def _context(root,repo):
 root=Path(__file__).resolve().parent if root is None else Path(root);blobs={}
 for name,pin in PINS.items():
  data=(root/name).read_bytes();need(hashlib.sha256(data).hexdigest()==pin,'Parent pin '+name);blobs[name]=data
 need(hashlib.sha256((Path(repo)/KERNEL).read_bytes()).hexdigest()==KERNEL_SHA,'Original kernel pin')
 path=root/'eager_tree_triangular_projection.py';m=types.ModuleType('_authenticated_triangular_for_constructors');m.__file__=str(path);exec(compile(blobs[path.name],str(path),'exec'),m.__dict__)
 return root,m,m.parent(root)

def _rewrite(old,flow):
 N=old['N'];definition_indices=[22*i+j for i in range(N)for j in range(1,6)];definition_names={old['residuals'][i]for i in definition_indices}
 targets={f'r{i}_{f}'for i in range(N)for f in FIELDS};aliases={};rows=[];definitions=[]
 for n,op,a,b in old['source']:
  aa=aliases.get(a,a);bb=aliases.get(b,b)
  if n in definition_names:
   need(op=='-'and a in targets and a not in aliases,'Literal unconditional constructor definition')
   aliases[a]=bb;definitions.append(dict(coordinate=a,computed_port=bb,parent_residual=n,parent_residual_index=old['residuals'].index(n)))
  else:rows.append([n,op,aa,bb])
 need(set(aliases)==targets and len(definitions)==5*N,'All five definitions in each row')
 residuals=[r for r in old['residuals']if r not in definition_names];free=[v for v in old['free']if v not in targets]
 poly,out=flow.finalizer(rows,residuals);cert=flow.inspect(rows,free,residuals);ledger=flow.inspect(poly,free,[out]);cleanup=old['cleanup']
 need((ledger['M'],ledger['A'],ledger['operations'])==((9*N*N+91*N+6)//2,6*N*N+(51-int(cleanup))*N+17,(21*N*N+193*N+40)//2-int(cleanup)*N),'Complete paid count formula')
 need({k:old['polynomial_ledger'][k]-ledger[k]for k in('M','A','operations')}==dict(M=5*N,A=10*N,operations=15*N),'Exact complete graph-row saving')
 need(len(free)-3==(3*N*N+23*N)//2 and len(residuals)==17*N+3 and ledger['degree_upper_bound']==10,'Interface and degree upper bound')
 return dict(N=N,cleanup=cleanup,free=free,source=rows,residuals=residuals,polynomial_source=poly,output=out,certificate_ledger=cert,polynomial_ledger=ledger,witnesses=len(free)-3,residual_count=len(residuals),exact_degree=10,
  removed_parent_coordinates=sorted(targets),removed_parent_residual_indices=definition_indices,constructor_definitions=definitions,parent_sha256=PINS['eager_tree_triangular_projection.py'],full_polynomial_graph_identity=True,
  domains='All supplied coordinates natural, including zero; external exact integer N>=1. Signed mode is polynomial evaluation only.',
  graph_relation='d=F(a,b), e=F(a,y), q=F(0,b), j=F(2a+1,b), k=F(d,c), with F(u,v)=(u+v)(u+v+1)+2v+2, separately in each row.',
  degree_certificate={'highest_homogeneous_polynomial':'sum_i t[i,4]^2*(a[i]+b[i])^8','nonzero_monomial':{'r0_t4':2,'r0_a':8},'coefficient':1,'reason':'Only the row constructor-input residuals have degree5; every other retained residual has degree at most3.'},
  historical_parent={'witnesses':old['witnesses'],'residual_count':old['residual_count'],'exact_degree':old['exact_degree'],'polynomial_ledger':copy.deepcopy(old['polynomial_ledger']),'fixed_parent_pointers':copy.deepcopy(old['fixed_parent_pointers'])},
  scope='Unique natural graph restoration on every child tuple and bijection of full natural zero fibers with the triangular parent. Same represented triples at each external N. No all-original-height-zero bijection, fixed-arity universal bound, ordinary-input recoder or unique computation-fiber claim.')

def canonical_parent(N,*,cleanup=False,root=None,repo):
 need(type(N)is int and N>=1 and type(cleanup)is bool,'Exact positive N and Boolean cleanup');root,m,flow=_context(root,repo);return m.build(N,cleanup=cleanup,root=root,repo=repo)
def build(N,*,cleanup=False,root=None,repo):
 need(type(N)is int and N>=1 and type(cleanup)is bool,'Exact positive N and Boolean cleanup');root,m,flow=_context(root,repo);return _rewrite(m.build(N,cleanup=cleanup,root=root,repo=repo),flow)
def rewrite(parent,*,root=None,repo):
 need(type(parent)is dict,'Complete parent packet');old=canonical_parent(parent.get('N'),cleanup=parent.get('cleanup'),root=root,repo=repo);need(exact(parent,old),'Entire canonical parent');_,_,flow=_context(root,repo);return _rewrite(old,flow)
def checked(packet,*,root=None,repo):
 need(type(packet)is dict,'Complete child packet');p=build(packet.get('N'),cleanup=packet.get('cleanup'),root=root,repo=repo);need(exact(packet,p),'Entire canonical child');return p

def _values(p,values,signed):
 need(type(values)is dict and set(values)==set(p['free'])and type(signed)is bool,'Complete assignment and exact mode')
 need(all(type(k)is str and type(v)is int for k,v in values.items()),'Exact integer coordinates')
 if not signed:need(all(v>=0 for v in values.values()),'Natural coordinates')
 return dict(values)
def _run(rows,values):
 d=dict(values)
 for n,op,a,b in rows:
  x=d[a]if type(a)is str else a;y=d[b]if type(b)is str else b;d[n]=x+y if op=='+'else x-y if op=='-'else x*y
 return d

def evaluate(packet,values,*,signed=False,root=None,repo):
 p=checked(packet,root=root,repo=repo);v=_values(p,values,signed);return _run(p['polynomial_source'],v)[p['output']]
def polynomial_source(packet,*,root=None,repo):return checked(packet,root=root,repo=repo)['polynomial_source']
def _restored(p,values):
 v=dict(values)
 F=lambda a,b:(a+b)*(a+b+1)+2*b+2
 for i in range(p['N']):
  a,b,c,y=[v[f'r{i}_{f}']for f in('a','b','c','y')];d=F(a,b)
  v.update({f'r{i}_{k}':x for k,x in zip(FIELDS,(d,F(a,y),F(0,b),F(2*a+1,b),F(d,c)))})
 return v

def restore_constructors(packet,values,*,signed=False,root=None,repo):
 p=checked(packet,root=root,repo=repo);return _restored(p,_values(p,values,signed))
def project_parent_zero(packet,values,*,root=None,repo):
 p=checked(packet,root=root,repo=repo);old=canonical_parent(p['N'],cleanup=p['cleanup'],root=root,repo=repo);v=_values(old,values,False)
 need(_run(old['polynomial_source'],v)[old['output']]==0,'Parent natural zero required');out={k:v[k]for k in p['free']};need(_restored(p,out)==v,'Unique constructor graph');return out

def _poly(rows,env,flow):
 env=dict(env)
 for n,op,a,b in rows:
  x=env[a]if type(a)is str else flow.atom(a);y=env[b]if type(b)is str else flow.atom(b)
  env[n]=flow.times(x,y)if op=='*'else flow.plus(x,y,-1 if op=='-'else 1)
 return env

def _restored_polynomials(p,flow):
 env={v:flow.atom(v)for v in p['free']};add=flow.plus;mul=flow.times;constant=flow.atom
 def F(a,b):
  s=add(a,b);return add(add(mul(s,add(s,constant(1))),mul(constant(2),b)),constant(2))
 for i in range(p['N']):
  a,b,c,y=[env[f'r{i}_{f}']for f in('a','b','c','y')];d=F(a,b)
  env.update({f'r{i}_{k}':x for k,x in zip(FIELDS,(d,F(a,y),F(constant(0),b),F(add(mul(constant(2),a),constant(1)),b),F(d,c)))})
 return env

def verify(root,repo):
 root,m,flow=_context(root,repo);forms=[];rng=random.Random(151710);counts=dict(full_polynomial_graph_identities=0,retained_residual_identities=0,restored_definition_identities=0,whole_evaluations=0,signed_cases=0,rational_cases=0,natural_graph_restorations=0,genuine_zero_bijections=0,necessary_permutation_cases=0,padded_zero_bijections=0,guards=0,copies=0)
 for N in range(1,9):
  for cleanup in(False,True):
   old=m.build(N,cleanup=cleanup,root=root,repo=repo);p=build(N,cleanup=cleanup,root=root,repo=repo);need(exact(rewrite(old,root=root,repo=repo),p),'canonical full rewrite')
   restored=_restored_polynomials(p,flow);new=_poly(p['polynomial_source'],{v:flow.atom(v)for v in p['free']},flow);before=_poly(old['polynomial_source'],restored,flow)
   need(before[old['output']]==new[p['output']],'Complete polynomial graph identity');counts['full_polynomial_graph_identities']+=1
   cursor=0
   for i,r in enumerate(old['residuals']):
    if i in p['removed_parent_residual_indices']:need(before[r]=={},'Restored constructor residual identically zero');counts['restored_definition_identities']+=1
    else:need(before[r]==new[p['residuals'][cursor]],'Retained residual coefficient identity');cursor+=1;counts['retained_residual_identities']+=1
   for item in p['constructor_definitions']:
    need(new[item['computed_port']]==restored[item['coordinate']],'Every literal RHS equals handwritten constructor graph')
   deg=lambda poly:max(map(len,poly),default=0);need(deg(new[p['output']])==10,'Exact complete degree10');resdegrees=[deg(new[r])for r in p['residuals']]
   need([i for i,d in enumerate(resdegrees)if d==5]==[17*i+1 for i in range(N)]and all(d<=3 or i%17==1 for i,d in enumerate(resdegrees)),'Only constructor input rows attain degree5')
   highest={mon:v for mon,v in new[p['output']].items()if len(mon)==10};leader={}
   for i in range(N):
    power=flow.atom(1);s=flow.plus(flow.atom(f'r{i}_a'),flow.atom(f'r{i}_b'))
    for _ in range(8):power=flow.times(power,s)
    t=flow.atom(f'r{i}_t4');leader=flow.plus(leader,flow.times(flow.times(t,t),power))
   need(highest==leader and highest[tuple(sorted(['r0_a']*8+['r0_t4']*2))]==1,'Entire nonzero leading polynomial')
   need(p['certificate_ledger']['M']==old['certificate_ledger']['M']and p['certificate_ledger']['A']==old['certificate_ledger']['A']-5*N,'Only5N defining subtraction gates removed from certificate')
   for case in range(6):
    v={n:rng.randint(-2,3)if case<3 else rng.randint(0,3)for n in p['free']}
    if case==2:v={n:Fraction(x,3)for n,x in v.items()}
    back=_restored(p,v);value=_run(p['polynomial_source'],v)[p['output']];need(_run(old['polynomial_source'],back)[old['output']]==value,'Full evaluated graph identity')
    if case!=2:need(evaluate(p,v,signed=case<3,root=root,repo=repo)==value and restore_constructors(p,v,signed=case<3,root=root,repo=repo)==back,'Public graph interfaces')
    if case>=3:need(all(x>=0 for x in back.values()),'Unconditional natural graph restoration');counts['natural_graph_restorations']+=1
    counts['whole_evaluations']+=1;counts['signed_cases']+=case<3;counts['rational_cases']+=case==2
   forms.append(dict(packet=p,parent_ledger=old['polynomial_ledger'],saved_from_parent={k:old['polynomial_ledger'][k]-p['polynomial_ledger'][k]for k in('M','A','operations')},proof=dict(full_polynomial_terms=len(new[p['output']]),full_polynomial_sha256=hashlib.sha256(json.dumps([[list(mon),v]for mon,v in sorted(new[p['output']].items())],separators=(',',':')).encode()).hexdigest(),residual_degrees=resdegrees,highest_homogeneous_polynomial=[[list(mon),v]for mon,v in sorted(highest.items())])))
 kernel=flow.parent(repo);covered=set()
 for x,y in [(x,y)for x in range(8)for y in range(3)]+[(154,1),(10,10),(8,0),(1014,0)]:
  ev=kernel.Evaluation(budget=100,max_bits=256)
  try:z=ev.app(x,y)
  except(kernel.Exhausted,kernel.RepeatedActiveCall,RecursionError):continue
  covered.update(r['tag']for r in ev.records.values())
  for pad in(0,1):
   data=kernel.certificate(ev,(x,y),pad=pad);N=len(data);tri=m.build(N,root=root,repo=repo);flowvalues=flow.flatten(data,x,y,z,flow.root_flow(data));oldvalues=m.normalize_parent_zero(tri,flowvalues,root=root,repo=repo)
   if x==154:
    need(sum(flowvalues[k]for k in tri['fixed_parent_pointers'])>0,'Genuine fixture requires pointer permutation');counts['necessary_permutation_cases']+=1
   for cleanup in(False,True):
    p=build(N,cleanup=cleanup,root=root,repo=repo);v=project_parent_zero(p,oldvalues,root=root,repo=repo);need(evaluate(p,v,root=root,repo=repo)==0,'Genuine child zero');need(restore_constructors(p,v,root=root,repo=repo)==oldvalues,'Unique zero-fiber inverse');counts['genuine_zero_bijections']+=1;counts['padded_zero_bijections']+=pad==1
 need(covered==set(range(5)),'All five eager Tree rules exercised');counts['genuine_rule_tags']=sorted(covered)
 def reject(fn):
  try:fn()
  except(ValueError,TypeError,KeyError):counts['guards']+=1
  else:raise AssertionError('Malformed public call accepted')
 for N in(True,False,0,-1,1.0,'1',None):reject(lambda N=N:build(N,root=root,repo=repo))
 for cleanup in(0,1,'false',None):reject(lambda cleanup=cleanup:build(1,cleanup=cleanup,root=root,repo=repo))
 p=build(2,root=root,repo=repo);old=canonical_parent(2,root=root,repo=repo)
 for key in p:
  q=copy.deepcopy(p);q.pop(key);reject(lambda q=q:checked(q,root=root,repo=repo))
 for key in('source','free','residuals','constructor_definitions'):
  q=copy.deepcopy(p);q[key]=tuple(q[key]);reject(lambda q=q:checked(q,root=root,repo=repo))
 for key in('exact_degree','witnesses','residual_count'):
  q=copy.deepcopy(p);q[key]=float(q[key]);reject(lambda q=q:checked(q,root=root,repo=repo))
 q=copy.deepcopy(p);q['polynomial_source'][-1][1]='-';reject(lambda:checked(q,root=root,repo=repo))
 q=copy.deepcopy(old);q['free'].reverse();reject(lambda:rewrite(q,root=root,repo=repo))
 values={n:0 for n in p['free']}
 for value in(True,0.0,-1,Fraction(0)):
  v=dict(values);v['program']=value
  for fn in(evaluate,restore_constructors):reject(lambda fn=fn,v=v:fn(p,v,root=root,repo=repo))
 for v in ({},dict(values,extra=0),list(values)):
  reject(lambda v=v:evaluate(p,v,root=root,repo=repo))
 for signed in(0,1,None):reject(lambda signed=signed:restore_constructors(p,values,signed=signed,root=root,repo=repo))
 reject(lambda:project_parent_zero(p,{n:0 for n in old['free']},root=root,repo=repo))
 for key in('source','polynomial_source','free','residuals','constructor_definitions','historical_parent'):
  q=build(2,root=root,repo=repo);q[key].clear();need(exact(build(2,root=root,repo=repo),p),'No shared mutable packet');counts['copies']+=1
 q=restore_constructors(p,values,root=root,repo=repo);q['r0_a']=999;need(values['r0_a']==0,'Restoration copy');counts['copies']+=1
 q=polynomial_source(p,root=root,repo=repo);q.clear();need(exact(checked(p,root=root,repo=repo),p),'Source accessor copy');counts['copies']+=1
 with tempfile.TemporaryDirectory(prefix='tree_constructor_pins_')as temp:
  private=Path(temp)/'parents';private.mkdir();privaterepo=Path(temp)/'repo';kpath=privaterepo/KERNEL;kpath.parent.mkdir(parents=True);kdata=(Path(repo)/KERNEL).read_bytes();kpath.write_bytes(kdata)
  blobs={n:(root/n).read_bytes()for n in PINS}
  for n,data in blobs.items():(private/n).write_bytes(data)
  build(1,root=private,repo=privaterepo);counts['warm_pin_rejections']=0
  for n,data in blobs.items():
   path=private/n;path.write_bytes(data+b'\n');reject(lambda:build(1,root=private,repo=privaterepo));path.write_bytes(data);counts['warm_pin_rejections']+=1
  kpath.write_bytes(kdata+b'\n');reject(lambda:build(1,root=private,repo=privaterepo));counts['warm_pin_rejections']+=1
 proc=subprocess.run([sys.executable,'-O',str(Path(__file__).resolve())],capture_output=True,text=True,timeout=30);need(proc.returncode!=0 and 'Run without -O'in proc.stderr,'Optimized mode rejected');counts['optimized_rejections']=1
 return dict(status='PASS_EAGER_TREE_CONSTRUCTOR_PROJECTION',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_pins=PINS,kernel_path=KERNEL,kernel_sha256=KERNEL_SHA,counts=counts,forms=forms,scope='Complete natural graph projection of five unconditional constructor coordinates per row. All-value full SOS restoration; natural zero-fiber bijection to triangular parent and same represented triples at external N. Degree10/cost tradeoff, no fixed-arity universality or unique computation fibers.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--repo',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root,a.repo)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Exact typed saved receipt mismatch')
 a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':out['status'],'counts':out['counts'],'ledgers':[[f['packet']['N'],f['packet']['cleanup'],f['packet']['polynomial_ledger']['operations']]for f in out['forms']]},sort_keys=True))
if __name__=='__main__':main()
