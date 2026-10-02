#!/usr/bin/env python3
"""Bounded independent complete-source/API review of frozen joint-affine536."""
import argparse,copy,hashlib,importlib.util,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path
CUTS=('J','S','Dir','W','WD','Qdev','Ndev')
SOURCE_SHA='eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330'
PINS={'u15_packed_downstream561.py':'c4411ccfc9b62b1d8efe366686b99d4287031378b3acc0f5c07a1c10c52ef126',
      'u15_packed_joint_affine586.py':'3467d394885167260ca7f85f2b23033661de056bdba1959a45c9fc15ff516d2a'}
if not __debug__:raise RuntimeError('Assertions required')
sys.dont_write_bytecode=True

def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def authenticate(source,root):
 if not source.is_file() or hashlib.sha256(source.read_bytes()).hexdigest()!=SOURCE_SHA:raise ValueError('Frozen 536 source changed or missing')
 for name,wanted in PINS.items():
  path=source.parent/name
  if not path.is_file():path=root/name
  if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=wanted:raise ValueError('Frozen dependency changed or missing: '+name)

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def affine(p,node):
 rows={n:(op,a,b) for n,op,a,b in p['source']};cache={}
 def get(x):
  if type(x)is int:return {'':x} if x else {}
  if x not in rows:return {x:1}
  if x in cache:return cache[x]
  op,a,b=rows[x];aa=get(a);bb=get(b)
  if op in ('+','-'):
   v=dict(aa)
   for k,c in bb.items():v[k]=v.get(k,0)+(c if op=='+' else -c)
  elif set(aa)<={''}:v={k:aa.get('',0)*c for k,c in bb.items()}
  elif set(bb)<={''}:v={k:bb.get('',0)*c for k,c in aa.items()}
  else:raise AssertionError('Nonlinear cut')
  cache[x]={k:c for k,c in v.items() if c};return cache[x]
 return get(node)

def exact_dag(old,new):
 intern={}
 def node(k):
  if k not in intern:intern[k]=len(intern)
  return intern[k]
 def walk(p):
  cuts={p['registers'][name]:name for name in CUTS};env={n:node(('input',n)) for n in p['parameters']+p['auxiliaries']}
  def at(x):return env[x] if type(x)is str else node(('integer',x))
  for n,op,a,b in p['polynomial_source']:
   a,b=at(a),at(b)
   if op in ('+','*'):a,b=sorted((a,b))
   env[n]=node(('affine',cuts[n])) if n in cuts else node((op,a,b))
  return [[at(a),at(b)] for a,b in p['comparisons']],{key:{n:at(v) for n,v in p[key].items()} for key in ('registers','tag_registers','computed_loader_fields')},at(p['output'])
 assert walk(old)==walk(new)
 return len(intern)

def execute(p,v):
 env=dict(v)
 for n,op,a,b in p['polynomial_source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 at=lambda x:env[x] if type(x)is str else x
 return env[p['output']],[at(a)-at(b) for a,b in p['comparisons']],env

def source_check(p):
 known=set(p['parameters']+p['auxiliaries']);assert len(known)==len(p['parameters'])+len(p['auxiliaries'])
 for n,op,a,b in p['polynomial_source']:
  assert n not in known and op in ('+','-','*') and all(type(v)is int or type(v)is str and v in known for v in (a,b));known.add(n)
 needed={p['output']}
 for n,op,a,b in reversed(p['polynomial_source']):
  if n in needed:needed.update(v for v in (a,b) if type(v)is str)
 assert all(n in needed for n,op,a,b in p['polynomial_source'])
 for kind,key in (('certificate','source'),('polynomial','polynomial_source')):
  rows=p[key];assert p['ledger'][kind]==dict(operations=len(rows),M=sum(r[1]=='*' for r in rows),A=sum(r[1]!='*' for r in rows))
 rows=list(p['source']);sq=[]
 for i,(a,b) in enumerate(p['comparisons']):
  n=f'poly_res{i}';q=f'poly_sq{i}';rows.extend([(n,'-',a,b),(q,'*',n,n)]);sq.append(q)
 out=sq[0]
 for i,n in enumerate(sq[1:],1):q=f'poly_sum{i}';rows.append((q,'+',out,n));out=q
 assert rows==p['polynomial_source'] and out==p['output']
 degrees=[]
 for prime in (998244353,1000000007):
  env={n:(0 if n in p['fixed_parameters'] else 1,(i%5)+2,{n} if n in p['fixed_parameters'] else set()) for i,n in enumerate(p['parameters']+p['auxiliaries'])}
  at=lambda x:env[x] if type(x)is str else (0,x,set())
  for n,op,a,b in p['polynomial_source']:
   da,ca,sa=at(a);db,cb,sb=at(b)
   if op=='*':env[n]=(da+db,ca*cb%prime,sa|sb)
   else:
    d=max(da,db);env[n]=(d,((ca if da==d else 0)+(cb if db==d else 0)*(1 if op=='+' else -1))%prime,(sa if da==d else set())|(sb if db==d else set()))
  degree,coefficient,dependencies=env[p['output']];assert degree==1936 and coefficient and not dependencies
  degrees.append({'prime':prime,'degree':degree,'nonzero_evaluated_leader':coefficient,'fixed_parameter_dependencies':[]})
 return degrees

def run(source,root):
 source,root=Path(source).resolve(),Path(root).resolve();authenticate(source,root)
 mod=load(source,'independent536');rng=random.Random(1929536);counts={};forms=[]
 def add(k,n=1):counts[k]=counts.get(k,0)+n
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):add('malformed_rejected');return
  raise AssertionError('Malformed accepted')
 for ordinary in (False,True):
  p=mod.build(ordinary,root=root);old=mod.canonical_parent(ordinary,root=root);ancestor=mod.graph_ancestor(ordinary,root=root)
  assert p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries'] and p['rules']==old['rules']
  expected={}
  for name in CUTS:
   col={'S':1,'Dir':3,'W':4,'Qdev':0,'Ndev':2}.get(name)
   weights=[1 if name=='J' else r[3]*r[4] if name=='WD' else r[col]-(7 if name in ('Qdev','Ndev') else 0) for r in p['rules']]
   form={f'edge{i}':v for i,v in enumerate(weights) if v}
   if sum(weights):form['']=-sum(weights)
   assert affine(p,p['registers'][name])==affine(old,old['registers'][name])==form;expected[name]=form;add('exact_affine_matrices')
  nodes=exact_dag(old,p);add('complete_residual_and_SOS_DAG_identities');degree=source_check(p);add('independent_leading_certificates',len(degree))
  assert p['ledger']['polynomial']['operations']==(536 if ordinary else 338)
  assert p['ledger']['positive_witnesses']==(87 if ordinary else 51) and p['ledger']['equations']==(31 if ordinary else 11)
  assert p['canonical_parent']['file']=='u15_packed_downstream561.py' and p['graph_ancestor']['file']=='u15_packed_centered_states611.py'
  assert 'comparison_map' not in p and p['computed_loader_fields']==old['computed_loader_fields']
  assert len(p['ancestor_comparison_map'])==len(ancestor['comparisons'])
  for row in p['ancestor_comparison_map']:
   assert tuple(row['old_pair'])==tuple(ancestor['comparisons'][row['old_index']])
   if row['new_index'] is not None:assert tuple(row['child_pair'])==tuple(p['comparisons'][row['new_index']])
  for case in range(32):
   signed=case>=16;v={n:rng.randrange(-4,7) if signed else rng.randrange(1,8) for n in p['parameters']+p['auxiliaries']}
   a,rr,_=execute(p,v);b,ro,_=execute(old,v);assert a==b and rr==ro
   assert mod.evaluate(p,v,signed=signed,root=root)==a
   full=mod.restore_ancestor_assignment(p,v,signed=signed,root=root)
   assert mod.project_ancestor_assignment(p,full,signed=signed,root=root)==v
   ap,ar,_=execute(ancestor,full);correction=0
   for row in p['ancestor_comparison_map']:
    i=row['new_index']
    if i is None:assert ar[row['old_index']]==0
    else:
     assert ar[row['old_index']]==row['factor']*rr[i]
     if row['factor']==2:correction+=3*rr[i]**2
   assert ap==a+correction
   assert mod.identity(p,v,signed=signed,root=root)['common_output']==a
   assert mod.ancestor_identity(p,v,signed=signed,root=root)['parent_output']==ap
   add('full_parent_and_ancestor_cases');add('scalar_parent_residuals',len(rr));add('signed_cases',int(signed))
  v={n:1 for n in p['parameters']+p['auxiliaries']}
  for name in list(v)[::7]:
   for bad in (True,1.0,None,-1):
    w=dict(v);w[name]=bad;reject(lambda w=w:mod.evaluate(p,w,root=root))
  for method in (mod.build,mod.canonical_parent,mod.graph_ancestor):
   for bad in (1,0,None,'yes'):reject(lambda method=method,bad=bad:method(bad,root=root))
  for bad in (1,0,None):
   reject(lambda bad=bad:mod.evaluate(p,v,signed=bad,root=root))
   reject(lambda bad=bad:mod.project_ancestor_assignment(p,mod.restore_ancestor_assignment(p,v,root=root),require_graph=bad,root=root))
  for field in ('canonical_parent','graph_ancestor','ancestor_comparison_map','source_lineage','computed_loader_fields','registers','affine_rewrite'):
   q=copy.deepcopy(p);q[field]=None;reject(lambda q=q:mod.checked(q,root=root))
  q=copy.deepcopy(p)
  for i,row in enumerate(q['source']):
   at=next((j for j in (2,3) if type(row[j])is int),None)
   if at is not None:
    changed=list(row);changed[at]=float(changed[at]);q['source'][i]=tuple(changed);break
  huge={n:10**100 for n in v};reject(lambda:mod.evaluate(q,huge,root=root))
  for method in (mod.build,mod.canonical_parent,mod.graph_ancestor):
   copy1=method(ordinary,root=root);copy2=method(ordinary,root=root);copy2['registers'].clear();copy2['source'].clear();assert copy1==method(ordinary,root=root);add('defensive_copy_checks')
  full=mod.restore_ancestor_assignment(p,v,root=root)
  for name in p['computed_loader_fields']:
   bad=dict(full);bad[name]+=1;reject(lambda bad=bad:mod.project_ancestor_assignment(p,bad,root=root))
   assert mod.project_ancestor_assignment(p,bad,require_graph=False,root=root)==v;add('explicit_nongraph_projection_cases')
  forms.append({'ordinary':ordinary,'ledger':p['ledger'],'affine_forms':expected,'expression_nodes':nodes,'independent_degree':degree})
 # Private copies exercise source checks after all canonical caches are warm.
 with tempfile.TemporaryDirectory(prefix='joint536-warm-') as td:
  td=Path(td)
  for name in ('u15_packed_joint_affine536.py','u15_packed_downstream561.py','u15_packed_joint_affine586.py','u15_packed_centered_states611.py'):
   candidate=source.parent/name
   if not candidate.is_file():candidate=root/name
   shutil.copyfile(candidate,td/name)
  warm=load(td/source.name,'warm_joint536');baseline=warm.build(True,root=root)
  for name in ('u15_packed_joint_affine586.py','u15_packed_downstream561.py','u15_packed_centered_states611.py'):
   path=td/name;before=path.read_bytes()
   try:
    path.write_bytes(before+b'\n# private warm-cache mutation\n')
    reject(lambda:warm.build(True,root=root));add('warm_source_pin_rejections')
   finally:path.write_bytes(before)
   assert warm.build(True,root=root)==baseline
 return {'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'counts':counts,'forms':forms,'scope':'Independent exact affine/DAG proof and bounded API/ancestor/degree checks;561 positivity proof reviewed separately.'}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--source',type=Path,required=True,help='Frozen u15_packed_joint_affine536.py')
 p.add_argument('--root',type=Path,required=True,help='Maintained native-stream-queue dependency directory')
 p.add_argument('--output',type=Path,required=True,help='Fresh independent review JSON')
 p.add_argument('--expect',type=Path,help='Optional full saved JSON for exact type-sensitive comparison')
 a=p.parse_args();r=run(a.source,a.root)
 if a.expect is not None and not exact(r,json.loads(a.expect.read_text())):raise ValueError('Saved independent receipt differs')
 a.output.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({'status':r['status'],'source_sha256':r['source_sha256'],'counts':r['counts']},indent=2))
