#!/usr/bin/env python3
"""Portable independent full-source review of the frozen factored-index compiler."""
import argparse,copy,hashlib,importlib.util,json,random,shutil,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions required')
SOURCE_SHA='ed716945027275990e5aff1f7d4d180533af3e44b2a8c1862c3db4a7db7cf954'
PARENT_SHA='eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330'
AFFINE_SHA='ffc6c36ee9ee4fc5701d9d6c9422e4fbc29aaa7f9bbea4e768fc1e2831aa2e44'
INPUTS=('native__scaled_A','native__q','native__padded_B','native__F3')
CUT='native__bs_packed'
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def pin(path,wanted):
 if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=wanted:raise ValueError('Pinned source changed: '+path.name)
def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def execute(p,v):
 env=dict(v)
 for n,op,a,b in p['polynomial_source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 at=lambda x:env[x] if type(x)is str else x
 return env[p['output']],[at(a)-at(b) for a,b in p['comparisons']],env
def local_rows(p):
 rows={r[0]:r for r in p['source']};needed=set()
 def visit(n):
  if type(n)is not str or n in INPUTS or n in needed:return
  assert n in rows;needed.add(n)
  for x in rows[n][2:]:visit(x)
 visit(CUT);return [r for r in p['source'] if r[0]in needed]
def sparse(rows):
 z=(0,0,0,0);env={name:{tuple(int(i==j) for i in range(4)):1} for j,name in enumerate(INPUTS)}
 def at(x):return env[x] if type(x)is str else ({z:x} if x else {})
 for n,op,a,b in rows:
  a,b=at(a),at(b);r={}
  if op=='*':
   for aa,c in a.items():
    for bb,d in b.items():
     key=tuple(x+y for x,y in zip(aa,bb));r[key]=r.get(key,0)+c*d
  else:
   r=dict(a)
   for k,v in b.items():r[k]=r.get(k,0)+(v if op=='+' else -v)
  env[n]={k:v for k,v in r.items() if v}
 return env[CUT]
def full_dag(old,new):
 nodes={}
 def node(k):
  if k not in nodes:nodes[k]=len(nodes)
  return nodes[k]
 def walk(p):
  env={n:node(('input',n)) for n in p['parameters']+p['auxiliaries']}
  def at(x):return env[x] if type(x)is str else node(('int',x))
  for n,op,a,b in p['polynomial_source']:
   a,b=at(a),at(b)
   if op in ('+','*'):a,b=sorted((a,b))
   env[n]=node(('proved index',)) if n==CUT else node((op,a,b))
  return ([env[n] for n in INPUTS],[(at(a),at(b)) for a,b in p['comparisons']],{key:{k:at(v) for k,v in p[key].items()} for key in ('registers','tag_registers','computed_loader_fields')},env[p['output']])
 assert walk(old)==walk(new);return len(nodes)
def degree_and_source(p):
 known=set(p['parameters']+p['auxiliaries']);assert len(known)==len(p['parameters'])+len(p['auxiliaries'])
 for n,op,a,b in p['polynomial_source']:
  assert n not in known and op in ('+','-','*') and all(type(x)is int or type(x)is str and x in known for x in (a,b));known.add(n)
 live={p['output']}
 for n,op,a,b in reversed(p['polynomial_source']):
  if n in live:live.update(v for v in (a,b) if type(v)is str)
 assert all(n in live for n,op,a,b in p['polynomial_source'])
 rows=list(p['source']);squares=[]
 for i,(a,b) in enumerate(p['comparisons']):
  n=f'poly_res{i}';q=f'poly_sq{i}';rows.extend([(n,'-',a,b),(q,'*',n,n)]);squares.append(q)
 out=squares[0]
 for i,n in enumerate(squares[1:],1):q=f'poly_sum{i}';rows.append((q,'+',out,n));out=q
 assert rows==p['polynomial_source'] and out==p['output']
 for k,field in (('certificate','source'),('polynomial','polynomial_source')):
  rows=p[field];assert p['ledger'][k]=={'operations':len(rows),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows)}
 leaders=[]
 for prime in (998244353,1000000007):
  env={n:(0 if n in p['fixed_parameters'] else 1,(i%5)+2,{n} if n in p['fixed_parameters'] else set()) for i,n in enumerate(p['parameters']+p['auxiliaries'])}
  at=lambda x:env[x] if type(x)is str else (0,x,set())
  for n,op,a,b in p['polynomial_source']:
   da,ca,sa=at(a);db,cb,sb=at(b)
   if op=='*':env[n]=(da+db,ca*cb%prime,sa|sb)
   else:
    d=max(da,db);env[n]=(d,((ca if da==d else 0)+(cb if db==d else 0)*(1 if op=='+' else -1))%prime,(sa if da==d else set())|(sb if db==d else set()))
  d,c,dep=env[p['output']];assert d==1936 and c and not dep
  leaders.append({'prime':prime,'exact_degree':d,'nonzero_leader':c,'fixed_parameter_dependencies':[]})
 return leaders
def run(source,root,affine):
 source,root,affine=map(lambda p:Path(p).resolve(),(source,root,affine));pin(source,SOURCE_SHA);pin(affine,AFFINE_SHA)
 parent=source.parent/'u15_packed_joint_affine536.py'
 if not parent.is_file():parent=root/parent.name
 pin(parent,PARENT_SHA);m=load(source,'independent532');a=load(affine,'independent_binary_affine');rng=random.Random(5320523);counts={};forms=[]
 def add(k,n=1):counts[k]=counts.get(k,0)+n
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):add('malformed_rejected');return
  raise AssertionError('Malformed accepted')
 expected={(1,1,0,0):1,(1,0,0,0):-1,(0,1,0,0):13,(0,0,0,0):-13,(0,2,1,0):1,(0,0,1,0):-1,(0,3,0,1):1,(0,2,0,1):-1,(0,1,0,1):-1,(0,0,0,1):1}
 for ordinary in (False,True):
  p=m.build(ordinary,root=root);old=m.canonical_parent(ordinary,root=root);before=local_rows(old);after=local_rows(p)
  assert len(before)==12 and len(after)==8 and sparse(before)==sparse(after)==expected;add('exact_local_polynomial_identities')
  oldprivate={r[0] for r in before}-{CUT};assert {r[0]:r for r in old['source'] if r[0]not in oldprivate|{CUT}}=={r[0]:r for r in p['source'] if r[0]not in {r[0] for r in after}}
  nodes=full_dag(old,p);add('full_residual_and_SOS_DAG_identities');leaders=degree_and_source(p);add('nonzero_leading_certificates',2)
  assert p['ledger']['polynomial']['operations']==(532 if ordinary else 334)
  assert p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries'] and p['rules']==old['rules']
  assert 'computed_truth_fields' not in p and 'computed_definitions' not in p
  assert p['proof_only_truth_reconstruction']['rows']==before[:6]
  assert p['proof_only_truth_reconstruction']['fields']==('native__F0','native__F1','native__F2')
  assert p['canonical_parent']=={'file':parent.name,'sha256':PARENT_SHA}
  def metadata(x,key):
   if type(x)is str:assert x not in oldprivate,(key,x)
   elif type(x)in(list,tuple):
    for v in x:metadata(v,key)
   elif type(x)is dict:
    for k,v in x.items():metadata(k,key);metadata(v,key)
  for k,v in p.items():
   if k not in ('proof_only_truth_reconstruction','removed_comparisons'):metadata(v,k)
  assert p['removed_comparisons']==old['removed_comparisons'];add('historical_metadata_scope_checks')
  child,proof=a.rewrite(p);assert child['ledger']['polynomial']['operations']==(523 if ordinary else 325);add('binary_affine_compositions')
  for case in range(24):
   signed=case>=12;v={n:rng.randrange(-5,8) if signed else rng.randrange(1,8) for n in p['parameters']+p['auxiliaries']}
   x,rr,env=execute(p,v);y,ro,oldenv=execute(old,v);z,rc,_=execute(child,v)
   assert x==y==z and rr==ro==rc and env[CUT]==oldenv[CUT]
   assert m.evaluate(p,v,signed=signed,root=root)==x and m.identity(p,v,signed=signed,root=root)['common_output']==x
   for n,op,left,right in p['proof_only_truth_reconstruction']['rows']:
    left=env[left] if type(left)is str else left;right=env[right] if type(right)is str else right;env[n]=left+right if op=='+' else left-right
    assert env[n]==oldenv[n]
   add('complete_parent_and_composed_cases');add('signed_cases',int(signed));add('scalar_residual_identities',len(rr));add('historical_truth_reconstruction_rows',6)
  v={n:1 for n in p['parameters']+p['auxiliaries']}
  if not ordinary:
   v['L0']=v['R0']=0;assert m.evaluate(p,v,root=root)==execute(p,v)[0];add('raw_zero_boundary')
  for n in list(v)[::7]:
   for bad in (True,1.0,None,-1):
    vv=dict(v);vv[n]=bad;reject(lambda vv=vv:m.evaluate(p,vv,root=root))
  for method in (m.build,m.canonical_parent):
   for bad in (0,1,None,'yes'):reject(lambda method=method,bad=bad:method(bad,root=root))
  for bad in (0,1,None):reject(lambda bad=bad:m.evaluate(p,v,signed=bad,root=root))
  for key in ('proof_only_truth_reconstruction','source','comparisons','registers','canonical_parent','source_lineage'):
   q=copy.deepcopy(p);q[key]=None;reject(lambda q=q:m.checked(q,root=root))
  q=copy.deepcopy(p);i=next(i for i,r in enumerate(q['source']) if r[0]=='packed_A_plus_one');q['source'][i]=(*q['source'][i][:3],13.0);huge={n:10**100 for n in v};reject(lambda:m.evaluate(q,huge,root=root))
  for method in (m.build,m.canonical_parent):
   x=method(ordinary,root=root);y=method(ordinary,root=root);y['source'].clear();y['registers'].clear();assert x==method(ordinary,root=root);add('defensive_copy_checks')
  fresh=m.polynomial_source(p,root=root);fresh.clear();assert m.polynomial_source(p,root=root)==p['polynomial_source'];add('defensive_copy_checks')
  forms.append({'ordinary':ordinary,'ledger':p['ledger'],'composed_binary_ledger':child['ledger'],'local_monomials':[[list(k),v] for k,v in sorted(expected.items())],'complete_expression_nodes':nodes,'degree':leaders,'affine_composition_proof':proof})
 with tempfile.TemporaryDirectory(prefix='factored532-warm-') as tmp:
  tmp=Path(tmp);shutil.copyfile(source,tmp/'u15_packed_factored_index532.py')
  for name in ('u15_packed_joint_affine536.py','u15_packed_downstream561.py'):
   src=source.parent/name
   if not src.is_file():src=root/name
   shutil.copyfile(src,tmp/name)
  warm=load(tmp/'u15_packed_factored_index532.py','warm532');baseline=warm.build(True,root=root)
  for name in ('u15_packed_joint_affine536.py','u15_packed_downstream561.py'):
   path=tmp/name;data=path.read_bytes()
   try:path.write_bytes(data+b'\n# private warm-cache edit\n');reject(lambda:warm.build(True,root=root));add('warm_source_pin_checks')
   finally:path.write_bytes(data)
   assert warm.build(True,root=root)==baseline
 return {'status':'PASS','source_sha256':SOURCE_SHA,'parent_sha256':PARENT_SHA,'affine_helper_sha256':AFFINE_SHA,'counts':counts,'forms':forms}
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 for name in ('source','root','affine','output'):ap.add_argument('--'+name,type=Path,required=True)
 ap.add_argument('--expect',type=Path);args=ap.parse_args();r=run(args.source,args.root,args.affine)
 if args.expect is not None and not exact(r,json.loads(args.expect.read_text())):raise ValueError('Saved independent receipt differs')
 args.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
