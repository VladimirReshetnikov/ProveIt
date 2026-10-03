#!/usr/bin/env python3
"""Portable independent actual-source composition/degree/guard review of511."""
import argparse,copy,hashlib,importlib.util,itertools,json,random,shutil,struct,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions required')
PIN='234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38'
PINS={'u15_packed_factored_index532.py':'ed716945027275990e5aff1f7d4d180533af3e44b2a8c1862c3db4a7db7cf954','u15_joint_binary_affine_rewrite.py':'ffc6c36ee9ee4fc5701d9d6c9422e4fbc29aaa7f9bbea4e768fc1e2831aa2e44','u15_packed_unit_product524.py':'667de9e6648af91c2fa1fe22801786fb78fd82156bce3132be05e9f10e513611'}
CUTS=('J','S','Dir','W','WD','Qdev','Ndev')
def pin(path,wanted):
 if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=wanted:raise ValueError('Pinned source changed: '+path.name)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def execute(rows,v):
 e=dict(v)
 for n,op,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e
def at(env,v):return env[v] if type(v)is str else v
def affine(p,node):
 rows={n:(op,a,b) for n,op,a,b in p['source']};cache={}
 def f(x):
  if type(x)is int:return {'':x} if x else {}
  if x not in rows:return {x:1}
  if x in cache:return cache[x]
  op,a,b=rows[x];a,b=f(a),f(b)
  if op in ('+','-'):
   z=dict(a)
   for k,v in b.items():z[k]=z.get(k,0)+(v if op=='+' else -v)
  elif set(a)<={''}:z={k:a.get('',0)*v for k,v in b.items()}
  else:assert set(b)<={''};z={k:b.get('',0)*v for k,v in a.items()}
  cache[x]={k:v for k,v in z.items() if v};return cache[x]
 return f(node)
def exact_dag(old,new):
 nodes={}
 def nd(k):
  if k not in nodes:nodes[k]=len(nodes)
  return nodes[k]
 def walk(p):
  cuts={p['registers'][k]:k for k in CUTS};env={n:nd(('input',n)) for n in p['parameters']+p['auxiliaries']}
  def get(x):return env[x] if type(x)is str else nd(('int',x))
  for n,op,a,b in p['polynomial_source']:
   a,b=get(a),get(b)
   if op in ('+','*'):a,b=sorted((a,b))
   env[n]=nd(('cut',cuts[n])) if n in cuts else nd((op,a,b))
  return ([(get(a),get(b)) for a,b in p['comparisons']],{key:{k:get(v) for k,v in p[key].items()} for key in ('registers','tag_registers','computed_loader_fields')},get(p['output']))
 assert walk(old)==walk(new);return len(nodes)
def trim(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x
def poly_run(p,prime,offset):
 # Literal complete univariate specialization; exact64-bit carry-free convolution.
 def plus(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
 def times(a,b):
  assert min(len(a),len(b))*(prime-1)**2<2**64
  aa=int.from_bytes(struct.pack('<'+'Q'*len(a),*a),'little');bb=int.from_bytes(struct.pack('<'+'Q'*len(b),*b),'little');size=len(a)+len(b)-1
  return trim([v%prime for v in struct.unpack('<'+'Q'*size,(aa*bb).to_bytes(size*8,'little'))])
 e={n:[i+2+offset] if n in p['fixed_parameters'] else [(i+offset)%11,(i%7)+1] for i,n in enumerate(p['parameters']+p['auxiliaries'])};e={n:[v%prime for v in x] for n,x in e.items()}
 for n,op,a,b in p['polynomial_source']:
  a=e[a] if type(a)is str else [a%prime];b=e[b] if type(b)is str else [b%prime];e[n]=times(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
 out=e[p['output']];return {'prime':prime,'offset':offset,'degree':len(out)-1,'nonzero_leader':out[-1],'factor_degrees':{m['factor']:len(e[m['factor']])-1 for m in p.get('unit_factors',[])}}
def source_check(p):
 known=set(p['parameters']+p['auxiliaries']);assert len(known)==len(p['parameters'])+len(p['auxiliaries'])
 for n,op,a,b in p['polynomial_source']:
  assert n not in known and op in ('+','-','*') and all(type(x)is int or type(x)is str and x in known for x in (a,b));known.add(n)
 live={p['output']}
 for n,op,a,b in reversed(p['polynomial_source']):
  if n in live:live.update(x for x in (a,b) if type(x)is str)
 assert all(n in live for n,op,a,b in p['polynomial_source'])
 for key,field in (('certificate','source'),('polynomial','polynomial_source')):
  rows=p[field];assert p['ledger'][key]=={'operations':len(rows),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows)}
 rows=list(p['source']);pairs=p['comparisons'];squares=[]
 if p.get('finalizer')=='anchor':
  last=1
  for i,(a,b) in enumerate(pairs[:-1]):
   n=f'unit_res{i}';q=f'unit_sq{i}';s=f'unit_anchor{i}';rows.extend([(n,'-',a,b),(q,'*',n,n),(s,'+',last,q)]);last=s
  rows.extend([('unit_times_anchor','*',p['unit_product_register'],last),('unit_polynomial','-','unit_times_anchor',1)]);out='unit_polynomial'
 else:
  for i,(a,b) in enumerate(pairs):
   n=f'poly_res{i}';q=f'poly_sq{i}';rows.extend([(n,'-',a,b),(q,'*',n,n)]);squares.append(q)
  out=squares[0]
  for i,n in enumerate(squares[1:],1):q=f'poly_sum{i}';rows.append((q,'+',out,n));out=q
 assert rows==p['polynomial_source'] and out==p['output']
def run(source,root):
 source,root=Path(source).resolve(),Path(root).resolve();pin(source,PIN);paths={}
 for name,wanted in PINS.items():
  path=source.parent/name
  if not path.is_file():path=root/name
  pin(path,wanted);paths[name]=path
 m=load(source,'independent_composition511');rng=random.Random(5112036);counts={};records=[]
 def add(k,n=1):counts[k]=counts.get(k,0)+n
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):add('malformed_rejected');return
  raise AssertionError('Malformed accepted')
 for a,c,d in itertools.product(range(4),repeat=3):assert (d*d-(a*a+4*a+3)*c*c)%4!=3;add('main_mod4_cases')
 for t,v,y in itertools.product(range(4),repeat=3):assert (t*t*(v*v-y*y)+y*y)%4!=3;add('auxiliary_mod4_cases')
 for ordinary in (False,True):
  old=m.canonical_parent(ordinary,root=root);middle=m.build(ordinary,grouped=False,root=root)
  for k in CUTS:
   weights=[1 if k=='J' else r[3]*r[4] if k=='WD' else r[{'S':1,'Dir':3,'W':4,'Qdev':0,'Ndev':2}[k]]-(7 if k in ('Qdev','Ndev') else 0) for r in old['rules']]
   want={f'edge{i}':v for i,v in enumerate(weights) if v}
   if sum(weights):want['']=-sum(weights)
   assert affine(old,old['registers'][k])==affine(middle,middle['registers'][k])==want;add('exact_affine_vectors')
  nodes=exact_dag(old,middle);add('exact_affine_full_DAG_identities')
  for grouped in (False,True):
   p=m.build(ordinary,grouped=grouped,root=root);source_check(p);add('complete_source_and_finalizer_checks')
   assert p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries'] and p['rules']==old['rules']
   assert p['canonical_parent']=={'file':'u15_packed_factored_index532.py','sha256':PINS['u15_packed_factored_index532.py']}
   assert p['composition']['arithmetic_parent_operations']==(523 if ordinary else 325)
   assert p['ledger']['polynomial']['operations']==((511 if ordinary else 323) if grouped else (523 if ordinary else 325))
   assert p['ledger']['positive_witnesses']==(87 if ordinary else 51) and p['ledger']['equations']==((25 if ordinary else 10) if grouped else (31 if ordinary else 11))
   removed=set();maps=[]
   if grouped:
    prefixes=(['input__geo__','input__and__'] if ordinary else [])+['native__']
    for prefix in prefixes:
     for kind,left,right in [('main','L15','R15'),('auxiliary','L17','P17')]:
      pair=(prefix+left,prefix+right);idx=old['comparisons'].index(pair);maps.append((idx,'unit_'+prefix+kind,1,kind,prefix))
    if ordinary:maps.append((old['comparisons'].index(('input__and__bs_q','input__and__q')),'unit_loader_checksum',-1,'checksum',None))
    assert [(x['old_index'],x['factor'],x['residual_sign'],x['kind'],x.get('prefix')) for x in p['unit_factors']]==maps
    removed={i for i,*_ in maps};remaining=[i for i in range(len(old['comparisons'])) if i not in removed]
    assert [r['old_index'] for r in p['unit_retained_comparison_map']]==remaining
    assert p['comparisons'][:-1]==[middle['comparisons'][i] for i in remaining] and p['comparisons'][-1]==(p['unit_product_register'],1)
    for i,rec in enumerate(p['unit_retained_comparison_map']):assert rec['new_index']==i and rec['pair']==p['comparisons'][i]
    assert 'ancestor_comparison_map' not in p and p['pre_unit_ancestor_comparison_map']==middle['ancestor_comparison_map']
    assert p['finalizer']==('anchor' if ordinary else 'sos')
    if ordinary:assert p['loader_comparison_count']==15 and all(all(type(x)is int or x.startswith('input__') for x in row) for row in p['comparisons'][:15])
   else:
    assert 'unit_factors' not in p and 'pre_unit_ancestor_comparison_map' not in p
    assert p['ancestor_comparison_map']==middle['ancestor_comparison_map']
    if ordinary:assert p['loader_comparison_count']==20
   assert p['outer_comparison_count']==5;add('current_and_historical_metadata_checks')
   for case in range(16):
    signed=case>=8;v={n:rng.randrange(-4,6) if signed else rng.randrange(1,6) for n in p['parameters']+p['auxiliaries']}
    if not ordinary and not signed:v['L0']=case%2;v['R0']=(case//2)%2
    a=execute(old['polynomial_source'],v);b=execute(p['polynomial_source'],v);res=[at(a,x)-at(a,y) for x,y in old['comparisons']]
    assert a[old['output']]==sum(r*r for r in res)
    if grouped:
     U=1
     for i,name,sign,kind,prefix in maps:
      factor=1+sign*res[i];assert b[name]==factor
      if kind!='checksum':assert factor%4!=3
      U*=factor;add('unit_factor_identities')
     S=sum(r*r for i,r in enumerate(res) if i not in removed)
     for row in p['unit_retained_comparison_map']:
      x,y=p['comparisons'][row['new_index']];assert at(b,x)-at(b,y)==res[row['old_index']]
     expected=S+(U-1)**2 if p['finalizer']=='sos' else U*(1+S)-1
     assert U==b[p['unit_product_register']]
    else:expected=a[old['output']]
    assert b[p['output']]==expected and (expected==0)==(a[old['output']]==0)
    assert m.evaluate(p,v,signed=signed,root=root)==expected and m.identity(p,v,signed=signed,root=root)['child_output']==expected
    add('complete_parent_finalizer_cases');add('signed_cases',int(signed));add('parent_scalar_residuals',len(res))
   degrees=[poly_run(p,prime,offset) for prime,offset in ((1009,0),(1013,7))]
   target=(4881 if ordinary else 3464) if grouped else 1936
   assert all(r['degree']==target and r['nonzero_leader'] for r in degrees);add('literal_full_polynomial_specializations',2)
   v={n:1 for n in p['parameters']+p['auxiliaries']}
   for n in list(v)[::9]:
    for bad in (True,1.0,None,0,-1):
     if bad==0 and type(bad)is int and not ordinary and n in ('L0','R0'):continue
     vv=dict(v);vv[n]=bad;reject(lambda vv=vv:m.evaluate(p,vv,root=root))
   for bad in (0,1,None,0.0):
    reject(lambda bad=bad:m.build(bad,grouped=grouped,root=root));reject(lambda bad=bad:m.build(ordinary,grouped=bad,root=root));reject(lambda bad=bad:m.evaluate(p,v,signed=bad,root=root))
   for key in ('composition','canonical_parent','source_lineage','ledger','comparisons','grouped_units'):
    q=copy.deepcopy(p);q[key]=None;reject(lambda q=q:m.checked(q,root=root))
   if grouped:
    for key in ('unit_factors','unit_retained_comparison_map','pre_unit_ancestor_comparison_map'):
     q=copy.deepcopy(p);q[key]=None;reject(lambda q=q:m.checked(q,root=root))
   q=copy.deepcopy(p);i=next(i for i,r in enumerate(q['source']) if any(type(v)is int for v in r[2:]));row=list(q['source'][i]);j=next(j for j in (2,3) if type(row[j])is int);row[j]=float(row[j]);q['source'][i]=tuple(row)
   huge={n:10**100 for n in v};reject(lambda:m.evaluate(q,huge,root=root))
   q=m.build(ordinary,grouped=grouped,root=root);q['source'].clear();q['composition'].clear();assert m.build(ordinary,grouped=grouped,root=root)==p;add('defensive_copy_checks')
   q=m.polynomial_source(p,root=root);q.clear();assert m.polynomial_source(p,root=root)==p['polynomial_source'];add('defensive_copy_checks')
   records.append({'ordinary':ordinary,'grouped':grouped,'ledger':p['ledger'],'literal_degree_specializations':degrees,'affine_expression_nodes':nodes})
 with tempfile.TemporaryDirectory(prefix='composed511-warm-') as tmp:
  tmp=Path(tmp);shutil.copyfile(source,tmp/'u15_packed_composed_units511.py')
  for name,path in paths.items():shutil.copyfile(path,tmp/name)
  parent536=source.parent/'u15_packed_joint_affine536.py'
  if not parent536.is_file():parent536=root/parent536.name
  shutil.copyfile(parent536,tmp/parent536.name)
  warm=load(tmp/'u15_packed_composed_units511.py','warm511');canonical=warm.build(True,root=root)
  for name in (*PINS,parent536.name):
   path=tmp/name;data=path.read_bytes()
   try:path.write_bytes(data+b'\n# private warm-cache test\n');reject(lambda:warm.build(True,root=root));add('warm_dependency_pin_checks')
   finally:path.write_bytes(data)
   assert warm.build(True,root=root)==canonical
 return {'status':'PASS','source_sha256':PIN,'dependency_pins':PINS,'counts':counts,'forms':records,'scope':'Complete composition/source/domain/guard audit; underlying native universality proofs inherited, no full universal zero materialized.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 for name in ('source','root','output'):ap.add_argument('--'+name,type=Path,required=True)
 ap.add_argument('--expect',type=Path);args=ap.parse_args();r=run(args.source,args.root)
 if args.expect is not None and not exact(r,json.loads(args.expect.read_text())):raise ValueError('Saved receipt differs')
 args.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'counts':r['counts']},indent=2))
