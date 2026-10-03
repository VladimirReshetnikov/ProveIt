#!/usr/bin/env python3
"""Independent finite grouping and complete U15 frontier source review."""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import struct
import sys

SOURCE_SHA='8e0514876e26b716e792dd7d8332c773fe15989eb558fc7e4fedff8046249ccf'
RECEIPT_SHA='3f3fd17dcb0f36f19b83f7aba7d3ebe081926c73786015d498540bf225bc6fc0'
WEIGHTS=(12,78,332,726,898,834,65)
BASE_SOS_DEGREE=1936

def need(x,m):
 if not x:raise ValueError(m)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def trim(x):
 while len(x)>1 and x[-1]==0:x.pop()
 return x

def poly_run(packet,prime,offset):
 """All coefficients, with exact carry-free Kronecker convolution."""
 def plus(a,b,sign):
  return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
 def times(a,b):
  need(min(len(a),len(b))*(prime-1)**2<2**64,'Convolution digits may carry')
  aa=int.from_bytes(struct.pack('<'+'Q'*len(a),*a),'little');bb=int.from_bytes(struct.pack('<'+'Q'*len(b),*b),'little')
  length=len(a)+len(b)-1;raw=(aa*bb).to_bytes(length*8,'little')
  return trim([x%prime for x in struct.unpack('<'+'Q'*length,raw)])
 env={n:[i+2+offset] if n in packet['fixed_parameters'] else [(i+offset)%11,(i%7)+1] for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
 env={n:[x%prime for x in v] for n,v in env.items()}
 for n,op,a,b in packet['polynomial_source']:
  a=env[a] if type(a) is str else [a%prime];b=env[b] if type(b) is str else [b%prime]
  env[n]=times(a,b) if op=='*' else plus(a,b,1 if op=='+' else -1)
 out=env[packet['output']]
 return dict(prime=prime,offset=offset,degree=len(out)-1,leading_coefficient=out[-1],factor_degrees={m['factor']:len(env[m['factor']])-1 for m in packet['unit_factors']})

def uniform_upper(p):
 """Degree and formal leading-form dependency, without numeric coefficients."""
 rows={n:(op,a,b) for n,op,a,b in p['polynomial_source']}
 main={m['factor']:m['prefix'] for m in p['unit_factors'] if m['kind']=='main'}
 env={n:(0,{n}) if n in p['fixed_parameters'] else (1,set()) for n in p['parameters']+p['auxiliaries']}
 def at(x):return env[x] if type(x) is str else (0,set())
 def mul(a,b):return (a[0]+b[0],a[1]|b[1])
 def add(a,b):
  d=max(a[0],b[0]);return (d,(a[1] if a[0]==d else set())|(b[1] if b[0]==d else set()))
 for n,op,a,b in p['polynomial_source']:
  if n in main:
   prefix=main[n];name=lambda v:prefix+v
   expected={
    n:('-',name('L15'),name('Ac2')),
    name('L15'):('*',name('R14'),name('R14')),
    name('Ac2'):('*',name('A'),name('c2')),
    name('A'):('+',name('a_square'),name('a4m5')),
    name('a_square'):('*',name('R12'),name('R12')),
    name('c2'):('*',name('R10a'),name('R10a')),
    name('a4m5'):('+',name('a4'),3),name('a4'):('*',4,name('R12')),
    name('cam2'):('*',name('R10a'),name('R12')),
    name('D1'):('+',name('wn2'),name('cam2')),
    name('gam'):('*',name('ga'),name('a4m5')),
    name('R14'):('+',name('D1'),name('gam'))}
   need(all(rows[k]==v for k,v in expected.items()),'Main norm cancellation source changed')
   A,C,H=map(at,(name('R12'),name('R10a'),name('a4m5')))
   V=add(at(name('wn2')),mul(at(name('ga')),H))
   env[n]=add(add(mul(at(2),mul(mul(A,C),V)),mul(V,V)),mul(H,mul(C,C)))
  else:env[n]=mul(at(a),at(b)) if op=='*' else add(at(a),at(b))
 degree,deps=env[p['output']]
 need(not deps,'Highest homogeneous output may depend on fixed program')
 for item,weight in zip(p['unit_factors'],WEIGHTS):
  need(env[item['factor']]==(weight,set()),'Factor upper degree or parameter dependence differs')
 return dict(refined_upper_degree=degree,highest_form_fixed_parameter_dependencies=sorted(deps),literal_main_norm_cancellations=len(main))

def partitions(n):
 def grow(labels):
  if len(labels)==n:
   yield tuple(tuple(i for i,v in enumerate(labels) if v==j) for j in range(max(labels)+1));return
  for value in range(max(labels)+2):yield from grow(labels+[value])
 yield from grow([0])

def enumerate_plans():
 census=Counter();best={};total=0;allplans=[]
 for groups in partitions(7):
  g=len(groups);census[g]+=1;sums=[sum(WEIGHTS[i] for i in group) for group in groups]
  for anchor in (None,*range(g)):
   degree=max([BASE_SOS_DEGREE]+[2*w for w in sums]) if anchor is None else sums[anchor]+max([BASE_SOS_DEGREE]+[2*w for j,w in enumerate(sums) if j!=anchor])
   cost=509+2*g
   row=dict(groups=groups,anchor=anchor,operations=cost,degree=degree,group_weights=sums)
   if g not in best or degree<best[g]['degree']:best[g]=row
   total+=1;allplans.append(row)
 assert sum(census.values())==877 and total==4140
 assert [best[g]['degree'] for g in range(1,8)]==[4881,3120,2116,1936,1936,1936,1936]
 frontier=[best[g] for g in range(1,5)]
 # Pigeonhole and anchor lower bounds independent of the enumeration.
 assert min(726+834,726+898,834+898)==1560
 assert min(332+726,332+834,332+898,726+834,726+898,834+898)==1058
 assert 2945-968+2*968==3913>3120
 assert 1936+332>2116 and 2*1560>2116
 return dict(status='PASS',weights=WEIGHTS,retained_residuals=24,retained_SOS_degree=1936,
  partitions=sum(census.values()),finalizer_choices=total,group_count_census={str(k):v for k,v in sorted(census.items())},
  optimal_by_group_count=[best[g] for g in range(1,8)],frontier=frontier,plans=allplans,
  scope='Exhaustive disjoint partitions and single-anchor/SOS finalizers of these seven factors only; no unrestricted arithmetic or degree optimum.')

def execute(rows,values):
 env=dict(values)
 for n,op,a,b in rows:
  a=env[a] if type(a) is str else a;b=env[b] if type(b) is str else b
  env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return env

def check_source(p):
 rows=p['polynomial_source'];free=set(p['parameters']+p['auxiliaries']);known=set(free)
 for n,op,a,b in rows:
  need(n not in known and op in ('+','-','*'),'Bad emitted row')
  need(all(type(x) is int or type(x) is str and x in known for x in (a,b)),'Bad emitted dependency');known.add(n)
 live={p['output']}
 for n,op,a,b in reversed(rows):
  if n in live:live.update(x for x in (a,b) if type(x) is str)
 need(all(n in live for n,_,_,_ in rows) and free<=live,'Dead gate/free field')
 for kind,part in [('certificate',p['source']),('polynomial',rows)]:
  c=Counter(op for _,op,_,_ in part)
  need(p['ledger'][kind]==dict(operations=len(part),M=c['*'],A=c['+']+c['-']),'Wrong full gate charge')
 g=len(p['groups'])
 need(p['ledger']['polynomial']==dict(operations=509+2*g,M=211,A=298+2*g),'Grouping cost formula')
 need(len(p['comparisons'])==24+g and len(p['auxiliaries'])==87,'Changed comparison/witness dimensions')
 return sorted(free)

def _verify(source,root,receipt):
 source,root,receipt=map(Path,(source,root,receipt))
 need(hashlib.sha256(source.read_bytes()).hexdigest()==SOURCE_SHA,'Author source pin')
 need(hashlib.sha256(receipt.read_bytes()).hexdigest()==RECEIPT_SHA,'Author receipt pin')
 saved=json.loads(receipt.read_text());need(saved['source_sha256']==SOURCE_SHA,'Receipt/source mismatch')
 spec=importlib.util.spec_from_file_location('_partition_frontier_review',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 independent=enumerate_plans();counts=Counter();records=[]
 key=lambda groups,anchor:(tuple(tuple(g) for g in groups),anchor)
 expected={key(r['groups'],r['anchor']):(r['operations'],r['degree']) for r in independent['plans']}
 actual={key(r['groups'],r['anchor']):(r['operations'],r['degree']) for r in saved['forms']}
 need(actual==expected and len(saved['forms'])==len(expected)==4140,'Complete finite objective differs')
 need({tuple(tuple(g) for g in p) for p in m.partitions()}=={tuple(tuple(g) for g in p) for p in partitions(7)},'Partition enumeration differs')
 counts['independent_partitions']=877;counts['independent_finalizer_choices']=4140
 old=m.canonical_parent(root=root);need(old['ledger']['polynomial']['operations']==523,'Wrong complete parent')
 oldpairs=[tuple(x) for x in old['comparisons']]
 wanted=[]
 for prefix in ('input__geo__','input__and__','native__'):
  for kind,left,right in (('main','L15','R15'),('auxiliary','L17','P17')):
   wanted.append((oldpairs.index((prefix+left,prefix+right)),'unit_'+prefix+kind,1))
 wanted.append((oldpairs.index(('input__and__bs_q','input__and__q')),'unit_loader_checksum',-1))
 removed={i for i,_,_ in wanted};retained=[pair for i,pair in enumerate(oldpairs) if i not in removed]
 rng=random.Random(5171002)
 for entry in saved['frontier_compilers']:
  declared=entry['compiler'];p=m.build(declared['groups'],anchor=declared['anchor'],root=root)
  need(json.loads(json.dumps(p))==declared,'Saved full frontier source differs')
  need(p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries'],'Changed complete coordinate interface')
  free=check_source(p);need(p['comparisons'][:24]==retained,'Changed retained comparisons')
  need([x['factor'] for x in p['unit_factors']]==[n for _,n,_ in wanted],'Changed factor order')
  for case in range(40):
   signed=case>=20
   v={n:rng.randrange(-4,5) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   before=execute(old['polynomial_source'],v);after=execute(p['polynomial_source'],v)
   at=lambda env,x:env[x] if type(x) is str else x
   rr=[at(before,a)-at(before,b) for a,b in oldpairs]
   S=sum(r*r for i,r in enumerate(rr) if i not in removed);factors=[]
   for i,n,sign in wanted:
    f=1+sign*rr[i];need(after[n]==f,'Unit factor changed');factors.append(f);counts['factor_identities']+=1
   for a,b in retained:need(at(before,a)-at(before,b)==at(after,a)-at(after,b),'Retained residual changed');counts['retained_residual_identities']+=1
   products=[]
   for j,group in enumerate(p['groups']):
    value=1
    for i in group:value*=factors[i]
    products.append(value);reg=p['unit_group_map'][j]['register']
    need(after[reg]==value and tuple(p['comparisons'][24+j])==(reg,1),'Wrong emitted group product')
   anchor=p['anchor'];answer=S+sum((u-1)**2 for u in products) if anchor is None else products[anchor]*(1+S+sum((u-1)**2 for j,u in enumerate(products) if j!=anchor))-1
   need(after[p['output']]==answer and before[old['output']]==sum(r*r for r in rr),'Complete finalizer mismatch')
   need(m.evaluate(p,v,signed=signed,root=root)==answer,'Public evaluation mismatch')
   counts['full_frontier_outputs']+=1;counts['signed_frontier_outputs']+=signed
  uniform=uniform_upper(p)
  degrees=[poly_run(p,prime,offset) for prime,offset in ((1009,0),(1013,7))]
  objective=expected[key(p['groups'],p['anchor'])][1]
  need(uniform['refined_upper_degree']==objective,'Refined upper differs from finite objective')
  need(all(x['degree']==objective and x['leading_coefficient'] for x in degrees),'Literal full polynomial degree not attained')
  need(all(tuple(x['factor_degrees'][n] for _,n,_ in wanted)==WEIGHTS for x in degrees),'Actual factor degree differs')
  need(m.degree_audit(p,root=root)['exact_degree']==objective,'Public guarded degree differs')
  for name in ('source','polynomial_source','groups','anchor','unit_group_map','ledger'):
   bad=deepcopy(p);bad[name]=False
   try:m.degree_audit(bad,root=root)
   except (ValueError,TypeError,KeyError):counts['changed_frontier_rejections']+=1
   else:raise ValueError('Noncanonical degree caller accepted')
  records.append(dict(groups=p['groups'],anchor=p['anchor'],ledger=p['ledger'],exact_degree=objective,free_coordinates=free,uniform_fixed_program_degree=uniform,full_modular_polynomial_checks=degrees))
 need(sorted((x['ledger']['polynomial']['operations'],x['exact_degree']) for x in records)==[(511,4881),(513,3120),(515,2116),(517,1936)],'Wrong complete frontier')
 return dict(status='PASS',source_sha256=SOURCE_SHA,author_receipt_sha256=RECEIPT_SHA,counts=dict(counts),independent_group_census=independent['group_count_census'],independent_group_minima=independent['optimal_by_group_count'],frontier=records,scope='Independent finite objective enumeration and four literal complete frontier sources; no repeated full511 API audit and no full universal Pell zero fixture.')

def verify(source,root,receipt):
 before=dict(sys.modules);oldpath=list(sys.path);bases=[Path(source).resolve().parent,Path(root).resolve(),Path(root).resolve().parents[1]/'verification']
 try:return _verify(source,root,receipt)
 finally:
  sys.path[:]=oldpath
  for name,module in list(sys.modules.items()):
   filename=getattr(module,'__file__',None)
   if filename:
    try:local=any(Path(filename).resolve().is_relative_to(base) for base in bases)
    except (TypeError,ValueError,OSError):local=False
    if local and name not in before:sys.modules.pop(name,None)
  for name,module in before.items():
   if sys.modules.get(name) is not module:sys.modules[name]=module

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--receipt',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 result=json.loads(json.dumps(verify(a.source,a.root,a.receipt)))
 if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 if a.expect:need(exact(result,json.loads(a.expect.read_text())),'Review receipt differs')
 print(json.dumps(result,indent=2,sort_keys=True))
