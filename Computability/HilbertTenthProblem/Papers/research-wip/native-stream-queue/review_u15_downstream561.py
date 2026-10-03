#!/usr/bin/env python3
"""Independent bounded source/graph audit for the downstream561 compiler."""
import argparse
from collections import Counter
from contextlib import contextmanager
from copy import deepcopy
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

SOURCE_SHA = 'c4411ccfc9b62b1d8efe366686b99d4287031378b3acc0f5c07a1c10c52ef126'
PARENT_SHA = '3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce'
DEFS = {
 'input__q':'input__input_bound', 'input__J':'input__geo__geometry_index_bound',
 'input__P':'input__repunit_P', 'input__Ahat':'input__restored_Ahat',
 **{'input__geo__'+x:'input__geo__'+y for x,y in dict(a='R12',c='R10a',d='R14',k='R10b',s='geometry_odd').items()},
 **{'input__and__'+x:'input__and__'+y for x,y in dict(a='R12',c='R10a',d='R14',k='R10b',r='bs_packed',s='bs_odd').items()}}

def require(x,s):
 if not x: raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
@contextmanager
def loaded(path):
 before=dict(sys.modules); paths=list(sys.path)
 try:
  spec=importlib.util.spec_from_file_location('_independent_downstream_audit',path)
  mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);yield mod
 finally:
  sys.path[:]=paths
  for name,mod in list(sys.modules.items()):
   if name not in before and (name.startswith('_') or 'native' in str(getattr(mod,'__file__','')) or 'verification' in str(getattr(mod,'__file__',''))):sys.modules.pop(name,None)
  for name,mod in before.items():
   if sys.modules.get(name) is not mod:sys.modules[name]=mod

def execute(rows,v):
 e=dict(v)
 for n,op,a,b in rows:
  a=e[a] if type(a) is str else a;b=e[b] if type(b) is str else b
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e

def residuals(p,e):return [(e[a] if type(a) is str else a)-(e[b] if type(b) is str else b) for a,b in p['comparisons']]

def check_source(p):
 known=set(p['parameters']+p['auxiliaries']);free=set(known);rows=p['polynomial_source']
 require(len(known)==len(p['parameters'])+len(p['auxiliaries']),'Duplicate coordinates')
 for n,op,a,b in rows:
  require(type(n) is str and n not in known and op in ('+','-','*'),'Bad destination/op')
  require(all(type(v) is int or type(v) is str and v in known for v in (a,b)),'Bad operand')
  known.add(n)
 used={p['output']}
 for n,op,a,b in reversed(rows):
  if n in used:used.update(x for x in (a,b) if type(x) is str)
 require(all(n in used for n,_,_,_ in rows),'Dead gate')
 require(free<=used,'Unused free coordinate')
 tail=[];last=None
 for i,(a,b) in enumerate(p['comparisons']):
  r,s='poly_res'+str(i),'poly_sq'+str(i);tail.extend([(r,'-',a,b),(s,'*',r,r)])
  # Production emits all squares first; independent literal finalizer follows that order.
 sums=[];last='poly_sq0'
 for i in range(1,len(p['comparisons'])):
  n='poly_sum'+str(i);sums.append((n,'+',last,'poly_sq'+str(i)));last=n
 require(rows==p['source']+tail+sums and p['output']==last,'Literal complete SOS differs')
 c=Counter('M' if op=='*' else 'A' for _,op,_,_ in rows)
 require(p['ledger']['polynomial']==dict(operations=len(rows),M=c['M'],A=c['A']),'Unpaid operation')
 return dict(operations=len(rows),M=c['M'],A=c['A'],free_coordinates=len(free),equations=len(p['comparisons']))

def positive_bounds(p):
 # Sound lower bounds for nonnegative expressions; unknown lower bounds are None.
 low={n:1 for n in p['parameters']+p['auxiliaries']}
 for n,op,a,b in p['source']:
  aa=low.get(a) if type(a) is str else a;bb=low.get(b) if type(b) is str else b
  if op=='+':v=None if aa is None or bb is None else aa+bb
  elif op=='*':v=aa*bb if aa is not None and bb is not None and aa>=0 and bb>=0 else None
  else:v=aa-b if aa is not None and type(b) is int else None
  low[n]=v
 out={n:low[r] for n,r in DEFS.items()}
 require(all(type(v) is int and v>0 for v in out.values()),'Definition positivity not proved')
 return {n:str(v) for n,v in out.items()}

def verify(source,root):
 source=Path(source).resolve();root=Path(root).resolve()
 require(sha(source)==SOURCE_SHA,'Compiler source pin mismatch')
 parent=source.parent/'u15_packed_centered_states611.py'
 if not parent.is_file():parent=root/'u15_packed_centered_states611.py'
 require(sha(parent)==PARENT_SHA,'Parent source pin mismatch')
 rng=random.Random(561202610);counts=Counter();forms=[]
 with loaded(source) as m:
  for ordinary in (False,True):
   p=m.build(ordinary,root=root);old=m.canonical_parent(ordinary,root=root)
   require(p['computed_loader_fields']==(DEFS if ordinary else {}),'Wrong graph map')
   require(p['parameters']==old['parameters'] and p['fixed_parameters']==old['fixed_parameters'],'Input change')
   require(set(old['auxiliaries'])-set(p['auxiliaries'])==set(DEFS if ordinary else ()),'Wrong removed fields')
   require(set(p['auxiliaries'])<=set(old['auxiliaries']),'New uncharged fields')
   record=dict(ordinary=ordinary,ledger=check_source(p),parent_ledger=check_source(old))
   if ordinary:record['strict_positive_restoration_lower_bounds']=positive_bounds(p)
   # Derive the row map independently from literal parent/child comparison pairs.
   removed={(n,r) for n,r in (DEFS.items() if ordinary else ())}
   if ordinary:removed|={('input__repunit_P','input__P'),('input__input_bound','input__q'),('input__geo__geometry_index_bound','input__J'),('input__congruence_left','input__congruence_right')}
   mapping=[];j=0
   for i,(a,b) in enumerate(old['comparisons']):
    if (a,b) in removed:mapping.append((i,None,0));continue
    sub=lambda v:DEFS.get(v,v) if ordinary else v
    pair=tuple({'v136':'v135','v147':'v146'}.get(sub(v),sub(v)) for v in (a,b))
    require(p['comparisons'][j]==pair,'Actual comparison order changed')
    factor=2 if a in ('v136','v147') else 1
    mapping.append((i,j,factor));j+=1
   require(j==len(p['comparisons']),'Incomplete row map')
   for case in range(80):
    rational=case>=72;signed=case>=36
    v={n:(Fraction(rng.randrange(-4,5),rng.randrange(1,4)) if rational else rng.randrange(-5,6) if signed else rng.randrange(1,5)) for n in p['parameters']+p['auxiliaries']}
    if not ordinary and not signed:v['L0']=case%3;v['R0']=case%2
    ne=execute(p['polynomial_source'],v)
    restored=dict(v,**{n:ne[r] for n,r in (DEFS.items() if ordinary else ())})
    pe=execute(old['polynomial_source'],restored);nr=residuals(p,ne);pr=residuals(old,pe)
    require(ne[p['output']]==sum(t*t for t in nr) and pe[old['output']]==sum(t*t for t in pr),'Non-SOS output')
    correction=0
    for i,j,factor in mapping:
     require(pr[i]==(0 if j is None else factor*nr[j]),'Independent residual restoration identity')
     if factor==2:correction+=3*nr[j]**2
     counts['residual_maps']+=1
    require(pe[old['output']]-ne[p['output']]==correction,'Complete correction')
    counts['complete_SOS_corrections']+=1;counts['rational_cases']+=rational;counts['signed_integer_cases']+=signed and not rational
    if not rational:
     require(m.restore_assignment(p,v,signed=signed,root=root)==restored,'Public restore differs')
     require(m.project_assignment(p,restored,signed=signed,root=root)==v,'Public projection differs')
     a=m.identity(p,v,signed=signed,root=root)
     require(a['parent_output']==pe[old['output']] and a['child_output']==ne[p['output']] and a['correction']==correction,'Public identity differs')
     counts['public_map_roundtrips']+=1
    if not signed:require(all(restored[n]>0 for n in old['auxiliaries']),'Nonpositive restored coordinate');counts['positive_restorations']+=1
   def reject(fn):
    try:fn()
    except (ValueError,TypeError,KeyError):counts['malformed_rejections']+=1;return
    raise ValueError('Accepted malformed input')
   v={n:1 for n in p['parameters']+p['auxiliaries']}
   for n in v:
    for bad in (True,1.0,None):
     badv=dict(v);badv[n]=bad;reject(lambda badv=badv:m.restore_assignment(p,badv,root=root))
   for k in p:
    bad=deepcopy(p);bad[k]=None
    reject(lambda bad=bad:m.checked(bad,root=root))
   for bad in (True,1.0):
    badp=deepcopy(p);badp['source'][0]=tuple([*badp['source'][0][:3],bad])
    reject(lambda badp=badp:m.checked(badp,root=root))
   for api in ('build','canonical_parent'):
    t=getattr(m,api)(ordinary,root=root);t['source'][0]=('tamper','-',0,0)
    require(getattr(m,api)(ordinary,root=root)['source'][0]!=t['source'][0],'Cache mutation');counts['defensive_copies']+=1
   t=m.polynomial_source(p,root=root);t[-1]=('tamper','-',0,0)
   require(m.polynomial_source(p,root=root)[-1]!=t[-1],'Export cache mutation');counts['defensive_copies']+=1
   forms.append(record)
 return dict(status='PASS',source_sha256=SOURCE_SHA,parent_sha256=PARENT_SHA,forms=forms,counts=dict(counts),scope='Independent literal complete SOS, row map and positive graph review; finite off-zero replays are not materialized universal Pell zeros.')

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 result=json.loads(json.dumps(verify(a.source,a.root)))
 if a.expect:require(exact(result,json.loads(a.expect.read_text())),'Saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
 print(json.dumps(result,sort_keys=True,indent=2))
