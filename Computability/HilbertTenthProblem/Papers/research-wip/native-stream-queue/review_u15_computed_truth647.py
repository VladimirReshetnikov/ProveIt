"""Independent literal-transform and complete-residual audit of U15 truth647."""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import sympy as sp

if not __debug__:raise RuntimeError('Assertions required')
TARGET_SHA='c363ea0679825559d5247608f748d877e75146dbb997b159db42294d9d676eb7'
AUDIT_SHA='e68c285be7718442e3730f37b94dcc4aeb35e89751ca176e246eee8f8fcfbda3'
FIELDS=('native__F0','native__F1','native__F2')
DEAD={'native__input_A','native__shared_sum02','native__bs_Q','native__bs_q','native__input_B'}
PAIRS={('native__bs_q','native__q'),('native__input_A','native__padded_A'),('native__input_B','native__padded_B')}

def load(path,name):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def execute(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  assert n not in e
  x=e[a] if type(a) is str else a;y=e[b] if type(b) is str else b
  e[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return e

def at(e,x):return e[x] if type(x) is str else x

def verify(target,root):
 assert hashlib.sha256(target.read_bytes()).hexdigest()==TARGET_SHA
 prior=root/'review_u15_packed_history.py'
 assert hashlib.sha256(prior.read_bytes()).hexdigest()==AUDIT_SHA
 sys.path.insert(0,str(root));audit=load(prior,'independent_baseline_arithmetic');m=load(target,'independent_truth_target')
 base=load(root/'u15_packed_two_tape_history.py','independent_truth_baseline')
 counts=Counter();rng=random.Random(20261002647)
 q,a,b,z=sp.symbols('q a b z');f1=a-z;f2=b-z;f0=q-a-f2-1
 for x in (f1+z-a,f2+z-b,f0+f1+f2+z+1-q):
  assert sp.expand(x)==0;counts['formal_deleted_graph_identities']+=1
 for ordinary in (False,True):
  old=base.build(ordinary);tag=m.tagged_parent(ordinary);p=m.build(ordinary)
  reg=old['registers'];cut=next(i for i,row in enumerate(old['source']) if row[0].startswith('native__'))
  scale=next(row for row in old['source'] if row[0]==reg['scale']);assert scale[1]=='*'
  T=scale[3] if scale[2]==reg['B'] else scale[2]
  aliases={reg['Hjoin']:'tag_A',reg['Mjoin']:'tag_M'}
  tags=[('tag_twice_T','*',2,T),('tag_A','+',reg['Hjoin'],'tag_twice_T'),('tag_M','+',reg['Mjoin'],T)]
  expected=old['source'][:cut]+tags+[(n,op,aliases.get(a,a),aliases.get(b,b)) for n,op,a,b in old['source'][cut:]]
  assert tag['source']==expected and tag['comparisons']==old['comparisons']
  defs=[('native__F1','-','native__padded_A','native__F3'),('native__F2','-','native__padded_B','native__F3'),('computed_q_minus_A','-','native__q','native__padded_A'),('computed_F0_plus_one','-','computed_q_minus_A','native__F2'),('native__F0','-','computed_F0_plus_one',1)]
  expected=[]
  for row in tag['source']:
   if row[0] not in DEAD:expected.append(row)
   if row[0]=='native__F3':expected+=defs
  assert p['source']==expected and p['comparisons']==[v for v in tag['comparisons'] if v not in PAIRS]
  assert p['auxiliaries']==[v for v in old['auxiliaries'] if v not in FIELDS]
  assert p['parameters']==old['parameters'];counts['complete_literal_source_transforms']+=1
  assert len(p['source'])==len(old['source'])+3
  assert len(p['polynomial_source'])==len(old['polynomial_source'])-6
  for case in range(32):
   v={n:rng.randrange(-3,5) if case>=16 else rng.randrange(1,6) for n in p['parameters']+p['auxiliaries']}
   raw={n:v[n] for n in base.build()['auxiliaries'] if n not in FIELDS}
   raw.update(dict.fromkeys(FIELDS,1));raw.update(L0=v['program_L'] if ordinary else v['L0'],R0=v['input_R0'] if ordinary else v['R0'])
   _,rs=audit.manual_raw(raw,base.RULES);top=rs['P']**34
   A=rs['Hjoin']+2*top;M=rs['Mjoin']+top;Z=rs['Zjoin'];cap=rs['scale']
   truth=(16*(cap-A-M+Z)-15,16*(A-Z)+4,16*(M-Z)+2)
   raw.update(dict(zip(FIELDS,truth)))
   before,_=audit.manual_raw(raw,base.RULES)
   rr=[r for i,r in enumerate(before) if i not in (5,12,13)]
   if ordinary:
    ld=base.loader.build(False)
    rename=lambda n:{'x':'x','L0':'program_L','R0':'input_R0',**{k:k for k in ('program_L','program_A','program_B','program_D')}}.get(n,'input__'+n)
    lv={n:v[rename(n)] for n in ld['parameters']+ld['auxiliaries']}
    first=base.loader.bridge.independent(base.loader.bridge.recoder(32),lv)
    first.append(base.loader.DENOM*v['input_R0']+v['program_D']-v['program_A']*lv['q']**32-v['program_B']*lv['z'])
    rr=first+rr
   env=execute(p['polynomial_source'],v)
   assert rr==[at(env,a)-at(env,b) for a,b in p['comparisons']]
   assert env[p['output']]==sum(x*x for x in rr)==m.evaluate(p,v,signed=True)
   restored=m.lift_to_tagged_parent(p,v,signed=True)
   assert tuple(restored[n] for n in FIELDS)==truth
   assert m.project_from_tagged_parent(p,restored,signed=True)==v
   assert execute(tag['polynomial_source'],restored)[tag['output']]==env[p['output']]
   counts['complete_independent_residual_and_SOS_cases']+=1;counts['signed_cases']+=case>=16
   counts['individual_residual_comparisons']+=len(rr)
 for L,R in ((6,0),(6,1),(6,3),(14,0)):
  v,_=base.outer_fixture(L,R,100);p=m.build();v={n:v[n] for n in p['parameters']+p['auxiliaries']}
  restored=m.lift_to_tagged_parent(p,v);assert min(restored[n] for n in FIELDS)>0
  assert m.project_from_tagged_parent(p,restored)==v
  counts['genuine_positive_graph_restorations']+=1
 return dict(status='PASS',source_sha256=TARGET_SHA,baseline_audit_sha256=AUDIT_SHA,counts=dict(counts),
  scope='Independent complete literal tagged-source/projection checks and residual evaluation using the separately reviewed baseline arithmetic; positive relation proof accompanies this audit. No full Pell witness fixture and no same-private-witness equality to untagged baseline.')

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--target',type=Path,required=True);a.add_argument('--root',type=Path,required=True);a.add_argument('--output',type=Path,required=True);v=a.parse_args();r=verify(v.target.resolve(),v.root.resolve());v.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
