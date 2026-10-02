#!/usr/bin/env python3
"""Independent integer-unit/finalizer and literal modular-degree audit."""
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
import struct
import sys

PIN='667de9e6648af91c2fa1fe22801786fb78fd82156bce3132be05e9f10e513611'
def need(x,m):
 if not x:raise ValueError(m)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if type(a) in (tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def run(rows,v):
 e=dict(v)
 for n,op,a,b in rows:
  a=e[a] if type(a) is str else a;b=e[b] if type(b) is str else b
  e[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return e

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

def _verify(source,root):
 source=Path(source);root=Path(root)
 need(hashlib.sha256(source.read_bytes()).hexdigest()==PIN,'Compiler source pin')
 spec=importlib.util.spec_from_file_location('_unit524_independent',source);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 counts=Counter();records=[];rng=random.Random(5241002)
 # Exact residue proof: all integer residues represented, independently of positivity.
 for a,c,d in itertools.product(range(4),repeat=3):
  need((d*d-(a*a+4*a+3)*c*c)%4!=3,'Negative main unit');counts['main_residue_cases']+=1
 for t,v,y in itertools.product(range(4),repeat=3):
  need((t*t*(v*v-y*y)+y*y)%4!=3,'Negative auxiliary unit');counts['auxiliary_residue_cases']+=1
 # Integer unit theorem covers unbounded factor sizes; this finite census is supplemental.
 for factors in itertools.product((-3,-2,0,1,2),repeat=6):
  product=1
  for z in factors:product*=z
  for checksum in (-2,-1,0,1,2):
   need((product*checksum==1)==(all(z==1 for z in factors) and checksum==1),'Unit census')
   counts['integer_unit_census']+=1
 for ordinary in (False,True):
  old=m.canonical_parent(ordinary,root=root)
  for finalizer in ('sos','anchor'):
   p=m.build(ordinary,finalizer=finalizer,root=root)
   need(p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries'],'Changed domain')
   prefixes=(['input__geo__','input__and__'] if ordinary else [])+['native__']
   maps=[]
   for prefix in prefixes:
    for kind,left,right,sign in [('main','L15','R15',1),('auxiliary','L17','P17',1)]:
     pair=(prefix+left,prefix+right);idx=[tuple(z) for z in old['comparisons']].index(pair)
     maps.append((idx,'unit_'+prefix+kind,sign))
   if ordinary:
    idx=[tuple(z) for z in old['comparisons']].index(('input__and__bs_q','input__and__q'));maps.append((idx,'unit_loader_checksum',-1))
   removed={i for i,_,_ in maps};retained=[tuple(pair) for i,pair in enumerate(old['comparisons']) if i not in removed]
   need(p['comparisons'][:-1]==retained and tuple(p['comparisons'][-1])==(p['unit_product_register'],1),'Wrong complete comparison transfer')
   def at(e,a):return e[a] if type(a) is str else a
   for case in range(48):
    signed=case>=24
    v={n:rng.randrange(-4,5) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
    if not ordinary and not signed:v['L0']=case%2;v['R0']=(case+1)%2
    oe=run(old['polynomial_source'],v);ne=run(p['polynomial_source'],v)
    rr=[at(oe,a)-at(oe,b) for a,b in old['comparisons']]
    S=sum(r*r for i,r in enumerate(rr) if i not in removed);U=1
    for i,name,sign in maps:
     need(ne[name]==1+sign*rr[i],'Factor identity');U*=ne[name];counts['factor_identities']+=1
    for pair in retained:need(at(oe,pair[0])-at(oe,pair[1])==at(ne,pair[0])-at(ne,pair[1]),'Retained comparison')
    expected=S+(U-1)**2 if finalizer=='sos' else U*(1+S)-1
    need(ne[p['output']]==expected and oe[old['output']]==sum(r*r for r in rr),'Complete finalizer')
    need(m.evaluate(p,v,signed=signed,root=root)==expected,'Public output')
    counts['complete_outputs']+=1;counts['signed_cases']+=signed;counts['parent_residuals']+=len(rr)
   co=Counter(op for _,op,_,_ in p['polynomial_source'])
   need(p['ledger']['polynomial']==dict(operations=len(p['polynomial_source']),M=co['*'],A=co['+']+co['-']),'Unpaid operation')
   def reject(fn):
    try:fn()
    except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
    raise ValueError('Accepted malformed caller')
   for key in p:
    bad=deepcopy(p);bad[key]=None;reject(lambda bad=bad:m.checked(bad,root=root))
   # The former public degree-audit hole must fail before any heuristic substitution.
   for name in ('unit_native__main','native__R14','native__a4m5'):
    bad=deepcopy(p);i=next(i for i,row in enumerate(bad['source']) if row[0]==name)
    bad['source'][i]=(name,'*','native__R14','native__R14') if name=='unit_native__main' else (name,'+',0,0)
    j=next(i for i,row in enumerate(bad['polynomial_source']) if row[0]==name);bad['polynomial_source'][j]=bad['source'][i]
    reject(lambda bad=bad:m.degree_audit(bad))
   for accessor in ('build','canonical_parent'):
    copy=getattr(m,accessor)(ordinary,root=root);copy['source'][0]=('tamper','-',0,0)
    need(getattr(m,accessor)(ordinary,root=root)['source'][0]!=copy['source'][0],'Cache leak');counts['copy_checks']+=1
   degrees=[poly_run(p,prime,offset) for prime,offset in ((1009,0),(1013,7))]
   expected_degree={(False,'sos'):3464,(False,'anchor'):3668,(True,'sos'):5890,(True,'anchor'):4881}[ordinary,finalizer]
   need(all(x['degree']==expected_degree and x['leading_coefficient'] for x in degrees),'Actual polynomial degree specialization')
   audit=m.degree_audit(p);need(audit['exact_degree']==expected_degree,'Degree API differs')
   records.append(dict(ordinary=ordinary,finalizer=finalizer,ledger=p['ledger'],complete_univariate_polynomial_checks=degrees))
 return dict(status='PASS',source_sha256=PIN,counts=dict(counts),forms=records,scope='Integer-unit transfer and actual complete-source algebra/degree audit; no complete universal native Pell zero materialized.')
def verify(source,root):
 before=dict(sys.modules);oldpath=list(sys.path)
 bases=[Path(source).resolve().parent,Path(root).resolve(),Path(root).resolve().parents[1]/'verification']
 try:return _verify(source,root)
 finally:
  sys.path[:]=oldpath
  for name,module in list(sys.modules.items()):
   filename=getattr(module,'__file__',None)
   local=False
   if filename:
    try:local=any(Path(filename).resolve().is_relative_to(base) for base in bases)
    except (TypeError,ValueError,OSError):pass
   if local and name not in before:sys.modules.pop(name,None)
  for name,module in before.items():
   if sys.modules.get(name) is not module:sys.modules[name]=module

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args()
 r=json.loads(json.dumps(verify(a.source,a.root)))
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Receipt differs')
 print(json.dumps(r,indent=2,sort_keys=True))
