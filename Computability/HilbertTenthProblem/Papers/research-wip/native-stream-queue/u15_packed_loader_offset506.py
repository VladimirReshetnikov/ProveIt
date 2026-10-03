"""One paid addition removed from all complete ordinary U15 frontier sources.

The local identity16*(u+1)-8=16*u+8 changes no complete polynomial.
Raw tape sources are retained unchanged. No coordinate is projected or erased.
"""
if not __debug__:
 raise RuntimeError('Historical authenticated parents require assertions; omit -O')
from pathlib import Path
from copy import deepcopy
from functools import lru_cache
from fractions import Fraction
from collections import Counter
import argparse,hashlib,json,random,types

PARENT_FILE='u15_packed_cross_projection507.py'
PARENT_SHA256='dc89cc030610a719b6f270ddfe9dbc5b75b1d7675bb9d13a223db160b23469a4'
PARENT_DIGESTS={'base:0:0':'0bbbb41cfd2c753ae3a1427c0a27b88ccaa6518ea680cb525847a259e932cc61','base:0:1':'e70fa3109e3ee9acacc3435e1da6f61fe28dbd5e5aa6fcca4b82abb6006b78b2','base:1:0':'59954fb8414bb37a113c5bb45f44430c619a34ebae373074f51b8448ffdd17c4','base:1:1':'e32e6c4b836244f15ced6368d3b41ecc8e6e4cc0d583be8f8d64ac26461ceceb','frontier:0':'1bc6715727c3210574c6053e1ace83f11cd7882ff463f002f206e7eb9b83c044','frontier:1':'30a2e7955e71de1471811a94123c3e36bdcdc5180842726eb33208f6fd71bf00','frontier:2':'348a29fa03537734b6bc18c1bd943a19747c6cfa4d420987398726e6d0217ad8','frontier:3':'d4ad03bbcaeafb59c736c5e6d0ca35127e2cfd60e750f85d77fe9dc1c7e1cfd1'}
EXPECTED={'input__restored_Ahat':('+','input__congruence_right0',1),'input__and__scaled_Z':('*',16,'input__restored_Ahat'),'input__and__F3':('-','input__and__scaled_Z',8)}
CUT='input__and__F3';ATOM='input__congruence_right0';ERASED='input__restored_Ahat'

def require(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
 if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def flag(x):require(type(x) is bool,'Exact Boolean required');return x
def typed(x):
 if type(x) is dict:
  require(all(type(k) is str for k in x),'String keys required');return ['dict',[[k,typed(x[k])] for k in sorted(x)]]
 if type(x) in (list,tuple):return [type(x).__name__,[typed(v) for v in x]]
 require(type(x) in (int,bool,str,type(None)),'Invalid metadata type');return [type(x).__name__,x]
def digest(x):return hashlib.sha256(json.dumps(typed(x),separators=(',',':')).encode()).hexdigest()
def count(rows):
 m=sum(op=='*' for _,op,_,_ in rows);return dict(operations=len(rows),M=m,A=len(rows)-m)
def execute(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  aa=e[a] if type(a) is str else a;bb=e[b] if type(b) is str else b
  e[n]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
 return e
def at(e,x):return e[x] if type(x) is str else x

def _paths(root=None):
 here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve()
 path=here/PARENT_FILE if (here/PARENT_FILE).is_file() else root/PARENT_FILE
 require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_SHA256,'Changed parent source')
 return root,path

@lru_cache(None)
def _load(path_text):
 path=Path(path_text);data=path.read_bytes();require(hashlib.sha256(data).hexdigest()==PARENT_SHA256,'Parent changed before execution')
 p=types.ModuleType('_loader_offset_parent507');p.__file__=str(path);exec(compile(data,str(path),'exec'),p.__dict__);return p

def _proof(parent,old,new):
 names=old['parameters']+old['auxiliaries'];cuts={CUT} if old['ordinary'] else set()
 if old['ordinary']:
  a=parent.local_polynomial(old['source'],CUT,(ATOM,));b=parent.local_polynomial(new['source'],CUT,(ATOM,))
  require(a==b=={(ATOM,):16,():8},'Literal offset polynomial identity failed')
 intern={};a=parent._signatures(old['polynomial_source'],names,cuts,intern);b=parent._signatures(new['polynomial_source'],names,cuts,intern)
 if old['ordinary']:require(a[ATOM]==b[ATOM],'Changed proof atom')
 require(exact(old['comparisons'],new['comparisons']),'Changed comparisons')
 for pair in old['comparisons']:
  for v in pair:
   if type(v) is str:require(a[v]==b[v],'Changed complete comparison operand '+v)
 require(a[old['output']]==b[new['output']],'Changed full finalizer polynomial')
 for u in old.get('unit_factors',[]):require(a[u['factor']]==b[u['factor']],'Changed native factor')
 return dict(cut=CUT if old['ordinary'] else None,independent_atom=ATOM if old['ordinary'] else None,
  identity='16*(u+1)-8=16*u+8' if old['ordinary'] else 'Identical raw source',
  unchanged_comparisons=len(old['comparisons']),unchanged_unit_factors=[v['factor'] for v in old.get('unit_factors',[])],
  complete_output_identity=True,scope='All supplied integer or rational tuples; identical full polynomial, all comparison residuals and all native unit factors.')

def _rewrite(parent,packet):
 parent.source_check(packet);flag(packet['ordinary']);p=deepcopy(packet)
 if p['ordinary']:
  rows={n:(op,a,b) for n,op,a,b in p['source']}
  require(all(exact(rows.get(n),v) for n,v in EXPECTED.items()),'Literal loader rows changed')
  uses=[n for n,op,a,b in p['polynomial_source'] for x in (a,b) if x==ERASED]
  require(uses==['input__and__scaled_Z'],'Restored loader field has another source consumer')
  require(p['computed_loader_fields'].get('input__Ahat')==ERASED,'Changed historical field map')
  replacements={'input__and__scaled_Z':('input__and__scaled_Z','*',16,ATOM),CUT:(CUT,'+','input__and__scaled_Z',8)}
  def rewrite_rows(rows):return [replacements.get(r[0],r) for r in rows if r[0]!=ERASED]
  p['source']=rewrite_rows(p['source']);p['polynomial_source']=rewrite_rows(p['polynomial_source'])
  # The eliminated arithmetic register was already a computed ancestor field,
  # never a coordinate of this parent. Keep its reconstruction as proof metadata.
  del p['computed_loader_fields']['input__Ahat']
  p['computed_loader_field_formulas']={'input__Ahat':dict(operation='+',arguments=[ATOM,1],
   scope='Historical ancestor-field restoration, not an emitted register or an additional paid gate.')}
 parent.source_check(p);proof=_proof(parent,packet,p)
 before=count(packet['polynomial_source']);after=count(p['polynomial_source']);saved=int(p['ordinary'])
 require(before['operations']-after['operations']==saved and before['M']==after['M'] and before['A']-after['A']==saved,'Unexpected complete paid count')
 live={p['output']}
 for n,op,a,b in reversed(p['polynomial_source']):
  require(n in live,'Dead complete-source operation');live.update(v for v in (a,b) if type(v) is str)
 for k in ('parameters','auxiliaries','fixed_parameters','comparisons','output'):
  require(exact(packet[k],p[k]),'Changed interface '+k)
 degrees={n:0 if n in p['fixed_parameters'] else 1 for n in p['parameters']+p['auxiliaries']}
 for n,op,a,b in p['polynomial_source']:
  da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0;degrees[n]=da+db if op=='*' else max(da,db)
 p['ledger']=dict(p['ledger'],certificate=count(p['source']),polynomial=after,formal_degree_upper_bound=degrees[p['output']],exact_degree_claimed=False)
 p['loader_offset_rewrite']=dict(proof=proof,parent_descriptor_sha256=digest(packet),removed_register=ERASED if p['ordinary'] else None,
  changed_intermediate='input__and__scaled_Z' if p['ordinary'] else None,
  scope='scaled_Z is now16*u instead of16*(u+1); its sole consumer F3 remains exactly unchanged. Every supplied coordinate remains.',saved_operations=saved)
 p['ancestor_canonical_parent']=p['canonical_parent'];p['canonical_parent']=dict(file=PARENT_FILE,sha256=PARENT_SHA256,form=p['cross_parent_form'])
 p['source_lineage']=dict(p['source_lineage'],**{PARENT_FILE:PARENT_SHA256})
 olddegree=p['exact_degree_certificate'];p['exact_degree_certificate']=dict(exact_degree=olddegree['exact_degree'],
  method='Exact complete-polynomial identity with the source-pinned507 parent; all fixed-program uniformity and degree certificates transfer unchanged.',
  parent_packet_digest=digest(packet),parent_certificate=olddegree)
 p.update(kind='u15_exact_loader_offset506',parent_relation='Identical complete polynomial and every comparison residual on the same coordinates. No witness projection.',
  scope='Complete parent raw-tape or ordinary-positive-input first-halt relation, valid fixed program slices and arbitrary duration preserved unchanged. No new global arithmetic bound.')
 return p

@lru_cache(None)
def _bundle(root_text,path_text):
 root,path=_paths(root_text);require(str(path)==path_text,'Changed source path');parent=_load(path_text);parent._context(root)
 old={}
 for ordinary in (False,True):
  for grouped in (False,True):old[f'base:{int(ordinary)}:{int(grouped)}']=parent.build(ordinary,grouped=grouped,root=root)
 for i in range(4):old[f'frontier:{i}']=parent.build_frontier(i,root=root)
 for p in old.values():parent.checked(p,root=root)
 require(exact({k:digest(v) for k,v in old.items()},PARENT_DIGESTS),'Actual canonical parent descriptor changed')
 return dict(parent=parent,old=old,packets={k:_rewrite(parent,v) for k,v in old.items()})
def _context(root=None):
 root,path=_paths(root);b=_bundle(str(root),str(path));b['parent']._context(root);return root,b

def build(ordinary=True,*,grouped=True,root=None):
 key=f'base:{int(flag(ordinary))}:{int(flag(grouped))}';return deepcopy(_context(root)[1]['packets'][key])
def build_frontier(index=3,*,root=None):
 require(type(index) is int and 0<=index<4,'Exact frontier index0..3 required');return deepcopy(_context(root)[1]['packets'][f'frontier:{index}'])
def checked(p,*,root=None):
 require(type(p) is dict and type(p.get('cross_parent_form')) is str,'Complete canonical packet required');b=_context(root)[1]
 require(p['cross_parent_form'] in b['packets'] and exact(p,b['packets'][p['cross_parent_form']]),'Noncanonical packet');return p
def canonical_parent(p,*,root=None):
 p=checked(p,root=root);return deepcopy(_context(root)[1]['old'][p['cross_parent_form']])
def polynomial_source(p,*,root=None):return deepcopy(checked(p,root=root)['polynomial_source'])
def _assignment(p,values,signed):
 flag(signed);require(type(values) is dict and values.keys()==set(p['parameters']+p['auxiliaries']),'Exact complete coordinate assignment required')
 for n,v in values.items():
  require(type(v) is int,'Exact integer required '+n)
  if not signed:require(v>=0 if not p['ordinary'] and n in ('L0','R0') else v>0,'Coordinate outside semantic domain '+n)
 return values
def evaluate(p,values,*,signed=False,root=None):
 p=checked(p,root=root);values=_assignment(p,values,signed);return execute(p['polynomial_source'],values)[p['output']]
def identity(p,values,*,signed=False,root=None):
 p=checked(p,root=root);values=_assignment(p,values,signed);q=canonical_parent(p,root=root)
 a=execute(q['polynomial_source'],values);b=execute(p['polynomial_source'],values)
 aa=[at(a,x)-at(a,y) for x,y in q['comparisons']];bb=[at(b,x)-at(b,y) for x,y in p['comparisons']]
 require(aa==bb and a[q['output']]==b[p['output']],'Complete identity failed')
 return dict(output=b[p['output']],residuals=bb)

def verify(root=None):
 root,b=_context(root);rng=random.Random(506512);c=Counter();forms=[]
 def reject(fn):
  try:fn()
  except (ValueError,KeyError,TypeError):c['malformed_rejections']+=1;return
  raise RuntimeError('Malformed input accepted')
 for key,packet in b['packets'].items():
  p=deepcopy(packet);q=canonical_parent(p,root=root)
  for j in range(24):
   signed=j>=12;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   result=identity(p,v,signed=signed,root=root);c['complete_identities']+=1;c['signed_identities']+=signed;c['residual_identities']+=len(result['residuals'])
  for j in range(3):
   v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']}
   a=execute(q['polynomial_source'],v);z=execute(p['polynomial_source'],v);require(a[q['output']]==z[p['output']],'Rational full identity');c['rational_identities']+=1
  if p['ordinary']:
   e=execute(p['source'],{n:1 for n in p['parameters']+p['auxiliaries']});old=execute(q['source'],{n:1 for n in q['parameters']+q['auxiliaries']})
   require(e[ATOM]+1==old[ERASED] and ERASED not in e,'Historical field restoration');c['historical_field_restorations']+=1
   for reg in EXPECTED:
    bad=deepcopy(q);i=next(i for i,row in enumerate(bad['source']) if row[0]==reg);row=list(bad['source'][i]);row[3]=2 if type(row[3]) is int else 0;bad['source'][i]=tuple(row);bad['polynomial_source'][i]=tuple(row)
    reject(lambda bad=bad:_rewrite(b['parent'],bad))
  for field in ('source','polynomial_source','comparisons','ledger','loader_offset_rewrite','exact_degree_certificate','computed_loader_fields'):
   if field not in p:continue
   bad=deepcopy(p);bad[field]=None;reject(lambda bad=bad:checked(bad,root=root))
  for i,row in enumerate(p['polynomial_source']):
   for k in (2,3):
    if type(row[k]) is int:
     for value in (float(row[k]),bool(row[k])):
      bad=deepcopy(p);rr=list(row);rr[k]=value;bad['polynomial_source'][i]=tuple(rr);reject(lambda bad=bad:checked(bad,root=root))
     break
  values={n:1 for n in p['parameters']+p['auxiliaries']}
  for name in list(values)[::7]:
   for value in (True,1.0,None,0,-1):
    if value==0 and type(value) is int and not p['ordinary'] and name in ('L0','R0'):continue
    bad=dict(values);bad[name]=value;reject(lambda bad=bad:evaluate(p,bad,root=root))
  if not p['ordinary']:
   identity(p,dict(values,L0=0,R0=0),root=root);c['natural_raw_zero_tape_checks']+=1
  getters=[lambda:canonical_parent(p,root=root),lambda:polynomial_source(p,root=root),
   (lambda key=key:build_frontier(int(key.split(':')[1]),root=root)) if key.startswith('frontier:') else
   (lambda key=key:build(bool(int(key.split(':')[1])),grouped=bool(int(key.split(':')[2])),root=root))]
  for getter in getters:
   a=getter();old=deepcopy(a);a.clear();require(exact(getter(),old),'Mutable cache leak');c['defensive_copies']+=1
  forms.append(dict(form=key,compiler=p,parent_ledger=q['ledger'],parent_descriptor_sha256=digest(q)))
 for bad in (0,1,None,0.0,'yes'):
  reject(lambda bad=bad:build(bad,root=root));reject(lambda bad=bad:build(grouped=bad,root=root))
 for bad in (False,True,-1,4,None,0.0):reject(lambda bad=bad:build_frontier(bad,root=root))
 return dict(status='PASS_COMPLETE_U15_LOADER_OFFSET506',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_source_pin=PARENT_SHA256,
  checks=dict(c),forms=forms,frontier=[dict(operations=b['packets'][f'frontier:{i}']['ledger']['polynomial']['operations'],exact_degree=b['packets'][f'frontier:{i}']['exact_degree_certificate']['exact_degree']) for i in range(4)],
  scope='Six complete ordinary sources and two unchanged raw forms. All-value polynomial identity, unchanged coordinates and complete first-halt/input scope inherited from authenticated507 parents.')

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args();r=json.loads(json.dumps(verify(a.root)));path=Path(__file__).with_suffix('.json')
 if a.write:path.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:require(exact(r,json.loads(path.read_text())),'Saved receipt differs')
 print(json.dumps({k:r[k] for k in ('status','checks','frontier')},indent=2))
