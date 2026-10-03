"""One complete U15 addition removed by rescheduling its consumed affine forms.

Replace the actual 91-gate controller closure by 90=6M+84A. All nine exposed
ports, all complete comparison residuals and the entire polynomial are equal.
"""
if not __debug__:
 raise RuntimeError('Authenticated historical parents require normal Python')
from pathlib import Path
from copy import deepcopy
from functools import lru_cache
from fractions import Fraction
from collections import Counter
import argparse,hashlib,json,random,types

PARENT_FILE='u15_packed_loader_offset506.py'
PARENT_SHA256='b8c2af63e5b102685944e5e18e31f037a257df2abb0fcbf8efbf0824a1685a9a'
PARENT_DIGESTS={'base:0:0': '825ac4609fc1f51fd58c668cc908d7fd1a3aa85f90e9fd77e9a7c2f9fb83b6da', 'base:0:1': '8908b3e61563137a1a8570ac64cacdedd3e9d1044fe89481154d0048357b3448', 'base:1:0': '7fbd5d8b607fc3117a6177d81d1be6fa28fa2d1c9b9060642fec7e1595bc1610', 'base:1:1': '3521cfca98dd336de16e726c509a5dcda3633def02e00212558210e1c2b54ccb', 'frontier:0': 'cc0a7fe129dcf86d4b6ee644a502de7bdfb33cf40fcb6062c626f2da6207e0c2', 'frontier:1': '2b4636e07dacb74a312f9370b18f21f57303d3e3c13cc1a26c1c3c1492afbb4c', 'frontier:2': '26c40efaa8b54cd59f62f80361333b970230f4aaab2a11f258eae9ed205d8649', 'frontier:3': 'c2b6f995d1e3ae5102f4987b8821eecdb0e18d8a6bb1f722ca0f97df648bcefa'}
_OLD_ROWS=(('binary0', '+', 'edge20', 'edge28'), ('binary1', '+', 'edge1', 'edge8'), ('binary2', '+', 'edge11', 'edge9'), ('binary3', '+', 'edge17', 'binary2'), ('binary4', '+', 'edge13', 'edge7'), ('binary5', '+', 'edge15', 'binary4'), ('binary6', '+', 'edge2', 'edge3'), ('binary7', '+', 'edge27', 'binary0'), ('binary8', '+', 'edge22', 'edge24'), ('binary9', '+', 'edge14', 'edge18'), ('binary10', '+', 'edge4', 'edge5'), ('binary11', '+', 'binary3', 'binary5'), ('binary12', '+', 'edge26', 'binary7'), ('binary13', '+', 'binary11', 'binary9'), ('binary14', '+', 'binary1', 'binary6'), ('binary15', '+', 'edge10', 'binary13'), ('binary16', '+', 'edge19', 'binary12'), ('binary17', '+', 'edge0', 'edge18'), ('binary18', '+', 'edge16', 'edge25'), ('binary19', '+', 'edge12', 'binary10'), ('binary20', '+', 'binary14', 'binary18'), ('binary21', '+', 'edge21', 'binary8'), ('binary22', '-', 'edge25', 'binary17'), ('binary23', '+', 'edge23', 'binary15'), ('binary24', '+', 'edge16', 'edge17'), ('binary25', '-', 'edge10', 'binary16'), ('binary26', '+', 'edge6', 'edge7'), ('binary27', '-', 'edge23', 'binary1'), ('binary28', '+', 'binary0', 'binary8'), ('binary29', '+', 'edge6', 'binary23'), ('binary30', '+', 'edge0', 'binary19'), ('binary31', '+', 'edge3', 'edge5'), ('binary32', '-', 'edge26', 'binary10'), ('binary33', '+', 'binary16', 'binary20'), ('binary34', '+', 'binary21', 'binary33'), ('binary35', '+', 'binary29', 'binary34'), ('binary36', '+', 'binary30', 'binary35'), ('binary37', '+', 'edge1', 'edge26'), ('binary38', '+', 'binary11', 'binary37'), ('binary39', '+', 'binary28', 'binary38'), ('binary40', '+', 'binary31', 'binary39'), ('binary41', '+', 'edge25', 'binary19'), ('binary42', '+', 'binary29', 'binary41'), ('binary45', '+', 'edge19', 'edge24'), ('binary46', '+', 'binary24', 'binary45'), ('binary47', '+', 'binary27', 'binary46'), ('binary48', '+', 'binary47', 'binary7'), ('binary49', '+', 'edge13', 'edge9'), ('binary50', '+', 'binary30', 'binary49'), ('binary51', '-', 'binary48', 'binary50'), ('binary52', '+', 'binary22', 'binary6'), ('binary53', '+', 'binary1', 'binary2'), ('binary54', '+', 'binary25', 'binary53'), ('binary55', '-', 'binary52', 'binary54'), ('binary56', '+', 'edge23', 'edge27'), ('binary57', '+', 'edge28', 'binary56'), ('binary58', '+', 'binary21', 'binary57'), ('binary59', '+', 'binary22', 'binary58'), ('binary60', '+', 'binary32', 'binary59'), ('binary61', '+', 'edge1', 'binary26'), ('binary62', '-', 'binary60', 'binary61'), ('binary63', '+', 'edge21', 'binary32'), ('binary64', '+', 'binary63', 'binary9'), ('binary65', '+', 'binary20', 'binary5'), ('binary66', '-', 'binary64', 'binary65'), ('binary67', '+', 'binary12', 'binary17'), ('binary68', '+', 'binary27', 'binary67'), ('binary69', '+', 'binary24', 'binary26'), ('binary70', '+', 'binary31', 'binary69'), ('binary71', '-', 'binary68', 'binary70'), ('binary72', '+', 'binary20', 'binary25'), ('binary73', '+', 'binary3', 'binary72'), ('binary74', '-', 'binary21', 'binary73'), ('binary75', '-', 'binary36', 29), ('binary76', '-', 'binary40', 14), ('binary77', '-', 'binary42', 15), ('binary79', '-', 'binary15', 9), ('binary80', '*', 'binary62', 2), ('binary81', '+', 'binary55', 'binary80'), ('binary82', '*', 'binary81', 2), ('binary83', '+', 'binary51', 'binary82'), ('binary85', '*', 'binary74', 2), ('binary86', '+', 'binary71', 'binary85'), ('binary87', '*', 'binary86', 2), ('binary88', '+', 'binary66', 'binary87'), ('binary89', '-', 'binary88', -17), ('v131', '*', 'binary79', 2), ('cross_write_sum', '+', 'binary28', 'binary14'), ('cross_write_only', '-', 'cross_write_sum', 8), ('v140', '*', 'cross_write_only', 2), ('v156', '+', 'binary83', 1))
_ROWS=(('consumed_c0', '+', 'edge1', 'edge8'), ('consumed_c1', '+', 'edge20', 'edge28'), ('consumed_c2', '+', 'edge11', 'edge9'), ('consumed_c3', '+', 'edge2', 'edge3'), ('consumed_c4', '+', 'edge15', 'edge7'), ('consumed_c5', '+', 'consumed_c2', 'edge17'), ('consumed_c6', '+', 'edge22', 'edge24'), ('consumed_c7', '+', 'consumed_c4', 'edge13'), ('consumed_c8', '+', 'consumed_c5', 'edge10'), ('consumed_c9', '+', 'consumed_c1', 'consumed_c6'), ('consumed_c10', '+', 'edge4', 'edge5'), ('consumed_c11', '+', 'consumed_c0', 'consumed_c3'), ('consumed_c12', '+', 'edge14', 'edge18'), ('consumed_c13', '+', 'edge26', 'edge27'), ('consumed_c14', '+', 'consumed_c12', 'consumed_c8'), ('consumed_c15', '+', 'consumed_c14', 'consumed_c7'), ('consumed_c16', '+', 'consumed_c13', 'edge19'), ('consumed_c17', '+', 'consumed_c10', 'edge12'), ('consumed_c18', '+', 'edge0', 'edge18'), ('consumed_c19', '+', 'consumed_c11', 'edge25'), ('consumed_c20', '+', 'consumed_c19', 'edge16'), ('consumed_c21', '-', 'consumed_c0', 'consumed_c1'), ('consumed_c22', '+', 'edge6', 'edge7'), ('consumed_c23', '+', 'consumed_c15', 'consumed_c17'), ('consumed_c24', '-', 'consumed_c10', 'edge21'), ('consumed_c25', '-', 'consumed_c22', 'edge23'), ('consumed_c26', '+', 'consumed_c9', 'edge21'), ('consumed_c27', '+', 'edge3', 'edge5'), ('consumed_c28', '+', 'edge16', 'edge17'), ('consumed_c29', '+', 'consumed_c23', 'edge6'), ('consumed_c30', '+', 'consumed_c29', 'edge23'), ('consumed_c31', '-', 'consumed_c18', 'edge25'), ('consumed_c32', '+', 'consumed_c11', 'consumed_c9'), ('consumed_c33', '+', 'consumed_c16', 'consumed_c26'), ('consumed_c34', '-', 'consumed_c13', 'consumed_c25'), ('consumed_c35', '+', 'consumed_c20', 'consumed_c30'), ('consumed_c36', '+', 'consumed_c33', 'consumed_c35'), ('consumed_c37', '+', 'consumed_c36', 'edge0'), ('consumed_c38', '+', 'consumed_c27', 'consumed_c5'), ('consumed_c39', '+', 'consumed_c38', 'consumed_c7'), ('consumed_c40', '+', 'consumed_c39', 'consumed_c9'), ('consumed_c41', '+', 'consumed_c40', 'edge1'), ('consumed_c42', '+', 'consumed_c41', 'edge26'), ('consumed_c43', '+', 'consumed_c30', 'edge25'), ('binary79', '-', 'consumed_c15', 9), ('cross_write_only', '-', 'consumed_c32', 8), ('consumed_c46', '+', 'consumed_c28', 'edge19'), ('consumed_c47', '+', 'consumed_c46', 'edge23'), ('consumed_c48', '+', 'consumed_c47', 'edge24'), ('consumed_c49', '+', 'consumed_c48', 'edge27'), ('consumed_c50', '+', 'consumed_c17', 'consumed_c21'), ('consumed_c51', '+', 'consumed_c50', 'edge0'), ('consumed_c52', '+', 'consumed_c51', 'edge13'), ('consumed_c53', '+', 'consumed_c52', 'edge9'), ('consumed_c54', '-', 'consumed_c49', 'consumed_c53'), ('consumed_c55', '+', 'consumed_c16', 'consumed_c3'), ('consumed_c56', '+', 'consumed_c2', 'consumed_c21'), ('consumed_c57', '+', 'consumed_c31', 'consumed_c56'), ('consumed_c58', '+', 'consumed_c57', 'edge10'), ('consumed_c59', '-', 'consumed_c55', 'consumed_c58'), ('consumed_c60', '+', 'consumed_c34', 'consumed_c6'), ('consumed_c61', '+', 'consumed_c60', 'edge28'), ('consumed_c62', '+', 'consumed_c24', 'consumed_c31'), ('consumed_c63', '+', 'consumed_c62', 'edge1'), ('consumed_c64', '-', 'consumed_c61', 'consumed_c63'), ('consumed_c65', '+', 'consumed_c12', 'edge26'), ('consumed_c66', '+', 'consumed_c20', 'consumed_c24'), ('consumed_c67', '+', 'consumed_c66', 'consumed_c7'), ('consumed_c68', '-', 'consumed_c65', 'consumed_c67'), ('consumed_c69', '+', 'consumed_c18', 'consumed_c34'), ('consumed_c70', '+', 'consumed_c21', 'consumed_c27'), ('consumed_c71', '+', 'consumed_c28', 'consumed_c70'), ('consumed_c72', '-', 'consumed_c69', 'consumed_c71'), ('consumed_c73', '+', 'consumed_c20', 'consumed_c8'), ('consumed_c74', '-', 'consumed_c33', 'consumed_c73'), ('binary75', '+', 'consumed_c37', -29), ('binary76', '+', 'consumed_c42', -14), ('binary77', '+', 'consumed_c43', -15), ('v131', '*', 'binary79', 2), ('v140', '*', 'cross_write_only', 2), ('consumed_c80', '*', 'consumed_c64', 2), ('consumed_c81', '+', 'consumed_c59', 'consumed_c80'), ('consumed_c82', '*', 'consumed_c81', 2), ('consumed_c83', '+', 'consumed_c54', 'consumed_c82'), ('v156', '+', 'consumed_c83', 1), ('consumed_c85', '*', 'consumed_c74', 2), ('consumed_c86', '+', 'consumed_c72', 'consumed_c85'), ('consumed_c87', '*', 'consumed_c86', 2), ('consumed_c88', '+', 'consumed_c68', 'consumed_c87'), ('binary89', '+', 'consumed_c88', 17))
PORTS=('binary75','binary76','binary77','binary79','cross_write_only','v131','v140','v156','binary89')
SEARCH={'binary': {'seeds': 500, 'best': 90, 'seed': 72, 'count_distribution': {'93': 46, '96': 102, '100': 7, '95': 83, '97': 95, '98': 52, '94': 67, '99': 17, '92': 19, '90': 3, '91': 9}}, 'naf': {'seeds': 500, 'best': 98, 'seed': 111, 'count_distribution': {'101': 193, '100': 129, '102': 98, '103': 31, '99': 43, '98': 3, '104': 3}}, 'direct': {'seeds': 500, 'best': 99, 'seed': 1, 'count_distribution': {'100': 199, '99': 275, '101': 26}}}

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

def replacement():return deepcopy(list(_ROWS))

def _rewrite(engine,packet):
 engine.source_check(packet);p=deepcopy(packet);oldrows={r[0]:r for r in packet['source']};closed=set()
 def visit(n):
  if type(n)is str and n in oldrows and n not in closed:
   closed.add(n)
   for x in oldrows[n][2:]:visit(x)
 for n in PORTS:visit(n)
 require(exact({n:oldrows[n] for n in closed},{r[0]:r for r in _OLD_ROWS}),'Actual affine closure changed')
 for row in packet['polynomial_source']:
  if row[0] not in closed:require(all(type(x)is int or x not in closed or x in PORTS for x in row[2:]),'Private affine node escapes')
 for pair in packet['comparisons']:require(all(type(x)is int or x not in closed or x in PORTS for x in pair),'Private affine comparison')
 newnames={r[0] for r in _ROWS};outside=set(packet['parameters']+packet['auxiliaries'])|{r[0] for r in packet['polynomial_source'] if r[0] not in closed}
 require(not newnames&outside,'Replacement source name collision')
 p['source']=list(_ROWS)+[r for r in packet['source'] if r[0] not in closed]
 tail=packet['polynomial_source'][len(packet['source']):]
 p['polynomial_source']=p['source']+deepcopy(tail)
 engine.source_check(p)
 leaves=tuple('edge'+str(i) for i in range(29));proof=[]
 for n in PORTS:
  a=engine.local_polynomial(packet['source'],n,leaves);b=engine.local_polynomial(p['source'],n,leaves)
  require(a==b,'Changed affine port '+n)
  proof.append(dict(port=n,terms=[dict(monomial=list(k),coefficient=v) for k,v in sorted(a.items())]))
 # Each cut is proved literally in the unchanged input coordinates, then the
 # complete expression DAGs are compared beyond those equal ports.
 names=packet['parameters']+packet['auxiliaries'];intern={}
 a=engine._signatures(packet['polynomial_source'],names,set(PORTS),intern)
 b=engine._signatures(p['polynomial_source'],names,set(PORTS),intern)
 token=lambda e,n:e[n] if type(n)is str else ('integer',n)
 for pair in packet['comparisons']:
  for n in pair:require(token(a,n)==token(b,n),'Changed comparison operand')
 for field in ('registers','tag_registers','computed_loader_fields'):
  for n in packet.get(field,{}).values():require(token(a,n)==token(b,n),'Changed active semantic field')
 for unit in packet.get('unit_factors',[]):require(a[unit['factor']]==b[unit['factor']],'Changed native unit factor')
 require(a[packet['output']]==b[p['output']],'Changed complete polynomial')
 used={p['output']}
 for n,op,x,y in reversed(p['polynomial_source']):
  require(n in used,'Dead paid gate');used.update(z for z in (x,y) if type(z)is str)
 before=count(packet['polynomial_source']);after=count(p['polynomial_source'])
 require(before['operations']==after['operations']+1 and before['M']==after['M'] and before['A']==after['A']+1,'Wrong complete saving')
 require(count(_OLD_ROWS)==dict(operations=91,M=6,A=85) and count(_ROWS)==dict(operations=90,M=6,A=84),'Wrong local ledger')
 for k in ('parameters','auxiliaries','fixed_parameters','comparisons','output'):
  require(exact(packet[k],p[k]),'Changed semantic interface')
 degrees={n:0 if n in p['fixed_parameters'] else 1 for n in names}
 for n,op,x,y in p['polynomial_source']:
  dx=degrees[x] if type(x)is str else 0;dy=degrees[y] if type(y)is str else 0;degrees[n]=dx+dy if op=='*' else max(dx,dy)
 p['ledger']=dict(p['ledger'],certificate=count(p['source']),polynomial=after,formal_degree_upper_bound=degrees[p['output']],exact_degree_claimed=False)
 p['consumed_affine_rewrite']=dict(parent_packet_digest=digest(packet),ports=proof,removed_rows=91,emitted_rows=90,
  saved=dict(operations=1,M=0,A=1),unchanged_comparisons=len(packet['comparisons']),
  unchanged_native_unit_factors=[u['factor'] for u in packet.get('unit_factors',[])],
  unchanged_active_metadata_ports=True,unchanged_finalizer_rows=True,full_polynomial_DAG_identity=True,
  scope='Exact polynomial identity on all supplied integer and rational coordinates; no witness projection or semantic weakening.')
 olddegree=packet['exact_degree_certificate']
 p['exact_degree_certificate']=dict(exact_degree=olddegree['exact_degree'],parent_certificate=olddegree,
  method='Complete all-value polynomial identity transfers the pinned506 exact-degree and fixed-program certificates unchanged.')
 archived={k:p.pop(k) for k in ('loader_offset_rewrite','cross_projection','canonical_parent','ancestor_canonical_parent') if k in p}
 p['parent_transform_provenance']=archived
 p['canonical_parent']=dict(file=PARENT_FILE,sha256=PARENT_SHA256,form=p['cross_parent_form'])
 p['source_lineage']=dict(p['source_lineage'],**{PARENT_FILE:PARENT_SHA256})
 p.update(kind='u15_consumed_affine505',parent_relation='Every exposed affine form and complete polynomial is unchanged on the same coordinates.',
  scope='Complete raw-tape or ordinary-positive-input first-halt relation of the authenticated506 parent, for valid fixed program slices and arbitrary duration; no new87-operation global record.')
 return p

@lru_cache(None)
def _bundle(root_text,path_text):
 root,path=_paths(root_text);require(str(path)==path_text,'Changed path');parent=_load(path_text);_,ctx=parent._context(root);engine=ctx['parent']
 old={k:deepcopy(p) for k,p in ctx['packets'].items()}
 for p in old.values():parent.checked(p,root=root)
 require(exact({k:digest(p) for k,p in old.items()},PARENT_DIGESTS),'Changed actual canonical parent packets')
 return dict(parent=parent,engine=engine,old=old,packets={k:_rewrite(engine,p) for k,p in old.items()})
def _context(root=None):
 root,path=_paths(root);b=_bundle(str(root),str(path));b['parent']._context(root);return root,b

def build(ordinary=True,*,grouped=True,root=None):
 key=f'base:{int(flag(ordinary))}:{int(flag(grouped))}';return deepcopy(_context(root)[1]['packets'][key])
def build_frontier(index=3,*,root=None):
 require(type(index)is int and 0<=index<4,'Exact frontier index0..3 required');return deepcopy(_context(root)[1]['packets'][f'frontier:{index}'])
def checked(p,*,root=None):
 require(type(p)is dict and type(p.get('cross_parent_form'))is str,'Complete canonical packet required');b=_context(root)[1]
 require(p['cross_parent_form'] in b['packets'] and exact(p,b['packets'][p['cross_parent_form']]),'Noncanonical packet');return p
def canonical_parent(p,*,root=None):
 p=checked(p,root=root);return deepcopy(_context(root)[1]['old'][p['cross_parent_form']])
def polynomial_source(p,*,root=None):return deepcopy(checked(p,root=root)['polynomial_source'])
def _assignment(p,values,signed):
 flag(signed);require(type(values)is dict and values.keys()==set(p['parameters']+p['auxiliaries']),'Exact complete assignment required')
 for n,v in values.items():
  require(type(v)is int,'Exact integer required '+n)
  if not signed:require(v>=0 if not p['ordinary'] and n in ('L0','R0') else v>0,'Outside semantic domain '+n)
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
 root,b=_context(root);rng=random.Random(505513);c=Counter();forms=[]
 def reject(fn):
  try:fn()
  except (ValueError,KeyError,TypeError):c['malformed_rejections']+=1;return
  raise RuntimeError('Malformed call accepted')
 for key,packet in b['packets'].items():
  p=deepcopy(packet);q=canonical_parent(p,root=root)
  expected={'base:0:0':(320,116,204,51,1936),'base:0:1':(318,116,202,51,3464),'base:1:0':(517,209,308,87,1936),'base:1:1':(505,209,296,87,4881),'frontier:0':(505,209,296,87,4881),'frontier:1':(507,209,298,87,3120),'frontier:2':(509,209,300,87,2116),'frontier:3':(511,209,302,87,1936)}[key]
  ledger=p['ledger']['polynomial'];require((ledger['operations'],ledger['M'],ledger['A'],len(p['auxiliaries']),p['exact_degree_certificate']['exact_degree'])==expected,'Unexpected complete frontier')
  for j in range(16):
   signed=j>=8;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   result=identity(p,v,signed=signed,root=root);c['complete_identities']+=1;c['signed_identities']+=signed;c['residual_identities']+=len(result['residuals'])
  for j in range(2):
   v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']};a=execute(q['polynomial_source'],v);z=execute(p['polynomial_source'],v)
   require(a[q['output']]==z[p['output']],'Rational polynomial identity');c['rational_identities']+=1
  for n in PORTS:
   bad=deepcopy(q);i=next(i for i,r in enumerate(bad['source']) if r[0]==n);r=list(bad['source'][i]);r[3]=r[3]+1 if type(r[3])is int else 0;bad['source'][i]=tuple(r);bad['polynomial_source'][i]=tuple(r)
   reject(lambda bad=bad:_rewrite(b['engine'],bad))
  # Strict canonical packet comparison rejects metadata aliases and source changes.
  for field in ('source','polynomial_source','comparisons','registers','ledger','consumed_affine_rewrite','exact_degree_certificate'):
   bad=deepcopy(p);bad[field]=None;reject(lambda bad=bad:checked(bad,root=root))
  for row_index in (0,44,45,75,78,79,89):
   bad=deepcopy(p);row=list(bad['source'][row_index]);row[3]=float(row[3]) if type(row[3])is int else None;bad['source'][row_index]=tuple(row);reject(lambda bad=bad:checked(bad,root=root))
  values={n:1 for n in p['parameters']+p['auxiliaries']}
  for n in list(values)[::13]:
   for v in (True,1.0,None,0,-1):
    if type(v)is int and v==0 and not p['ordinary'] and n in ('L0','R0'):continue
    bad=dict(values);bad[n]=v;reject(lambda bad=bad:evaluate(p,bad,root=root))
  if not p['ordinary']:identity(p,dict(values,L0=0,R0=0),root=root);c['natural_raw_zero_checks']+=1
  for getter in (lambda:canonical_parent(p,root=root),lambda:polynomial_source(p,root=root),lambda:replacement()):
   v=getter();copy=deepcopy(v);v.clear();require(exact(getter(),copy),'Cache mutation');c['defensive_copies']+=1
  forms.append(dict(form=key,compiler=p,parent_ledger=q['ledger'],parent_packet_digest=digest(q)))
 for bad in (0,1,None,0.0,'yes'):
  reject(lambda bad=bad:build(bad,root=root));reject(lambda bad=bad:build(grouped=bad,root=root))
 for bad in (False,True,-1,4,None,0.0):reject(lambda bad=bad:build_frontier(bad,root=root))
 return dict(status='PASS_COMPLETE_U15_CONSUMED_AFFINE505',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  parent_source_sha256=PARENT_SHA256,checks=dict(c),forms=forms,search_evidence=SEARCH,
  frontier=[dict(operations=b['packets'][f'frontier:{i}']['ledger']['polynomial']['operations'],exact_degree=b['packets'][f'frontier:{i}']['exact_degree_certificate']['exact_degree']) for i in range(4)],
  scope='Eight complete canonical sources, exact all-value polynomial identity and nine affine port identities. Bounded search is not a minimum-circuit claim; full native/input/unbounded-duration semantics inherit unchanged.')
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args();r=json.loads(json.dumps(verify(a.root)));path=Path(__file__).with_suffix('.json')
 if a.write:path.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 else:require(exact(r,json.loads(path.read_text())),'Saved receipt differs')
 print(json.dumps({k:r[k] for k in ('status','checks','frontier')},indent=2))
