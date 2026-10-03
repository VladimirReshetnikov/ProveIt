#!/usr/bin/env python3
"""Exact binary-plane seven-cut affine rewrite of the reviewed 99-gate block.

rewrite(packet) accepts compatible complete sources with the frozen99 affine
closure and seven cut names. It preserves every comparison and the full SOS
on all integer tuples, saving8 multiplications and1 addition. Downstream edits
and reordered sources are allowed; private affine consumers are rejected.
This narrow source transformer is not a canonical full compiler.
"""
import argparse,copy,hashlib,json,random
from pathlib import Path
if not __debug__:raise RuntimeError('Exact-affine research checker requires assertions; omit -O')
CUTS=('J','S','Dir','W','WD','Qdev','Ndev')
PARENT_SOURCE_SHA256='eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330'
PARENT_RECEIPT_SHA256='5a734c98ad6c6cda6efa5ced74ff7617e305419f11d9d960def8b292c83d0023'
_RULES=((0, 0, 9, 0, 0), (0, 1, 0, 0, 1), (9, 0, 2, 0, 1), (9, 1, 0, 0, 1), (2, 0, 6, 1, 0), (2, 1, 4, 1, 0), (3, 0, 5, 1, 0), (3, 1, 4, 1, 1), (4, 0, 0, 0, 1), (4, 1, 3, 1, 1), (5, 0, 3, 1, 1), (5, 1, 3, 1, 1), (6, 0, 7, 1, 0), (6, 1, 6, 1, 1), (7, 0, 8, 1, 1), (7, 1, 6, 1, 1), (8, 0, 0, 0, 0), (8, 1, 1, 1, 1), (1, 0, 10, 1, 1), (10, 0, 11, 0, 0), (10, 1, 13, 0, 1), (11, 0, 12, 0, 0), (11, 1, 11, 0, 1), (12, 0, 9, 1, 0), (12, 1, 11, 0, 1), (13, 0, 2, 1, 0), (13, 1, 14, 0, 0), (14, 0, 13, 0, 0), (14, 1, 13, 0, 1))
_OLD_CUTS=(('J', 'joint43'), ('S', 'joint50'), ('Dir', 'joint44'), ('W', 'joint45'), ('WD', 'joint46'), ('Qdev', 'joint70'), ('Ndev', 'joint99'))
_OLD_ROWS=(('joint0', '+', 'edge0', 'edge1'), ('joint1', '+', 'edge4', 'edge5'), ('joint2', '+', 'edge6', 'edge7'), ('joint3', '+', 'edge8', 'edge9'), ('joint4', '+', 'edge10', 'edge11'), ('joint5', '+', 'edge12', 'edge13'), ('joint7', '+', 'edge16', 'edge17'), ('joint8', '+', 'edge2', 'edge3'), ('joint9', '+', 'edge19', 'edge20'), ('joint10', '+', 'edge21', 'edge22'), ('joint11', '+', 'edge23', 'edge24'), ('joint12', '+', 'edge25', 'edge26'), ('joint13', '+', 'edge27', 'edge28'), ('joint14', '+', 'edge22', 'edge24'), ('joint15', '+', 'edge13', 'edge15'), ('joint16', '+', 'edge0', 'edge16'), ('joint17', '+', 'edge19', 'joint16'), ('joint18', '+', 'edge21', 'joint17'), ('joint19', '+', 'edge27', 'joint18'), ('joint20', '+', 'edge2', 'edge8'), ('joint21', '+', 'edge4', 'edge6'), ('joint22', '+', 'edge12', 'joint21'), ('joint23', '+', 'edge23', 'joint22'), ('joint24', '+', 'edge25', 'joint23'), ('joint25', '+', 'edge10', 'edge14'), ('joint26', '+', 'edge18', 'joint25'), ('joint27', '+', 'edge1', 'edge3'), ('joint28', '+', 'edge20', 'joint27'), ('joint29', '+', 'joint14', 'joint28'), ('joint30', '+', 'edge28', 'joint29'), ('joint31', '+', 'edge7', 'edge9'), ('joint32', '+', 'edge11', 'joint31'), ('joint33', '+', 'joint15', 'joint32'), ('joint34', '+', 'edge17', 'joint33'), ('joint35', '+', 'edge26', 'joint19'), ('joint36', '+', 'joint20', 'joint30'), ('joint37', '+', 'edge5', 'joint24'), ('joint38', '+', 'joint26', 'joint34'), ('joint39', '+', 'joint37', 'joint38'), ('joint40', '+', 'joint36', 'joint38'), ('joint41', '+', 'joint36', 'joint39'), ('joint42', '+', 'joint35', 'joint41'), ('joint43', '-', 'joint42', 29), ('joint44', '-', 'joint39', 15), ('joint45', '-', 'joint40', 17), ('joint46', '-', 'joint38', 9), ('joint47', '+', 'edge26', 'joint30'), ('joint48', '+', 'edge5', 'joint47'), ('joint49', '+', 'joint34', 'joint48'), ('joint50', '-', 'joint49', 14), ('joint51', '-', 'joint7', 'joint5'), ('joint52', '-', 'joint8', 'joint4'), ('joint53', '*', 'joint52', 2), ('joint54', '-', 'joint9', 'joint3'), ('joint55', '*', 'joint54', 3), ('joint56', '-', 'joint10', 'joint2'), ('joint57', '*', 'joint56', 4), ('joint58', '-', 'joint11', 'joint1'), ('joint59', '*', 'joint58', 5), ('joint60', '-', 'joint12', 'edge18'), ('joint61', '*', 'joint60', 6), ('joint62', '-', 'joint13', 'joint0'), ('joint63', '*', 'joint62', 7), ('joint64', '+', 'joint51', 'joint53'), ('joint65', '+', 'joint55', 'joint64'), ('joint66', '+', 'joint57', 'joint65'), ('joint67', '+', 'joint59', 'joint66'), ('joint68', '+', 'joint61', 'joint67'), ('joint69', '+', 'joint63', 'joint68'), ('joint70', '-', 'joint69', 6), ('joint71', '+', 'edge8', 'joint27'), ('joint72', '+', 'edge16', 'joint71'), ('joint73', '+', 'edge2', 'edge25'), ('joint74', '+', 'edge9', 'joint4'), ('joint75', '+', 'edge5', 'edge7'), ('joint76', '+', 'edge4', 'joint15'), ('joint77', '+', 'edge0', 'edge23'), ('joint78', '+', 'edge19', 'joint14'), ('joint79', '+', 'edge20', 'joint13'), ('joint80', '-', 'edge14', 'joint76'), ('joint81', '-', 'joint77', 'edge6'), ('joint82', '*', 'joint81', 2), ('joint83', '-', 'edge18', 'joint75'), ('joint84', '*', 'joint83', 3), ('joint85', '-', 'joint78', 'joint74'), ('joint86', '*', 'joint85', 4), ('joint87', '-', 'edge21', 'joint73'), ('joint88', '*', 'joint87', 5), ('joint89', '-', 'joint79', 'edge17'), ('joint90', '*', 'joint89', 6), ('joint91', '-', 'edge26', 'joint72'), ('joint92', '*', 'joint91', 7), ('joint93', '+', 'joint80', 'joint82'), ('joint94', '+', 'joint84', 'joint93'), ('joint95', '+', 'joint86', 'joint94'), ('joint96', '+', 'joint88', 'joint95'), ('joint97', '+', 'joint90', 'joint96'), ('joint98', '+', 'joint92', 'joint97'), ('joint99', '-', 'joint98', -17))
_NEW_ROWS=(('binary0', '+', 'edge20', 'edge28'), ('binary1', '+', 'edge1', 'edge8'), ('binary2', '+', 'edge11', 'edge9'), ('binary3', '+', 'edge17', 'binary2'), ('binary4', '+', 'edge13', 'edge7'), ('binary5', '+', 'edge15', 'binary4'), ('binary6', '+', 'edge2', 'edge3'), ('binary7', '+', 'edge27', 'binary0'), ('binary8', '+', 'edge22', 'edge24'), ('binary9', '+', 'edge14', 'edge18'), ('binary10', '+', 'edge4', 'edge5'), ('binary11', '+', 'binary3', 'binary5'), ('binary12', '+', 'edge26', 'binary7'), ('binary13', '+', 'binary11', 'binary9'), ('binary14', '+', 'binary1', 'binary6'), ('binary15', '+', 'edge10', 'binary13'), ('binary16', '+', 'edge19', 'binary12'), ('binary17', '+', 'edge0', 'edge18'), ('binary18', '+', 'edge16', 'edge25'), ('binary19', '+', 'edge12', 'binary10'), ('binary20', '+', 'binary14', 'binary18'), ('binary21', '+', 'edge21', 'binary8'), ('binary22', '-', 'edge25', 'binary17'), ('binary23', '+', 'edge23', 'binary15'), ('binary24', '+', 'edge16', 'edge17'), ('binary25', '-', 'edge10', 'binary16'), ('binary26', '+', 'edge6', 'edge7'), ('binary27', '-', 'edge23', 'binary1'), ('binary28', '+', 'binary0', 'binary8'), ('binary29', '+', 'edge6', 'binary23'), ('binary30', '+', 'edge0', 'binary19'), ('binary31', '+', 'edge3', 'edge5'), ('binary32', '-', 'edge26', 'binary10'), ('binary33', '+', 'binary16', 'binary20'), ('binary34', '+', 'binary21', 'binary33'), ('binary35', '+', 'binary29', 'binary34'), ('binary36', '+', 'binary30', 'binary35'), ('binary37', '+', 'edge1', 'edge26'), ('binary38', '+', 'binary11', 'binary37'), ('binary39', '+', 'binary28', 'binary38'), ('binary40', '+', 'binary31', 'binary39'), ('binary41', '+', 'edge25', 'binary19'), ('binary42', '+', 'binary29', 'binary41'), ('binary43', '+', 'binary14', 'binary15'), ('binary44', '+', 'binary28', 'binary43'), ('binary45', '+', 'edge19', 'edge24'), ('binary46', '+', 'binary24', 'binary45'), ('binary47', '+', 'binary27', 'binary46'), ('binary48', '+', 'binary47', 'binary7'), ('binary49', '+', 'edge13', 'edge9'), ('binary50', '+', 'binary30', 'binary49'), ('binary51', '-', 'binary48', 'binary50'), ('binary52', '+', 'binary22', 'binary6'), ('binary53', '+', 'binary1', 'binary2'), ('binary54', '+', 'binary25', 'binary53'), ('binary55', '-', 'binary52', 'binary54'), ('binary56', '+', 'edge23', 'edge27'), ('binary57', '+', 'edge28', 'binary56'), ('binary58', '+', 'binary21', 'binary57'), ('binary59', '+', 'binary22', 'binary58'), ('binary60', '+', 'binary32', 'binary59'), ('binary61', '+', 'edge1', 'binary26'), ('binary62', '-', 'binary60', 'binary61'), ('binary63', '+', 'edge21', 'binary32'), ('binary64', '+', 'binary63', 'binary9'), ('binary65', '+', 'binary20', 'binary5'), ('binary66', '-', 'binary64', 'binary65'), ('binary67', '+', 'binary12', 'binary17'), ('binary68', '+', 'binary27', 'binary67'), ('binary69', '+', 'binary24', 'binary26'), ('binary70', '+', 'binary31', 'binary69'), ('binary71', '-', 'binary68', 'binary70'), ('binary72', '+', 'binary20', 'binary25'), ('binary73', '+', 'binary3', 'binary72'), ('binary74', '-', 'binary21', 'binary73'), ('binary75', '-', 'binary36', 29), ('binary76', '-', 'binary40', 14), ('binary77', '-', 'binary42', 15), ('binary78', '-', 'binary44', 17), ('binary79', '-', 'binary15', 9), ('binary80', '*', 'binary62', 2), ('binary81', '+', 'binary55', 'binary80'), ('binary82', '*', 'binary81', 2), ('binary83', '+', 'binary51', 'binary82'), ('binary84', '-', 'binary83', 6), ('binary85', '*', 'binary74', 2), ('binary86', '+', 'binary71', 'binary85'), ('binary87', '*', 'binary86', 2), ('binary88', '+', 'binary66', 'binary87'), ('binary89', '-', 'binary88', -17))
_NEW_CUTS=(('J', 'binary75'), ('S', 'binary76'), ('Dir', 'binary77'), ('W', 'binary78'), ('WD', 'binary79'), ('Qdev', 'binary84'), ('Ndev', 'binary89'))

def _affine(rows,node):
 rows={n:(op,a,b) for n,op,a,b in rows};cache={}
 def get(n):
  if type(n)is int:return {'':n} if n else {}
  if n not in rows:return {n:1}
  if n in cache:return cache[n]
  op,a,b=rows[n];a=get(a);b=get(b)
  if op in ('+','-'):
   z=dict(a)
   for k,v in b.items():z[k]=z.get(k,0)+(v if op=='+' else -v)
  elif set(a)<={''}:z={k:a.get('',0)*v for k,v in b.items()}
  elif set(b)<={''}:z={k:b.get('',0)*v for k,v in a.items()}
  else:raise ValueError('nonlinear cut')
  cache[n]={k:v for k,v in z.items() if v};return cache[n]
 return get(node)

def _count(rows):return {'operations':len(rows),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows)}

def _require(condition,message):
 if not condition:raise ValueError(message)

def _exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and _exact(a[k],b[k]) for k in a)
 if type(a)in (list,tuple):return len(a)==len(b) and all(_exact(x,y) for x,y in zip(a,b))
 return a==b

def _atom(v):return type(v)is int or type(v)is str

def _canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)

def _rows(value):
 _require(type(value)in (list,tuple),'Rows must be a list/tuple')
 result=[]
 for row in value:
  _require(type(row)in (list,tuple) and len(row)==4,'Binary row required')
  n,op,a,b=row
  _require(type(n)is str and type(op)is str and op in ('+','-','*') and _atom(a) and _atom(b),'Exact binary integer row required')
  result.append((n,op,a,b))
 return tuple(result)

def _finish(packet):
 p=copy.deepcopy(packet);source=[list(row) for row in _rows(p['source'])];squares=[]
 for i,(a,b) in enumerate(p['comparisons']):
  n=f'poly_res{i}';q=f'poly_sq{i}';source.extend([[n,'-',a,b],[q,'*',n,n]]);squares.append(q)
 out=squares[0]
 for i,n in enumerate(squares[1:],1):q=f'poly_sum{i}';source.append([q,'+',out,n]);out=q
 available=set(p['parameters']+p['auxiliaries']);needed={out}
 for n,op,a,b in source:
  _require(n not in available and all(type(x)is int or x in available for x in (a,b)),'Invalid or duplicate/forward source reference');available.add(n)
 for n,op,a,b in reversed(source):
  if n in needed:needed.update(x for x in (a,b) if type(x)is str)
 _require(all(n in needed for n,op,a,b in source),'Dead emitted source')
 degrees={n:0 if n in p['fixed_parameters'] else 1 for n in p['parameters']+p['auxiliaries']}
 for n,op,a,b in source:
  da=degrees[a] if type(a)is str else 0;db=degrees[b] if type(b)is str else 0;degrees[n]=da+db if op=='*' else max(da,db)
 p.update(polynomial_source=source,output=out,ledger={'certificate':_count(p['source']),'polynomial':_count(source),'positive_witnesses':len(p['auxiliaries']),'equations':len(p['comparisons']),'formal_degree_upper_bound':degrees[out],'exact_degree_claimed':False})
 return p

def _data(value):
 t=type(value)
 if t in (int,str,bool,type(None)):return
 if t in (list,tuple):
  for v in value:_data(v)
 elif t is dict:
  _require(all(type(k)is str for k in value),'Metadata keys must be strings')
  for v in value.values():_data(v)
 else:raise ValueError('Exact builtin data required, no fractional/foreign scalar types')

def _validate(packet):
 _require(type(packet)is dict,'Packet dictionary required');_data(packet)
 _require(type(packet.get('ordinary'))is bool,'ordinary must be Boolean')
 for key in ('parameters','auxiliaries','fixed_parameters'):
  v=packet.get(key);_require(type(v)is list and all(type(n)is str for n in v) and len(v)==len(set(v)),key+' must be distinct names')
 _require(not set(packet['parameters'])&set(packet['auxiliaries']) and set(packet['fixed_parameters'])<=set(packet['parameters']),'Coordinate declarations overlap')
 _require(type(packet.get('registers'))is dict and all(_atom(v) for v in packet['registers'].values()),'Named register map required')
 _require(type(packet.get('rules'))in (list,tuple) and all(type(r)in (list,tuple) for r in packet['rules']),'Rule table required')
 _require(_exact(tuple(tuple(r) for r in packet['rules']),_RULES),'Relabeled29-rule table changed')
 _require(_exact(tuple((n,packet['registers'].get(n)) for n in CUTS),_OLD_CUTS),'Seven canonical536 cut names changed')
 pairs=packet.get('comparisons');_require(type(pairs)is list and bool(pairs),'Nonempty complete comparison list required')
 _require(all(type(pair)in (list,tuple) and len(pair)==2 and all(_atom(v) for v in pair) for pair in pairs),'Exact comparison operands required')
 source=_rows(packet['source']);actual={n:(n,op,a,b) for n,op,a,b in source};closure=set()
 def visit(n):
  if n in actual and n not in closure:
   closure.add(n)
   for v in actual[n][2:]:
    if type(v)is str:visit(v)
 for name,n in _OLD_CUTS:visit(n)
 _require(_exact({n:actual[n] for n in closure},{r[0]:r for r in _OLD_ROWS}),'Canonical536 affine closure changed')
 cutnodes={n for name,n in _OLD_CUTS}
 for n,op,a,b in source:
  if n not in closure:_require(all(v not in closure or v in cutnodes for v in (a,b)),'Affine intermediate has another downstream consumer')
 for pair in pairs:_require(all(v not in closure or v in cutnodes for v in pair),'Affine intermediate appears in another comparison')
 known=set(packet['parameters']+packet['auxiliaries'])|set(actual)
 _require(all(type(v)is int or v in known for v in packet['registers'].values()),'Unknown semantic register')
 current=_finish(packet)
 _require(_exact(_rows(packet['polynomial_source']),_rows(current['polynomial_source'])) and _exact(packet['output'],current['output']),'Stored complete SOS does not match source/comparisons')
 return closure

def replacement():
 """Return fresh fully paid90 rows and the seven new cut registers."""
 return [list(r) for r in _NEW_ROWS],dict(_NEW_CUTS)

def _identity_certificate(old,new,cuts):
 # Independently intern the entire emitted SOS after replacing only the seven
 # already proved affine vectors by formal cut symbols.
 intern={}
 def node(key):
  if key not in intern:intern[key]=len(intern)
  return intern[key]
 def walk(packet,named):
  cut={v:k for k,v in named.items()};env={n:node(('input',n)) for n in packet['parameters']+packet['auxiliaries']}
  def at(x):return env[x] if type(x)is str else node(('integer',x))
  for n,op,a,b in packet['polynomial_source']:
   aa,bb=at(a),at(b)
   if op in ('+','*'):aa,bb=sorted((aa,bb))
   env[n]=node(('cut',cut[n])) if n in cut else node((op,aa,bb))
  return ([(at(a),at(b)) for a,b in packet['comparisons']],
    {name:{k:at(v) for k,v in packet.get(name,{}).items()} for name in ('registers','tag_registers','computed_loader_fields')},at(packet['output']))
 _require(walk(old,dict(_OLD_CUTS))==walk(new,cuts),'Complete residual/SOS DAG identity failed')
 return {'full_polynomial_DAG_identity':True,'expression_nodes':len(intern),'comparison_operands':2*len(old['comparisons'])}

def rewrite(packet):
 """Return (fresh complete packet, exact affine-cut certificate).

Only the canonical536 affine closure is required; unrelated downstream source,
comparisons, coordinate lists and their ordering may already have been changed.
Their complete source/SOS must be valid, and no removed private affine node may
be referenced by a downstream row, comparison or other metadata entry.
"""
 removed=_validate(packet);rows,cuts=replacement();oldcuts=dict(_OLD_CUTS)
 aliases={oldcuts[name]:cuts[name] for name in CUTS}
 available=set(packet['parameters']+packet['auxiliaries'])|{n for n,op,a,b in packet['source'] if n not in removed}
 _require(not available&{n for n,op,a,b in rows},'Replacement node name collision')
 forms={}
 for name in CUTS:
  old=_affine(packet['source'],oldcuts[name]);new=_affine(rows,cuts[name]);_require(_exact(old,new),'Affine coefficient identity failed');forms[name]=new
 def metadata(value):
  if type(value)is str:
   _require(value not in removed or value in aliases,'Removed affine intermediate referenced in metadata')
   return aliases.get(value,value)
  if type(value)is list:return [metadata(x) for x in value]
  if type(value)is tuple:return tuple(metadata(x) for x in value)
  if type(value)is dict:return {metadata(k):metadata(v) for k,v in value.items()}
  return value
 p={k:metadata(copy.deepcopy(v)) for k,v in packet.items() if k not in ('source','polynomial_source','comparisons','ledger','output')}
 subst=lambda v:aliases.get(v,v)
 p['source']=rows+[[n,op,subst(a),subst(b)] for n,op,a,b in packet['source'] if n not in removed]
 p['comparisons']=[[subst(a),subst(b)] for a,b in packet['comparisons']]
 p=_finish(p)
 proof={'parent_affine_anchor_sha256':hashlib.sha256(_canonical(_OLD_ROWS).encode()).hexdigest(),
        'incoming_complete_polynomial_sha256':hashlib.sha256(_canonical(packet['polynomial_source']).encode()).hexdigest(),
        'replacements':aliases,'exact_affine_forms':forms,'removed_rows':99,'replacement_rows':90,
        'saved_additions':1,'saved_multiplications':8,'complete_polynomial_identity_on_all_integers':True,
        'unchanged_downstream_source_rows':len(packet['source'])-99,
        'full_source_certificate':_identity_certificate(packet,p,cuts)}
 p['affine_rewrite']={'source':'u15_joint_binary_affine_rewrite.py','canonical536_source_sha256':PARENT_SOURCE_SHA256,
   'contract':'Exact canonical536 seven-cut affine closure; complete integer-polynomial identity relative to supplied valid parent source/SOS.',
   'replacements':dict(aliases),'saved_additions':1,'saved_multiplications':8}
 before=_count(packet['polynomial_source']);after=p['ledger']['polynomial']
 _require(before['operations']==after['operations']+9 and before['M']==after['M']+8 and before['A']==after['A']+1,'Complete operation saving changed')
 return p,proof

def _execute(packet,values):
 env=dict(values)
 for n,op,a,b in packet['polynomial_source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 residuals=[(env[a] if type(a)is str else a)-(env[b] if type(b)is str else b) for a,b in packet['comparisons']]
 return env[packet['output']],residuals

def _verify(source,receipt):
 _require(hashlib.sha256(source.read_bytes()).hexdigest()==PARENT_SOURCE_SHA256,'Frozen536 source changed')
 _require(hashlib.sha256(receipt.read_bytes()).hexdigest()==PARENT_RECEIPT_SHA256,'Frozen536 receipt changed')
 parents=[row['compiler'] for row in json.loads(receipt.read_text())['forms']];rng=random.Random(5862900);records=[];stats={'exact_full_DAG_identities':0,'full_output_and_residual_cases':0,'signed_cases':0,'malformed_rejected':0,'defensive_copy_checks':0,'adapter_cases':0}
 def reject(p):
  try:rewrite(p)
  except (ValueError,TypeError,KeyError):stats['malformed_rejected']+=1;return
  raise AssertionError('Malformed affine source accepted')
 for parent in parents:
  child,proof=rewrite(parent);stats['exact_full_DAG_identities']+=1
  _require(child['ledger']['polynomial']['operations']==(527 if parent['ordinary'] else 329),'Expected527/329')
  for case in range(32):
   values={n:rng.randrange(-4,7) if case>=16 else rng.randrange(1,8) for n in parent['parameters']+parent['auxiliaries']}
   assert _execute(parent,values)==_execute(child,values);stats['full_output_and_residual_cases']+=1;stats['signed_cases']+=int(case>=16)
  for value in (1.0,True):
   for location in ('source','poly','rule'):
    p=copy.deepcopy(parent)
    if location=='source':next(r for r in p['source'] if r[0]==dict(_OLD_CUTS)['J'])[3]=value
    elif location=='poly':p['polynomial_source'][-1][3]=value
    else:p['rules'][0][0]=value
    reject(p)
  for name in CUTS:
   p=copy.deepcopy(parent);p['registers'][name]='edge0';reject(p)
  p=copy.deepcopy(parent);p['registers']['extra_private']='joint0';reject(p)
  p=copy.deepcopy(parent);p.setdefault('tag_registers',{})['extra_private']='joint0';reject(p)
  p=copy.deepcopy(parent);p['source'].append(['illegal_alias','+','joint0',1]);p['comparisons'].append(['illegal_alias',0]);p=_finish(p);reject(p)
  p=copy.deepcopy(parent);p['comparisons'].append(['joint0',0]);p=_finish(p);reject(p)
  p=copy.deepcopy(parent);p['source'].append(['binary0','+','edge0',1]);p['comparisons'].append(['binary0',0]);p=_finish(p);reject(p)
  p=copy.deepcopy(parent);p['source'][0][2]='missing_input';reject(p)
  # Additional downstream use of an allowed cut plus its metadata alias remains valid.
  p=copy.deepcopy(parent);p['source'].append(['adapter_extra','+',p['registers']['J'],1]);p['comparisons'].append(['adapter_extra',0]);p['registers']['J_alias']=p['registers']['J'];p=_finish(p)
  c,pr=rewrite(p);assert c['registers']['J_alias']==c['registers']['J']
  assert _execute(p,values)==_execute(c,values);stats['adapter_cases']+=1
  # Move the entire independent affine block before other source. No order pin.
  p=copy.deepcopy(parent);selected={r[0] for r in _OLD_ROWS};p['source']=[r for r in p['source'] if r[0] in selected]+[r for r in p['source'] if r[0] not in selected];p=_finish(p)
  c,_=rewrite(p);assert _execute(p,values)==_execute(c,values);stats['adapter_cases']+=1
  for name in ('source','registers','affine_rewrite'):
   mutant=copy.deepcopy(child);mutant[name].clear();fresh,_=rewrite(parent);assert _exact(fresh,child);stats['defensive_copy_checks']+=1
  rows,cuts=replacement();rows[0][2]='mutant';cuts.clear();assert replacement()[0][0][2]!='mutant';stats['defensive_copy_checks']+=1
  records.append({'ordinary':parent['ordinary'],'parent_ledger':parent['ledger'],'ledger':child['ledger'],'proof':proof,'compiler':child})
 return {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'canonical536_source_sha256':PARENT_SOURCE_SHA256,'canonical536_receipt_sha256':PARENT_RECEIPT_SHA256,'counts':stats,'forms':records,'scope':'Narrow exact seven-cut affine rewrite, no new machine semantics or exact-degree claim.'}

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--parent-source',type=Path,required=True);parser.add_argument('--parent-receipt',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);parser.add_argument('--expect',type=Path);args=parser.parse_args()
 result=_verify(args.parent_source,args.parent_receipt)
 if args.expect is not None:_require(_exact(result,json.loads(args.expect.read_text())),'Saved receipt differs')
 args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'counts':result['counts'],'ledgers':[r['ledger'] for r in result['forms']]},indent=2))
