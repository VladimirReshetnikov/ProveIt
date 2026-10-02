#!/usr/bin/env python3
"""Narrow exact affine rewrite611→586, reusable after independent downstream edits.

rewrite(packet) requires the exact reviewed611 affine block and seven cut names,
valid complete binary source/SOS and no other consumers of removed intermediates.
It preserves the complete polynomial on every integer supplied tuple. It does not
validate arbitrary program semantics or provide a new halting-universality theorem.
No cache or mutable canonical object is exposed. replacement() returns fresh data.
"""
import argparse,copy,hashlib,json,random
from pathlib import Path
if not __debug__:raise RuntimeError('Exact-affine research checker requires assertions; omit -O')
CUTS=('J','S','Dir','W','WD','Qdev','Ndev')
PARENT_SOURCE_SHA256='3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce'
PARENT_RECEIPT_SHA256='440da084053344360ee21ffc6a7ad41c9aab72732663d7f2b201f27cdfb44244'
_RULES=((0, 0, 9, 0, 0), (0, 1, 0, 0, 1), (9, 0, 2, 0, 1), (9, 1, 0, 0, 1), (2, 0, 6, 1, 0), (2, 1, 4, 1, 0), (3, 0, 5, 1, 0), (3, 1, 4, 1, 1), (4, 0, 0, 0, 1), (4, 1, 3, 1, 1), (5, 0, 3, 1, 1), (5, 1, 3, 1, 1), (6, 0, 7, 1, 0), (6, 1, 6, 1, 1), (7, 0, 8, 1, 1), (7, 1, 6, 1, 1), (8, 0, 0, 0, 0), (8, 1, 1, 1, 1), (1, 0, 10, 1, 1), (10, 0, 11, 0, 0), (10, 1, 13, 0, 1), (11, 0, 12, 0, 0), (11, 1, 11, 0, 1), (12, 0, 9, 1, 0), (12, 1, 11, 0, 1), (13, 0, 2, 1, 0), (13, 1, 14, 0, 0), (14, 0, 13, 0, 0), (14, 1, 13, 0, 1))
_OLD_CUTS=(('J', 'v28'), ('S', 'v68'), ('Dir', 'v109'), ('W', 'v122'), ('WD', 'v129'), ('Qdev', 'v54'), ('Ndev', 'v99'))
_OLD_ROWS=(('v0', '+', 'edge0', 'edge1'), ('v1', '+', 'edge2', 'edge3'), ('v2', '+', 'edge4', 'edge5'), ('v3', '+', 'edge6', 'edge7'), ('v4', '+', 'edge8', 'edge9'), ('v5', '+', 'edge10', 'edge11'), ('v6', '+', 'edge12', 'edge13'), ('v7', '+', 'edge14', 'edge15'), ('v8', '+', 'edge16', 'edge17'), ('v9', '+', 'edge19', 'edge20'), ('v10', '+', 'edge21', 'edge22'), ('v11', '+', 'edge23', 'edge24'), ('v12', '+', 'edge25', 'edge26'), ('v13', '+', 'edge27', 'edge28'), ('v14', '+', 'v0', 'v1'), ('v15', '+', 'v14', 'v2'), ('v16', '+', 'v15', 'v3'), ('v17', '+', 'v16', 'v4'), ('v18', '+', 'v17', 'v5'), ('v19', '+', 'v18', 'v6'), ('v20', '+', 'v19', 'v7'), ('v21', '+', 'v20', 'v8'), ('v22', '+', 'edge18', 'v21'), ('v23', '+', 'v22', 'v9'), ('v24', '+', 'v10', 'v23'), ('v25', '+', 'v11', 'v24'), ('v26', '+', 'v12', 'v25'), ('v27', '+', 'v13', 'v26'), ('v28', '-', 'v27', 29), ('v35', '-', 'v8', 'v6'), ('v36', '-', 'v1', 'v5'), ('v37', '*', 'v36', 2), ('v38', '-', 'v9', 'v4'), ('v39', '*', 'v38', 3), ('v40', '-', 'v10', 'v3'), ('v41', '*', 'v40', 4), ('v42', '-', 'v11', 'v2'), ('v43', '*', 'v42', 5), ('v44', '-', 'v12', 'edge18'), ('v45', '*', 'v44', 6), ('v46', '-', 'v13', 'v0'), ('v47', '*', 'v46', 7), ('v48', '+', 'v35', 'v37'), ('v49', '+', 'v39', 'v48'), ('v50', '+', 'v41', 'v49'), ('v51', '+', 'v43', 'v50'), ('v52', '+', 'v45', 'v51'), ('v53', '+', 'v47', 'v52'), ('v54', '-', 'v53', 6), ('v55', '+', 'edge1', 'edge3'), ('v56', '+', 'edge5', 'v55'), ('v57', '+', 'edge7', 'v56'), ('v58', '+', 'edge9', 'v57'), ('v59', '+', 'edge11', 'v58'), ('v60', '+', 'edge13', 'v59'), ('v61', '+', 'edge15', 'v60'), ('v62', '+', 'edge17', 'v61'), ('v63', '+', 'edge20', 'v62'), ('v64', '+', 'edge22', 'v63'), ('v65', '+', 'edge24', 'v64'), ('v66', '+', 'edge26', 'v65'), ('v67', '+', 'edge28', 'v66'), ('v68', '-', 'v67', 14), ('v69', '+', 'edge8', 'v55'), ('v70', '+', 'edge16', 'v69'), ('v71', '+', 'edge2', 'edge25'), ('v72', '+', 'edge9', 'v5'), ('v73', '+', 'edge5', 'edge7'), ('v74', '+', 'edge13', 'edge4'), ('v75', '+', 'edge15', 'v74'), ('v76', '+', 'edge0', 'edge23'), ('v77', '+', 'edge19', 'edge22'), ('v78', '+', 'edge24', 'v77'), ('v79', '+', 'edge20', 'v13'), ('v80', '-', 'edge14', 'v75'), ('v81', '-', 'v76', 'edge6'), ('v82', '*', 'v81', 2), ('v83', '-', 'edge18', 'v73'), ('v84', '*', 'v83', 3), ('v85', '-', 'v78', 'v72'), ('v86', '*', 'v85', 4), ('v87', '-', 'edge21', 'v71'), ('v88', '*', 'v87', 5), ('v89', '-', 'v79', 'edge17'), ('v90', '*', 'v89', 6), ('v91', '-', 'edge26', 'v70'), ('v92', '*', 'v91', 7), ('v93', '+', 'v80', 'v82'), ('v94', '+', 'v84', 'v93'), ('v95', '+', 'v86', 'v94'), ('v96', '+', 'v88', 'v95'), ('v97', '+', 'v90', 'v96'), ('v98', '+', 'v92', 'v97'), ('v99', '-', 'v98', -17), ('v100', '+', 'v2', 'v3'), ('v101', '+', 'edge9', 'v100'), ('v102', '+', 'v101', 'v5'), ('v103', '+', 'v102', 'v6'), ('v104', '+', 'v103', 'v7'), ('v105', '+', 'edge17', 'v104'), ('v106', '+', 'edge18', 'v105'), ('v107', '+', 'edge23', 'v106'), ('v108', '+', 'edge25', 'v107'), ('v109', '-', 'v108', 15), ('v110', '+', 'edge1', 'v1'), ('v111', '+', 'edge7', 'v110'), ('v112', '+', 'v111', 'v4'), ('v113', '+', 'v112', 'v5'), ('v114', '+', 'edge13', 'v113'), ('v115', '+', 'v114', 'v7'), ('v116', '+', 'edge17', 'v115'), ('v117', '+', 'edge18', 'v116'), ('v118', '+', 'edge20', 'v117'), ('v119', '+', 'edge22', 'v118'), ('v120', '+', 'edge24', 'v119'), ('v121', '+', 'edge28', 'v120'), ('v122', '-', 'v121', 17), ('v123', '+', 'edge7', 'edge9'), ('v124', '+', 'v123', 'v5'), ('v125', '+', 'edge13', 'v124'), ('v126', '+', 'v125', 'v7'), ('v127', '+', 'edge17', 'v126'), ('v128', '+', 'edge18', 'v127'), ('v129', '-', 'v128', 9))

class _DAG:
 def __init__(self):self.rows=[];self.cache={};self.pairs=[]
 def g(self,op,a,b):
  if type(a)is int and type(b)is int:return a+b if op=='+' else a-b if op=='-' else a*b
  if op=='*' and (a==0 or b==0):return 0
  if op=='*' and a==1:return b
  if op=='*' and b==1:return a
  if op=='+' and a==0:return b
  if op in ('+','-') and b==0:return a
  if op=='-' and a==b:return 0
  if op in ('+','*') and repr(a)>repr(b):a,b=b,a
  key=(op,a,b)
  if key not in self.cache:
   n='joint'+str(len(self.rows));self.rows.append([n,op,a,b]);self.cache[key]=n
  return self.cache[key]
 def add(self,*args):
  active=list(args)
  if len(active)>1 and all(type(x)is str and x.startswith('edge') for x in active):
   for ids,value in self.pairs:
    names=[f'edge{i}' for i in ids]
    if all(active.count(n)==1 for n in names):
     first=min(active.index(n) for n in names);active=[n for n in active if n not in names];active.insert(first,value)
  a=0
  for b in active:a=self.g('+',a,b)
  return a
 def sub(self,a,b):return self.g('-',a,b)
 def mul(self,a,b):return self.g('*',a,b)
 def hats(self,ids):return self.add(*(f'edge{i}' for i in ids))
 def offset(self,a,n):return self.sub(a,n)
 def state(self,rules,col):
  bins={q:self.hats([i for i,r in enumerate(rules) if r[col]==q]) for q in range(15) if q!=7}
  return self.offset(self.add(*(self.mul(k,self.sub(bins[7+k],bins[7-k])) for k in range(1,8))),sum(r[col]-7 for r in rules))

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
 _require(_exact(tuple((n,packet['registers'].get(n)) for n in CUTS),_OLD_CUTS),'Seven canonical611 cut names changed')
 pairs=packet.get('comparisons');_require(type(pairs)is list and bool(pairs),'Nonempty complete comparison list required')
 _require(all(type(pair)in (list,tuple) and len(pair)==2 and all(_atom(v) for v in pair) for pair in pairs),'Exact comparison operands required')
 source=_rows(packet['source']);actual={n:(n,op,a,b) for n,op,a,b in source};closure=set()
 def visit(n):
  if n in actual and n not in closure:
   closure.add(n)
   for v in actual[n][2:]:
    if type(v)is str:visit(v)
 for name,n in _OLD_CUTS:visit(n)
 _require(_exact({n:actual[n] for n in closure},{r[0]:r for r in _OLD_ROWS}),'Canonical611 affine closure changed')
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
 """Fresh fully charged99-row replacement and the seven new cut registers."""
 d=_DAG()
 for q in range(15):
  ids=[i for i,r in enumerate(_RULES) if r[0]==q]
  if len(ids)==2:
   value=d.hats(ids);d.pairs.append((tuple(ids),value))
 for ids in ((22,24),(13,15)):
  value=d.hats(ids);d.pairs.insert(0,(ids,value))
 bins={(s,a,b):d.hats([i for i,r in enumerate(_RULES) if (r[1],r[3],r[4])==(s,a,b)]) for s in range(2) for a in range(2) for b in range(2)}
 groups={(a,b):d.add(bins[0,a,b],bins[1,a,b]) for a in range(2) for b in range(2)}
 C,A,B,D=[groups[p] for p in [(1,1),(1,0),(0,1),(0,0)]]
 dhat=d.add(C,A);what=d.add(C,B);jhat=d.add(dhat,B,D)
 cuts={'J':d.offset(jhat,29),'Dir':d.offset(dhat,15),'W':d.offset(what,17),'WD':d.offset(C,9),'S':d.offset(d.add(*(bins[1,a,b] for a in range(2) for b in range(2))),14)}
 cuts['Qdev']=d.state(_RULES,0);cuts['Ndev']=d.state(_RULES,2)
 needed=set(cuts.values())
 for n,op,a,b in reversed(d.rows):
  if n in needed:needed.update(v for v in (a,b) if type(v)is str)
 rows=[row for row in d.rows if row[0] in needed]
 _require(_count(rows)=={'operations':99,'M':12,'A':87},'Fixed schedule count changed')
 return copy.deepcopy(rows),dict(cuts)

def rewrite(packet):
 """Return (fresh complete packet, exact affine-cut certificate).

Only the canonical611 affine closure is required; unrelated downstream source,
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
        'replacements':aliases,'exact_affine_forms':forms,'removed_rows':124,'replacement_rows':99,
        'saved_additions':25,'saved_multiplications':0,'complete_polynomial_identity_on_all_integers':True,
        'unchanged_downstream_source_rows':len(packet['source'])-124}
 p['affine_rewrite']={'source':'u15_packed_joint_affine586.py','canonical611_source_sha256':PARENT_SOURCE_SHA256,
   'contract':'Exact canonical611 seven-cut affine closure; complete integer-polynomial identity relative to supplied valid parent source/SOS.',
   'replacements':dict(aliases),'saved_additions':25,'saved_multiplications':0}
 _require(_count(packet['polynomial_source'])['operations']==p['ledger']['polynomial']['operations']+25,'Complete operation saving changed')
 return p,proof

def _execute(packet,values):
 env=dict(values)
 for n,op,a,b in packet['polynomial_source']:
  a=env[a] if type(a)is str else a;b=env[b] if type(b)is str else b;env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 residuals=[(env[a] if type(a)is str else a)-(env[b] if type(b)is str else b) for a,b in packet['comparisons']]
 return env[packet['output']],residuals

def _verify(source,receipt):
 _require(hashlib.sha256(source.read_bytes()).hexdigest()==PARENT_SOURCE_SHA256,'Frozen611 source changed')
 _require(hashlib.sha256(receipt.read_bytes()).hexdigest()==PARENT_RECEIPT_SHA256,'Frozen611 receipt changed')
 parents=[row['compiler'] for row in json.loads(receipt.read_text())['forms']];rng=random.Random(5862900);records=[];stats={'full_output_and_residual_cases':0,'signed_cases':0,'malformed_rejected':0,'defensive_copy_checks':0,'adapter_cases':0}
 def reject(p):
  try:rewrite(p)
  except (ValueError,TypeError,KeyError):stats['malformed_rejected']+=1;return
  raise AssertionError('Malformed affine source accepted')
 for parent in parents:
  child,proof=rewrite(parent)
  _require(child['ledger']['polynomial']['operations']==(586 if parent['ordinary'] else 343),'Expected586/343')
  for case in range(32):
   values={n:rng.randrange(-4,7) if case>=16 else rng.randrange(1,8) for n in parent['parameters']+parent['auxiliaries']}
   assert _execute(parent,values)==_execute(child,values);stats['full_output_and_residual_cases']+=1;stats['signed_cases']+=int(case>=16)
  for value in (1.0,True):
   for location in ('source','poly','rule'):
    p=copy.deepcopy(parent)
    if location=='source':next(r for r in p['source'] if r[0]=='v28')[3]=value
    elif location=='poly':p['polynomial_source'][-1][3]=value
    else:p['rules'][0][0]=value
    reject(p)
  for name in CUTS:
   p=copy.deepcopy(parent);p['registers'][name]='edge0';reject(p)
  p=copy.deepcopy(parent);p['registers']['extra_private']='v0';reject(p)
  p=copy.deepcopy(parent);p.setdefault('tag_registers',{})['extra_private']='v0';reject(p)
  p=copy.deepcopy(parent);p['source'].append(['illegal_alias','+','v0',1]);p['comparisons'].append(['illegal_alias',0]);p=_finish(p);reject(p)
  p=copy.deepcopy(parent);p['comparisons'].append(['v0',0]);p=_finish(p);reject(p)
  p=copy.deepcopy(parent);p['source'].append(['joint0','+','edge0',1]);p['comparisons'].append(['joint0',0]);p=_finish(p);reject(p)
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
 return {'status':'PASS','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'canonical611_source_sha256':PARENT_SOURCE_SHA256,'canonical611_receipt_sha256':PARENT_RECEIPT_SHA256,'counts':stats,'forms':records,'scope':'Narrow exact seven-cut affine rewrite, no new machine semantics or exact-degree claim.'}

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--parent-source',type=Path,required=True);parser.add_argument('--parent-receipt',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
 result=_verify(args.parent_source,args.parent_receipt);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':result['status'],'counts':result['counts'],'ledgers':[r['ledger'] for r in result['forms']]},indent=2))
