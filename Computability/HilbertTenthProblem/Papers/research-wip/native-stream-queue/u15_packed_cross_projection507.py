"""Four paid operations removed from complete U15 sources by exact identities.

The 511 ordinary compiler becomes507; raw323 becomes319. The four ordinary
partition points become507/509/511/513 with identical complete polynomials.
No native factor, input, witness, comparison or finalizer is discarded.
"""
if not __debug__:
 raise RuntimeError('This research compiler requires assertions; omit -O')
from pathlib import Path
from copy import deepcopy
from functools import lru_cache
from collections import Counter
from fractions import Fraction
import argparse, hashlib, json, random, types

PINS={
 'u15_packed_composed_units511.py':'234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38',
 'u15_unit_partition_frontier.py':'8e0514876e26b716e792dd7d8332c773fe15989eb558fc7e4fedff8046249ccf',
}
FRONTIER=[([[0,1,2,3,4,5,6]],0,4881),([[0,1,2,4,6],[3,5]],None,3120),
          ([[0,1,4,6],[2,3],[5]],None,2116),([[0,1,2,6],[3],[4],[5]],None,1936)]
PARENT_DIGESTS = {'base:0:0': 'f8d71c1a07ada45796c6a4c9eb1f278edbec9be2c1d0345991b77862d2eb68d3', 'base:0:1': 'e0e7cdf28d003dc52fc38ce24fcc780985896190d025d8c9f3ceb773b7ab1896', 'base:1:0': '27a194397a48109ab3c1017a06b78961532bbaeda6d505b8d2e7e57538181a24', 'base:1:1': 'dcfee6dd08e839db69d0f66a31980e85cba04c95cc237a5bf578091d0e80ba20', 'frontier:0': '1fe1bb2b0ddd870aa1cef506b7bd6e0048cdd46903211603bf5b056894140e14', 'frontier:1': 'fca9624454701ff5d006a6d397c4fdb4a7eb0c829e88ffda2cfbba2fecddecbf', 'frontier:2': 'f63c885b84f3f2766cc7793b7c81c94501d8eb940633a3a333abc5ddf5dc534a', 'frontier:3': 'e1940c4c6c1f238c39f0cbe1641a9ebbc6c641aae6a699efcecf32a902f269f0'}

def require(ok,msg):
 if not ok:raise ValueError(msg)
def flag(x):require(type(x) is bool,'Exact Boolean required');return x
def exact(a,b):
 if type(a) is not type(b):return False
 if type(a) is dict:return a.keys()==b.keys() and all(type(k) is str and exact(a[k],b[k]) for k in a)
 if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def typed(x):
 if type(x) is dict:
  require(all(type(k) is str for k in x),'String keys required');return ['dict',[[k,typed(x[k])] for k in sorted(x)]]
 if type(x) in (list,tuple):return [type(x).__name__,[typed(y) for y in x]]
 require(type(x) in (int,bool,str,type(None)),'Unsupported canonical metadata type');return [type(x).__name__,x]
def digest(x):return hashlib.sha256(json.dumps(typed(x),separators=(',',':')).encode()).hexdigest()
def count(rows):
 m=sum(op=='*' for _,op,_,_ in rows);return dict(operations=len(rows),M=m,A=len(rows)-m)
def execute(rows,values):
 e=dict(values)
 for n,op,a,b in rows:
  x=e[a] if type(a) is str else a;y=e[b] if type(b) is str else b
  e[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return e
def at(e,x):return e[x] if type(x) is str else x

def source_check(p):
 require(type(p) is dict,'Packet required');typed(p)
 names=p['parameters']+p['auxiliaries'];require(all(type(n) is str for n in names) and len(set(names))==len(names),'Invalid coordinate list')
 require(type(p['source']) is list and type(p['polynomial_source']) is list,'Source lists required')
 for rows in (p['source'],p['polynomial_source']):
  known=set(names)
  for row in rows:
   require(type(row) is tuple and len(row)==4,'Exact source tuple required');n,op,a,b=row
   require(type(n) is str and n not in known and op in ('+','-','*'),'Invalid source register')
   require(all(type(x) is int or type(x) is str and x in known for x in (a,b)),'Invalid or unbound source operand');known.add(n)
 require(exact(p['polynomial_source'][:len(p['source'])],p['source']),'Certificate not complete prefix')
 require(type(p['comparisons']) is list and all(type(pair) is tuple and len(pair)==2 for pair in p['comparisons']),'Comparison tuples required')
 require(all(type(v) is int or type(v) is str and v in known for pair in p['comparisons'] for v in pair),'Unbound comparison')
 require(type(p['output']) is str and p['output'] in known,'Unbound output')

def local_polynomial(rows,target,leaves):
 env={name:{(name,):1} for name in leaves};table={n:(op,a,b) for n,op,a,b in rows}
 def value(x):
  if type(x) is int:return {():x} if x else {}
  if x in env:return env[x]
  require(x in table,'Local proof reached undeclared atom '+x);op,a,b=table[x];A=value(a);B=value(b);C=Counter()
  if op=='*':
   for ka,va in A.items():
    for kb,vb in B.items():C[tuple(sorted(ka+kb))]+=va*vb
  else:
   C.update(A)
   for k,v in B.items():C[k]+=v if op=='+' else -v
  env[x]={k:v for k,v in C.items() if v};return env[x]
 return value(target)

CUTS={
 'v142':('v139','ZU','binary28','binary14','binary15'),
 'v156':('binary83',),
 'v175':('binary77','v32','v169','v170'),
 'v262':('v175','v167','binary75','v169','v181','v193','v254'),
}

def _signatures(rows,names,cuts,intern):
 e={n:('input',n) for n in names}
 def val(x):return e[x] if type(x) is str else ('integer',x)
 # Hash-cons exact expression DAGs; the cut tokens stand for separately proved identities.
 for n,op,a,b in rows:
  key=(op,val(a),val(b))
  e[n]=('proved_cut',n) if n in cuts else ('node',intern.setdefault(key,len(intern)))
 return e

def _proof(old,new):
 local=[]
 for cut,leaves in CUTS.items():
  a=local_polynomial(old['source'],cut,leaves);b=local_polynomial(new['source'],cut,leaves);require(a==b,'Local polynomial identity failed '+cut)
  local.append(dict(cut=cut,independent_atoms=list(leaves),terms=[dict(monomial=list(k),coefficient=v) for k,v in sorted(a.items())]))
 names=old['parameters']+old['auxiliaries'];intern={}
 a=_signatures(old['polynomial_source'],names,CUTS,intern);b=_signatures(new['polynomial_source'],names,CUTS,intern)
 def token(e,x):return e[x] if type(x) is str else ('integer',x)
 # Leaves may be derived registers. They must themselves remain identical; otherwise local proofs do not compose.
 for leaves in CUTS.values():
  for n in leaves:require(a[n]==b[n],'Changed local proof atom '+n)
 require(exact(old['comparisons'],new['comparisons']),'Comparison list changed')
 for x,y in old['comparisons']:require(token(a,x)==token(b,x) and token(a,y)==token(b,y),'Complete comparison operand changed')
 require(a[old['output']]==b[new['output']],'Complete polynomial DAG differs beyond proved cuts')
 units=[]
 for f in old.get('unit_factors',[]):
  n=f['factor'];require(a[n]==b[n],'Native unit factor changed');units.append(n)
 return dict(local_polynomial_identities=local,unchanged_comparisons=len(old['comparisons']),
  identical_unit_factors=units,complete_output_identity=True,
  statement='Every complete polynomial and every comparison residual is identical on all integer tuples; all six protected factors and the sole checksum are unchanged when present.')

def rewrite(packet):
 """Typed local exact-polynomial transform; caller supplies the parent theorem.

This reusable pre-finalizer transform verifies its literal local arithmetic,
all cut dependencies, every comparison, and the complete finalizer DAG. It
makes no universality assertion for arbitrary caller-provided packet metadata.
"""
 source_check(packet);p=deepcopy(packet);oldrows={n:(op,a,b) for n,op,a,b in p['source']}
 expected={
 'binary43':('+','binary14','binary15'),'binary44':('+','binary28','binary43'),
 'binary78':('-','binary44',17),'binary79':('-','binary15',9),
 'binary84':('-','binary83',6),'v156':('+','binary84',7),
 'v131':('*','binary79',2),'v132':('+','ZU','v131'),'v140':('*','binary78',2),
 'v141':('+','v139','v140'),'v142':('-','v141','v132'),
 'v166':('*','binary77','v32'),'v173':('*','v166','v169'),'v174':('*','binary77','v170'),'v175':('+','v173','v174'),
 'v168':('*','v167','binary75'),'v251':('*','v193','binary75'),
 'v258':('*','v168','v169'),'v259':('*','v181','v258'),'v260':('*','v251','v254'),
 'v261':('+','v175','v259'),'v262':('+','v260','v261'),
 }
 require(all(oldrows.get(n)==r for n,r in expected.items()),'Literal cross-projection source contract changed')
 added={
 'v140':[('cross_write_sum','+','binary28','binary14'),('cross_write_only','-','cross_write_sum',8),('v140','*','cross_write_only',2)],
 'v142':[('v142','-','v141','ZU')],
 'v156':[('v156','+','binary83',1)],
 'v175':[('cross_direction_pair','*','v32','v169'),('cross_direction_factor','+','cross_direction_pair','v170'),('v175','*','binary77','cross_direction_factor')],
 'v262':[('cross_range_pair','*','v167','v169'),('cross_range_low','*','cross_range_pair','v181'),
         ('cross_range_high','*','v193','v254'),('cross_range_inner','+','cross_range_low','cross_range_high'),
         ('cross_range_total','*','binary75','cross_range_inner'),('v262','+','v175','cross_range_total')],
 }
 newnames={r[0] for rr in added.values() for r in rr}-set(added)
 require(not newnames.intersection(oldrows),'Replacement register collision')
 expanded=[r for row in p['source'] for r in added.get(row[0],[row])]
 # Prune only through the actual complete output, keeping every paid finalizer row.
 tail=p['polynomial_source'][len(p['source']):];allrows=expanded+tail;live={p['output']}
 for n,op,a,b in reversed(allrows):
  if n in live:live.update(x for x in (a,b) if type(x) is str)
 kept=[r for r in allrows if r[0] in live];source=[r for r in expanded if r[0] in live]
 removed=[n for n,_,_,_ in packet['source'] if n not in live]
 require(all(r[0] in live for r in tail),'A finalizer gate became dead')
 p.update(source=source,polynomial_source=kept);source_check(p)
 proof=_proof(packet,p)
 before=count(packet['polynomial_source']);after=count(kept)
 require(before['operations']-after['operations']==4 and before['M']-after['M']==2 and before['A']-after['A']==2,'Unexpected full paid saving')
 # Removed metadata was an ancestor convenience interface, never an extra paid witness.
 proof_only={}
 for name,reg in list(p.get('registers',{}).items()):
  if reg in removed:proof_only[name]=reg;del p['registers'][name]
 p['registers']['WminusWD']='cross_write_only';p['registers']['Qdev_plus7']='v156'
 p['pre_cross_projection_metadata']={k:p.pop(k) for k in ('affine_rewrite','common_affine_cuts','state_deviation_fields','composition','full_polynomial_identity') if k in p}
 p['proof_only_eliminated_registers']=dict(registers=proof_only,
  formulas={'W':'WminusWD+WD','Qdev':'Qdev_plus7-7','direction_mask':'Dir*(B-1)','range_mask':'(D-1)*J','Mc':'J*K29'},
  scope='Historical mathematical values, not emitted registers, supplied coordinates or unpaid source gates.')
 p['common_affine_cuts']=['J','S','Dir','WD','WminusWD'];p['state_deviation_fields']=['Ndev','Qdev_plus7']
 p['centered_state_equation']='B*Ndev+6P=Qdev_plus7'
 p['cross_projection']=dict(removed_registers=removed,exact_local_source_guard=expected,proof=proof,saved_operations=dict(operations=4,M=2,A=2),parent_descriptor_sha256=digest(packet))
 degrees={n:0 if n in p['fixed_parameters'] else 1 for n in p['parameters']+p['auxiliaries']}
 for n,op,a,b in kept:
  da=degrees[a] if type(a) is str else 0;db=degrees[b] if type(b) is str else 0;degrees[n]=da+db if op=='*' else max(da,db)
 p['ledger']=dict(p['ledger'],certificate=count(source),polynomial=after,formal_degree_upper_bound=degrees[p['output']],exact_degree_claimed=False)
 p.update(kind='u15_exact_cross_projection',full_polynomial_identity=True,parent_relation='Identical complete polynomial and every comparison residual on all supplied integer tuples; same coordinates and domains.',
  scope='Local exact-polynomial rewrite. Its caller authenticates the parent ordinary-input/unbounded first-halt theorem; no global arithmetic-bound claim.')
 require(all(n in live for n,_,_,_ in p['polynomial_source']),'Dead emitted gate')
 return p

def _paths(root=None):
 here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve();out=[]
 for name,wanted in PINS.items():
  p=here/name if (here/name).is_file() else root/name
  require(p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==wanted,'Changed pinned source '+name);out.append(p)
 return root,out

def _load(p,name):
 data=p.read_bytes();require(hashlib.sha256(data).hexdigest()==PINS[p.name],'Source changed before execution')
 m=types.ModuleType(name);m.__file__=str(p);exec(compile(data,str(p),'exec'),m.__dict__);return m

@lru_cache(None)
def _bundle(root_text,*path_texts):
 root,paths=_paths(root_text);require(tuple(map(str,paths))==path_texts,'Source paths changed')
 parent,partition=[_load(p,'_cross507_'+str(i)) for i,p in enumerate(paths)];old={};degrees={};degree_proofs={}
 for ordinary in (False,True):
  for grouped in (False,True):
   key=f'base:{int(ordinary)}:{int(grouped)}';q=parent.build(ordinary,grouped=grouped,root=root);parent.checked(q,root=root);old[key]=q
   degrees[key]=(4881 if ordinary else 3464) if grouped else 1936
   degree_proofs[key]=deepcopy(parent._context(root)[1]['certificates'][ordinary,grouped]['degree'])
   require(degree_proofs[key]['exact_degree']==degrees[key],'Wrong base parent degree')
 for i,(groups,anchor,degree) in enumerate(FRONTIER):
  key=f'frontier:{i}';q=partition.build(deepcopy(groups),anchor=anchor,root=root);partition.checked(q,root=root);old[key]=q
  degree_proofs[key]=partition.degree_audit(q,root=root)
  require(degree_proofs[key]['exact_degree']==degree,'Wrong parent degree');degrees[key]=degree
 require(exact({k:digest(v) for k,v in old.items()},PARENT_DIGESTS),'Canonical actual parent descriptors changed')
 packets={}
 for key,q in old.items():
  p=rewrite(q);p['cross_parent_form']=key
  p['canonical_parent']=dict(file=list(PINS)[key.startswith('frontier:')],sha256=PINS[list(PINS)[key.startswith('frontier:')]],form=key)
  p['source_lineage']=dict(p['source_lineage'],**PINS)
  p['exact_degree_certificate']=dict(exact_degree=degrees[key],method='Complete integer polynomial identity with the source-pinned parent, uniform in its fixed program parameters where present.',parent_form=key,parent_packet_digest=digest(q),parent_certificate=degree_proofs[key])
  p['scope']='Complete direct U15 natural-raw-tape or positive-ordinary-input first-halt relation; all fixed valid program slices and arbitrary duration inherited unchanged. No new global87 bound.'
  packets[key]=p
 return dict(parent=parent,partition=partition,old=old,packets=packets)

def _context(root=None):
 root,paths=_paths(root);b=_bundle(str(root),*map(str,paths));b['parent']._context(root);b['partition']._context(root);return root,b

def build(ordinary=False,*,grouped=True,root=None):
 key=f'base:{int(flag(ordinary))}:{int(flag(grouped))}';return deepcopy(_context(root)[1]['packets'][key])
def build_frontier(index=3,*,root=None):
 require(type(index) is int and 0<=index<4,'Exact frontier index0..3 required');return deepcopy(_context(root)[1]['packets'][f'frontier:{index}'])
def checked(p,*,root=None):
 require(type(p) is dict and type(p.get('cross_parent_form')) is str,'Complete canonical packet required');b=_context(root)[1]
 require(p['cross_parent_form'] in b['packets'] and exact(p,b['packets'][p['cross_parent_form']]),'Noncanonical cross-projection packet');return p
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
 p=checked(p,root=root);v=_assignment(p,values,signed);return execute(p['polynomial_source'],v)[p['output']]
def identity(p,values,*,signed=False,root=None):
 p=checked(p,root=root);values=_assignment(p,values,signed);q=canonical_parent(p,root=root)
 a=execute(q['polynomial_source'],values);b=execute(p['polynomial_source'],values)
 rr=[at(a,x)-at(a,y) for x,y in q['comparisons']];ss=[at(b,x)-at(b,y) for x,y in p['comparisons']]
 require(rr==ss and a[q['output']]==b[p['output']],'Complete source identity failed')
 return dict(complete_output=a[q['output']],residuals=rr)

def verify(root=None):
 root,b=_context(root);rng=random.Random(507513);counts=Counter();forms=[]
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_calls_rejected']+=1;return
  raise RuntimeError('Malformed call accepted')
 for key,p0 in b['packets'].items():
  p=deepcopy(p0);q=canonical_parent(p,root=root)
  for j in range(32):
   signed=j>=16;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
   r=identity(p,v,signed=signed,root=root);counts['complete_identities']+=1;counts['signed_cases']+=signed;counts['residual_comparisons']+=len(r['residuals'])
  # Rational evaluations corroborate a polynomial identity, not just integer zero equivalence.
  for j in range(4):
   v={n:Fraction(rng.randrange(-3,4),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']}
   a=execute(q['polynomial_source'],v);z=execute(p['polynomial_source'],v);require(a[q['output']]==z[p['output']],'Rational polynomial identity failed');counts['rational_identities']+=1
  for field in ('source','polynomial_source','comparisons','registers','cross_projection','exact_degree_certificate','ledger'):
   bad=deepcopy(p);bad[field]=None;reject(lambda bad=bad:checked(bad,root=root))
  for j,row in enumerate(p['polynomial_source']):
   for k in (2,3):
    if type(row[k]) is int:
     for badvalue in (float(row[k]),bool(row[k])):
      bad=deepcopy(p);r=list(row);r[k]=badvalue;bad['polynomial_source'][j]=tuple(r);reject(lambda bad=bad:checked(bad,root=root))
     break
   if counts['malformed_calls_rejected']%31==0:break
  v={n:1 for n in p['parameters']+p['auxiliaries']}
  for n in list(v)[::5]:
   for badvalue in (True,1.0,None):
    bad=dict(v);bad[n]=badvalue;reject(lambda bad=bad:evaluate(p,bad,root=root))
  for getter in (lambda:canonical_parent(p,root=root),lambda:polynomial_source(p,root=root),
                 (lambda key=key:build_frontier(int(key.split(':')[1]),root=root)) if key.startswith('frontier:') else
                 (lambda key=key:build(bool(int(key.split(':')[1])),grouped=bool(int(key.split(':')[2])),root=root))):
   a=getter();old=deepcopy(a);a.clear();require(exact(getter(),old),'Public cache leaked');counts['defensive_copy_checks']+=1
  # Generic transform rejects altered literal rows and inexact source coefficients.
  for register in ('binary78','binary84','v175','v262'):
   bad=deepcopy(q);i=next(i for i,row in enumerate(bad['source']) if row[0]==register);row=list(bad['source'][i]);row[1]='*' if row[1]!='*' else '+';bad['source'][i]=tuple(row);bad['polynomial_source'][i]=tuple(row)
   reject(lambda bad=bad:rewrite(bad))
  if not p['ordinary']:
   vv=dict(v,L0=0,R0=0);identity(p,vv,root=root);counts['raw_natural_zero_tape_checks']+=1
  forms.append(dict(form=key,compiler=p,parent_ledger=q['ledger'],parent_descriptor_sha256=digest(q)))
 for bad in (0,1,0.0,None,'yes'):
  reject(lambda bad=bad:build(bad,root=root));reject(lambda bad=bad:build(grouped=bad,root=root))
 for bad in (False,True,0.0,-1,4,None):reject(lambda bad=bad:build_frontier(bad,root=root))
 return dict(status='PASS_COMPLETE_U15_CROSS_PROJECTION507',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),dependency_pins=PINS,
  counts=dict(counts),forms=forms,frontier=[dict(operations=b['packets'][f'frontier:{i}']['ledger']['polynomial']['operations'],exact_degree=degree) for i,(_,_,degree) in enumerate(FRONTIER)],
  scope='Four exact source identities transferred to four complete511 modes and four reviewed ordinary partition representatives; no new global optimum or native-domain theorem.')

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path);parser.add_argument('--write',action='store_true');args=parser.parse_args()
 result=json.loads(json.dumps(verify(args.root)));path=Path(__file__).with_suffix('.json')
 if args.write:path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 else:require(exact(result,json.loads(path.read_text())),'Saved receipt differs')
 print(json.dumps({k:result[k] for k in ('status','counts','frontier')},indent=2))
