#!/usr/bin/env python3
"""Complete weak-cone Grill205: source-pinned composition with a checked diamond."""
if not __debug__:raise RuntimeError('Run without -O')
import argparse,copy,hashlib,json,random,tempfile,types
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
PINS={
 'weak':('grill_tag_native_weak_cone.py','8f636a7954fce4335c2977baf849da0107b29d146aaa008fbb9732acedcf60b9'),
 'strong':('grill_tag_native_phase_residual206.py','b9eaa5edf08f355607adf496d9477b806960c3438a81099f64cf08d0b7471af1')}
def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def args(program,unit):
 need(type(program)is tuple and bool(program) and all(type(n)is int and n>=0 for n in program),'Nonempty exact natural tuple program')
 need(type(unit)is bool,'Exact Boolean finalizer flag')
@lru_cache(None)
def _load(path,pin):
 data=Path(path).read_bytes();need(hashlib.sha256(data).hexdigest()==pin,'Pinned source changed before execution')
 m=types.ModuleType('_grill_composition_'+Path(path).stem);m.__file__=path;exec(compile(data,path,'exec'),m.__dict__);return m
def _context(root=None):
 here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve();loaded=[];paths=[]
 for key,(name,pin) in PINS.items():
  path=here/name if (here/name).is_file() else root/name
  need(hashlib.sha256(path.read_bytes()).hexdigest()==pin,'Pinned composition source '+key)
  m=_load(str(path),pin);m._context(root);loaded.append(m);paths.append(str(path))
 return root,tuple(paths),tuple(loaded)
@lru_cache(None)
def _parents(program,unit,root,paths):
 return tuple(_load(path,PINS[key][1]).build(program,unit_product=unit,root=Path(root)) for key,path in zip(PINS,paths))

def _compose(weak,strong,W,S):
 # Only authenticated full canonical packets reach these pinned generic routines.
 p=S._rewrite(weak)
 other=W._rewrite(strong)
 same_fields=('source','polynomial_source','comparisons','interfaces','parameters','auxiliaries','maps','groups_U','groups_V','baselines','K','unit_factors','unit_register','root_coordinate','projection_aliases','scale_exponent','region_exponents','native_prefix','group_hat_registers','polynomial_ledger')
 for key in same_fields:need(exact(p.get(key),other.get(key)),'Composition order changed normative source field '+key)
 diamond=W._proof(strong,p)
 need(S._audit(p)==p['polynomial_ledger']['degree_upper'],'Complete source bound mismatch')
 for key in ('parameters','auxiliaries','maps','groups_U','groups_V','baselines','K','unit_factors','unit_register','root_coordinate','projection_aliases','scale_exponent','region_exponents','input_cone','scope'):
  need(exact(p.get(key),weak.get(key)),'Changed inherited weak interface '+key)
 # Archive relations whose old comparison operands are no longer the live ones.
 p['historical_weak_cone_rewrite']=p.pop('weak_cone_rewrite')
 p['kind']='grill_native_weak_composed205'
 p['full_polynomial_identity']=True
 p['polynomial_identity_parent']=dict(file=PINS['weak'][0],sha256=PINS['weak'][1],relation='Identical full polynomial on the same supplied coordinates.')
 r=p['phase_residual_rewrite'];r['parent_file'],r['parent_sha256']=PINS['weak'];r['source_rewriter']=dict(file=PINS['strong'][0],sha256=PINS['strong'][1])
 r['scope']='Exact phase residual and complete-polynomial identity relative to the canonical weak-cone208 parent, with P0=x+Z0.'
 p['composition']=dict(source_pins={k:dict(file=n,sha256=h) for k,(n,h) in PINS.items()},
  identity_parent='weak208',strong_reference='strong206',commuting_complete_source_fields=list(same_fields),diamond=diamond,
  positive_relation='Same supplied positive zeros as weak208. Strong206 has the same existential positive-input language by inherited period padding; its positive supplied fibers are not identified.',
  parent_ledger=copy.deepcopy(weak['polynomial_ledger']),strong_ledger=copy.deepcopy(strong['polynomial_ledger']),
  scope='All-value equality to weak208; signed affine substitution to strong206. Native factors, ordinary input, positive witness list and packed arbitrary duration remain unchanged.')
 need(p['input_cone']['width']=='x+Z0' and p['input_cone']['positive_fiber_bijection']is False,'Keep weak input semantics')
 need(p['exact_degree']is None,'No exact degree claim')
 return p
@lru_cache(None)
def _packet(program,unit,root,paths):
 W=_load(paths[0],PINS['weak'][1]);S=_load(paths[1],PINS['strong'][1]);weak,strong=_parents(program,unit,root,paths);return _compose(weak,strong,W,S)
def build(program=(0,1,1),*,unit_product=True,root=None):
 args(program,unit_product);root,paths,mods=_context(root);return copy.deepcopy(_packet(program,unit_product,str(root),paths))
def checked(p,*,root=None):
 need(type(p)is dict,'Canonical whole composed packet required');q=build(p.get('program'),unit_product=p.get('unit_product'),root=root);need(exact(p,q),'Noncanonical composed packet');return p
def _parent(p,index,root):
 checked(p,root=root);root,paths,mods=_context(root);return copy.deepcopy(_parents(p['program'],p['unit_product'],str(root),paths)[index])
def canonical_parent(p,*,root=None):return _parent(p,0,root)
def canonical_strong(p,*,root=None):return _parent(p,1,root)
def rewrite(weak_packet,*,root=None):
 need(type(weak_packet)is dict,'Canonical complete weak208 packet required');args(weak_packet.get('program'),weak_packet.get('unit_product'));root,paths,mods=_context(root)
 weak,_=_parents(weak_packet['program'],weak_packet['unit_product'],str(root),paths);need(exact(weak_packet,weak),'Noncanonical weak parent')
 return copy.deepcopy(_packet(weak['program'],weak['unit_product'],str(root),paths))
def polynomial_source(p,*,root=None):return copy.deepcopy(checked(p,root=root)['polynomial_source'])
def _values(p,values,signed):
 need(type(signed)is bool,'Exact signed flag required')
 need(type(values)is dict and all(type(k)is str for k in values) and values.keys()==set(p['parameters']+p['auxiliaries']),'Complete exact coordinate dictionary')
 need(all(type(v)is int and (signed or v>0) for v in values.values()),'Exact positive integers, or explicit signed algebra mode required')
def _execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def _at(e,x):return e[x] if type(x)is str else x
def evaluate(p,values,*,signed=False,root=None):
 checked(p,root=root);_values(p,values,signed);return _execute(p['polynomial_source'],values)[p['output']]
def integer_pullback(p,values,*,signed=False,root=None):
 """Strong206 integer coordinates; the returned slack need not be positive."""
 checked(p,root=root);_values(p,values,signed);v=dict(values);v['Z0']-=2*v['x'];return v
def strong_to_weak_assignment(p,values,*,root=None):
 checked(p,root=root);_values(p,values,False);v=dict(values);v['Z0']+=2*v['x'];return v
def _compare(p,values,q,other):
 a=_execute(p['polynomial_source'],values);b=_execute(q['polynomial_source'],other)
 rr=[_at(a,x)-_at(a,y) for x,y in p['comparisons']];ss=[_at(b,x)-_at(b,y) for x,y in q['comparisons']]
 need(rr==ss and a[p['output']]==b[q['output']],'Complete polynomial/residual identity failed');return dict(output=a[p['output']],residuals=rr)
def identity(p,values,*,signed=False,root=None):
 checked(p,root=root);_values(p,values,signed);return _compare(p,values,canonical_parent(p,root=root),values)
def diamond_identity(p,values,*,signed=False,root=None):
 checked(p,root=root);_values(p,values,signed);other=integer_pullback(p,values,signed=signed,root=root);r=_compare(p,values,canonical_strong(p,root=root),other)
 r.update(strong_slack=other['Z0'],strong_tuple_positive=min(other.values())>0);return r

def verify(root=None):
 root,paths,(W,S)=_context(root);rng=random.Random(205229);counts=Counter();forms=[]
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejections']+=1;return
  raise ValueError('Malformed input accepted')
 for program in ((0,),(1,),(0,1,1),(2,0,1)):
  for unit in (False,True):
   p=build(program,unit_product=unit,root=root);weak=canonical_parent(p,root=root);strong=canonical_strong(p,root=root)
   need(exact(rewrite(weak,root=root),p),'Public canonical composition changed')
   counts['complete_commuting_source_checks']+=1;counts['formal_same_coordinate_identities']+=1;counts['formal_diamond_identities']+=1;counts['formal_residual_identities']+=2*len(p['comparisons'])
   old=weak['polynomial_ledger'];new=p['polynomial_ledger'];ss=strong['polynomial_ledger']
   need((old['operations']-new['operations'],old['M']-new['M'],old['A']-new['A'])==(3,1,2),'Exact three-operation residual saving')
   need((ss['operations']-new['operations'],ss['M']-new['M'],ss['A']-new['A'])==(1,1,0),'Exact one-operation width saving')
   S._audit(p);counts['full_ledger_liveness_checks']+=1
   for j in range(16):
    signed=j>=8;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
    a=identity(p,v,signed=signed,root=root);b=diamond_identity(p,v,signed=signed,root=root);need(a['output']==b['output'],'Diamond apex')
    counts['complete_same_coordinate_evaluations']+=1;counts['complete_diamond_evaluations']+=1;counts['signed_cases']+=signed;counts['numeric_residual_comparisons']+=2*len(a['residuals'])
    if not signed:
     w=strong_to_weak_assignment(p,v,root=root);need(min(w.values())>0 and integer_pullback(p,w,root=root)==v,'Positive one-way assignment map')
     _compare(p,w,strong,v);counts['positive_one_way_maps']+=1
   for j in range(2):
    v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']};z=dict(v);z['Z0']-=2*z['x'];_compare(p,v,weak,v);_compare(p,v,strong,z);counts['rational_diamonds']+=1
   values={n:1 for n in p['parameters']+p['auxiliaries']};r=diamond_identity(p,values,root=root)
   need(r['strong_slack']==-1 and not r['strong_tuple_positive'],'No false positivity of pullback')
   need(evaluate(p,values,root=root)!=_execute(strong['polynomial_source'],values)[strong['output']],'No same-coordinate strong identity');counts['strong_fiber_separations']+=1
   removed=set(p['phase_residual_rewrite']['removed_registers'])|{'three_x__0'}
   historical={'historical_weak_cone_rewrite','strong_parent_metadata','phase_residual_rewrite','proof_only_phase_formulas'}
   def scan(v):
    if type(v)is dict:
     for x in v.values():scan(x)
    elif type(v)in(tuple,list):
     for x in v:scan(x)
    elif type(v)is str:need(v not in removed,'Stale active source register '+v)
   scan({k:v for k,v in p.items() if k not in historical});counts['active_metadata_checks']+=1
   for field in ('source','polynomial_source','comparisons','interfaces','input_cone','composition','phase_residual_rewrite','polynomial_ledger','scope','auxiliaries'):
    bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:checked(bad,root=root))
   for field in ('source','scope','weak_cone_rewrite'):
    bad=copy.deepcopy(weak);bad[field]=None;reject(lambda bad=bad:rewrite(bad,root=root))
   reject(lambda:rewrite(strong,root=root))
   for typ in (bool,float):
    bad=copy.deepcopy(p);i,j=next((i,j) for i,r in enumerate(bad['polynomial_source']) for j in (2,3) if type(r[j])is int and (typ is float or r[j]in(0,1)))
    r=list(bad['polynomial_source'][i]);r[j]=typ(r[j]);bad['polynomial_source'][i]=tuple(r);reject(lambda bad=bad:checked(bad,root=root))
   for name in list(values)[::9]:
    for value in (True,1.0,None,0,-1):reject(lambda name=name,value=value:evaluate(p,dict(values,**{name:value}),root=root))
   for getter in (lambda:build(program,unit_product=unit,root=root),lambda:canonical_parent(p,root=root),lambda:canonical_strong(p,root=root),lambda:polynomial_source(p,root=root)):
    v=getter();old=copy.deepcopy(v);v.clear();need(exact(getter(),old),'Public cache alias');counts['copy_checks']+=1
   forms.append(dict(program=list(program),unit_product=unit,compiler=p))
 for bad in (None,(),[0],(True,),(1.0,),(-1,)):reject(lambda bad=bad:build(bad,root=root))
 for bad in (None,1,0):reject(lambda bad=bad:build(unit_product=bad,root=root))
 p=build(root=root);values={n:1 for n in p['parameters']+p['auxiliaries']}
 for bad in (None,1,0):reject(lambda bad=bad:diamond_identity(p,values,signed=bad,root=root))
 for bad in ({'x':1},dict(values,extra=1)):reject(lambda bad=bad:evaluate(p,bad,root=root))
 class ForeignKey(str):pass
 bad=copy.deepcopy(p);bad[ForeignKey('program')]=bad.pop('program');reject(lambda:checked(bad,root=root))
 bad=dict(values);bad[ForeignKey('x')]=bad.pop('x');reject(lambda:evaluate(p,bad,root=root))
 # A complete private dependency tree allows warm source tests without repository edits.
 with tempfile.TemporaryDirectory(prefix='grill-composed-warm-') as directory:
  directory=Path(directory);child=directory/Path(__file__).name;child.write_bytes(Path(__file__).read_bytes())
  copies=[]
  for path in paths:
   q=directory/Path(path).name;q.write_bytes(Path(path).read_bytes());copies.append(q)
  _,phasepath,phase=W._context(root);phasecopy=directory/W.PARENT_NAME;phasecopy.write_bytes(phasepath.read_bytes())
  _,nativepath,native=phase._context(root);nativecopy=directory/phase.PARENT_NAME;nativecopy.write_bytes(nativepath.read_bytes())
  private_papers=directory/'Papers';private_root=private_papers/'research-wip'/'native-stream-queue'
  for relative,h in native.PINS.values():
   q=private_papers/relative;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((root.parents[1]/relative).read_bytes())
  module=types.ModuleType('_private_grill_composition_guard');module.__file__=str(child);exec(compile(child.read_bytes(),str(child),'exec'),module.__dict__)
  pristine=module.build((0,),root=private_root)
  for target in [*copies,phasecopy,nativecopy,private_root/'pcp_affine_slope_class_history.py']:
   data=target.read_bytes()
   try:target.write_bytes(data+b'\n# private source guard regression\n');reject(lambda:module.build((0,),root=private_root));counts['warm_source_pin_rejections']+=1
   finally:target.write_bytes(data)
   need(exact(module.build((0,),root=private_root),pristine),'Restored cached source changed')
 return json.loads(json.dumps(dict(status='PASS_NATIVE_GRILL_COMPOSED_WEAK205',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),source_pins=PINS,counts=dict(counts),forms=forms,
  scope='Same complete polynomial and supplied positive zeros as weak208; exact signed affine diamond to strong206, whose positive fibers need not correspond. Fixed finite programs, packed arbitrary duration, no universal instance/decoder claim.')))
if __name__=='__main__':
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',type=Path);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);args_=a.parse_args();r=verify(args_.root)
 if args_.expect:need(exact(r,json.loads(args_.expect.read_text())),'Saved typed receipt mismatch')
 if args_.output:args_.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],ledgers=[dict(program=f['program'],unit_product=f['unit_product'],**f['compiler']['polynomial_ledger']) for f in r['forms']]),indent=2))
