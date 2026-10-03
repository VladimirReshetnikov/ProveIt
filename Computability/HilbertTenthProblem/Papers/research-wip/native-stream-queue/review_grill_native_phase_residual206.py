#!/usr/bin/env python3
"""Independent all-value source audit of the strong Grill phase-residual child."""
import argparse,copy,hashlib,json,random,sys,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path
SOURCE_SHA256='b9eaa5edf08f355607adf496d9477b806960c3438a81099f64cf08d0b7471af1'
PARENT_SHA256='760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069'
PROGRAMS=((0,),(1,),(0,1,1),(2,0,1))
HISTORICAL=('Q','Next','phase_lhs','phase_rhs')
def need(b,m):
 if not b:raise ValueError(m)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def load(path,pin,name):
 data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==pin,'Source pin '+str(path))
 m=types.ModuleType(name);m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m
def run(p,v):
 e=dict(v)
 for n,o,a,b in p['polynomial_source']:
  need(n not in e,'SSA output');a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def at(e,v):return e[v] if type(v)is str else v
# Tiny exact sparse integer polynomials, used only for width/global-row ancestors.
def poly(v):return {():v} if type(v)is int and v else {} if type(v)is int else {(v,):1}
def add(a,b,sgn=1):
 z=dict(a)
 for k,v in b.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   q=tuple(sorted(k+l));z[q]=z.get(q,0)+v*w
 return {k:v for k,v in z.items() if v}
def symbolic(p,sub=None):
 rows={n:(o,a,b) for n,o,a,b in p['polynomial_source']};env={n:poly(n) for n in p['parameters']+p['auxiliaries']};env.update(sub or {})
 def get(v):
  if type(v)is int:return poly(v)
  if v not in env:
   o,a,b=rows[v];a=get(a);b=get(b);env[v]=mul(a,b) if o=='*' else add(a,b,1 if o=='+' else -1)
  return env[v]
 return get

def sum_poly(vs):
 z={}
 for v in vs:z=add(z,v)
 return z

def prove(old,new,c):
 m=len(new['program']);B=old['interfaces']['B'];q='phase_initial';hats=['Shat'+str(i) for i in range(2*m)]
 blocks=[add(add(poly(hats[2*i]),poly(hats[2*i+1])),poly(2),-1) for i in range(m)]
 J=sum_poly(blocks);T=sum_poly([mul(poly(m-i),blocks[i]) for i in range(1,m)])
 wanted=add(add(add(mul(poly(m),blocks[0]),mul(add(poly(B),poly(1),-1),T),-1),poly(q)),add(J,poly(m)),-1)
 atoms={B:poly(B)};a=symbolic(old,atoms);b=symbolic(new,atoms)
 need(a(old['interfaces']['J'])==b(new['interfaces']['J'])==J,'Actual source J expanded from every original hat')
 need(a(old['interfaces']['P'])==b(new['interfaces']['P'])==add(mul(add(poly(B),poly(1),-1),J),poly(1)),'Actual source P expanded from B and hats')
 r=add(a(old['comparisons'][3][0]),a(old['comparisons'][3][1]),-1);s=add(b(new['comparisons'][3][0]),b(new['comparisons'][3][1]),-1)
 need(r==s==wanted,'Independent exact full phase identity in B, all hats and q0')
 if m==1:need(r==add(poly(q),poly(1),-1),'One-phase identity has no hats or B')
 oldtail=old['polynomial_source'][len(old['source']):];newtail=new['polynomial_source'][len(new['source']):]
 residuals=[n for n,o,x,y in oldtail if o=='-' and (x,y)==old['comparisons'][3]];need(len(residuals)==1,'Unique actual old phase subtraction');cut=residuals[0]
 expected=[(n,o,*new['comparisons'][3]) if n==cut else (n,o,x,y) for n,o,x,y in oldtail]
 need(exact(newtail,expected),'Complete finalizer changes only the proved phase subtraction operands')
 nodes={}
 def node(k):
  if k not in nodes:nodes[k]=len(nodes)
  return nodes[k]
 def dag(p):
  e={n:node(('coordinate',n)) for n in p['parameters']+p['auxiliaries']}
  def val(v):return e[v] if type(v)is str else node(('integer',v))
  for n,o,x,y in p['polynomial_source']:e[n]=node(('proved phase residual',)) if n==cut else node((o,val(x),val(y)))
  return e,val
 od,ov=dag(old);nd,nv=dag(new)
 need(od[B]==nd[B],'Derived B proof atom is unchanged in the complete DAG')
 for i,(left,right) in enumerate(old['comparisons']):
  if i==3:continue
  need(exact((left,right),new['comparisons'][i]),'Other residual pair literal equality')
  need(ov(left)==nv(left) and ov(right)==nv(right),'Other residual full DAG unchanged')
 for n in old.get('unit_factors',[]):need(od[n]==nd[n],'Native unit-factor complete DAG unchanged')
 for k,v in old['interfaces'].items():
  if k not in HISTORICAL:need(ov(v)==nv(new['interfaces'][k]),'Retained complete interface '+k)
 need(od[old['output']]==nd[new['output']],'Entire final polynomial exact DAG equality after proven local cut')
 need(exact(old['parameters'],new['parameters']) and exact(old['auxiliaries'],new['auxiliaries']),'Exact same coordinates')
 known=set(new['parameters']+new['auxiliaries']);degree={n:1 for n in known};free=set(known);live={new['output']};ops=Counter()
 for n,o,x,y in new['polynomial_source']:
  need(type(n)is str and n not in known and o in ('+','-','*'),'Typed unique gate')
  need(all(type(v)is int or type(v)is str and v in known for v in (x,y)),'Closed topological operands')
  dx=degree[x] if type(x)is str else 0;dy=degree[y] if type(y)is str else 0;degree[n]=dx+dy if o=='*' else max(dx,dy);known.add(n);ops['M' if o=='*' else 'A']+=1
 for n,o,x,y in reversed(new['polynomial_source']):need(n in live,'Every paid operation live');live.update(v for v in (x,y) if type(v)is str)
 need(live-set(n for n,o,x,y in new['polynomial_source'])==free,'Exact complete free-coordinate closure')
 cert=Counter('M' if o=='*' else 'A' for n,o,x,y in new['source']);ledger=new['polynomial_ledger']
 need(new['operations']==len(new['source']) and new['multiplications']==cert['M'] and new['additions_subtractions']==cert['A'],'Certificate paid counts')
 need(exact(new['polynomial_source'][:len(new['source'])],new['source']),'Actual certificate prefix')
 need(ledger['operations']==sum(ops.values()) and all(ledger[k]==ops[k] for k in ('M','A')),'Entire paid ledger')
 need(ledger['witnesses']==len(new['auxiliaries']) and ledger['comparisons']==len(new['comparisons']),'Same paid arity and rows')
 need(degree[new['output']]==ledger['degree_upper']==old['polynomial_ledger']['degree_upper'] and new['exact_degree']is None,'Only formal upper degree retained')
 need(new['wrapper_operations']==sum(not n.startswith(new['native_prefix']) for n,o,x,y in new['source']),'Current wrapper count')
 # Current live interfaces are distinct from removed proof-only phase metadata.
 for k,v in new['interfaces'].items():need(type(v)is int or v in known,'Current emitted interface exists '+k)
 chosen=new['phase_residual_rewrite']['selected']=='residual'
 if chosen:
  need(all(k not in new['interfaces'] for k in HISTORICAL),'Removed phase outputs are not unpaid current ports')
  need((new['interfaces']['phase_residual_left'],new['interfaces']['phase_residual_right'])==new['comparisons'][3],'Current phase pair ports')
  need(exact(new['proof_only_phase_formulas']['parent_registers'],{k:old['interfaces'][k] for k in HISTORICAL}),'Historical phase register attribution')
  need('phase_sharing' not in new and exact(new['historical_phase_sharing'],old['phase_sharing']),'Historical phase provenance isolated')
 removed=set(new['phase_residual_rewrite']['removed_registers'])
 def scan(v):
  if type(v)is dict:
   for a in v.values():scan(a)
  elif type(v)in(list,tuple):
   for a in v:scan(a)
  elif type(v)is str:need(v not in removed,'Removed register exposed as live metadata '+v)
 scan({k:v for k,v in new.items() if k not in ('phase_residual_rewrite','historical_phase_sharing','proof_only_phase_formulas')})
 need(new['full_polynomial_identity']is True,'Current full identity metadata')
 for k in ('maps','baselines','groups_U','groups_V','K','scale_exponent','region_exponents','unit_factors','projection_aliases','scope'):
  need(exact(old.get(k),new.get(k)),'Preserved inherited mathematical structure '+k)
 # Strong cone was not accidentally replaced with the separately reviewed weak cone.
 inp=symbolic(new);need(inp(new['interfaces']['P0'])==add(mul(poly(3),poly('x')),poly('Z0')),'Literal paid strong input cone')
 c['exact_expanded_phase_polynomials']+=1;c['whole_polynomial_DAG_proofs']+=1;c['nonphase_residual_DAGs']+=len(new['comparisons'])-1;c['native_factor_DAGs']+=len(new.get('unit_factors',[]));c['complete_ledger_degree_metadata_audits']+=1
 return dict(program=list(new['program']),unit_product=new['unit_product'],ledger=ledger,savings={k:old['polynomial_ledger'][k]-ledger[k] for k in ('operations','M','A')},phase_terms=[dict(monomial=list(k),coefficient=v) for k,v in sorted(r.items())],source_sha256=hashlib.sha256(json.dumps(new['polynomial_source'],separators=(',',':')).encode()).hexdigest())

def verify(source,root):
 m=load(source,SOURCE_SHA256,'_independent_grill_phase_residual');pname=source.parent/m.PARENT_NAME
 if not pname.is_file():pname=root/m.PARENT_NAME
 parent=load(pname,PARENT_SHA256,'_independent_grill_strong209');c=Counter();rng=random.Random(206918);forms=[]
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):c['malformed_rejections']+=1;return
  raise ValueError('Malformed accepted')
 for program in PROGRAMS:
  for unit in (False,True):
   p=m.build(program,unit_product=unit,root=root);q=parent.build(program,unit_product=unit,root=root)
   need(exact(m.canonical_parent(p,root=root),q) and exact(m.rewrite(q,root=root),p),'Independently loaded canonical parent and public rewrite')
   record=prove(q,p,c);need(record['savings']==dict(operations=3,M=1,A=2),'Each representative saves exactly1M2A');forms.append(record)
   names=p['parameters']+p['auxiliaries'];vals={n:1 for n in names}
   for case in range(16):
    signed=case>=8;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in names};a=run(q,v);b=run(p,v)
    need(a[q['output']]==b[p['output']]==m.evaluate(p,v,signed=signed,root=root),'Independent whole integer polynomial identity')
    rr=[at(a,x)-at(a,y) for x,y in q['comparisons']];ss=[at(b,x)-at(b,y) for x,y in p['comparisons']]
    need(rr==ss==m.identity(p,v,signed=signed,root=root)['residuals'],'Every integer residual and public identity')
    c['complete_integer_identities']+=1;c['signed_identities']+=signed;c['numeric_residual_identities']+=len(rr)
   for case in range(2):
    v={n:Fraction(rng.randrange(-3,4),rng.randrange(1,4)) for n in names};need(run(q,v)[q['output']]==run(p,v)[p['output']],'Exact rational full identity');c['rational_identities']+=1
   for key in p:
    bad=copy.deepcopy(p);bad[key]=None if p[key]is not None else 0;reject(lambda bad=bad:m.checked(bad,root=root))
   for name in names[::5]:
    for v in (True,1.0,Fraction(1),0,-1,None):
     bad=dict(vals);bad[name]=v;reject(lambda bad=bad:m.evaluate(p,bad,root=root))
   for bad in ({},dict(vals,extra=1)):reject(lambda bad=bad:m.evaluate(p,bad,root=root))
   for key in ('scope','interfaces','source','polynomial_source'):
    bad=copy.deepcopy(q);bad[key]=None;reject(lambda bad=bad:m.rewrite(bad,root=root))
   for get in (lambda:m.build(program,unit_product=unit,root=root),lambda:m.canonical_parent(p,root=root),lambda:m.polynomial_source(p,root=root),lambda:m.rewrite(q,root=root)):
    a=get();saved=copy.deepcopy(a)
    if type(a)is dict:a['polynomial_source'][-1]=('poison','+',0,0)
    else:a.clear()
    need(exact(get(),saved),'Public defensive source copies');c['copy_checks']+=1
 # Extend the symbolic proof to periods absent from the receipt table; no cost claim assumed.
 extra=[]
 for program in ((0,1),(2,0,1,0),(0,1,0,1,0)):
  for unit in (False,True):
   p=m.build(program,unit_product=unit,root=root);q=parent.build(program,unit_product=unit,root=root);extra.append(prove(q,p,c))
 for bad in (None,(),[0],(True,),(1.0,),(-1,)):reject(lambda bad=bad:m.build(bad,root=root))
 for bad in (None,0,1,1.0):reject(lambda bad=bad:m.build(unit_product=bad,root=root))
 p=m.build(root=root);vals={n:1 for n in p['parameters']+p['auxiliaries']}
 for bad in (0,1,None):reject(lambda bad=bad:m.evaluate(p,vals,signed=bad,root=root))
 class StringSubclass(str):pass
 bad=dict(vals);bad[StringSubclass('x')]=bad.pop('x');reject(lambda:m.evaluate(p,bad,root=root))
 bad=copy.deepcopy(p);bad[StringSubclass('program')]=bad.pop('program');reject(lambda:m.checked(bad,root=root))
 for typ in (float,bool):
  bad=copy.deepcopy(p);i,j=next((i,j) for i,r in enumerate(bad['polynomial_source']) for j in (2,3) if type(r[j])is int and (typ is float or r[j]in (0,1)));r=list(bad['polynomial_source'][i]);r[j]=typ(r[j]);bad['polynomial_source'][i]=tuple(r);reject(lambda bad=bad:m.checked(bad,root=root))
 name=m.PARENT_NAME[:-3];present=name in sys.modules;previous=sys.modules.get(name);fake=types.ModuleType(name);sys.modules[name]=fake
 try:
  cold=load(source,SOURCE_SHA256,'_phase_residual_cold');need(exact(cold.build((0,),root=root),m.build((0,),root=root)),'Cold loader ignores fake parent');need(sys.modules[name]is fake,'Caller fake object preserved');c['cold_fake_module_checks']+=1
 finally:
  if present:sys.modules[name]=previous
  else:sys.modules.pop(name,None)
 with tempfile.TemporaryDirectory(prefix='independent-phase206-') as tmp:
  tmp=Path(tmp);child=tmp/source.name;child.write_bytes(source.read_bytes());target=tmp/m.PARENT_NAME;data=pname.read_bytes();target.write_bytes(data)
  private=load(child,SOURCE_SHA256,'_phase_residual_private');before=private.build((0,),root=root);target.write_bytes(data+b'\n# private pin mutation\n');reject(lambda:private.build((0,),root=root));target.write_bytes(data)
  need(exact(private.build((0,),root=root),before),'Warm source pin after restoration');c['warm_source_pin_checks']+=1
 return json.loads(json.dumps(dict(status='PASS_INDEPENDENT_GRILL_PHASE_RESIDUAL206',reviewed_source_sha256=SOURCE_SHA256,parent_sha256=PARENT_SHA256,counts=dict(c),representative_forms=forms,extra_period_forms=extra,
 scope='Same entire strong-cone polynomial in each mode, with symbolic J/P expansion and complete DAG proof. Eight published representative ledgers plus six additional period2/4/5 symbolic forms. No native witness materialization or new universal/degree claim.')))

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,default=Path(__file__).with_name('grill_tag_native_phase_residual206.py'));ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.source.resolve(),a.root.resolve())
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Typed deterministic saved receipt')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],ledgers=[f['ledger'] for f in r['representative_forms']]),indent=2))
