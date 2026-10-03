#!/usr/bin/env python3
"""Exact complete-polynomial phase sharing for the pinned native Grill compiler."""
if not __debug__:raise RuntimeError('Run without -O')
import argparse,copy,hashlib,json,random,tempfile,types
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
PARENT_NAME='grill_tag_native_word_closure.py'
PARENT_SHA256='80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7'

def need(v,s):
 if not v:raise ValueError(s)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def _args(program,unit):
 need(type(program)is tuple and bool(program) and all(type(n)is int and n>=0 for n in program),'Nonempty exact natural program tuple')
 need(type(unit)is bool,'Exact Boolean finalizer flag')

def _paths(root):
 root=Path(__file__).resolve().parent if root is None else Path(root).resolve()
 here=Path(__file__).resolve().parent;path=here/PARENT_NAME if (here/PARENT_NAME).is_file() else root/PARENT_NAME
 need(hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_SHA256,'Pinned Grill parent source mismatch')
 return root,path
@lru_cache(None)
def _load(path):
 data=Path(path).read_bytes();need(hashlib.sha256(data).hexdigest()==PARENT_SHA256,'Parent changed before execution')
 m=types.ModuleType('_native_grill_phase_parent');m.__file__=str(path);exec(compile(data,str(path),'exec'),m.__dict__);return m

def _context(root):
 root,path=_paths(root);m=_load(str(path));papers=root.parents[1]
 # Keep all inherited source guards active even when a canonical packet is cached.
 for name,(relative,h) in m.PINS.items():need(hashlib.sha256((papers/relative).read_bytes()).hexdigest()==h,'Inherited source pin '+name)
 return root,path,m
@lru_cache(None)
def _canonical(program,unit,root,path):
 return _load(path).build(program,unit_product=unit,root=Path(root))

def _affine(rows,target,hats):
 defs={n:(o,a,b) for n,o,a,b in rows};env={n:{n:1} for n in hats}
 def val(v):
  if type(v)is int:return {'':v} if v else {}
  if v in env:return env[v]
  need(v in defs,'Affine proof undeclared leaf '+v);o,a,b=defs[v];a=val(a);b=val(b)
  if o=='*':
   need(not any(k for k in a) or not any(k for k in b),'Nonlinear phase projection')
   if any(k for k in a):a,b=b,a
   z={k:a.get('',0)*v for k,v in b.items()}
  else:
   z=dict(a)
   for k,v in b.items():z[k]=z.get(k,0)+(v if o=='+' else -v)
  env[v]={k:v for k,v in z.items() if v};return env[v]
 return val(target)

def _proof(old,new):
 m=old['phase_count'];hats=[f'Shat{i}' for i in range(2*m)]
 wanted={
  'J':{**{n:1 for n in hats},'':-2*m},
  'Q':{**{n:i//2+1 for i,n in enumerate(hats)},'':-m*(m+1)},
  'Next':{**{n:(i//2-1)%m+1 for i,n in enumerate(hats)},'':-m*(m+1)}}
 for name in wanted:
  a=_affine(old['source'],old['interfaces'][name],hats);b=_affine(new['source'],new['interfaces'][name],hats)
  need(a==b==wanted[name],'Joint affine identity from actual selector hats '+name)
 nodes={}
 def node(v):
  if v not in nodes:nodes[v]=len(nodes)
  return nodes[v]
 def graph(p):
  env={n:node(('coordinate',n)) for n in p['parameters']+p['auxiliaries']}
  cuts={p['interfaces'][name]:tuple(sorted(v.items())) for name,v in wanted.items()}
  def get(v):return env[v] if type(v)is str else node(('integer',v))
  for n,o,a,b in p['polynomial_source']:
   env[n]=node(('proved_affine',cuts[n])) if n in cuts else node((o,get(a),get(b)))
  return env,get
 a,aa=graph(old);b,bb=graph(new)
 need(old['comparisons']==new['comparisons'],'Comparison list changed')
 for x,y in old['comparisons']:need(aa(x)==bb(x) and aa(y)==bb(y),'Residual operand changed')
 need(a[old['output']]==b[new['output']],'Complete output DAG differs outside proved affine cuts')
 for key,v in old['interfaces'].items():need(aa(v)==bb(new['interfaces'][key]),'Semantic interface changed '+key)
 for n in old.get('unit_factors',[]):need(a[n]==b[n],'Native unit factor changed')
 return dict(affine_coefficients=wanted,proved_from=hats,complete_polynomial_identity=True,
  identical_residuals=len(old['comparisons']),identical_unit_factors=old.get('unit_factors',[])[:],
  scope='Exact polynomial identity on all integer or rational supplied tuples; J is expanded from selector hats, never assumed independent.')

def _count(rows):
 c=Counter(o for _,o,_,_ in rows);return dict(operations=len(rows),M=c['*'],A=c['+']+c['-'])

def _candidate(old):
 p=copy.deepcopy(old);defs={n:(n,o,a,b) for n,o,a,b in old['source']};seen={}
 for n,o,a,b in old['source']:
  if o in ('+','*'):a,b=sorted((a,b),key=repr)
  seen[o,a,b]=n
 def gate(label,o,a,b):
  if type(a)is int and type(b)is int:return a+b if o=='+' else a-b if o=='-' else a*b
  if o=='+' and (a==0 or b==0):return b if a==0 else a
  if o=='-' and b==0:return a
  if o=='*':
   if a==0 or b==0:return 0
   if a==1 or b==1:return b if a==1 else a
  if o in ('+','*'):a,b=sorted((a,b),key=repr)
  if (o,a,b) in seen:return seen[o,a,b]
  n='phase_shared__'+label;need(n not in defs,'Phase register collision');defs[n]=(n,o,a,b);seen[o,a,b]=n;return n
 def total(vs,label):
  out=0
  for i,v in enumerate(vs):out=gate(label+str(i),'+',out,v)
  return out
 m=p['phase_count'];pairs=[gate('pair'+str(i),'+',f'Shat{2*i}',f'Shat{2*i+1}') for i in range(m)]
 J=gate('J','-',total(pairs,'jsum'),2*m)
 R=gate('R','-',total([gate('weight'+str(i),'*',i,pairs[i]) for i in range(1,m)],'rsum'),m*(m-1))
 Q=gate('Q','+',J,R);Next=gate('Next','+',R,gate('wrap','*',m,gate('phase0','-',pairs[0],2)))
 replacement={}
 for key,target in (('J',J),('Q',Q),('Next',Next)):
  name=p['interfaces'][key]
  need(name not in replacement or replacement[name]==target,'Inconsistent one-phase alias')
  replacement[name]=target
 tail=old['polynomial_source'][len(old['source']):]
 need(old['polynomial_source'][:len(old['source'])]==old['source'],'Parent certificate prefix')
 tailnames={n for n,o,a,b in tail}
 for row in tail:defs[row[0]]=tuple(row)
 emitted=[];done=set(p['parameters']+p['auxiliaries']);busy=set()
 def emit(n):
  if type(n)is int or n in done:return n
  if n in replacement and replacement[n]!=n:return emit(replacement[n])
  need(type(n)is str and n in defs and n not in busy,'Phase substitution cycle or missing gate')
  busy.add(n);_,o,a,b=defs[n];a=emit(a);b=emit(b);emitted.append((n,o,a,b));done.add(n);busy.remove(n);return n
 emit(p['output'])
 source=[r for r in emitted if r[0] not in tailnames]
 emitted_tail={r[0]:r for r in emitted if r[0] in tailnames}
 need(set(emitted_tail)==tailnames,'Finalizer gate became dead')
 final=[emitted_tail[r[0]] for r in tail]
 need(final==tail,'Literal finalizer changed')
 p['source']=source;p['polynomial_source']=source+final
 p['interfaces']={k:replacement.get(v,v) for k,v in old['interfaces'].items()}
 return p,dict(pairs=pairs,R=R),replacement

def _audit(p):
 known=set(p['parameters']+p['auxiliaries']);degree={n:1 for n in known};live={p['output']}
 need(len(known)==len(p['parameters'])+len(p['auxiliaries']),'Duplicate coordinates')
 for n,o,a,b in p['polynomial_source']:
  need(type(n)is str and n not in known and o in ('+','-','*'),'Source SSA')
  need(all(type(v)is int or type(v)is str and v in known for v in (a,b)),'Source closure')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0;degree[n]=da+db if o=='*' else max(da,db);known.add(n)
 for n,o,a,b in reversed(p['polynomial_source']):
  need(n in live,'Dead paid complete gate');live.update(v for v in (a,b) if type(v)is str)
 need(set(p['parameters']+p['auxiliaries'])<=live,'Unused declared coordinate')
 for n in p['interfaces'].values():need(type(n)is int or n in known,'Unavailable interface')
 for n in p['group_hat_registers']:need(type(n)is int or n in known,'Unavailable group hat')
 for f in p['linear_forms']:need(f['output'] in known,'Unavailable linear-form output')
 for n in p.get('projection_aliases',{}).values():need(n in known,'Unavailable inherited native projection alias')
 return degree[p['output']]

def _rewrite(old):
 p,regs,replacement=_candidate(old);candidate_count=_count(p['polynomial_source']);before=_count(old['polynomial_source'])
 use=candidate_count['operations']<before['operations']
 if not use:p=copy.deepcopy(old);regs={};replacement={}
 proof=_proof(old,p);degree=_audit(p);cert=_count(p['source']);full=_count(p['polynomial_source'])
 p['operations']=cert['operations'];p['multiplications']=cert['M'];p['additions_subtractions']=cert['A']
 p['wrapper_operations']=sum(not n.startswith(p['native_prefix']) for n,o,a,b in p['source'])
 historical={}
 if 'parent_operations' in p:historical['parent_operations']=p.pop('parent_operations')
 p['polynomial_ledger']=dict(full,witnesses=len(p['auxiliaries']),comparisons=len(p['comparisons']),degree_upper=degree)
 p['phase_sharing']=dict(parent_file=PARENT_NAME,parent_sha256=PARENT_SHA256,selected='shared' if use else 'unchanged_parent',
  saved={k:before[k]-full[k] for k in before},candidate_count=candidate_count,parent_count=before,
  source_alias_replacements=replacement,shared_registers=regs,proof=proof,historical_native_metadata=historical,
  removed_source_registers=[n for n,o,a,b in old['source'] if n not in {r[0] for r in p['source']}],
  scope='All source and native/finalizer requirements retained; historical parent count is not a live child count. Non-improving candidates keep the exact parent source.')
 p['kind']='grill_native_exact_phase_sharing';p['full_polynomial_identity']=True
 need(p['exact_degree'] is None,'Do not introduce unsupported exact degree')
 need(p['polynomial_ledger']['degree_upper']==old['polynomial_ledger']['degree_upper'],'Unexpected degree upper-bound change')
 return p

@lru_cache(None)
def _packet(program,unit,root,path):return _rewrite(_canonical(program,unit,root,path))
def build(program=(0,1,1),*,unit_product=True,root=None):
 _args(program,unit_product);root,path,m=_context(root)
 return copy.deepcopy(_packet(program,unit_product,str(root),str(path)))
def checked(p,*,root=None):
 need(type(p)is dict,'Canonical full phase-sharing packet required')
 q=build(p.get('program'),unit_product=p.get('unit_product'),root=root);need(exact(p,q),'Noncanonical full packet');return p
def canonical_parent(p,*,root=None):
 checked(p,root=root);root,path,m=_context(root)
 return copy.deepcopy(_canonical(p['program'],p['unit_product'],str(root),str(path)))
def rewrite(parent_packet,*,root=None):
 need(type(parent_packet)is dict,'Canonical pinned parent packet required')
 _args(parent_packet.get('program'),parent_packet.get('unit_product'));root,path,m=_context(root)
 old=_canonical(parent_packet['program'],parent_packet['unit_product'],str(root),str(path));need(exact(parent_packet,old),'Noncanonical complete parent packet')
 return copy.deepcopy(_packet(old['program'],old['unit_product'],str(root),str(path)))
def polynomial_source(p,*,root=None):return copy.deepcopy(checked(p,root=root)['polynomial_source'])
def _values(p,values,signed):
 need(type(signed)is bool,'Exact signed flag required')
 need(type(values)is dict and all(type(k)is str for k in values) and values.keys()==set(p['parameters']+p['auxiliaries']),'Complete exact coordinate assignment')
 need(all(type(v)is int and (signed or v>0) for v in values.values()),'Exact positive integer values, or signed=True')
def _execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b;e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
def _at(e,v):return e[v] if type(v)is str else v
def evaluate(p,values,*,signed=False,root=None):
 checked(p,root=root);_values(p,values,signed);return _execute(p['polynomial_source'],values)[p['output']]
def identity(p,values,*,signed=False,root=None):
 checked(p,root=root);_values(p,values,signed);q=canonical_parent(p,root=root)
 a=_execute(q['polynomial_source'],values);b=_execute(p['polynomial_source'],values)
 rr=[_at(a,x)-_at(a,y) for x,y in q['comparisons']];ss=[_at(b,x)-_at(b,y) for x,y in p['comparisons']]
 need(rr==ss and a[q['output']]==b[p['output']],'Complete source identity failed')
 return dict(output=b[p['output']],residuals=ss)

def verify(*,root=None):
 root,path,parent=_context(root);counts=Counter();forms=[];rng=random.Random(209233)
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejections']+=1;return
  raise ValueError('Invalid call accepted')
 for program in ((0,),(1,),(0,1,1),(2,0,1)):
  for unit in (False,True):
   p=build(program,unit_product=unit,root=root);q=canonical_parent(p,root=root);_audit(p);pr=_proof(q,p)
   need(exact(rewrite(q,root=root),p),'Canonical source transform');counts['complete_formal_source_identities']+=1;counts['affine_identities']+=3;counts['formal_residual_identities']+=len(p['comparisons'])
   for key in ('parameters','auxiliaries','comparisons','maps','groups_U','groups_V','baselines','K','unit_factors','unit_register','root_coordinate','projection_aliases','scale_exponent','region_exponents','scope'):
    need(exact(p.get(key),q.get(key)),'Changed theorem/domain interface '+key)
   for case in range(12):
    signed=case>=6;values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']}
    result=identity(p,values,signed=signed,root=root);counts['complete_integer_identities']+=1;counts['signed_cases']+=signed;counts['numeric_residual_identities']+=len(result['residuals'])
   for case in range(2):
    values={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']}
    a=_execute(q['polynomial_source'],values);b=_execute(p['polynomial_source'],values);need(a[q['output']]==b[p['output']],'All-rational full identity');counts['rational_identities']+=1
   # Every metadata occurrence of a removed arithmetic name is proof-only.
   removed=set(p['phase_sharing']['removed_source_registers'])
   def scan(v):
    if type(v)is dict:
     for k,x in v.items():scan(x)
    elif type(v)in(list,tuple):
     for x in v:scan(x)
    elif type(v)is str:need(v not in removed,'Stale active source-register metadata '+v)
   scan({k:v for k,v in p.items() if k!='phase_sharing'})
   for field in ('source','polynomial_source','interfaces','phase_sharing','polynomial_ledger','program','auxiliaries'):
    bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:checked(bad,root=root))
   for parentfield in ('source','comparisons','scope'):
    bad=copy.deepcopy(q);bad[parentfield]=None;reject(lambda bad=bad:rewrite(bad,root=root))
   vals={n:1 for n in p['parameters']+p['auxiliaries']}
   for n in list(vals)[::9]:
    for badvalue in (True,1.0,0,-1,None):
     bad=dict(vals);bad[n]=badvalue;reject(lambda bad=bad:evaluate(p,bad,root=root))
   for getter in (lambda:build(program,unit_product=unit,root=root),lambda:canonical_parent(p,root=root),lambda:polynomial_source(p,root=root)):
    a=getter();old=copy.deepcopy(a)
    if type(a)is dict:a['source'].clear()
    else:a.clear()
    need(exact(getter(),old),'Mutable public cache alias');counts['defensive_copy_checks']+=1
   forms.append(dict(program=list(program),unit_product=unit,parent_ledger=q['polynomial_ledger'],compiler=p))
 for bad in ((),[0,1],(True,),(1.0,),(-1,),None):reject(lambda bad=bad:build(bad,root=root))
 for bad in (True,1,None,0.0):
  if type(bad)is not bool:reject(lambda bad=bad:build(unit_product=bad,root=root))
 p=build(root=root);values={n:1 for n in p['parameters']+p['auxiliaries']}
 for bad in (1,0,None):reject(lambda bad=bad:evaluate(p,values,signed=bad,root=root))
 for vals in ({'x':1},dict(values,extra=1)):reject(lambda vals=vals:evaluate(p,vals,root=root))
 class ForeignKey(str):pass
 bad=copy.deepcopy(p);bad[ForeignKey('program')]=bad.pop('program');reject(lambda:checked(bad,root=root))
 bad=dict(values);bad[ForeignKey('x')]=bad.pop('x');reject(lambda:evaluate(p,bad,root=root))
 bad=copy.deepcopy(p);i=next(i for i,r in enumerate(bad['polynomial_source']) if any(type(x)is int for x in r[2:]));rr=list(bad['polynomial_source'][i]);j=next(j for j in (2,3) if type(rr[j])is int);rr[j]=float(rr[j]);bad['polynomial_source'][i]=tuple(rr)
 reject(lambda:evaluate(bad,{n:10**100 for n in values},root=root))
 # A newly cached child must still reject changed direct and inherited sources.
 with tempfile.TemporaryDirectory(prefix='grill-phase-warm-') as directory:
  directory=Path(directory);child=directory/Path(__file__).name;child.write_bytes(Path(__file__).read_bytes())
  parentcopy=directory/PARENT_NAME;parentcopy.write_bytes(path.read_bytes())
  private_papers=directory/'Papers';private_root=private_papers/'research-wip'/'native-stream-queue'
  for relative,h in parent.PINS.values():
   target=private_papers/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((root.parents[1]/relative).read_bytes())
  module=types.ModuleType('_private_grill_phase_guard');module.__file__=str(child);exec(compile(child.read_bytes(),str(child),'exec'),module.__dict__)
  pristine=module.build((0,),root=private_root)
  for target in (parentcopy,private_root/'pcp_affine_slope_class_history.py'):
   data=target.read_bytes()
   try:
    target.write_bytes(data+b'\n# private source authentication regression\n');reject(lambda:module.build((0,),root=private_root));counts['warm_source_pin_rejections']+=1
   finally:target.write_bytes(data)
   need(exact(module.build((0,),root=private_root),pristine),'Restored private source packet changed')
 return json.loads(json.dumps(dict(status='PASS_NATIVE_GRILL_EXACT_PHASE_SHARING',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_sha256=PARENT_SHA256,
  counts=dict(counts),forms=forms,
  scope='Same complete polynomial, coordinates, native factors and positive semantics as the fixed-arity native Grill parent. No new universal instance or decoder claim; only formal degree upper bounds retained.')))

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(root=a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Saved full receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':r['status'],'counts':r['counts'],'ledgers':[{'program':f['program'],'unit_product':f['unit_product'],**f['compiler']['polynomial_ledger'],'saved':f['compiler']['phase_sharing']['saved']} for f in r['forms']]},indent=2))
