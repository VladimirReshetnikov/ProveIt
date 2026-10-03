#!/usr/bin/env python3
"""Exact phase-residual compression of the strong-cone native Grill compiler.

The complete 011 unit polynomial drops 209 to 206; raw 233 to 230.
The input cone remains P0=3x+Z0. This is not the separate weak-cone208 source.
"""
if not __debug__:raise RuntimeError('Run without -O')
import argparse,copy,hashlib,json,random,tempfile,types
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
PARENT_NAME='grill_tag_native_phase_sharing.py'
PARENT_SHA256='760ce9a0ea6e6020ecb52737ccc5c4197f7b84a212c73dc351b9ae3e6ef60069'
HISTORICAL_INTERFACES=('Q','Next','phase_lhs','phase_rhs')

def need(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def args(program,unit):
 need(type(program)is tuple and program and all(type(n)is int and n>=0 for n in program),'Nonempty exact natural program tuple')
 need(type(unit)is bool,'Exact Boolean finalizer flag')
def count(rows):
 m=sum(o=='*' for _,o,_,_ in rows);return dict(operations=len(rows),M=m,A=len(rows)-m)
def execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  aa=e[a] if type(a)is str else a;bb=e[b] if type(b)is str else b;e[n]=aa*bb if o=='*' else aa+bb if o=='+' else aa-bb
 return e
def at(e,x):return e[x] if type(x)is str else x

def _paths(root=None):
 here=Path(__file__).resolve().parent;root=here if root is None else Path(root).resolve();path=here/PARENT_NAME if (here/PARENT_NAME).is_file() else root/PARENT_NAME
 need(hashlib.sha256(path.read_bytes()).hexdigest()==PARENT_SHA256,'Changed pinned phase parent');return root,path
@lru_cache(None)
def _load(path):
 data=Path(path).read_bytes();need(hashlib.sha256(data).hexdigest()==PARENT_SHA256,'Phase parent changed before execution')
 p=types.ModuleType('_grill_phase_residual_parent');p.__file__=str(path);exec(compile(data,str(path),'exec'),p.__dict__);return p
def _context(root=None):
 root,path=_paths(root);p=_load(str(path));p._context(root);return root,path,p
@lru_cache(None)
def _canonical(program,unit,root,path):return _load(path).build(program,unit_product=unit,root=Path(root))

def _poly(rows,target,atoms):
 table={n:(o,a,b) for n,o,a,b in rows};e={n:{(n,):1} for n in atoms}
 def value(x):
  if type(x)is int:return {():x} if x else {}
  if x not in e:
   need(x in table,'Undeclared local polynomial atom '+x);o,a,b=table[x];A=value(a);B=value(b);C=Counter()
   if o=='*':
    for ka,va in A.items():
     for kb,vb in B.items():C[tuple(sorted(ka+kb))]+=va*vb
   else:
    C.update(A)
    for k,v in B.items():C[k]+=v if o=='+' else -v
   e[x]={k:v for k,v in C.items() if v}
  return e[x]
 return value(target)

def _phase_residual(p):
 pair=p['comparisons'][3];tail=p['polynomial_source'][len(p['source']):]
 need(exact(pair,(p['interfaces']['phase_lhs'],p['interfaces']['phase_rhs'])),'Phase comparison interface changed')
 names=[n for n,o,a,b in tail if o=='-' and exact((a,b),pair)];need(len(names)==1,'Unique literal phase residual required');return names[0]

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
  if (o,a,b)in seen:return seen[o,a,b]
  n='phase_residual__'+label;need(n not in defs,'Fresh phase register collision');defs[n]=(n,o,a,b);seen[o,a,b]=n;return n
 def total(vs,label):
  out=0
  for i,v in enumerate(vs):out=gate(label+str(i),'+',out,v)
  return out
 m=old['phase_count'];J=old['interfaces']['J'];B=old['interfaces']['B'];residual=_phase_residual(old)
 if m==1:left,right='phase_initial',1;regs=dict(T=0)
 else:
  pairs=[gate('pair'+str(i),'+',f'Shat{2*i}',f'Shat{2*i+1}') for i in range(m)]
  T=gate('T','-',total([gate('weight'+str(i),'*',m-i,pairs[i]) for i in range(1,m)],'sum'),m*(m-1))
  Bm1=gate('Bm1','-',B,1);prod=gate('weighted_T','*',Bm1,T);first=gate('first_phase','*',m,pairs[0])
  difference=gate('difference','-',first,prod);left=gate('left','+',difference,'phase_initial');right=gate('right','+',J,3*m)
  regs=dict(T=T,pair0=pairs[0],Bm1=Bm1)
 tail=old['polynomial_source'][len(old['source']):];need(exact(old['polynomial_source'][:len(old['source'])],old['source']),'Complete source prefix required')
 for row in tail:defs[row[0]]=tuple(row)
 defs[residual]=(residual,'-',left,right);tailnames={r[0] for r in tail};out=[];done=set(p['parameters']+p['auxiliaries']);busy=set()
 def visit(n):
  if type(n)is int or n in done:return
  need(type(n)is str and n in defs and n not in busy,'Closed acyclic source required');busy.add(n);row=defs[n];visit(row[2]);visit(row[3]);out.append(row);done.add(n);busy.remove(n)
 visit(p['output']);need(tailnames<=done,'Finalizer gate became dead')
 source=[r for r in out if r[0]not in tailnames];newtail=[defs[r[0]] for r in tail]
 need(all(exact(a,b) for a,b in zip(tail,newtail) if a[0]!=residual),'Changed finalizer beyond phase residual')
 p['source']=source;p['polynomial_source']=source+newtail;p['comparisons'][3]=(left,right)
 return p,regs,residual

def _proof(old,new,residual):
 B=old['interfaces']['B'];hats=[f'Shat{i}' for i in range(2*old['phase_count'])];atoms=[B,*hats,'phase_initial']
 a=_poly(old['polynomial_source'],residual,atoms);b=_poly(new['polynomial_source'],residual,atoms)
 need(a==b,'Phase residual identity failed after expanding actual J and P definitions')
 # Every atom is either a supplied coordinate or a literally unchanged derived B.
 intern={}
 def node(key):
  if key not in intern:intern[key]=len(intern)
  return intern[key]
 def graph(p):
  e={n:node(('coordinate',n)) for n in p['parameters']+p['auxiliaries']}
  def v(x):return e[x] if type(x)is str else node(('integer',x))
  for n,o,x,y in p['polynomial_source']:
   e[n]=node(('proved exact phase residual',)) if n==residual else node((o,v(x),v(y)))
  return e,v
 oe,ov=graph(old);ne,nv=graph(new)
 for atom in atoms:need(oe[atom]==ne[atom],'Changed proof atom '+atom)
 need(len(old['comparisons'])==len(new['comparisons']),'Changed comparison count')
 for i,(before,after) in enumerate(zip(old['comparisons'],new['comparisons'])):
  if i!=3:
   need(exact(before,after),'Changed nonphase comparison')
   for x in before:need(ov(x)==nv(x),'Changed nonphase comparison operand')
 for name in old.get('unit_factors',[]):need(oe[name]==ne[name],'Changed native unit factor')
 for key,x in old['interfaces'].items():
  if key not in HISTORICAL_INTERFACES:need(ov(x)==nv(new['interfaces'][key]),'Changed nonphase interface '+key)
 need(oe[old['output']]==ne[new['output']],'Changed complete final polynomial')
 return dict(residual_register=residual,expanded_atoms=atoms,terms=[dict(monomial=list(k),coefficient=v) for k,v in sorted(a.items())],
  J_and_P_expanded_from_source=True,identical_comparison_residuals=len(old['comparisons']),native_unit_factors=old.get('unit_factors',[])[:],complete_polynomial_identity=True,
  statement='The phase comparison operands change, but their difference is the identical polynomial; every other residual and the full native/finalizer polynomial are unchanged on all supplied tuples.')

def _audit(p):
 names=p['parameters']+p['auxiliaries'];known=set(names);live={p['output']};degree={n:1 for n in names}
 need(len(known)==len(names),'Unique coordinates required')
 for n,o,a,b in p['polynomial_source']:
  need(type(n)is str and n not in known and o in ('+','-','*'),'SSA source required')
  need(all(type(x)is int or type(x)is str and x in known for x in (a,b)),'Exact source operands required')
  da=degree[a] if type(a)is str else 0;db=degree[b] if type(b)is str else 0;degree[n]=da+db if o=='*' else max(da,db);known.add(n)
 for n,o,a,b in reversed(p['polynomial_source']):need(n in live,'Dead emitted operation');live.update(x for x in (a,b) if type(x)is str)
 need(set(names)<=live,'Unused supplied coordinate')
 for x in p['interfaces'].values():need(type(x)is int or x in known,'Unavailable live interface')
 return degree[p['output']]

def _rewrite(old):
 p,regs,residual=_candidate(old);before=count(old['polynomial_source']);after=count(p['polynomial_source']);use=after['operations']<before['operations']
 if not use:p=copy.deepcopy(old);regs={};after=before
 proof=_proof(old,p,residual);historical={}
 if use:
  historical={k:p['interfaces'].pop(k) for k in HISTORICAL_INTERFACES}
  p['interfaces'].update(phase_residual_left=p['comparisons'][3][0],phase_residual_right=p['comparisons'][3][1])
  if 'phase_sharing'in p:p['historical_phase_sharing']=p.pop('phase_sharing')
  p['proof_only_phase_formulas']=dict(definitions={'T':'sum_{p=1}^{m-1}(m-p)*(Shat[2p]+Shat[2p+1]-2)','S0':'Shat0+Shat1-2',
   'Next':'m*J-T','Q':'(m+1)*J-m*S0-T','phase_lhs':'B*Next+phase_initial','phase_rhs':'Q+m*P'},
   parent_registers=historical,scope='Historical mathematical values, not emitted interfaces, additional coordinates, or unpaid current gates.')
 degree=_audit(p);cert=count(p['source']);p.update(operations=cert['operations'],multiplications=cert['M'],additions_subtractions=cert['A'])
 p['wrapper_operations']=sum(not n.startswith(p['native_prefix']) for n,o,a,b in p['source'])
 p['polynomial_ledger']=dict(after,witnesses=len(p['auxiliaries']),comparisons=len(p['comparisons']),degree_upper=degree)
 p['phase_residual_rewrite']=dict(parent_file=PARENT_NAME,parent_sha256=PARENT_SHA256,selected='residual' if use else 'unchanged_parent',proof=proof,
  active_registers=regs,saved={k:before[k]-after[k] for k in before},parent_count=before,
  removed_registers=[n for n,o,a,b in old['source'] if n not in {r[0] for r in p['source']}],
  scope='Exact residual and complete-polynomial identity on the existing strong P0=3x+Z0 input cone; not the separate weak-cone208 compiler.')
 p['kind']='grill_native_strong_phase_residual206';p['full_polynomial_identity']=True
 need(p['exact_degree']is None and degree==old['polynomial_ledger']['degree_upper'],'Retain only the checked formal degree bound')
 return p
@lru_cache(None)
def _packet(program,unit,root,path):return _rewrite(_canonical(program,unit,root,path))
def build(program=(0,1,1),*,unit_product=True,root=None):
 args(program,unit_product);root,path,parent=_context(root);return copy.deepcopy(_packet(program,unit_product,str(root),str(path)))
def checked(p,*,root=None):
 need(type(p)is dict,'Canonical packet required');q=build(p.get('program'),unit_product=p.get('unit_product'),root=root);need(exact(p,q),'Noncanonical residual packet');return p
def canonical_parent(p,*,root=None):
 p=checked(p,root=root);root,path,parent=_context(root);return copy.deepcopy(_canonical(p['program'],p['unit_product'],str(root),str(path)))
def rewrite(p,*,root=None):
 need(type(p)is dict,'Canonical phase parent packet required');args(p.get('program'),p.get('unit_product'));root,path,parent=_context(root)
 q=_canonical(p['program'],p['unit_product'],str(root),str(path));need(exact(p,q),'Noncanonical complete parent');return copy.deepcopy(_packet(p['program'],p['unit_product'],str(root),str(path)))
def polynomial_source(p,*,root=None):return copy.deepcopy(checked(p,root=root)['polynomial_source'])
def _values(p,values,signed):
 need(type(signed)is bool,'Exact signed flag required');need(type(values)is dict and all(type(k)is str for k in values) and values.keys()==set(p['parameters']+p['auxiliaries']),'Complete exact coordinate assignment required')
 need(all(type(v)is int and (signed or v>0) for v in values.values()),'Exact positive integers, or explicit signed algebra mode required')
def evaluate(p,values,*,signed=False,root=None):
 p=checked(p,root=root);_values(p,values,signed);return execute(p['polynomial_source'],values)[p['output']]
def identity(p,values,*,signed=False,root=None):
 p=checked(p,root=root);_values(p,values,signed);q=canonical_parent(p,root=root);a=execute(q['polynomial_source'],values);b=execute(p['polynomial_source'],values)
 rr=[at(a,x)-at(a,y) for x,y in q['comparisons']];ss=[at(b,x)-at(b,y) for x,y in p['comparisons']]
 need(rr==ss and a[q['output']]==b[p['output']],'Complete source identity failed');return dict(output=b[p['output']],residuals=ss)

def verify(root=None):
 root,path,parent=_context(root);rng=random.Random(206230);c=Counter();forms=[]
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):c['malformed_rejections']+=1;return
  raise ValueError('Malformed API input accepted')
 for program in ((0,),(1,),(0,1,1),(2,0,1)):
  for unit in (False,True):
   p=build(program,unit_product=unit,root=root);q=canonical_parent(p,root=root)
   need(exact(rewrite(q,root=root),p),'Canonical transform');_audit(p);c['complete_formal_polynomial_identities']+=1;c['formal_residual_identities']+=len(p['comparisons'])
   for field in ('parameters','auxiliaries','maps','groups_U','groups_V','baselines','K','unit_factors','unit_register','root_coordinate','projection_aliases','scale_exponent','region_exponents','scope'):
    need(exact(p.get(field),q.get(field)),'Changed inherited relation interface '+field)
   need(p['phase_residual_rewrite']['saved']==dict(operations=3,M=1,A=2),'Representative complete three-operation saving')
   for j in range(20):
    signed=j>=10;v={n:rng.randrange(-3,4) if signed else rng.randrange(1,5) for n in p['parameters']+p['auxiliaries']};r=identity(p,v,signed=signed,root=root)
    c['complete_numeric_identities']+=1;c['signed_identities']+=signed;c['numeric_residual_identities']+=len(r['residuals'])
   for j in range(3):
    v={n:Fraction(rng.randrange(-2,3),rng.randrange(1,4)) for n in p['parameters']+p['auxiliaries']};a=execute(q['polynomial_source'],v);b=execute(p['polynomial_source'],v)
    need(a[q['output']]==b[p['output']],'All-rational complete identity');c['rational_identities']+=1
   removed=set(p['phase_residual_rewrite']['removed_registers'])
   def scan(v):
    if type(v)is dict:
     for x in v.values():scan(x)
    elif type(v)in(tuple,list):
     for x in v:scan(x)
    elif type(v)is str:need(v not in removed,'Stale active register metadata '+v)
   scan({k:v for k,v in p.items() if k not in ('phase_residual_rewrite','historical_phase_sharing','proof_only_phase_formulas')});c['active_metadata_checks']+=1
   for field in ('source','polynomial_source','interfaces','comparisons','phase_residual_rewrite','polynomial_ledger','auxiliaries'):
    bad=copy.deepcopy(p);bad[field]=None;reject(lambda bad=bad:checked(bad,root=root))
   bad=copy.deepcopy(q);bad['scope']='changed';reject(lambda bad=bad:rewrite(bad,root=root))
   for typ in (float,bool):
    bad=copy.deepcopy(p);i,j=next((i,j) for i,row in enumerate(bad['polynomial_source']) for j in (2,3) if type(row[j])is int and (typ is float or row[j]in(0,1)))
    row=list(bad['polynomial_source'][i]);row[j]=typ(row[j]);bad['polynomial_source'][i]=tuple(row);reject(lambda bad=bad:checked(bad,root=root))
   values={n:1 for n in p['parameters']+p['auxiliaries']}
   for n in list(values)[::9]:
    for badvalue in (True,1.0,None,0,-1):reject(lambda n=n,badvalue=badvalue:evaluate(p,dict(values,**{n:badvalue}),root=root))
   for getter in (lambda:build(program,unit_product=unit,root=root),lambda:canonical_parent(p,root=root),lambda:polynomial_source(p,root=root)):
    z=getter();saved=copy.deepcopy(z);z.clear();need(exact(getter(),saved),'Public mutable cache');c['copy_checks']+=1
   forms.append(dict(program=list(program),unit_product=unit,parent_ledger=q['polynomial_ledger'],compiler=p))
 for bad in (None,(),[0],(True,),(1.0,),(-1,)):reject(lambda bad=bad:build(bad,root=root))
 for bad in (None,0,1):reject(lambda bad=bad:build(unit_product=bad,root=root))
 p=build(root=root);values={n:1 for n in p['parameters']+p['auxiliaries']}
 for bad in (1,0,None):reject(lambda bad=bad:evaluate(p,values,signed=bad,root=root))
 for bad in ({'x':1},dict(values,extra=1)):reject(lambda bad=bad:evaluate(p,bad,root=root))
 class ForeignKey(str):pass
 bad=copy.deepcopy(p);bad[ForeignKey('program')]=bad.pop('program');reject(lambda:checked(bad,root=root))
 bad=dict(values);bad[ForeignKey('x')]=bad.pop('x');reject(lambda:evaluate(p,bad,root=root))
 # Authenticate all consumed source bytes on warm public calls, not only imports.
 with tempfile.TemporaryDirectory(prefix='grill-residual-warm-') as directory:
  directory=Path(directory);child=directory/Path(__file__).name;child.write_bytes(Path(__file__).read_bytes())
  phasecopy=directory/PARENT_NAME;phasecopy.write_bytes(path.read_bytes())
  _,nativepath,native=parent._context(root);nativecopy=directory/parent.PARENT_NAME;nativecopy.write_bytes(nativepath.read_bytes())
  private_papers=directory/'Papers';private_root=private_papers/'research-wip'/'native-stream-queue'
  for relative,h in native.PINS.values():
   target=private_papers/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((root.parents[1]/relative).read_bytes())
  module=types.ModuleType('_private_grill_phase_residual_guard');module.__file__=str(child);exec(compile(child.read_bytes(),str(child),'exec'),module.__dict__)
  pristine=module.build((0,),root=private_root)
  for target in (phasecopy,nativecopy,private_root/'pcp_affine_slope_class_history.py'):
   data=target.read_bytes()
   try:
    target.write_bytes(data+b'\n# private warm source pin regression\n');reject(lambda:module.build((0,),root=private_root));c['warm_source_pin_rejections']+=1
   finally:target.write_bytes(data)
   need(exact(module.build((0,),root=private_root),pristine),'Restored private source packet changed')
 return json.loads(json.dumps(dict(status='PASS_STRONG_NATIVE_GRILL_PHASE_RESIDUAL206',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_sha256=PARENT_SHA256,checks=dict(c),forms=forms,
  scope='Same full polynomial and all comparison residuals as strong-cone209; changed phase operands are explicitly historical. Arbitrary duration/input/native hypotheses unchanged, no universal program instantiated.')))

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],checks=r['checks'],ledgers=[dict(program=f['program'],unit_product=f['unit_product'],**f['compiler']['polynomial_ledger']) for f in r['forms']]),indent=2))
