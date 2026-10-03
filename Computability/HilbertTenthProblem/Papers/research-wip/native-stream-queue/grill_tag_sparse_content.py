#!/usr/bin/env python3
"""Pinned sparse content-row transformation of finite Grill word closure."""
if not __debug__:
 raise RuntimeError('Run this research checker without -O')
import argparse,copy,hashlib,itertools,json,random,tempfile,types
from collections import Counter
from fractions import Fraction
from pathlib import Path

PARENT_NAME='grill_tag_word_closure.py'
PARENT_SHA256='144129bb04e271588ed1c95d9c91f5682d30c6b5a540154c6c0b9b0c40331d96'

def need(v,m):
 if not v:raise ValueError(m)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
 if type(a)in(tuple,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def _parent(root=None):
 need(root is None or type(root)is str or isinstance(root,Path),'Parent directory path required')
 path=(Path(__file__).resolve().parent if root is None else Path(root))/PARENT_NAME
 data=path.read_bytes();need(hashlib.sha256(data).hexdigest()==PARENT_SHA256,'Pinned parent source mismatch')
 # Execute authenticated bytes directly: no sibling imports or cached bytecode.
 m=types.ModuleType('_grill_sparse_pinned_parent');m.__file__=str(path)
 exec(compile(data,str(path),'exec'),m.__dict__)
 return m

def canonical_parent(program,horizon,*,square_boolean=False,root=None):
 return _parent(root).build(program,horizon,mode='scaled',square_boolean=square_boolean)

def _rewrite(old):
 # Called only with a freshly built or whole-packet-checked scaled parent.
 program=old['program'];t=old['horizon'];squared=old['square_boolean']
 defs={n:(n,o,a,b) for n,o,a,b in old['source']};seen={}
 for n,o,a,b in old['source']:
  if o in ('+','*') and repr(a)>repr(b):a,b=b,a
  seen[o,a,b]=n
 def gate(n,o,a,b):
  if type(a)is int and type(b)is int:return a+b if o=='+' else a-b if o=='-' else a*b
  if o=='+':
   if a==0:return b
   if b==0:return a
  if o=='-' and b==0:return a
  if o=='*':
   if a==0 or b==0:return 0
   if a==1:return b
   if b==1:return a
  if o in ('+','*') and repr(a)>repr(b):a,b=b,a
  if (o,a,b) in seen:return seen[o,a,b]
  need(n not in defs,'Duplicate sparse label');defs[n]=(n,o,a,b);seen[o,a,b]=n;return n
 coeffs=[2*(4**program[i%len(program)]-1)//3 for i in range(t)]
 weighted=[];total=0
 for i,(c,T) in enumerate(zip(coeffs,old['registers']['weighted_terms'])):
  v=gate(f'sparse_cT{i}','*',c,T);weighted.append(v)
  total=gate(f'sparse_acc{i}','+',total,v)
 e=gate('sparse_content_residual','-',gate('word_minus_input','-',old['registers']['binary'],'x'),total)
 need(defs['content_square']==('content_square','*',old['residuals'][1],old['residuals'][1]),'Parent second-square contract')
 defs['content_square']=('content_square','*',e,e)
 rows=[];done=set(old['inputs']+old['witnesses']);visiting=set()
 def emit(n):
  if type(n)is int or n in done:return
  need(type(n)is str and n in defs and n not in visiting,'Live DAG closure');visiting.add(n)
  _,o,a,b=defs[n];emit(a);emit(b);rows.append(defs[n]);done.add(n);visiting.remove(n)
 emit(old['output'])
 cnt=Counter(o for _,o,_,_ in rows)
 return dict(kind='grill_sparse_content_word_closure',program=program,horizon=t,square_boolean=squared,
  inputs=old['inputs'][:],witnesses=old['witnesses'][:],source=rows,output=old['output'],
  residuals=[old['residuals'][0],e]+old['boolean_residuals'],boolean_residuals=old['boolean_residuals'][:],
  registers=dict(P0=old['registers']['P0'],head_digits=old['registers']['head_digits'][:],scales=old['registers']['scales'][:],
   weighted_terms=old['registers']['weighted_terms'][:],binary=old['registers']['binary'],final_width=old['registers']['final_width'],
   append_coefficients=coeffs,append_terms=weighted,append_content=total,word_residual=e),
  ledger=dict(operations=len(rows),M=cnt['*'],A=cnt['+']+cnt['-'],positive_witnesses=t+1,residuals=t+2,exact_degree=2*t+2),
  parent=dict(source=PARENT_NAME,sha256=PARENT_SHA256,mode='scaled',ledger=copy.deepcopy(old['ledger'])),
  relation=dict(coordinates='Identical named coordinates; identity map in both directions.',
   integer_zero_sets='Exactly equal on every supplied integer tuple, in both Boolean-finalizer modes.',
   full_polynomial_identity=False,old_content_row='r+3e',old_minus_new='r^2+6*r*e+8*e^2',
   notation='r is the retained width residual; e is the new content residual.'),
  scope='Same positive integer x,Z0,D_i and fixed program/external horizon as the pinned parent. Positive zero implies padded-input halt at or before horizon; a halt exactly at horizon gives zero. Posthalt zeros remain. No uniform fixed-arity or universal decoder claim.')

def rewrite(parent_packet,*,root=None):
 m=_parent(root);old=m.checked(parent_packet);need(old['mode']=='scaled','Only canonical scaled parent packets accepted')
 return _rewrite(old)
def build(program,horizon,*,square_boolean=False,root=None):
 return _rewrite(canonical_parent(program,horizon,square_boolean=square_boolean,root=root))
def checked(p,*,root=None):
 need(type(p)is dict,'Canonical full sparse packet required')
 q=build(p.get('program'),p.get('horizon'),square_boolean=p.get('square_boolean'),root=root)
 need(exact(p,q),'Noncanonical full sparse packet');return p

def _assignment(p,values,signed):
 need(type(signed)is bool,'Exact signed flag required')
 need(type(values)is dict and values.keys()==set(p['inputs']+p['witnesses']),'Exact full coordinate assignment required')
 need(all(type(k)is str for k in values) and all(type(v)is int and (signed or v>0) for v in values.values()),'Exact positive integer coordinates required (or signed=True)')

def _execute(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  a=e[a] if type(a)is str else a;b=e[b] if type(b)is str else b
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e

def evaluate(p,values,*,signed=False,root=None):
 checked(p,root=root);_assignment(p,values,signed)
 return _execute(p['source'],values)[p['output']]

def correction(p,values,*,signed=False,root=None):
 checked(p,root=root);_assignment(p,values,signed)
 old=canonical_parent(p['program'],p['horizon'],square_boolean=p['square_boolean'],root=root)
 en=_execute(p['source'],values);eo=_execute(old['source'],values);r=en[p['residuals'][0]];e=en[p['residuals'][1]];s=eo[old['residuals'][1]]
 oldvalue=eo[old['output']];newvalue=en[p['output']];delta=r*r+6*r*e+8*e*e
 need(s==r+3*e and oldvalue-newvalue==delta,'Full correction identity')
 return dict(old=oldvalue,new=newvalue,width=r,sparse_content=e,old_content=s,old_minus_new=delta)

def decode_zero(p,values,*,root=None):
 need(evaluate(p,values,root=root)==0,'Positive sparse zero required')
 m=_parent(root);old=m.build(p['program'],p['horizon'],mode='scaled',square_boolean=p['square_boolean'])
 return m.decode_zero(old,values)

def _audit(p):
 names=set(p['inputs']+p['witnesses']);live={p['output']}
 for n,o,a,b in p['source']:
  need(type(n)is str and n not in names and o in ('+','-','*'),'Unique binary gate')
  need(all(type(v)is int or type(v)is str and v in names for v in (a,b)),'Exact topological gate inputs');names.add(n)
 for n,o,a,b in reversed(p['source']):
  need(n in live,'Dead charged gate');live.update(v for v in (a,b) if type(v)is str)
 def reg(v):
  if type(v)is list:
   for x in v:reg(x)
  else:need(type(v)is int or type(v)is str and v in names,'Current metadata register unavailable')
 for v in p['registers'].values():reg(v)
 t=p['horizon'];z=sum(p['program'][i%len(p['program'])]==0 for i in range(t));M=5*t+2-2*z+t*p['square_boolean'];A=6*t+3-z
 need(p['ledger']==dict(operations=M+A,M=M,A=A,positive_witnesses=t+1,residuals=t+2,exact_degree=2*t+2),'Full generic paid ledger')
 need(p['parent']['ledger']['operations']-(M+A)==2+2*z-t,'Sparse saving formula')
 return z

def _manual(m,program,t,squared):
 # Closed product formula, independent of the emitted scaled recurrence.
 add=m.add;mul=m.mul;constant=m.constant;one=constant(1)
 x={('x',):1};z={('Z0',):1};P=add(mul(constant(3),x),z);S=one;weighted={};B={};bs=[]
 for i in range(t):
  d=add({(f'D{i}',):1},one,-1);H=4**program[i%len(program)];T=mul(mul(P,S),d)
  weighted=add(weighted,mul(constant(2*(H-1)//3),T));B=add(B,mul(constant(1<<i),d))
  S=mul(S,add(one,mul(constant(2*H-1),d)));bs.append(mul(d,add(d,one,-1)))
 r=add(mul(P,S),constant(1<<t),-1);e=add(add(B,x,-1),weighted,-1);F=add(mul(r,r),mul(e,e))
 for b in bs:F=add(F,mul(b,b) if squared else b)
 return F,[r,e]+bs

def verify(*,root=None):
 m=_parent(root);counts=Counter();rng=random.Random(1070309);programs=((0,),(1,),(0,1,1),(2,0,1));packets=[];tradeoffs=[]
 for program,t,squared in itertools.product(programs,range(1,13),(False,True)):
  old=m.build(program,t,mode='scaled',square_boolean=squared);p=_rewrite(old);_audit(p);counts['complete_paid_live_DAG_ledgers']+=1
  need(exact(p,rewrite(old,root=root)),'Public canonical rewrite');counts['canonical_parent_rewrites']+=1
  if t<=4:
   pe=m.polynomial_source(p);oe=m.polynomial_source(old);F,rr=_manual(m,program,t,squared)
   need(pe[p['output']]==F and all(pe[r]==q for r,q in zip(p['residuals'],rr)),'Full independent formal source polynomial and rows')
   r,e=rr[:2];s=oe[old['residuals'][1]]
   need(s==m.add(r,m.mul(m.constant(3),e)),'Exact content-row identity')
   delta=m.add(m.add(m.mul(r,r),m.mul(m.constant(6),m.mul(r,e))),m.mul(m.constant(8),m.mul(e,e)))
   need(m.add(oe[old['output']],F,-1)==delta,'Full formal off-zero correction')
   need(max(map(len,F))==2*t+2,'Exact attained degree')
   counts['full_formal_polynomial_corrections']+=1;counts['formal_residual_identities']+=t+2;counts['exact_expanded_degrees']+=1
  for j in range(4):
   values={n:rng.randrange(-4,6) for n in p['inputs']+p['witnesses']};en=_execute(p['source'],values);eo=_execute(old['source'],values)
   r=en[p['residuals'][0]];e=en[p['residuals'][1]]
   need(eo[old['residuals'][1]]==r+3*e and eo[old['output']]-en[p['output']]==r*r+6*r*e+8*e*e,'All-value signed correction')
   need((eo[old['output']]==0)==(en[p['output']]==0),'Signed integer zero equivalence');counts['signed_complete_corrections']+=1
  if program==(0,1,1) and t in (1,3,6):packets.append(p)
  if not squared and t in (1,3,6,12):tradeoffs.append(dict(program=list(program),horizon=t,parent=old['ledger'],sparse=p['ledger'],saved=old['ledger']['operations']-p['ledger']['operations']))
 # Exhaustive unfiltered signed tuples: no natural/Boolean assumptions in filtering.
 for program,t in itertools.product(programs[:3],range(1,4)):
  p=build(program,t,root=root);old=m.build(program,t)
  for x,z,ds in itertools.product(range(-2,3),range(-2,3),itertools.product(range(-1,4),repeat=t)):
   v={'x':x,'Z0':z,**{f'D{i}':d for i,d in enumerate(ds)}};en=_execute(p['source'],v);eo=_execute(old['source'],v)
   rows=all(en[r]==0 for r in p['residuals']);need((en[p['output']]==0)==rows==(eo[old['output']]==0),'Complete signed zero conjunction')
   counts['unfiltered_signed_integer_tuples']+=1;counts['signed_zero_tuples']+=rows
 # Reconstruct every positive zero from its Boolean head word in the finite census.
 zeros=[]
 for program,t in itertools.product(programs,range(1,10)):
  p=build(program,t,root=root);old=m.build(program,t)
  for heads in itertools.product((0,1),repeat=t):
   counts['enumerated_Boolean_head_words']+=1;S,C,B,scales=m.direct_values(program,heads)
   if (1<<t)%S:continue
   P0=(1<<t)//S;Z0=(1<<t)-P0*C-3*B
   if Z0<=0 or (P0-Z0)%3:continue
   x=(P0-Z0)//3
   if x<=0:continue
   v={'x':x,'Z0':Z0,**{f'D{i}':d+1 for i,d in enumerate(heads)}}
   need(_execute(p['source'],v)[p['output']]==0 and _execute(old['source'],v)[old['output']]==0,'Both positive zero directions')
   result=decode_zero(p,v,root=root);zeros.append(dict(program=list(program),values=v,**result));counts['positive_zero_census']+=1;counts['posthalt_zero_census']+=result['has_posthalt_extension']
 post=build((0,1,1),6,root=root);postv={'x':1,'Z0':1,**{f'D{i}':int(c)+1 for i,c in enumerate('100010')}}
 postproof=decode_zero(post,postv,root=root);need(postproof['actual_first_halt']==3 and postproof['formal_widths'][4]=='1/2','Same posthalt witness')
 # The natural/positive-real boundary remains explicit.
 real=build((0,1,1),3,root=root);realv={'x':1,'Z0':1,'D0':2,'D1':1+Fraction(1,3333),'D2':1}
 need(_execute(real['source'],realv)[real['output']]==0,'Positive-real nonboolean false zero')
 # Zero equivalence itself fails if the integer restriction is removed.
 rp=build((0,),1,root=root);ro=m.build((0,),1)
 real_separations=[]
 for v in ({'x':Fraction(1,2),'Z0':Fraction(1,6),'D0':Fraction(3,2)},
           {'x':Fraction(1,3),'Z0':Fraction(1,3),'D0':Fraction(3,2)}):
  nv=_execute(rp['source'],v)[rp['output']];ov=_execute(ro['source'],v)[ro['output']]
  need((nv==0)!=(ov==0),'Positive-real zero sets need not coincide')
  real_separations.append(dict(values={k:str(x) for k,x in v.items()},old=str(ov),new=str(nv)))
  counts['positive_real_zero_set_separations']+=1
 def reject(fn):
  try:fn()
  except (ValueError,TypeError,KeyError):counts['malformed_rejected']+=1;return
  raise ValueError('Malformed value accepted')
 for bad in ((),[0,1],(True,),(1.0,),(-1,),None):reject(lambda bad=bad:build(bad,3,root=root))
 for bad in (True,0,-1,1.0,None):reject(lambda bad=bad:build((0,),bad,root=root))
 for bad in (0,1,1.0,None):reject(lambda bad=bad:build((0,),3,square_boolean=bad,root=root))
 reject(lambda:rewrite(m.build((0,),3,mode='direct'),root=root))
 for field in ('source','ledger','registers','residuals','witnesses','scope','parent','relation'):
  p=build((0,1,1),3,root=root);p[field]=None;reject(lambda p=p:checked(p,root=root))
 for bad in (True,3.0):
  p=build((0,1,1),3,root=root);r=list(p['source'][0]);j=next(j for j in (2,3) if type(r[j])is int);r[j]=bad;p['source'][0]=tuple(r);reject(lambda p=p:checked(p,root=root))
 p=build((0,1,1),3,root=root);v={'x':1,'Z0':1,'D0':2,'D1':1,'D2':1}
 for key in v:
  for bad in (True,1.0,0,-1,None):
   vv=dict(v);vv[key]=bad;reject(lambda vv=vv:evaluate(p,vv,root=root))
 for bad in (0,1,None):reject(lambda bad=bad:evaluate(p,v,signed=bad,root=root))
 reject(lambda:evaluate(real,realv,root=root));reject(lambda:decode_zero(p,{**v,'Z0':2},root=root))
 for what in ('source','registers','parent'):
  q=build((0,1,1),3,root=root);q[what].clear();need(exact(build((0,1,1),3,root=root),p),'Fresh packet isolation');counts['defensive_copy_checks']+=1
 old=m.build((0,1,1),3);q=rewrite(old,root=root);q['registers']['scales'].clear();need(bool(old['registers']['scales']),'Parent packet not mutated');counts['defensive_copy_checks']+=1
 with tempfile.TemporaryDirectory(prefix='grill-sparse-source-guard-') as d:
  path=Path(d)/PARENT_NAME;path.write_bytes((Path(m.__file__)).read_bytes());need(exact(build((0,),1,root=d),build((0,),1,root=root)),'Private valid source copy')
  path.write_bytes(path.read_bytes()+b'\n# unauthorized source change\n');reject(lambda:build((0,),1,root=d));counts['source_pin_tamper_rejections']+=1
 # Keep the public identity API exercised on both positive and signed assignments.
 for v in ({'x':1,'Z0':1,'D0':2,'D1':1,'D2':1},{'x':-4,'Z0':3,'D0':0,'D1':-2,'D2':5}):
  c=correction(p,v,signed=True,root=root);need(c['old']-c['new']==c['old_minus_new'],'Public correction');counts['public_correction_checks']+=1
 return json.loads(json.dumps(dict(status='PASS_SPARSE_GRILL_CONTENT',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),parent_sha256=PARENT_SHA256,
  counts=dict(counts),packets=packets,tradeoffs=tradeoffs,positive_zero_census=zeros,
  posthalt_fixture=dict(values=postv,proof=postproof),
  real_counterexample=dict(values={k:str(v) for k,v in realv.items()},polynomial='delta*(3333*delta-1)'),
  real_zero_set_separations=real_separations,
  scope='Complete polynomial changes by the displayed exact correction; supplied integer zero sets and positive coordinates are identical to the pinned scaled parent. Fixed program/external horizon; no universal decoder or uniform packing claim.')))

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,help='Directory containing the pinned parent source (default: sibling)');p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(root=a.root)
 if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Full saved receipt mismatch')
 if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts']),indent=2))
