#!/usr/bin/env python3
"""Independent bounded review of immutable extracted 808b53ed8 report sources.
No archive or report edits. Original constructor defects are recorded as expected.
"""
from pathlib import Path
import importlib.util,sys,json,hashlib,itertools,random,math,argparse,subprocess,shutil,tempfile
from collections import defaultdict
from fractions import Fraction
if not __debug__:
 raise RuntimeError('This development checker requires assertions; do not run Python with -O.')
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--parallel-root',type=Path,required=True)
parser.add_argument('--order-root',type=Path,required=True)
parser.add_argument('--receipt',type=Path,required=True)
args=parser.parse_args()
P=args.parallel_root.resolve();O=args.order_root.resolve()
def load(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);return m
R={'status':'PASS_WITH_TWO_PARALLEL_CONSTRUCTOR_DEFECTS','scope':'Finite exact independent checks; proof review is in companion MD. No universal polynomial instantiated.'}
pins={
 'parallel/code/parallel_certificates.py':'27cb3689fa8329f940055489756a977befd98ee2ab4b2c59651451d440f26111',
 'parallel/code/verify.py':'f65bf1ad71c6abaadb4c755634ea3a738b042af0d2df9ee93a12491136945f1a',
 'parallel/article.tex':'88d261e789ef21bd31248859031024c46c8df3194017796e8246d4aef98d6c83',
 'order/code/pair_geometry.py':'7d5e783760ce8a0d0358e10d13ae455fe82fb1fc3fbd554714c3ebfda3178c3a',
 'order/code/verify.py':'fdd5120ceb28e1852325dc7d4f5ba8f874b55740314a196506d44a9ba32719b3',
 'order/article.tex':'0901b8d55182737f1f241ba737d85bad37e95739cf26baa8f0ce774c04e2346a'}
for rel,digest in pins.items():
 key,rel=rel.split('/',1);base=P if key=='parallel' else O
 assert hashlib.sha256((base/rel).read_bytes()).hexdigest()==digest
R['provenance']=pins
p=load('parallel_review_original',P/'code/parallel_certificates.py')
o=load('order_review_original',O/'code/pair_geometry.py')
# Accepted mutable input changes the declared network behind a compiled polynomial.
cons=[[1]];prod=[[0]];net=p.Network(cons,prod);cert=p.RoundCertificate(net)
w=cert.canonical_assignment((1,),(1,));cons[0][0]=2
assert cert.polynomial.evaluate(w)==0 and not net.legal((1,),(1,))
# Invalid bool field is interpreted differently by semantic oracle and compiler.
valid=p.Network(((1,),),((0,),),((p.Atom(0,1,True),),))
bad=p.Network(((1,),),((0,),),((p.Atom(0,1,2),),))
w=p.RoundCertificate(valid).canonical_assignment((1,),(1,))
assert not bad.legal((1,),(1,)) and p.RoundCertificate(bad).polynomial.evaluate(w)==0
R['defects']={'mutable_network':{'initial_consume':1,'mutated_consume':2,'x':[1],'f':[1],'export_consume':cert.as_dict()['consume_columns'],'polynomial':0,'legal':False},'invalid_guard_present':{'present':2,'semantic_enabled':bad.enabled((1,)),'polynomial':0,'legal':False}}
# Oracle uses explicit componentwise feasible extensions, independently of Network.legal.
def semantic(A,B,G,x,f,flat,keep):
 if flat and any(z>1 for z in f):return None
 enabled=[all((x[i]>=t) if yes else (x[i]<t) for i,t,yes in g) for g in G]
 if any(f[j] and not enabled[j] for j in range(len(A))):return None
 r=tuple(x[i]-sum(col[i]*fj for col,fj in zip(A,f)) for i in range(len(x)))
 if min(r)<0:return None
 if any(enabled[j] and (not flat or f[j]==0) and all(A[j][i]<=r[i] for i in range(len(x))) for j in range(len(A))):return None
 return tuple(keep[i]*r[i]+sum(B[j][i]*f[j] for j in range(len(A))) for i in range(len(x)))
rng=random.Random(80853)
counts=defaultdict(int)
for z in range(100):
 d,m=rng.randrange(1,4),rng.randrange(1,4)
 A=[]
 for j in range(m):
  col=tuple(rng.randrange(3) for _ in range(d))
  if not any(col):col=(1,)+col[1:]
  A.append(col)
 A=tuple(A);B=tuple(tuple(rng.randrange(3) for _ in range(d)) for _ in range(m))
 G=tuple(tuple((rng.randrange(d),rng.randrange(1,4),bool(rng.randrange(2))) for _ in range(rng.randrange(4))) for _ in range(m))
 net=p.Network(A,B,tuple(tuple(p.Atom(*a) for a in g) for g in G))
 flat=bool(z%2);keep=tuple(rng.randrange(2) for _ in range(d));cert=p.RoundCertificate(net,flat=flat,retention=keep)
 for _ in range(60):
  x=tuple(rng.randrange(6) for _ in range(d));f=tuple(rng.randrange(5) for _ in range(m))
  out=semantic(A,B,G,x,f,flat,keep);w=cert.canonical_assignment(x,f)
  assert (w is None)==(out is None)
  counts['independent_round_candidates']+=1
  if w is not None:
   assert tuple(w[n] for n in cert.output_names)==out and cert.polynomial.evaluate(w)==0
   counts['round_natural_zeros']+=1
   for _ in range(3):
    new=dict(w)
    for name in rng.sample(cert.auxiliary_names,min(3,len(cert.auxiliary_names))):new[name]=rng.randrange(5)
    q=cert.polynomial.evaluate(new);assert q>=0
    if q==0:assert new==w
    counts['joint_witness_mutations']+=1
 # supplied arbitrary tuples: may be noncanonical rather than generated witnesses
 for _ in range(70):
  env={n:rng.randrange(5) for n in cert.input_names+cert.output_names+cert.auxiliary_names}
  q=cert.polynomial.evaluate(env);assert q>=0
  if q==0:
   x=tuple(env[n] for n in cert.input_names);f=tuple(env[f'f{j}'] for j in range(m))
   y=semantic(A,B,G,x,f,flat,keep)
   assert y==tuple(env[n] for n in cert.output_names) and env==cert.canonical_assignment(x,f,y)
  counts['arbitrary_natural_round_assignments']+=1
 for _ in range(2):
  env={n:Fraction(rng.randrange(10),rng.randrange(1,6)) for n in cert.input_names+cert.output_names+cert.auxiliary_names}
  assert cert.polynomial.evaluate(env)>=0
  counts['rational_orthant_assignments']+=1
# Exact full natural root box with guarded/flat/retention certificates and tiny single species.
for flat in (False,True):
 for yes in (False,True):
  net=p.Network(((1,),),((0,),),((p.Atom(0,1,yes),),));c=p.RoundCertificate(net,flat=flat,retention=(0,))
  for vals in itertools.product((0,1),repeat=len(c.auxiliary_names)):
   for x in (0,1):
    env={'x0':x,'y0':0,**dict(zip(c.auxiliary_names,vals))};v=c.polynomial.evaluate(env)
    assert v>=0
    if v==0:assert env==c.canonical_assignment((x,),(env['f0'],),(0,));counts['full_box_roots']+=1
    counts['full_guarded_boolean_box']+=1
# Horizon boundaries and non-reuse/first-halt are checked through independently enumerated histories.
for net in (p.Network(((1,),),((0,),)),p.Network(((1,),),((1,),)),p.Network(((2,),),((1,),)),p.Network(((1,),(2,)),((0,),(1,)))):
 for t in range(4):
  for halt in (False,True):
   c=p.HistoryCertificate(net,t,first_halt=halt)
   for x in range(5):
    hist=[]
    def visit(state,seq):
     if len(seq)==t:
      dead=all(any(state[i]<a for i,a in enumerate(col)) for col in net.consume)
      if (not halt) or (dead and all(sum(f)>0 for f in seq)):hist.append(tuple(seq))
      return
     for f in itertools.product(range(5),repeat=net.m):
      out=semantic(net.consume,net.produce,((),)*net.m,state,f,False,(1,)*net.d)
      if out is not None:visit(out,seq+[f])
    visit((x,),[])
    for seq in hist:
     w=c.canonical_assignment((x,),seq);assert w is not None and c.polynomial.evaluate(w)==0
     counts['independent_history_zeros']+=1
    assert len(c.witness_names)==t*(2*net.d+2*net.m+4*len(net.thresholds))+(t+4*len(net.thresholds)+net.m if halt else 0)
    counts['history_count_ledgers']+=1
R['parallel_checks']=dict(counts)
# Complete word sets beyond author word-length scope; direct position-pair loops.
cnt=defaultdict(int);fibres=defaultdict(set)
for n in (9,10):
 for w in itertools.product('ABC',repeat=n):
  ns=tuple(w.count(s) for s in 'ABC')
  k,pv,q=tuple(sum(w[i]==s and w[j]==t for i in range(n) for j in range(i+1,n)) for s,t in ('AB','AC','BC'))
  assert o.pair_profile(w)==(ns,(k,pv,q))
  fibres[ns,pv,q].add(k);cnt['direct_words_lengths9_10']+=1
for (ns,pv,q),vals in fibres.items():
 assert vals==set(range(min(vals),max(vals)+1));cnt['full_interval_slices']+=1
 if ns[2]==2:
  assert o.corner_bounds(ns[0],ns[1],pv,q)==(min(vals),max(vals));cnt['corner_slices']+=1
for _ in range(300):
 w=''.join(rng.choice('ABC') for _ in range(rng.randrange(11,35)))
 ns,(k,pv,q)=o.pair_profile(w);last=k
 for word in o.normalization_path(w):
  nn,(kk,pp,qq)=o.pair_profile(word);assert (nn,pp,qq)==(ns,pv,q) and abs(kk-last)<=1;last=kk;cnt['normalization_vertices']+=1
 cnt['longer_normalization_words']+=1
# Profile input strict guards on each supplied parameter and environment field.
badvalues=(-1,True,False,1.0,0.5,'1',None)
for name in ('a','b','p','q','k'):
 for bad in badvalues:
  env=dict(a=3,b=2,p=2,q=1,k=4);env[name]=bad
  try:o.canonical_c2(env)
  except (ValueError,TypeError):cnt['profile_parameter_rejections']+=1
  else:raise AssertionError('bad profile scalar accepted')
system,_=o.canonical_c2();poly=system.polynomial()
assert system.serial()==json.loads((O/'data/canonical_c2_quartic.json').read_text())
for bad in (True,1.0,0.5,'1',None):
 try:o.Poly(((('x',),bad),))
 except TypeError:cnt['coefficient_rejections']+=1
 else:raise AssertionError('bad coefficient')
raw=[[['x'],2]];owned=o.Poly(raw);raw[0][0].append('y');raw[0][1]=7
assert owned.terms==((('x',),2),);cnt['deep_snapshot_checks']+=1
# Canonical initial/bound/tie/all-zero fixtures; jointly vary every witness pair.
fixtures=[dict(a=0,b=0,p=0,q=0,k=0),dict(a=3,b=2,p=2,q=1,k=4),dict(a=2,b=2,p=4,q=0,k=4),dict(a=2,b=2,p=2,q=2,k=2)]
for inp in fixtures:
 _,env=o.canonical_c2(inp);assert system.verify(env)
 for n1,n2 in itertools.combinations(system.witnesses,2):
  for v1,v2 in itertools.product(range(3),repeat=2):
   new=dict(env);new[n1]=v1;new[n2]=v2
   assert system.verify(new)==(new==env);cnt['joint_pair_witness_cases']+=1
 for name in system.parameters+system.witnesses:
  for bad in (-1,True,1.0):
   new=dict(env);new[name]=bad
   try:system.verify(new)
   except (ValueError,TypeError):cnt['full_environment_rejections']+=1
   else:raise AssertionError('bad environment scalar')
# Literal polynomial simplification: eight split products and two parity products
# are nonnegative on all natural assignments; keep remaining residuals squared.
raw_indices=(1,3,5,7,11,13,15,17,19,21)
assert len(raw_indices)==10
newpoly=sum((r if i in raw_indices else r*r for i,r in enumerate(system.residuals)),o.Poly.const(0))
correction=sum((system.residuals[i]*system.residuals[i]-system.residuals[i] for i in raw_indices),o.Poly.const(0))
assert (poly-newpoly-correction).terms==()
assert newpoly.degree==4
orthant_indices=tuple(i for i in raw_indices if i not in (5,7))
orthant_poly=sum((r if i in orthant_indices else r*r for i,r in enumerate(system.residuals)),o.Poly.const(0))
orthant_correction=sum((system.residuals[i]*system.residuals[i]-system.residuals[i] for i in orthant_indices),o.Poly.const(0))
assert (poly-orthant_poly-orthant_correction).terms==() and orthant_poly.degree==4
for natural in (False,True):
 for _ in range(1500):
  env={n:rng.randrange(0 if natural else -5,8) for n in system.parameters+system.witnesses}
  vals=system.residual_values(env);qnew=sum(v if i in raw_indices else v*v for i,v in enumerate(vals))
  assert newpoly.evaluate(env)==qnew and poly.evaluate(env)-qnew==correction.evaluate(env)
  qorthant=sum(v if i in orthant_indices else v*v for i,v in enumerate(vals))
  assert orthant_poly.evaluate(env)==qorthant and poly.evaluate(env)-qorthant==orthant_correction.evaluate(env)
  if natural:
   assert all(vals[i]>=0 for i in raw_indices) and qnew>=0 and (qnew==0)==all(v==0 for v in vals)
  cnt['natural_transfer_assignments' if natural else 'signed_transfer_identities']+=1
for inp in fixtures:
 _,env=o.canonical_c2(inp);assert newpoly.evaluate(env)==0;cnt['transfer_zero_fixtures']+=1
# Real orthant boundary is deliberately not preserved: all unspecified entries0.
rational_env={n:Fraction(0) for n in system.parameters+system.witnesses}
rational_env.update(a=Fraction(1,4),p=Fraction(1,2),xlower_plus=Fraction(1,4),p_rem=Fraction(1,2))
def rational_eval(poly):
 return sum(Fraction(c)*math.prod(rational_env[n] for n in monomial) for monomial,c in poly.terms)
assert rational_eval(poly)==Fraction(1,16) and rational_eval(newpoly)==Fraction(-1,4)
R['real_orthant_transfer_boundary']={'nonzero_coordinates':{k:str(v) for k,v in rational_env.items() if v},'old_value':'1/16','new_value':'-1/4'}
R['order_checks']=dict(cnt)
R['orthant_preserving_order_transfer']={'raw_residual_indices_zero_based':orthant_indices,'squared_residuals':16,'raw_residuals':8,'finalizer_multiplications_saved':8,'degree':orthant_poly.degree,'expanded_monomials':len(orthant_poly.terms),'scope':'Same complete natural zero set; remains nonnegative on the full real nonnegative orthant.'}
R['order_transfer']={'scope':'Natural-zero equivalence only, identity coordinates; no universal bound claim. Finalizer delta10M under schedule retaining identical residual evaluations.','raw_residual_indices_zero_based':raw_indices,'squared_residuals':14,'raw_residuals':10,'degree':newpoly.degree,'expanded_monomials':len(newpoly.terms),'old_minus_new':'sum over ten indices of (residual^2-residual)','nonnegative_on_entire_real_orthant_not_claimed':True}
# Compare author's regenerated artifacts on isolated copies.
R['author_replays']={}
with tempfile.TemporaryDirectory(prefix='parallel-order-author-') as temp:
 for root,name in ((P,'Maximal_Parallel_Diophantine'),(O,'order_is_not_a_moment')):
  dest=Path(temp)/name;shutil.copytree(root,dest)
  proc=subprocess.run([sys.executable,str(dest/'code/verify.py')],timeout=300,capture_output=True,text=True)
  assert proc.returncode==0,proc.stderr
  files={}
  for path in (root/'data').iterdir():
   if path.suffix=='.json':
    assert path.read_bytes()==(dest/'data'/path.name).read_bytes()
    files[path.name]=hashlib.sha256(path.read_bytes()).hexdigest()
  R['author_replays'][name]={'command':'python code/verify.py','json_files_unchanged':files}
args.receipt.write_text(json.dumps(R,indent=2)+'\n')
print(json.dumps({k:v for k,v in R.items() if k!='provenance'},indent=2))
