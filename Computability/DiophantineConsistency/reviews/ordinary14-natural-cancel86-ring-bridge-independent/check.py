#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-natural-cancel86-ring-bridge-draft';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'fd3487f7b466f308e4cef1dd5dad800e26df4ba1470f42a574c91029f33ecf6e',A/'RingNatural86To74.lean':'f7418af67e32119d47179e8bb92bfade6e24f305800f7abeb0d8f900bcfe47d4',A/'Natural86Model.lean':'66abbf4981f27d9e59f6c46537925035f6f7ecfb83adcb9e87e3d3345df4082d',A/'check_source.py':'c94a254de2a2e2280898a5b2d2e8478381a07da56046876b001262c93e049296',A/'observation.json':'513b52857186ade2f37ef1f5dfc701f65ba1b65574ee47900a6b71407f2380da',D/'research/ordinary14-root74-natural-cancel86/candidate.json':'0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170',D/'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093'}
tail=b"\nIndependent source review: [natural-86 ring/model bridge](../../reviews/ordinary14-natural-cancel86-ring-bridge-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='5b6493ddbc052e2a329c5a5cd4312d4635ba0cee5cb1222b09d9fa25d90139eb'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
s=(A/'RingNatural86To74.lean').read_text();m=(A/'Natural86Model.lean').read_text()
for token in ('theorem qF_cut (b f : R) : (1+b)-(f+1)=b-f','theorem guard_cut (g b f h : R) : g+(b-f)-b*(h+1)=g-f-b*h','theorem restricted_eval','theorem guard_eval','theorem output_eval','theorem positiveShift_eval','induction e <;> simp_all [positiveShift,Expr.subst,Expr.evalRing,shift]','theorem output_eq_positiveShift'):
 assert token in s,token
for token in ('InternalZero (P86NaturalCancel.graph p).output v ↔','InternalZero (positiveShift (P74PositiveGuard.graph p).output) v','ModelDifferenceRing.internalZero_iff','RingNatural86To74Draft.output_eq_positiveShift'):
 assert token in m,token
rep=(D/'Lean/DiophantineConsistency/Representation.lean').read_text();ev=(D/'Lean/DiophantineConsistency/WeightedExpressionDegree.lean').read_text();adaptive=(D/'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean').read_text();model=(D/'Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text()
for constructor in ('.constant','.var','.add','.sub','.mul'):
 assert '| '+constructor in rep and '| '+constructor in ev
assert 'e.subst (fun i => Expr.var i + Expr.constant 1)' in adaptive
assert 'AdaptiveEquationSyntax2011.InternalZero e v ↔ e.evalRing (fun i => ι (v i)) = 0' in model
# Independent exact local identities over Z[b,f,h,g], represented sparsely.
def add(a,b,sgn=1):
 out=a.copy()
 for k,v in b.items():out[k]=out.get(k,0)+sgn*v
 return {k:v for k,v in out.items() if v}
def mul(a,b):
 out={}
 for k,x in a.items():
  for l,y in b.items():
   z=tuple(i+j for i,j in zip(k,l));out[z]=out.get(z,0)+x*y
 return {k:v for k,v in out.items() if v}
def var(i):return {tuple(int(i==j) for j in range(4)):1}
b,f,h,g=(var(i) for i in range(4));one={(0,)*4:1}
assert add(add(one,b),add(f,one),-1)==add(b,f,-1)
assert add(add(g,add(b,f,-1)),mul(b,add(h,one)),-1)==add(add(g,f,-1),mul(b,h),-1)
# Exercise generic five-constructor substitution/evaluation induction in
# characteristic 4 and 12 as a finite control, not as a proof of elaboration.
def sub(e):
 tag=e[0]
 if tag=='c':return e
 if tag=='v':return ('a',e,('c',1))
 return (tag,sub(e[1]),sub(e[2]))
def val(e,v,n):
 tag=e[0]
 if tag=='c':return e[1]%n
 if tag=='v':return v[e[1]]%n
 a=val(e[1],v,n);b=val(e[2],v,n)
 return {'a':lambda:a+b,'s':lambda:a-b,'m':lambda:a*b}[tag]()%n
rng=random.Random(8674)
def expr(depth):
 if depth==0:return ('c',rng.randrange(-8,9)) if rng.randrange(2) else ('v',rng.randrange(3))
 return (rng.choice('asm'),expr(depth-1),expr(depth-1))
for mod in (4,12,17):
 for _ in range(150):
  e=expr(4);v=[rng.randrange(-8,9) for _ in range(3)];assert val(sub(e),v,mod)==val(e,[x+1 for x in v],mod)
# Prior independent exact-DAG graph and literal source review are replayed.
for directory in ('ordinary14-root74-natural-cancel86-independent','ordinary14-natural-cancel86-lean-independent'):
 p=D/'reviews'/directory;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),directory
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interfaces, exact local identities and finite induction controls; no Lean or file binding','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'exact_cut_identities':2,'expression_controls':450,'prior_reviews_replayed':2,'author_receipt_replayed':True},sort_keys=True,indent=2))
