#!/usr/bin/env python3
"""Independent nested witness/port polynomial reconstruction and port binding."""
import copy,gzip,hashlib,json,subprocess,sys
from collections import Counter
from pathlib import Path
if not __debug__:raise RuntimeError('independent review requires assertions enabled')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';TASK=BASE/'research/frontier13-low-degree-shear-obstruction';GRAPH=BASE/'research/adaptive-square-sums/candidate.json';PORTS=BASE/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';BINDING=BASE/'reviews/frontier13-pdf-historical-lean-binding-independent-audit/receipt.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
files=[Path(__file__),TASK/'check.py',TASK/'run.py',TASK/'receipt.json',TASK/'terminal-observation.json',GRAPH,PORTS,BINDING];before={str(p.resolve()):H(p) for p in files}
for f in files[1:]:
 rel=str(f.relative_to(ROOT));b=subprocess.check_output(['git','show','8ea2aafe22:'+rel],cwd=ROOT);assert hashlib.sha256(b).hexdigest()==H(f)
assert H(GRAPH)=='11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'
assert H(PORTS)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e'
assert H(BINDING)=='44d14b51deca8b68c033b28f6244ee857c187386269730bb144e8b11913890de'
# Nested representation: each witness monomial maps to a sparse polynomial in
# four port symbols. This separates witness degree from coefficient degree.
g=J(GRAPH);W=g['witnesses'];P=g['fixed_numerals'];assert len(W)==13 and len(set(W))==13 and P==['beta','K0','MC','MF']
wz=(0,)*13;pz=(0,)*4
def add(a,b,sgn=1):
 d={w:dict(c) for w,c in a.items()}
 for w,c in b.items():
  q=d.setdefault(w,{})
  for p,v in c.items():q[p]=q.get(p,0)+sgn*v
  d[w]={p:v for p,v in q.items() if v}
 return {w:c for w,c in d.items() if c}
def mul(a,b):
 out={}
 for x,c in a.items():
  for y,d in b.items():
   w=tuple(i+j for i,j in zip(x,y));q=out.setdefault(w,{})
   for p,v in c.items():
    for r,u in d.items():
     s=tuple(i+j for i,j in zip(p,r));q[s]=q.get(s,0)+v*u
 return {w:{p:v for p,v in q.items() if v} for w,q in out.items() if any(q.values())}
def constant(n):return {} if not n else {wz:{pz:n}}
def atom(n):
 if n in W:
  w=list(wz);w[W.index(n)]=1;return {tuple(w):{pz:1}}
 p=list(pz);p[P.index(n)]=1;return {wz:{tuple(p):1}}
def degree(a):return max((sum(w) for w in a),default=-1)
def evaluate(graph):
 vals={n:atom(n) for n in W+P}
 for name,op,a,b in graph['source']:
  if name=='firstSquare':break
  assert name not in vals and op in ('+','-','*')
  left=constant(a) if isinstance(a,int) else vals[a];right=constant(b) if isinstance(b,int) else vals[b]
  vals[name]=mul(left,right) if op=='*' else add(left,right,-1 if op=='-' else 1)
 return vals
def verify(graph):
 v=evaluate(graph);expected={'A0':15,'A1':13,'g72':10,'auxResidual':18};assert {n:degree(v[n]) for n in expected}==expected
 counts={}
 for n in ('A0','A1','g72'):
  support=[w for w in v[n] if sum(w)==expected[n]];assert support
  assert all(w[W.index('eta')]+w[W.index('zeta')]>0 for w in support);counts[n]=len(support)
 target=tuple({'J':8,'f':6,'X':2,'Y':2}.get(n,0) for n in W)
 assert v['auxResidual'][target]=={(8,0,0,0):1}
 return v,counts
v,counts=verify(g)
# Verify all output additions terminate in exactly the four squares, not a
# weighted sum or a different expression.
rows={x[0]:x for x in g['source']};assert len(rows)==len(g['source'])
def leaves(n):
 r=rows[n]
 if r[1]=='+':return leaves(r[2])+leaves(r[3])
 assert r[1]=='*' and r[2]==r[3];return [r[2]]
assert Counter(leaves(g['output']))==Counter(['A0','A1','g72','auxResidual'])
# Independently confirm the three producer mutations destroy this certificate.
for name,row in (('qm',['qm','*','J',0]),('A0',['A0','+','g38','g42']),('g82',['g82','+','Q','g81'])):
 bad=copy.deepcopy(g);i=next(i for i,x in enumerate(bad['source']) if x[0]==name);bad['source'][i]=row
 try:verify(bad)
 except (AssertionError,KeyError):pass
 else:raise AssertionError(('mutation accepted',name))
carrier=J(PORTS);binding=J(BINDING);assert binding['status']=='PASS_INDEPENDENT_FRONTIER13_PDF_BINDING_REVIEW'
meta=carrier['coefficient_binding']['ports']['beta'];packed=PORTS.parent/'coefficients'/meta['file'];files.append(packed);before[str(packed.resolve())]=H(packed)
raw=gzip.decompress(packed.read_bytes());assert H(packed)==meta['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==meta['raw_sha256']==binding['ports'][0]['integer_sha256'] and binding['ports'][0]['name']=='beta'
beta=int.from_bytes(raw,'big');assert beta==(1<<94517)-1 and beta>0
# Substitution eta=zeta=0 removes every top term from the first three
# residuals while retaining exactly the target coefficient beta^8 in N.
for n in ('A0','A1','g72'):
 vanishing={w:c for w,c in v[n].items() if not w[W.index('eta')] and not w[W.index('zeta')]}
 assert degree(vanishing)<degree(v[n])
# The arbitrary-multiplier and shifted-degree conclusions are proved in the
# accompanying review, not by testing finitely many multipliers.
p=subprocess.run([sys.executable,str(TASK/'check.py')],capture_output=True,text=True,timeout=120);assert p.returncode==0 and p.stdout.startswith('PASS_BOUNDED_SHEAR_DEGREE ')
assert json.loads(p.stdout.split(' ',1)[1])==J(TASK/'receipt.json')['normal']['result']
o=subprocess.run([sys.executable,'-O',str(TASK/'check.py')],capture_output=True,text=True,timeout=30);assert o.returncode!=0 and 'optimized Python is unsupported' in o.stderr
assert before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_INDEPENDENT_BOUNDED_SHEAR_REVIEW','inputs_sha256':before,'witness_degrees':{n:degree(v[n]) for n in ('A0','A1','g72','auxResidual')},'leading_witness_support_sizes':counts,'retained_witness_monomial':{'J':8,'f':6,'X':2,'Y':2},'exact_port_coefficient':{'beta^8':1},'actual_beta_bit_length':beta.bit_length(),'original_checker_exit':p.returncode,'original_optimized_exit':o.returncode,'mutation_controls':3,'scope':'Bounded polynomial residual shear only; no unrestricted degree lower bound, Lean theorem, or proof of PDF decoder transcription.'};path=HERE/'receipt.json'
if path.exists():raise ValueError('refusing receipt overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
