#!/usr/bin/env python3
"""Fresh read-only manuscript/source consistency checks; no submitted code runs."""
from pathlib import Path
import hashlib,json,re,itertools,collections
ROOT=Path('/workspace/shared/sandpile-target-report52-release-20261004')
OUT=Path('/workspace/shared/report52-manuscript-audit-20261004')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=ROOT.joinpath('Research_Report52.tex').read_text()
d=json.loads(ROOT.joinpath('science/evidence/polynomial-dag.json').read_text())
a=json.loads(ROOT.joinpath('independent_audit/audit-receipt.json').read_text())
pins={
'science/evidence/polynomial-dag.json':'352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504',
'science/build_target_certificate.py':'6a9ced103676ce7ba0b052e00779177fb522101fc5479866273e3908d299c975',
'science/ARCHITECTURE.md':'dabbe1685bb050eca578c29472a00426c940df6002c383fe5c3a558797bf93c9',
'independent_audit/audit-manifest.json':'dd6a27229d204f993b36e3f74a794353fa925e34926fd60fa3974eb1c50a33ab',
'independent_audit/independent_check.py':'60ba30d2d32fd8005fd403973ae2dfdaac028eb721a2a0b12109ffa12295db7c',
'independent_audit/semantics_check.py':'ff2245ef181fa8cb97450fccd33bb9bd2850fc7d35241911c84693285a3751da',
'baseline_report50/MANIFEST.json':'a0458d81f2ec02b5c75d03c68d64da5a428bbf4304d69e4d94f82384fdb5958d',
'baseline_report50/independent_audit/AUDIT.md':'fd95a520aa0c12f86bc27fa8554c24a53c80854e4ae053681f838e0bcf8bdd5e',
'baseline_report50/science/sources/pell-source.lean':'993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a'}
for path,h in pins.items():
 assert sha(ROOT/path)==h,(path,'changed')
 assert h in s,(path,'pin absent from manuscript')
# Compare copies to independently frozen inputs without executing any submitted code.
for sub,original in [('science','/workspace/shared/sandpile-target-firing-20261004'),('independent_audit','/workspace/shared/sandpile-target-independent-audit-20261004')]:
 for p in Path(original).rglob('*'):
  if p.is_file(): assert sha(p)==sha(ROOT/sub/p.relative_to(original)),str(p)
# Source graph integrity and literal SOS assembly.
assert len(d['witnesses'])==len(set(d['witnesses']))==3308
assert len(d['equalities'])==1923 and len(d['ports'])==36
assert len(d['gates'])==14778 and d['body_gate_count']==9010
macros=collections.Counter(x['kind'] for x in d['macros'])
assert dict(macros)==dict(power=118,subset=30,**{'and':5,'spread':4})
counts=collections.Counter(x[0] for x in d['gates']); assert counts=={'+':5078,'-':3890,'*':5810}
refs={'input:InputPlus'}|{'witness:'+x for x in d['witnesses']}
deg={x:1 for x in refs}; vals={x:[0] for x in refs}
chosen={'witness:descriptor.'+z for z in 'pqrdef'}|{'witness:box.t'+z for z in 'xyz'}
for r in chosen: vals[r]=[0,1]
def get(r):
 if r.startswith('constant:'): return [int(r[9:])]
 return vals[r]
def dget(r): return 0 if r.startswith('constant:') else deg[r]
def trim(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
for i,(op,l,r) in enumerate(d['gates']):
 assert op in '+-*'
 for v in (l,r): assert v in refs or re.fullmatch(r'constant:-?\d+',v),v
 z='gate:'+str(i); refs.add(z)
 x,y=get(l),get(r)
 if op=='*':
  o=[0]*(len(x)+len(y)-1)
  for j,u in enumerate(x):
   for k,v in enumerate(y):o[j+k]+=u*v
  deg[z]=dget(l)+dget(r)
 else:
  o=[(x[j] if j<len(x) else 0)+(1 if op=='+' else -1)*(y[j] if j<len(y) else 0) for j in range(max(len(x),len(y)))]
  deg[z]=max(dget(l),dget(r))
 vals[z]=trim(o)
expected=[]
for j,(l,r,name) in enumerate(d['equalities']):
 assert all(v in refs or re.fullmatch(r'constant:-?\d+',v) for v in (l,r))
 k=9010+2*j
 assert d['gates'][k]==['-',l,r]
 assert d['gates'][k+1]==['*','gate:'+str(k),'gate:'+str(k)]
 expected.append('gate:'+str(k+1))
last=expected[0]
for j,r in enumerate(expected[1:]):
 i=9010+2*1923+j
 assert d['gates'][i]==['+',last,r]
 last='gate:'+str(i)
assert last==d['output']
assert deg[d['output']]==18
assert len(vals[d['output']])==19 and vals[d['output']][-1]==48
hi=[]
for j,(l,r,n) in enumerate(d['equalities']):
 o=vals['gate:'+str(9010+2*j)]
 if len(o)==10:hi.append((n,o[-1]))
assert sorted(hi)==sorted((f'patch.shift.eq{n}',-4) for n in (8,9,11))
# TeX cross-references, without compilation and without rewriting the manuscript.
labels=re.findall(r'\\label\{([^}]+)\}',s)
assert len(labels)==len(set(labels))
refnames=re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',s)
assert not set(refnames)-set(labels),set(refnames)-set(labels)
keys=set(re.findall(r'\\bibitem\{([^}]+)\}',s))
assert not set(re.findall(r'\\cite\{([^}]+)\}',s))-keys
# Exhaustive independent two-slot cumulative recurrence probes, K=1,2,3.
# These test the displayed mathematics, not the submitted checkers.
rc=valid=0
b=32; Q=b*b
sp=[(m&1)+b*((m>>1)&1) for m in range(4)]
for K in (1,2,3):
 for parts in itertools.product(sp,repeat=2*K+1):
  pre,new,V=parts[:K],parts[K:2*K],parts[-1]
  A=sum(x*Q**t for t,x in enumerate(pre)); E=sum(x*Q**t for t,x in enumerate(new))
  eq=Q*(A+E)==A+Q**K*V
  history=0; good=True
  for x,y in zip(pre,new):
   good=good and x==history and (history&y)==0
   history+=y
  good=good and V==history
  assert eq==good
  rc+=1;valid+=eq
# Every five-bit slack and available-height combination.
lc=0
for c in range(27):
 for bits in itertools.product((0,1),repeat=5):
  mask=not(bits[3] and bits[4]); L=sum(t*2**j for j,t in enumerate(bits))
  accept=mask and c==6+L
  assert accept==(6<=c<=26 and L==c-6)
  lc+=1
# Explicit original physical separator, using only direct chip bookkeeping.
height={(0,0,0):12,(1,0,0):4}
neighbors=lambda v:[tuple(v[j]+(sgn if j==axis else 0) for j in range(3)) for axis in range(3) for sgn in (-1,1)]
def fire(v):
 assert height.get(v,0)>=6
 height[v]-=6
 for w in neighbors(v):height[w]=height.get(w,0)+1
fire((0,0,0))
assert not any(n>=6 and v!=(0,0,0) for v,n in height.items())
fire((0,0,0));fire((1,0,0))
receipt={'status':'PASS','manuscript_sha256':sha(ROOT/'Research_Report52.tex'),'pins_verified':pins,'frozen_science_and_audit_copies_unchanged':True,'dag':{'witnesses':3308,'residuals':1923,'gates':14778,'macros':dict(macros),'syntactic_degree_upper_bound':18,'fresh_diagonal_degree':18,'fresh_diagonal_leading_coefficient':48,'diagonal_degree_nine_residuals':hi,'sos_assembly_exact':True},'tex':{'labels':len(labels),'all_references_resolve':True,'all_citations_resolve':True},'fresh_finite_checks':{'recurrence_candidates':rc,'valid_recurrences':valid,'legality_bitplane_cases':lc,'repeat_separator_pass':True},'no_submitted_or_upstream_code_executed':True}
(OUT/'text-check-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
