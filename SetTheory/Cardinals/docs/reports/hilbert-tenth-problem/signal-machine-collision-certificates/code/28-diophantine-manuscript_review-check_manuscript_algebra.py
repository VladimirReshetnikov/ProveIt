#!/usr/bin/env python3
"""Fresh manuscript-specific audit of inert JSON DAGs, written 2026-10-04.
No supplied program is imported or executed. Polynomial specifications below
are transcribed independently from Report58 equations O1--O14, P1--P15, D1--D2.
Monomials are sorted tuples of variable names, repeated according to exponent.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from math import gcd
import hashlib,json,re
ROOT=Path('/workspace/shared/five-signal-certificate58-release-20261004')
OUT=Path('/workspace/shared/report58-independent-manuscript-review-20261004')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
class P:
 def __init__(self,x=0):
  if isinstance(x,P):self.d=x.d.copy()
  elif isinstance(x,int):self.d={():x} if x else {}
  elif isinstance(x,str):self.d={(x,):1}
  else:self.d={m:c for m,c in x.items() if c}
 def __add__(self,o):
  d=self.d.copy()
  for m,c in P(o).d.items():d[m]=d.get(m,0)+c
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.d.items()})
 def __sub__(self,o):return self+-P(o)
 def __rsub__(self,o):return P(o)+-self
 def __mul__(self,o):
  d={}
  for m,c in self.d.items():
   for n,b in P(o).d.items():
    k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*b
  return P(d)
 __rmul__=__mul__
 def __pow__(self,k):
  assert isinstance(k,int) and k>=0
  r=P(1)
  for _ in range(k):r=r*self
  return r
 def __eq__(self,o):return self.d==P(o).d
 def degree(self):return max(map(len,self.d),default=-1)
 def record(self):return [[list(m),c] for m,c in sorted(self.d.items())]
 def digest(self):return hashlib.sha256(json.dumps(self.record(),separators=(',',':')).encode()).hexdigest()
 def evaluate(self,v):
  z=0
  for m,c in self.d.items():
   for x in m:c*=v[x]
   z+=c
  return z
W=lambda s:P('w:'+s)
N=lambda s:W(s+'.Plus')-1
S=lambda s:W(s+'.Positive')-W(s+'.Negative')
def specification(one,quartic):
 E={}
 g1,g2,g3=[W('gap.'+str(i)) if one else P('i:g'+str(i)) for i in (1,2,3)]
 if one:
  a,b,c=g1-1,g2-1,g3-1;j=N('decode.inner');z=P('i:code')
  E['decode.inner_cantor']=(2*j,(b+c)*(b+c+1)+2*c)
  E['decode.outer_cantor']=(2*(z-1),(a+j)*(a+j+1)+2*j)
 D=g1+g2+g3;A=3*g1-D;B=3*(g1+g2)-2*D;U=6*A-13*B;V=13*A+6*B
 delta=N('radius.delta');h=W('fraction.h');q=W('fraction.q');u=S('fraction.u');v=S('fraction.v')
 n=N('valuation.n');r=W('valuation.r');k=N('valuation.k');s=W('valuation.s');P5=W('power5.out');T=W('power_complex.out');b=4*P5+1
 C=S('complex.C');SS=S('complex.S');kap=S('complex.quotient')
 E['radius.nonnegative']=(4*D**2,205*(A**2+B**2)+delta)
 E['fraction.real']=(U,h*u);E['fraction.imag']=(V,h*v);E['fraction.denominator']=(2*D,h*q)
 E['fraction.primitive']=(S('bezout.1')*u+S('bezout.2')*v+S('bezout.3')*q,P(1))
 E['valuation.decompose']=(q,P5*r);E['valuation.remainder']=(r,5*k+s)
 E['valuation.nonzero_remainder']=((s-1)*(s-2)*(s-3)*(s-4),P(0)) if quartic else (s+W('valuation.t'),P(5))
 E['complex.C_lower']=(C+P5,N('complex.bound.1'));E['complex.C_upper']=(P5-C,N('complex.bound.2'))
 E['complex.S_lower']=(SS+P5,N('complex.bound.3'));E['complex.S_upper']=(P5-SS,N('complex.bound.4'))
 E['complex.remainder']=(T-C-b*SS,kap*(b*b+1))
 E['acceptance.strict']=(delta**2+(r-1)**2+(u-C)**2+(v+SS)**2,W('acceptance.positive'))
 for prefix,base in [('power5',P(5)),('power_complex',3+4*b)]:
  w=lambda x:W(prefix+'.'+x)
  nat=lambda x:N(prefix+'.'+x)
  out,a,beta=w('out'),w('aMinus1')+1,w('betaMinus1')+1
  ww,M,g,x,y,uu,vv,ss,t,qb,qv,J=[w(z) for z in ('w','M','g','x','y','u','v','s','t','qb','qv','strict')]
  k0=n+1;m0=base*out
  pairs=[(x*x,1+(a*a-1)*y*y),(uu*uu,1+(a*a-1)*vv*vv),(ss*ss,1+(beta*beta-1)*t*t),
   (beta,1+4*y*qb),(beta+uu*nat('alpha1'),a+uu*nat('alpha2')),(vv,y*y*qv),
   (ss+uu*nat('sigma1'),x+uu*nat('sigma2')),(t+4*y*nat('tau1'),k0+4*y*nat('tau2')),
   (y,k0+nat('dyk')),(ww,base+nat('dwb')),(ww,k0+nat('dwk')),(M,m0+J),
   (a*a,1+((ww+1)**2-1)*(ww*g)**2),(2*a*base,M+(base*base+1)),
   (x+M*nat('rho1'),y*(a-base)+m0+M*nat('rho2'))]
  for i,pair in enumerate(pairs,1):E[prefix+'.eq'+str(i)]=pair
 return E
expected={
 'three-input-linear':(3,81,44,136,110,98,344,772),
 'one-input-linear':(1,85,46,144,118,105,367,802),
 'three-input-quartic':(3,80,44,139,109,102,350,775),
 'one-input-quartic':(1,84,46,147,117,109,373,805)}
receipts={};polynomials={};dags={}
for variant,counts in expected.items():
 f=ROOT/'science/evidence'/(variant+'.dag.json');d=json.loads(f.read_text());dags[variant]=d
 one=variant.startswith('one');quartic=variant.endswith('quartic');E=specification(one,quartic)
 assert len(d['inputs'])==len(set(d['inputs'])) and len(d['witnesses'])==len(set(d['witnesses']))
 leaves={'i:'+s for s in d['inputs']}|{'w:'+s for s in d['witnesses']}
 values={x:P(x) for x in leaves};refs={}
 def get(ref):
  if ref.startswith('c:'):
   assert re.fullmatch(r'c:-?(0|[1-9][0-9]*)',ref);return P(int(ref[2:]))
  assert ref in values,ref
  return values[ref]
 for j,gate in enumerate(d['gates']):
  assert len(gate)==3;op,a,b=gate;assert op in ('+','-','*')
  x,y=get(a),get(b);values['g:'+str(j)]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  refs['g:'+str(j)]=(a,b)
 eqs=d['equations'];assert set(E)=={s[0] for s in eqs} and len(eqs)==len(E)
 residuals=[];details=[]
 for label,a,b in eqs:
  left,right=E[label]
  assert get(a)==left,(variant,label,'left');assert get(b)==right,(variant,label,'right')
  r=left-right;residuals.append(r);details.append({'label':label,'degree':r.degree(),'terms':len(r.d),'sha256':r.digest()})
 total=sum((r*r for r in residuals),P(0));assert get(d['output'])==total
 # Verify each tail node, without relying on a polynomial-only comparison.
 start=d['body_gate_count'];tail=[];squares=[]
 for label,a,b in eqs:
  ri='g:'+str(start+len(tail));tail.append(['-',a,b]);squares.append('g:'+str(start+len(tail)));tail.append(['*',ri,ri])
 running=squares[0]
 for square in squares[1:]:
  idx='g:'+str(start+len(tail));tail.append(['+',running,square]);running=idx
 assert d['gates'][start:]==tail and d['output']==running
 ops=Counter(g[0] for g in d['gates']);actual=(len(d['inputs']),len(d['witnesses']),len(eqs),ops['*'],ops['+'],ops['-'],len(d['gates']),len(total.d))
 assert actual==counts,(variant,actual,counts)
 top={m:c for m,c in total.d.items() if len(m)==12}
 wanted={tuple(sorted(['w:'+p+'.w']*8+['w:'+p+'.g']*4)):1 for p in ('power5','power_complex')}
 assert total.degree()==12 and top==wanted
 assert {x for m in total.d for x in m}==leaves
 visited=set()
 def visit(ref):
  if ref in visited or ref.startswith('c:'):return
  visited.add(ref)
  if ref in refs:
   for r in refs[ref]:visit(r)
 visit(d['output']);assert visited==leaves|set(refs)
 ledgers=[]
 for reg in d['regions']:
  l,rng=reg['gate_range'];ec0,ec1=reg['equation_range'];w0,w1=reg['witness_range'];op=Counter(g[0] for g in d['gates'][l:rng])
  ledgers.append({'region':reg['name'],'gates':rng-l,'witnesses':w1-w0,'equations':ec1-ec0,'operations':dict(sorted(op.items()))})
 receipts[variant]={'sha256':sha(f),'counts':actual,'degree':12,'top_form':P(top).record(),'expanded_polynomial_sha256':total.digest(),'all_sides_match':True,'literal_tail_match':True,'graph_and_algebraic_liveness':True,'residuals':details,'region_counts':ledgers}
 polynomials[variant]=total
# Stored witnesses are data, not an executed checker. Re-evaluate every raw gate exactly.
fixtures=json.loads((ROOT/'independent_audit/full-positive-witnesses.json').read_text());full=[]
for f in fixtures:
 variant=f.get('variant') or f.get('source')
 if variant and variant.endswith('.dag.json'):variant=variant[:-9]
 if variant not in dags:
  candidates=[v for v,d in dags.items() if set(d['inputs'])==set(f['inputs']) and set(d['witnesses'])==set(f['positive_witnesses'])]
  assert len(candidates)==1;variant=candidates[0]
 d=dags[variant];values={'i:'+k:v for k,v in f['inputs'].items()}|{'w:'+k:v for k,v in f['positive_witnesses'].items()}
 assert all(type(v)==int and v>0 for v in values.values())
 def value(ref):return int(ref[2:]) if ref.startswith('c:') else values[ref]
 for j,(op,a,b) in enumerate(d['gates']):
  x,y=value(a),value(b);values['g:'+str(j)]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 assert values[d['output']]==0 and all(value(a)==value(b) for _,a,b in d['equations'])
 assert polynomials[variant].evaluate(values)==0
 full.append({'variant':variant,'gaps':f['gaps'],'output':0,'witnesses':len(d['witnesses'])})
assert len(full)==12
# Independently reproduce the printed geometric/orientation fixtures.
geo=[]
for gaps in [(1,1,1),(217,167,231),(233,171,211),(193,243,179),(231,191,193),(1,1,10)]:
 g1,g2,g3=gaps;D=g1+g2+g3;A=3*g1-D;B=3*(g1+g2)-2*D;U=6*A-13*B;V=13*A+6*B;delta=4*D*D-205*(A*A+B*B)
 assert U*U+V*V==205*(A*A+B*B)
 assert Fraction(4,1845)-Fraction(A*A+B*B,9*D*D)==Fraction(delta,1845*D*D)
 h=gcd(gcd(U,V),2*D);u,v,q=U//h,V//h,2*D//h;n=0;r=q
 while r%5==0:n+=1;r//=5
 C,SS=1,0
 for _ in range(n):C,SS=3*C-4*SS,4*C+3*SS
 J=delta*delta+(r-1)**2+(u-C)**2+(v+SS)**2
 geo.append({'gaps':gaps,'delta':delta,'primitive':[u,v,q],'n':n,'J':J})
assert geo[1]['J']==0 and geo[2]['J']==64 and geo[-1]['delta']==-82449
# Bind displayed Appendix B pins and every supplied provenance pin to actual bytes.
source=(ROOT/'Report58.tex').read_text();pins=re.findall(r'\\file\{([^}]+)\} & \\sha\{([0-9a-f]{64})\}',source)
assert len(pins)==16
for path,digest in pins:assert sha(ROOT/path)==digest,path
sourcepins=json.loads((ROOT/'science/sources/SOURCE_PINS.json').read_text())
for p in sourcepins:
 f=ROOT/'science/sources'/p['file'];assert f.stat().st_size==p['bytes'] and sha(f)==p['sha256']
# Bind independently rerendered pages to the author render, without trusting its receipt.
render=Path('/workspace/shared/report58-final-review-render-20261004')
page_matches=[]
for p in sorted((OUT/'pages').glob('page-*.png')):
 assert p.read_bytes()==(render/'pages'/p.name).read_bytes()
 page_matches.append({'page':int(p.stem.split('-')[1]),'sha256':sha(p),'bytes':p.stat().st_size})
assert len(page_matches)==19
assert (OUT/'Report58-independent.txt').read_bytes()==(render/'Report58.txt').read_bytes()
receipt={'status':'PASS','manuscript_sha256':sha(ROOT/'Report58.tex'),'pdf_sha256':sha(ROOT/'Report58.pdf'),
 'method':'Fresh independent standard-library sparse integer algebra; no author or prior checker executed; local source dependencies read inertly.',
 'polynomial_hash_convention':'SHA256 of compact JSON sorted monomial tuples with repeated variable names, paired with integer coefficients.',
 'dags':receipts,'full_positive_witness_evaluations':full,'printed_fixture_checks':geo,'appendix_pin_checks':len(pins),'source_pin_checks':len(sourcepins),'independent_render_matches':page_matches}
(OUT/'ALGEBRA_AND_BINDING_RECEIPT.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','variants':4,'residual_sides_matched':2*sum(len(d['equations']) for d in dags.values()),'full_positive_zero_evaluations':12,'render_pages_matched':19,'degree':12},sort_keys=True))
