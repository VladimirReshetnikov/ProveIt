#!/usr/bin/env python3
"""Exact 42-integer quartic construction; upstream JSON is data, never executed."""
import ast,gzip,hashlib,itertools,json
from pathlib import Path
R=Path(__file__).resolve().parent

def require(v,m):
 if not v: raise ValueError(m)

def build():
 pins=json.loads((R/'SOURCE_PINS.json').read_text())
 for name,h in pins['files'].items():require(hashlib.sha256((R/name).read_bytes()).hexdigest()==h,'source hash '+name)
 parent=json.loads((R/'upstream/q45/quartic45.json').read_text())
 removed={f'{v}_pos{i}' for v in ['eta','zeta'] for i in [1,2,3]}
 added=['pair_pos1','pair_pos2','pair_pos3']
 variables=[x for x in parent['variables'] if x not in removed]+added
 rows=[x for x in parent['residuals'] if not any(t in x for t in removed)]
 require(rows.count('-u**2 + w')==1,'exact original square-scale row')
 rows=[x.replace('-u**2 + w','-4*u**2 + w') for x in rows]
 rows+=['eta*zeta-pair_pos1**2-pair_pos2**2-pair_pos3*(pair_pos3+1)-1']
 fixed=parent['fixed_numerals'];names=variables+fixed;n=len(names);zero=(0,)*n
 def con(k):return {zero:k} if k else {}
 def add(a,b):
  d=dict(a)
  for m,c in b.items():d[m]=d.get(m,0)+c
  return {m:c for m,c in d.items() if c}
 def mul(a,b):
  d={}
  for u,c in a.items():
   for v,e in b.items():
    m=tuple(x+y for x,y in zip(u,v));d[m]=d.get(m,0)+c*e
  return {m:c for m,c in d.items() if c}
 def parse(t):
  if isinstance(t,ast.Expression):return parse(t.body)
  if isinstance(t,ast.Constant) and type(t.value)==int:return con(t.value)
  if isinstance(t,ast.Name):
   require(t.id in names,'unknown symbol '+t.id);e=[0]*n;e[names.index(t.id)]=1;return {tuple(e):1}
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return mul(con(-1),parse(t.operand))
  if isinstance(t,ast.BinOp):
   a=parse(t.left)
   if isinstance(t.op,ast.Pow):
    require(isinstance(t.right,ast.Constant) and type(t.right.value)==int and 0<=t.right.value<=4,'literal power');b=con(1)
    for _ in range(t.right.value):b=mul(b,a)
    return b
   b=parse(t.right)
   if isinstance(t.op,ast.Add):return add(a,b)
   if isinstance(t.op,ast.Sub):return add(a,mul(con(-1),b))
   if isinstance(t.op,ast.Mult):return mul(a,b)
  raise ValueError('invalid syntax')
 polys=[parse(ast.parse(s,mode='eval')) for s in rows]
 deg=lambda p:max(sum(m[:len(variables)]) for m in p)
 require(len(variables)==len(set(variables))==42,'42 variables');require(len(rows)==27,'27 residuals')
 require(all(deg(p)==2 for p in polys),'quadratic residuals')
 require(all(any(any(m[i] for m in p) for p in polys) for i in range(42)),'all variables live')
 Q={}
 for p in polys:Q=add(Q,mul(p,p))
 require(deg(Q)==4,'quartic');tau4=[0]*n;tau4[names.index('tau')]=4;require(Q.get(tuple(tau4))==1,'tau4 coefficient')
 binding=parent['coefficient_binding'].copy()
 for key in ['manifest','compiler_manifest','transfer_proof']:binding[key]='upstream/q45/'+binding[key]
 payload=R/'upstream/q45/upstream/34-integer14/coefficients/payloads';b=json.loads((payload/'COEFFICIENT_BINDING.json').read_text());ports={}
 for name in ['beta','K','MC','MF_source']:
  raw=(payload/(name+'.bin')).read_bytes();require(gzip.decompress((payload/(name+'.bin.gz')).read_bytes())==raw,'gzip '+name)
  require(hashlib.sha256(raw).hexdigest()==b['payloads'][name]['sha256'],'coefficient '+name);ports[name]=hashlib.sha256(raw).hexdigest()
 require(int.from_bytes((payload/'beta.bin').read_bytes(),'little')==(1<<1064921)-1,'whole tuple radix')
 packet={'name':'quartic42_oriented_common_sign','domain':'unrestricted integers','variables':variables,'variable_count':42,'equation_count':27,'fixed_numerals':fixed,'coefficient_binding':binding,'residuals':rows,'residual_degrees':[2]*27,'single_polynomial':'sum of squares of the 27 residuals','exact_degree':4,'exact_degree_certificate':'coefficient of tau^4 is 1, including after specialization to the fixed tuple','parent_sha256':hashlib.sha256((R/'upstream/q45/quartic45.json').read_bytes()).hexdigest(),'proof':'PROOF.md','status':'Ordinary mathematical proof with explicitly inherited compiler and Pell theorems; not a new kernel certificate.'}
 (R/'quartic42.json').write_text(json.dumps(packet,indent=2)+'\n')
 expanded={'variables':names,'terms':[{'coefficient':c,'exponents':list(m)} for m,c in sorted(Q.items())]}
 (R/'quartic42_expanded.json').write_text(json.dumps(expanded,separators=(',',':'))+'\n')
 count=0
 for q,X,Z in itertools.product(range(4,13),range(16,60),range(64,80)):
  if X<4*q or Z<q**3:continue
  E=X*Z
  for rr in [q*(q*q-1)+1,q**4-3]:
   if not 0<rr<q**4-2:continue
   require(E>3*rr+1,'scale gap');require((E-rr-1)>2*rr,'negative-index gap');count+=1
 receipt={'status':'PASS','variables':42,'quadratic_residuals':27,'quartic_terms':len(Q),'exact_degree':4,'uniform_tau4_coefficient':1,'pinned_inputs':len(pins['files']),'coefficient_raw_hashes':ports,'finite_scale_cases':count,'scope':'Exact finite polynomial/source/payload checks; sign orientation and cofinal completeness are universal arguments in PROOF.md.'}
 (R/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':build()
