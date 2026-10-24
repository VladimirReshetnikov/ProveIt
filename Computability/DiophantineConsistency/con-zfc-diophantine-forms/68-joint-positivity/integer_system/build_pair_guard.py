"""Own code. Reads inert JSON, never executes upstream scripts."""
import ast, hashlib, json, math
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT/'inherited/octic30.json'
raw=SOURCE.read_bytes(); src=json.loads(raw)
PORTABLE_BINDING={
 'manifest':'../integer_system_audit/BINDING.json',
 'compiler_manifest':'../integer_system_audit/coefficients/COEFFICIENT_BINDING.json',
 'transfer_proof':'../integer_system_audit/coefficients/COEFFICIENT_PROOF.md',
 'mask_convention':'MF is the already shifted MF_source',
 'ports':{'beta':'../integer_system_audit/coefficients/beta.bin','K0':'../integer_system_audit/coefficients/K.bin','MC':'../integer_system_audit/coefficients/MC.bin','MF':'../integer_system_audit/coefficients/MF_source.bin'},
 'encoding':'minimal unsigned little-endian'
}
syms={n:s.Symbol(n) for n in src['variables']+src['fixed_numerals']+['pair_root','pair_pos1','pair_pos2','pair_pos3']}
def parse(text):
 def go(n):
  if isinstance(n,ast.Expression): return go(n.body)
  if isinstance(n,ast.Name) and n.id in syms:return syms[n.id]
  if isinstance(n,ast.Constant) and type(n.value)==int:return s.Integer(n.value)
  if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand)
  if isinstance(n,ast.BinOp):
   a,b=go(n.left),go(n.right)
   if isinstance(n.op,ast.Add):return a+b
   if isinstance(n.op,ast.Sub):return a-b
   if isinstance(n.op,ast.Mult):return a*b
   if isinstance(n.op,ast.Pow) and b.is_Integer and 0<=b<=12:return a**b
  raise ValueError(ast.dump(n))
 return go(ast.parse(text,mode='eval'))
def check(b,msg):
 if not b: raise RuntimeError(msg)
x=parse('F*alpha');y=parse('F*(beta*J+1-F-alpha)')
check(s.expand(parse(src['residuals'][12])-(x-parse('1+FA_pos1**2+FA_pos2**2+FA_pos3*(FA_pos3+1)')))==0,'first source guard')
check(s.expand(parse(src['residuals'][13])-(y-parse('1+FC_pos1**2+FC_pos2**2+FC_pos3*(FC_pos3+1)')))==0,'second source guard')
g=x*y-(syms['pair_root']**2-x-y+1)**2
new=g-parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
vars=[n for n in src['variables'] if not n.startswith(('FA_pos','FC_pos'))]+['pair_root','pair_pos1','pair_pos2','pair_pos3']
rows=src['residuals'][:12]+[str(s.expand(new))]+src['residuals'][14:]
polys=[s.Poly(parse(t),*[syms[n] for n in vars]) for t in rows]
check(len(vars)==28 and len(rows)==14,'dimension')
check(max(p.total_degree() for p in polys)==4,'degree')
check(set().union(*(p.as_expr().free_symbols for p in polys))-set(syms[n] for n in src['fixed_numerals'])==set(syms[n] for n in vars),'live')
# No new guard contains a or f, so prior a^4 f^4 witness remains exact.
qpoly=s.Poly(sum(p.as_expr()**2 for p in polys),*[syms[n] for n in vars])
check(qpoly.coeff_monomial(syms['a']**4*syms['f']**4)==1,'a4 f4 coefficient')
check(qpoly.total_degree()==8,'exact degree')
cases=0
for a in range(1,301):
 for b in range(1,301):
  n=a+b-1;m=math.isqrt(n);t=m if n-m*m<=m else m+1
  check(a*b-(t*t-n)**2>0,'positive construction');cases+=1
for a in range(-30,31):
 for b in range(-30,31):
  for t in range(-20,21):
   if a*b-(t*t-a-b+1)**2>0:check(a>0 and b>0,'soundness diagnostic')
packet={k:src[k] for k in ['domain','fixed_numerals','coefficient_binding']}
packet['coefficient_binding']=PORTABLE_BINDING
packet.update(name='octic28_nearest_square_pair_guard',source_sha256=hashlib.sha256(raw).hexdigest(),variables=vars,variable_count=len(vars),residuals=rows,equation_count=len(rows),residual_degrees=[p.total_degree() for p in polys],single_polynomial='sum of squares of all residuals',exact_degree=8,exact_degree_certificate={'monomial':{'a':4,'f':4},'coefficient':1},proof='PAIR_GUARD_PROOF.md')
(ROOT/'octic28.json').write_text(json.dumps(packet,indent=2)+'\n')
result={'source_sha256':packet['source_sha256'],'variables':len(vars),'equations':len(rows),'degree':8,'monomials':len(qpoly.terms()),'positive_pairs_checked':cases,'bounded_signed_triples_checked':61*61*41,'status':'PASS. Finite algebra and diagnostics only; universal equivalence proved in PAIR_GUARD_PROOF.md.'}
(ROOT/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
# A higher-degree companion merges the remaining eta*zeta guard as well.
syms['second_root']=s.Symbol('second_root')
z=parse('eta*(1-V+j*c+h*E-eta)')
check(s.expand(parse(src['residuals'][14])-(z-parse('1+EZ_pos1**2+EZ_pos2**2+EZ_pos3*(EZ_pos3+1)')))==0,'third source guard')
nested=g*z-(syms['second_root']**2-g-z+1)**2-parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
vars26=[n for n in src['variables'] if not n.startswith(('FA_pos','FC_pos','EZ_pos'))]+['pair_root','second_root','pair_pos1','pair_pos2','pair_pos3']
rows26=src['residuals'][:12]+[str(s.expand(nested))]
polys26=[s.Poly(parse(t),*[syms[n] for n in vars26]) for t in rows26]
check(len(vars26)==26 and len(rows26)==13,'nested dimension')
check(max(p.total_degree() for p in polys26)==8,'nested residual degree')
check(set().union(*(p.as_expr().free_symbols for p in polys26))-set(syms[n] for n in src['fixed_numerals'])==set(syms[n] for n in vars26),'nested live')
# The only residual containing pair_root is nested; coefficient pair_root^8=-1.
check(polys26[-1].coeff_monomial(syms['pair_root']**8)==-1,'nested leading coefficient')
check(all(p.degree(syms['pair_root'])==0 for p in polys26[:-1]),'private root')
packet26={k:src[k] for k in ['domain','fixed_numerals','coefficient_binding']}
packet26['coefficient_binding']=PORTABLE_BINDING
packet26.update(name='degree16_26_nearest_square_triple_guard',source_sha256=hashlib.sha256(raw).hexdigest(),variables=vars26,variable_count=26,residuals=rows26,equation_count=13,residual_degrees=[p.total_degree() for p in polys26],single_polynomial='sum of squares of all residuals',exact_degree=16,exact_degree_certificate={'monomial':{'pair_root':16},'coefficient':1},proof='PAIR_GUARD_PROOF.md, Section 5')
(ROOT/'degree16_26.json').write_text(json.dumps(packet26,indent=2)+'\n')
result['nested_companion']={'variables':26,'equations':13,'degree':16,'degree_witness':'[pair_root^16]=1','new_residual_monomials':len(polys26[-1].terms())}
(ROOT/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result['nested_companion'],indent=2))
