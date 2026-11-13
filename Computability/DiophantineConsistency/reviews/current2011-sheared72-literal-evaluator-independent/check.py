#!/usr/bin/env python3
"""Independent AST-shaped row reader, update cut, and sparse ring audit."""
import ast,hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-sheared72-literal-evaluator-draft/README.md':'008752590ec4d116ee26f195d70acf4f3f16d994a8856a28c5dc6eba1cf8d1a6',
'research/current2011-sheared72-literal-evaluator-draft/Shear72Literal.lean.src':'5f06d64754d71f75b7fef0a9a046c1de9656c9f94e1f36f968c3b81a915a8739',
'research/current2011-sheared72-literal-evaluator-draft/check.py':'99624fa2e801a1a8166cfea7d2b1638e6572b17a18dc192ccd78a93cf249c2a0',
'research/current2011-sheared72-literal-evaluator-draft/pins.json':'a13d081bb3d12a808c3d8593af2d3c635ef61d1daf462d3a95409c6014423278',
'research/current2011-sheared72-literal-evaluator-draft/receipt.json':'96f3575afcab6317b574ba96e6144a4b0a1edaf6272cfded14f4f56e9fe2a5a9',
'research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean':'554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a',
'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
'Lean/DiophantineConsistency/Carrier65.lean':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154'}
def need(b,m):
 if not b:raise RuntimeError(m)
for path,h in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==h,'pin '+path)
s=(root/'research/current2011-sheared72-literal-evaluator-draft/Shear72Literal.lean.src').read_text();block=s.split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=',1)[1].split('\nsection Ring',1)[0]
c=json.loads((root/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes());p=json.loads((root/'research/current2011-ordinary71-60-candidate/polynomial.json').read_bytes())
lines=[x.strip() for x in block.splitlines() if x.strip()];need(lines[-1]=='polynomial','output')
expected_headers=[f'let {v} : Expr (Fin 14) := .var {i}' for i,v in enumerate(c['witnesses'])]+[f'let {n} : Expr (Fin 14) := .constant (p {i})' for i,n in enumerate(c['fixed_numerals'])]
need(lines[:18]==expected_headers and len(lines)==18+72+1,'headers/row count')
ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}
def operand(n):
 if isinstance(n,ast.Name):return n.id
 if isinstance(n,ast.Constant) and type(n.value)==int:return n.value
 raise RuntimeError('unsupported AST operand')
rows=[]
for line in lines[18:-1]:
 need(line.startswith('let ') and ' := ' in line,'row syntax');name,rhs=line[4:].split(' := ',1);tree=ast.parse(rhs,mode='eval').body
 need(isinstance(tree,ast.BinOp) and type(tree.op) in ops,'binary row')
 rows.append([name,ops[type(tree.op)],operand(tree.left),operand(tree.right)])
need(rows==c['source'],'all 72 literal rows')
need(c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals'] and c['coefficient_binding']==p['coefficient_binding'],'port/domain interface')
need(c['source'][:55]==p['source'][:55] and c['source'][61:]==p['source'][60:],'common parent graph')
need('Function.update v 12 ((Carrier65.core p v).V + v 12)' in s,'coordinate update')
core=(root/'Lean/DiophantineConsistency/Carrier65.lean').read_text();need('let y := v 12' in core,'parent y coordinate')
parent=(root/'research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean').read_text()
for token in ['def auxiliary','def value71','theorem eval_expression']:
 need(token in parent,'parent interface '+token)
for token in ['theorem eval_expression','theorem value72_eq_sheared71','theorem eval_eq_sheared71','OrdinarySphere7160Literal.eval_expression']:
 need(token in s,'proposed theorem '+token)
# Verify auxiliary identity as an exact polynomial over Z[A,V,y].
def add(a,b,k=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+k*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for x,u in a.items():
  for y,v in b.items():
   m=tuple(i+j for i,j in zip(x,y));z[m]=z.get(m,0)+u*v
 return {m:v for m,v in z.items() if v}
A={(1,0,0):1};V={(0,1,0):1};y={(0,0,1):1};z=add(V,y)
need(add(mul(A,add(mul(V,V),mul(z,z),-1)),mul(z,z))==add(mul(z,z),mul(mul(A,y),add(z,V)),-1),'ring identity')
print(json.dumps({'source_pins_verified':len(pins),'witness_indices':14,'fixed_port_indices':4,'ast_parsed_rows':len(rows),'parent_y_index':12,'common_graph_port_binding':True,'exact_auxiliary_Z_polynomial_identity':True,'scope':'source and algebra review; no Lean elaboration, positivity, or provider audit'},sort_keys=True,indent=2))
