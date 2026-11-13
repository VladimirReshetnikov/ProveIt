#!/usr/bin/env python3
"""Read-only source/AST and interface checks; no elaboration or providers."""
import ast,hashlib,json,re,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];h=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def require(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((h/'pins.json').read_bytes())
for p,v in pins.items():require(sha((r/p).read_bytes())==v,'pin '+p)
def read(p):return (r/p).read_text()
g=json.loads(read('research/adaptive87-four-square-current88-30/graph.json'));old=json.loads(read('research/adaptive-first-root-factor87/candidate.json'))
s=read('research/adaptive87-four-square-current88-model-draft/AdaptiveFourSquare88Graph.lean.src');model=read('research/adaptive87-four-square-current88-model-draft/FourSquare88Model.lean.src');gen=read('research/adaptive87-four-square-current88-model-draft/FourUnitGeneric.lean.src')
inputs=g['witnesses'];ports=g['fixed_numerals']
for j,n in enumerate(inputs):require(f'let {n} : Expr (Fin 13) := .var {j}' in s,'var '+n)
for j,n in enumerate(ports):require(f'let {n} : Expr (Fin 13) := .constant (p {j})' in s,'port '+n)
require('⟨A0,A1,Fa,g72,q,Z,g41,U,a,c,Dstar,f,I,V,g78,output,parent⟩' in s,'graph fields')
require('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 13) := (graph p).output' in s,'output field')
# Hash-consed operation trees compare exact parent association without exponential expansion.
def leaf(x):return sha(('leaf:'+str(x)).encode())
def node(op,a,b):return sha((op+':'+a+':'+b).encode())
def do_rows(rows):
 env={n:leaf(n) for n in inputs+ports}
 for name,op,a,b in rows:env[name]=node(op,env[a] if isinstance(a,str) else leaf(a),env[b] if isinstance(b,str) else leaf(b))
 return env
p=do_rows(old['source']);c=do_rows(g['source'])
parsed=[]
for line in s.splitlines():
 m=re.fullmatch(r'\s*let ([A-Za-z][A-Za-z0-9_]*) := ([A-Za-z0-9_]+) ([+*\-]) ([A-Za-z0-9_]+)',line)
 if m:
  n,a,op,b=m.groups();parsed.append([n,op,int(a) if a.isdigit() else a,int(b) if b.isdigit() else b])
require(parsed==g['source'],'full graph rows')
match=re.search(r'let parent := ([^\n]+)',s);require(match is not None,'parent declaration')
ops={ast.Add:'+',ast.Sub:'-',ast.Mult:'*'}
def expr(t):
 if isinstance(t,ast.Name):return c[t.id]
 if isinstance(t,ast.Constant) and type(t.value)==int:return leaf(t.value)
 if isinstance(t,ast.BinOp) and type(t.op) in ops:return node(ops[type(t.op)],expr(t.left),expr(t.right))
 raise RuntimeError('unsupported parent expression')
require(expr(ast.parse(match.group(1),mode='eval').body)==p[old['output']],'exact parent AST')
require('import DiophantineConsistency.ModelArithmetic' in model,'explicit model import')
ma=read('Lean/DiophantineConsistency/ModelArithmetic.lean');md=read('Lean/DiophantineConsistency/ModelDifferenceRing.lean');facts=read('Lean/DiophantineConsistency/DiscreteOrderedRingFacts.lean')
for x in ['import DiophantineConsistency.ModelDifferenceRing','theorem model_discrete : Discrete (DiffRing V)','def mod4 : DiffRing V →+* ZMod 4']:require(x in ma,'model interface '+x)
require('theorem internalZero_iff {σ : Type*}' in md and 'theorem eq_one_or_neg_one_of_mul_eq_one (hd : Discrete R)' in facts,'difference/units interface')
for x in ['fs*(fa*(f0*f1))-1=0 ↔','(f0-1)^2+(f1-1)^2+(fa-1)^2+(fs-1)^2=0','first_bad _ _ _ hm','main_bad _ _ _ _ hm','aux_bad (φ a) (φ f) (φ V) (φ y)','strong_bad _ _ _ hm']:
 require(x in gen,'generic '+x)
for x in ['factor_exclusions (mod4 (V:=V))','product_iff_squares model_discrete (1+first) (1+main) aux (1+strong) h0 h1 ha hs','first^2+main^2+(aux-1)^2+strong^2','(1+strong)*(aux*((1+first)*(1+main)))-1','internalZero_positiveShift,internalZero_positiveShift','theorem bridge (hp : PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87)','IPRAExpressionNative.equivalence_of_bridge naturalExpression (bridge hp)']:
 require(x in model,'model '+x)
print(json.dumps({'scope':'source/AST and selected interfaces only; no Lean, tactic or provider checks','pins_sha256':sha((h/'pins.json').read_bytes()),'child_rows':len(parsed),'parent_ast_exact':True,'model_import_and_mod4_interface':True,'same_valuation_and_parent_bridge_markers':True},indent=2,sort_keys=True))
