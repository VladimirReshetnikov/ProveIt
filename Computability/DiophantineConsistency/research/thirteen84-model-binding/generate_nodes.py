#!/usr/bin/env python3
"""Generate transparent Lean node definitions from the pinned 84-row graph."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
GRAPH=BASE/'research/thirteen-first-norm-correction92/polynomial.json'
EXPECTED='a214fc19ea776e4e3880e13a7cd92260e76e71588c8c6b391669007a180ab3be'
raw=GRAPH.read_bytes()
if hashlib.sha256(raw).hexdigest()!=EXPECTED:raise ValueError('graph digest')
d=json.loads(raw);rows=d['source'];vars=d['witnesses'];ports=d['fixed_numerals']
if len(rows)!=84 or d['output']!='polynomial' or len(vars)!=13 or len(ports)!=4:raise ValueError('graph shape')
seen=set(vars+ports);names=set();lines=['import DiophantineConsistency.ModelDifferenceRing','','set_option autoImplicit false','set_option Elab.async false','set_option linter.unusedVariables false','set_option maxHeartbeats 4000000','noncomputable section','namespace Thirteen84Nodes','open DiophantineConsistency AdaptiveEquationSyntax2011','', 'section Generic','variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 3] [OfNat R 4] [OfNat R 16]']
def term(x):
 if isinstance(x,int):return str(x)
 if x in vars:return '(v '+str(vars.index(x))+')'
 if x in ports:return '(p '+str(ports.index(x))+')'
 if x in names:return '(node_'+x+' p v)'
 raise ValueError(('unknown operand',x))
for name,op,left,right in rows:
 if name in seen or op not in ('+','-','*'):raise ValueError(('invalid row',name,op))
 lines.append('def node_'+name+' (p : Fin 4 → R) (v : Fin 13 → R) : R := '+term(left)+' '+op+' '+term(right));names.add(name);seen.add(name)
lines+=['end Generic','','def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=','  node_polynomial (fun j => Expr.constant (p j)) Expr.var','','section Eval','variable {R : Type*} [CommRing R]']
for name,op,left,right in rows:
 lemmas=['node_'+name,{'+' : 'Expr.evalRing_add','-' : 'Expr.evalRing_sub','*' : 'Expr.evalRing_mul'}[op]]
 for x in (left,right):
  if isinstance(x,int):lemmas+=['Expr.evalRing_ofNat', 'Nat.cast_one' if x==1 else 'Nat.cast_ofNat']
  elif x in vars:lemmas+=['Expr.evalRing_var']
  elif x in ports:lemmas+=['Expr.evalRing_constant']
  else:lemmas+=['eval_'+x]
 lemmas=list(dict.fromkeys(lemmas))
 lines+=['','theorem eval_'+name+' (p : Fin 4 → ℤ) (v : Fin 13 → R) :','    (node_'+name+' (fun j => Expr.constant (p j)) Expr.var).evalRing v =','      node_'+name+' (fun j => (p j : R)) v := by','  simp only ['+', '.join(lemmas)+']']
lines+=['','theorem eval_literal (p : Fin 4 → ℤ) (v : Fin 13 → R) :','    (literal p).evalRing v = node_polynomial (fun j => (p j : R)) v := eval_polynomial p v','','end Eval','end Thirteen84Nodes','#print axioms Thirteen84Nodes.eval_literal','']
out=HERE/'Thirteen84Nodes.lean';out.write_text('\n'.join(lines));print('GENERATED_84_NODES',hashlib.sha256(out.read_bytes()).hexdigest())
