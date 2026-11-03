#!/usr/bin/env python3
"""Generate a closed Lean instruction table from the pinned free-J JSON."""
import hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent
root=here.parents[2]
p=root/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json'
expected='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!=expected:raise RuntimeError('graph hash mismatch')
data=json.loads(raw)
variables=['J','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
ports=['beta','K0','MC','MF']
if data['witnesses']!=variables or data['fixed_numerals']!=ports or len(data['source'])!=95 or data['output']!='P12':raise RuntimeError('graph metadata mismatch')
seen={};out=[]
def arg(v):
 if isinstance(v,int):return f'.lit {v}'
 if v in variables:return f'.var {variables.index(v)}'
 if v in ports:return f'.port {ports.index(v)}'
 if v in seen:return f'.gate {seen[v]}'
 raise ValueError('unknown or forward operand '+repr(v))
for idx,(name,op,a,b) in enumerate(data['source']):
 if name in seen or name in variables or name in ports:raise ValueError('duplicate name')
 x,y=arg(a),arg(b)
 if op not in ('+','-','*'):raise ValueError('unknown operator')
 out.append(f'    ⟨.{ {"+":"add","-":"sub","*":"mul"}[op]}, {x}, {y}⟩')
 seen[name]=idx
if seen['P12']!=94:raise ValueError('unexpected output')
header='''import DiophantineConsistency.Ordinary12FreeJ

/-! A finite 95-row program independently transcribed from pinned retained
JSON. File-to-table correspondence is an external provenance boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
noncomputable section
namespace FreeJRetainedProgram
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ

inductive Ref where
  | var : Fin 12 → Ref
  | port : Fin 4 → Ref
  | lit : ℤ → Ref
  | gate : Nat → Ref

inductive Op where | add | sub | mul
structure Row where
  op : Op
  left : Ref
  right : Ref

def program : List Row := [
'''
footer='''
  ]

def lookup (p : Fin 4 → ℤ) (xs : Array (Expr (Fin 12))) : Ref → Expr (Fin 12)
  | .var j => .var j
  | .port j => .constant (p j)
  | .lit n => .constant n
  | .gate j => xs.getD j (.constant 0)

def execute (p : Fin 4 → ℤ) (xs : Array (Expr (Fin 12))) (row : Row) : Array (Expr (Fin 12)) :=
  let a := lookup p xs row.left
  let b := lookup p xs row.right
  let x := match row.op with
    | .add => a+b
    | .sub => a-b
    | .mul => a*b
  xs.push x

def retainedExpression (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  (program.foldl (execute p) #[]).getD 94 (.constant 0)

theorem row_count : program.length = 95 := rfl

/-- The internal instruction table yields the formal free-J literal, with
arbitrary integer ports; no filesystem or PDF equality is asserted. -/
theorem retained_eq_literal (p : Fin 4 → ℤ) : retainedExpression p = literal p := by
  rfl

#print axioms FreeJRetainedProgram.row_count
#print axioms FreeJRetainedProgram.retained_eq_literal
end FreeJRetainedProgram
'''
(here/'FreeJRetainedProgram.lean').write_text(header+',\n'.join(out)+footer)
print('95 rows; pinned JSON sha256 '+expected)
