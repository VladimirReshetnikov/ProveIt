#!/usr/bin/env python3
"""Produce the literal Lean table from a pinned external JSON transcription."""
from pathlib import Path
from hashlib import sha256
import json,sys
here=Path(__file__).resolve().parent
source=here.parent/'indexed-tile-enumeration/TILES.json'
expected='f06d1b9858281f1adcbc431d3c0df9b07df1a231793629650b2d3c09eac56549'
raw=source.read_bytes()
if sha256(raw).hexdigest()!=expected: raise SystemExit('unexpected input hash')
rows=json.loads(raw)
if len(rows)!=943 or any(not isinstance(x,list) or len(x)!=4 or any(type(v) is not int or v<0 for v in x) for x in rows): raise SystemExit('invalid table')
header='''import DiophantineConsistency.CompactSymbolicKernelGeneric

/-! Direct-index BFS row transcription and its symbolic kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace DirectBFSSymbolicKernel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernel CompactSymbolicKernelGeneric
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators

def rows : List (Nat × Nat × Nat × Nat) := [
'''
body=''.join('  ('+', '.join(str(v) for v in row)+'),\n' for row in rows)
tail='''  ]

theorem rows_length : rows.length=943 := by decide

theorem row_widths : rows.all (fun t => decide (t.1<256 ∧ t.2.1<512 ∧ t.2.2.1<256 ∧ t.2.2.2<512))=true := by decide

def row (i : Fin 943) : Nat × Nat × Nat × Nat :=
  rows.get ⟨i.val, by simpa only [rows_length] using i.isLt⟩

theorem row_bounds (i : Fin 943) :
    (row i).1<256 ∧ (row i).2.1<512 ∧ (row i).2.2.1<256 ∧ (row i).2.2.2<512 := by
  have hm : row i ∈ rows := List.get_mem rows _
  exact of_decide_eq_true ((List.all_eq_true.mp row_widths) (row i) hm)

def paramKernel (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2201 +
  (∑ i : Fin 943, CompactCoefficientMass.selector (row i) *
     (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-position i)+r^(5495-position i))) +
  r^8807*r^42

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cast_paramKernel (r : ℕ) :
    ((paramKernel r:ℕ):V) =
      ((r:V)^30+(r:V)^62+(r:V)^1100+(r:V)^2201)
      + (∑ i : Fin 943,
          (CompactCoefficientMass.selector (row i):V)*
            ((r:V)^(4393-i.val)+(r:V)^(5495-i.val)))
      + (∑ i : Fin 41,
          ((2^(10+i.val):ℕ):V)*((r:V)^(4393-position i)+(r:V)^(5495-position i)))
      + (r:V)^8807*(r:V)^42 := by
  exact cast_kernel_generic r 30 62 1100 2201 4393 5495 8807 42
    (fun i : Fin 943 => i.val) (fun i => CompactCoefficientMass.selector (row i))
    (fun i : Fin 41 => position i) (fun i => 2^(10+i.val))

#print axioms DirectBFSSymbolicKernel.rows_length
#print axioms DirectBFSSymbolicKernel.row_widths
#print axioms DirectBFSSymbolicKernel.row_bounds
#print axioms DirectBFSSymbolicKernel.cast_paramKernel
end DirectBFSSymbolicKernel
'''
output=header+body+tail
out=here/'DirectBFSSymbolicKernel.lean'
if '--check' in sys.argv:
 if out.read_text()!=output: raise SystemExit('table transcription mismatch')
 print('exact transcription check passed')
elif out.exists(): raise SystemExit('refusing to overwrite')
else: out.write_text(output)
