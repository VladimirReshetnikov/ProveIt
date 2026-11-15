import Mathlib

/-!
# Executable finite kernel: formalization scaffold

STATUS: source outline, not compiled in the delivery environment. No claim that
this file is a completed proof of finite pigeonhole or of iPRA derivability.
There are no `sorry` declarations and no added axioms. The mathematical
obligations still to be implemented are listed explicitly at the end.

All algorithms below have finite loop bounds supplied by their input. The
List/Fin presentation is convenient for Lean; it must still be compiled into
natural-number codes and explicit `ConciseIPRA.PR` symbols for the object proof.
-/

namespace MinkowskiIPRA

abbrev IVec (n : Nat) := Fin n → Int

/-- A point of the mesh is indexed by its integer cell coordinates. -/
structure MeshInput where
  dimension : Nat
  modulus : Nat
  cells : List (IVec dimension)

/-- Euclidean integer residues. Positivity of the modulus is a validity check. -/
def residue {n : Nat} (m : Nat) (a : IVec n) : IVec n :=
  fun k => a k % (m : Int)

/-- All pairs i < j, in increasing j and then increasing i. -/
def candidatePairs (length : Nat) : List (Nat × Nat) :=
  (List.range length).flatMap fun j =>
    (List.range j).map fun i => (i, j)

/-- A deterministic, total search. Invalid inputs are allowed and may return none. -/
def collision? (c : MeshInput) : Option (Nat × Nat) :=
  (candidatePairs c.cells.length).find? fun ij =>
    decide (residue c.modulus (c.cells.getD ij.1 (fun _ => 0)) =
            residue c.modulus (c.cells.getD ij.2 (fun _ => 0)))

/-- The integer vector extracted from a collision, with division totalized by Lean. -/
def difference (c : MeshInput) (ij : Nat × Nat) : IVec c.dimension :=
  fun k => ((c.cells.getD ij.1 (fun _ => 0)) k -
            (c.cells.getD ij.2 (fun _ => 0)) k) / (c.modulus : Int)

/-- The finite arithmetic hypotheses. Geometry is deliberately absent. -/
def MeshInput.Valid (c : MeshInput) : Prop :=
  0 < c.dimension ∧ 0 < c.modulus ∧ c.cells.Nodup ∧
  c.modulus ^ c.dimension < c.cells.length

/-- The exact output relation that the finite proof must establish. -/
def MeshInput.GoodPair (c : MeshInput) (ij : Nat × Nat) : Prop :=
  ij.1 < ij.2 ∧ ij.2 < c.cells.length ∧
  difference c ij ≠ (fun _ => 0) ∧
  ∀ k, (c.cells.getD ij.1 (fun _ => 0)) k -
       (c.cells.getD ij.2 (fun _ => 0)) k =
       (c.modulus : Int) * difference c ij k

/-!
IMPLEMENTATION OBLIGATIONS, not declarations assumed elsewhere:

1. candidatePairs specification:
     (i,j) ∈ candidatePairs L ↔ i < j ∧ j < L.
2. residue coding:
     code_m(a) = sum_{k<n} (a_k mod m) m^k < m^n,
   and equality of codes implies coordinatewise equality of residues.
3. bounded finite pigeonhole:
     if L > M and each color is below M, collision? returns some pair.
   Use the explicit visited-color/occupancy invariant in the paper. Its
   arithmetic implementation uses only quantifier-free induction.
4. integer Euclidean division:
     a mod m = b mod m implies a-b = m*((a-b)/m), for m>0.
5. distinctness:
     Nodup plus i<j implies the selected cells differ. Consequently the
   quotient vector is nonzero.
6. combine 1--5 to prove the following target (not yet implemented):
     ∀ c, c.Valid → ∃ ij, collision? c = some ij ∧ c.GoodPair ij.

A proof of 6 in host Lean is useful but is NOT the final iPRA claim. The final
claim is the derivability target specified in ObjectTarget.lean.
-/

end MinkowskiIPRA
