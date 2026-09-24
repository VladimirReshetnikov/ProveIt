import Diophantine.Common.MRDPCore

/-!
# Diophantine graphs of primitive recursive functions

These scalar interfaces adapt `MRDP.primrec_diophFn`, whose proof uses
arity-indexed primitive recursion and Chinese-remainder coding. They preserve
arbitrary Diophantine input substitutions and include input zero.
-/

namespace Diophantine

open Dioph
open scoped Vector3

/-- Primitive recursive functions preserve Diophantine input substitutions.
The input index type is arbitrary within Mathlib's Diophantine universe. -/
theorem natPrimrec_dioph_comp {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∀ {α : Type} {input : (α → ℕ) → ℕ}, DiophFn input →
      DiophFn (fun v => f (input v)) := by
  intro α input dinput
  have dfunction := MRDP.primrec_diophFn
    (Nat.Primrec'.prim_iff₁.mpr (Primrec.nat_iff.mpr hf))
  exact diophFn_comp dfunction [input] dinput

/-- Every primitive recursive natural function has a Diophantine graph. -/
theorem natPrimrec_dioph {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    DiophFn (fun v : Unit → ℕ => f (v ())) :=
  natPrimrec_dioph_comp hf (Dioph.proj_dioph ())

end Diophantine
