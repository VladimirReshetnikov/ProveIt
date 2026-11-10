import Mathlib.Computability.PartrecCode
import Mathlib.Computability.RE

/-!
# Selection from a recursively enumerable relation

`exists_selector`: for a recursively enumerable relation `R` between a parameter `a` and a number
`y` there is a partial recursive function `f` with `R (a, y)` for every `y ∈ f a`, and with `f a`
defined whenever some `y` has `R (a, y)`.

The selector dovetails. The semi-decision procedure of `R` is first made to return its candidate:
a code `cg` returns `y` on the code of `(a, y)` exactly when `R (a, y)`. Stage `k` reads `k` as a
pair `(y, s)` and runs `cg` on the code of `(a, y)` for `s` steps (`Nat.Partrec.Code.evaln`).
`Nat.rfindOpt` returns the result of the first successful stage.

This module depends on Mathlib only.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open Nat.Partrec.Code Computable

/-- A recursively enumerable relation has a partial recursive selector. -/
theorem exists_selector {α : Type*} [Primcodable α] {R : α × ℕ → Prop} (hR : REPred R) :
    ∃ f : α →. ℕ, Partrec f ∧ (∀ a, ∀ y ∈ f a, R (a, y)) ∧ ∀ a n, R (a, n) → (f a).Dom := by
  obtain ⟨cg, hcg⟩ := exists_code.1 (hR.map (snd.comp fst).to₂)
  -- `cg` returns the candidate `n` on the code of `(a, n)` exactly when `R (a, n)`.
  have hmem (a : α) (n y : ℕ) :
      y ∈ eval cg (Encodable.encode (a, n)) ↔ R (a, n) ∧ y = n := by
    simp [hcg, eq_comm]
  have hstage : Computable₂ fun (a : α) (k : ℕ) =>
      evaln k.unpair.2 cg (Encodable.encode (a, k.unpair.1)) :=
    (primrec_evaln.to_comp.comp (((snd.comp (unpair.comp snd)).pair (const cg)).pair
      (Computable.encode.comp (fst.pair (fst.comp (unpair.comp snd)))))).to₂
  refine ⟨_, Partrec.rfindOpt hstage, fun a y hy => ?_, fun a n hn => ?_⟩
  · obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hy
    obtain ⟨h, rfl⟩ := (hmem a k.unpair.1 y).mp (evaln_sound hk)
    exact h
  · obtain ⟨s, hs⟩ := evaln_complete.mp ((hmem a n n).mpr ⟨hn, rfl⟩)
    exact Nat.rfindOpt_dom.mpr ⟨Nat.pair n s, n, by simpa using hs⟩

#print axioms exists_selector

end PAFlexibleOutput
