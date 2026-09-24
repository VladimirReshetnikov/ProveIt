import Surreal.Algebra.AdicCompletionTopology
import Mathlib.Algebra.Group.Idempotent

/-!
# Adic completion at an idempotent ideal

The completion prerequisite of `odg:cor:Pglobal`: when `I² = I`, the
adic completion is the discrete quotient `R / I`. The equivalence is
induced by evaluation at the first residue and preserves the canonical map.
-/

namespace Surreal.AdicCompletionTopology

open Topology

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R) (hI : IsIdempotentElem I)

include hI in
/-- The first residue determines an adic element when all positive ideal powers coincide. -/
theorem eval_one_injective_of_idempotent : Function.Injective (AdicCompletion.evalₐ I 1) := by
  intro x y h
  apply AdicCompletion.ext_evalₐ
  intro n
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n y)
  rw [← ha, ← hb, Ideal.Quotient.eq]
  by_cases hn : n = 0
  · simp only [hn, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    rw [← eval_compatible I hn1 x, ← eval_compatible I hn1 y, ← ha, ← hb,
      Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h
    rw [hI.pow_eq hn]
    simpa only [pow_one] using h

/-- Completion at an idempotent ideal is ring-isomorphic to the quotient by the ideal. -/
def idempotentEquiv : AdicCompletion I R ≃+* R ⧸ I :=
  (RingEquiv.ofBijective (AdicCompletion.evalₐ I 1).toRingHom
    ⟨eval_one_injective_of_idempotent I hI, AdicCompletion.surjective_evalₐ I 1⟩).trans
    (Ideal.quotEquivOfEq (pow_one I))

/-- The ring equivalence sends the canonical completion map to the quotient map. -/
@[simp] theorem idempotentEquiv_of (x : R) :
    idempotentEquiv I hI (AdicCompletion.of I R x) = Ideal.Quotient.mk I x := by
  change Ideal.quotEquivOfEq (pow_one I) (AdicCompletion.evalₐ I 1 (AdicCompletion.of I R x)) = _
  rw [AdicCompletion.evalₐ_of, Ideal.quotEquivOfEq_mk]

local instance idempotentQuotientTopology : TopologicalSpace (R ⧸ I) := ⊥
local instance idempotentQuotientDiscrete : DiscreteTopology (R ⧸ I) := ⟨rfl⟩
local instance powerQuotientTopology (n : ℕ) : TopologicalSpace (R ⧸ I ^ n) := ⊥
local instance powerQuotientDiscrete (n : ℕ) : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩

/-- The inverse-limit topology of an idempotent completion is the discrete quotient topology. -/
def idempotentHomeomorph : AdicCompletion I R ≃ₜ R ⧸ I where
  toEquiv := (idempotentEquiv I hI).toEquiv
  continuous_toFun := by
    change Continuous (fun x => Ideal.quotEquivOfEq (pow_one I) (AdicCompletion.evalₐ I 1 x))
    exact continuous_of_discreteTopology.comp (continuous_eval I 1)
  continuous_invFun := continuous_of_discreteTopology

/-- The homeomorphism uses the previously constructed quotient ring equivalence. -/
@[simp] theorem idempotentHomeomorph_apply (x : AdicCompletion I R) :
    idempotentHomeomorph I hI x = idempotentEquiv I hI x := rfl

end
end Surreal.AdicCompletionTopology
