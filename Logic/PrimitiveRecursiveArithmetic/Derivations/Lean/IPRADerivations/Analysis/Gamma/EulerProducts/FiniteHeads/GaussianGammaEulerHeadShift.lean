import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadLower

/-!
# Finite shift cancellation for the original Euler head

The polynomial part of the C20 shift is an exact identity of the
original Gaussian rational head program at every numerical cutoff.
At the successor, the old final linear factor and the new Euler factor
exchange their translated numerators. The proof stays valid at
zeros because it uses multiplication throughout.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadShift

open_ipra
open GaussianGammaEulerHead (factor head run head_zero head_succ program_at)
open GaussianGammaEulerHeadLower (translated factor_represents)
open GaussianRationalHorner (ofGaussian qmul represents positive_product ofGaussian_represents qmul_represents
  canonical_unique represents_congr qmul_canonical)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shifted (z B : PTm n) : PTm n := translated z B one
def linear (z B k : PTm n) : PTm n := ofGaussian (translated z B k) B

ipra_subst shifted

ipra_subst linear

theorem shifted_translation (z B j : PTm n) : Γ ⊢[PRAAx]
    equal (translated (shifted z B) B j) (translated z B (succ j)) := by
  apply equal_of_values <;>
    simp only [translated,shifted,re_add,im_add,re_scale,im_scale,re_one,im_one] <;>
    ipra_simps <;> ring

theorem factor_exchange (z B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (linear z B (succ j)) (factor j (shifted z B) B) ≐
      qmul (factor j z B) (linear z B (succ (succ j))) := by
  let u := translated z B (succ j)
  let v := translated z B (succ (succ j))
  let D := B*succ j
  have hD := positive_product (Γ := Γ) _ _ hB (zero_lt_succ j)
  have x := factor_represents j z B hB
  have y : Γ ⊢[PRAAx] represents (factor j (shifted z B) B) v D :=
    represents_congr (.eqRefl _) (shifted_translation z B (succ j)) (.eqRefl _)
      (factor_represents j (shifted z B) B hB)
  have lhs := qmul_represents _ _ _ _ _ _ hB hD (ofGaussian_represents u B hB) y
  have rhs : Γ ⊢[PRAAx] represents (qmul (factor j z B) (linear z B (succ (succ j))))
      (ComplexLogarithmRemainder.mul u v) (B*D) :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _)
      (qmul_represents _ _ _ _ _ _ hD hB x (ofGaussian_represents v B hB))
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (qmul_canonical _ _)
    (positive_product _ _ hB hD) lhs rhs

def shiftLaw (z B N : PTm n) : Fm PTm n :=
  qmul (ofGaussian z B) (head (shifted z B) B N) ≐ qmul (head z B N) (linear z B (succ N))

ipra_subst shiftLaw

theorem shift_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] shiftLaw z B zero :=
  (qmul_congr (.eqRefl _) (head_zero (shifted z B) B hB)).eqTrans
    (qmul_congr (head_zero z B hB).eqSymm (.eqRefl _))

theorem shift_step (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (ih : Γ ⊢[PRAAx] shiftLaw z B N) :
    Γ ⊢[PRAAx] shiftLaw z B (succ N) :=
  (qmul_congr (.eqRefl _) (head_succ (shifted z B) B N)).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans ((qmul_congr ih (.eqRefl _)).eqTrans
      ((qmul_associative _ _ _).eqTrans ((qmul_congr (.eqRefl _) (factor_exchange z B N hB)).eqTrans
        ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_congr (head_succ z B N).eqSymm (.eqRefl _)))))))

theorem shift_identity (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] shiftLaw z B N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hB.shift
  have all : Γ ⊢[PRAAx] .all (shiftLaw (Syn.shift z) (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_shiftLaw]
    · exact shift_zero z B hB
    · exact shift_step _ _ _ hs.wk Prf.hyp0
  simpa only [subst_shiftLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem returned_shift_identity (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (ofGaussian z B) (run (shifted z B) B N) ≐ qmul (run z B N) (linear z B (succ N)) :=
  (qmul_congr (.eqRefl _) (program_at (shifted z B) B N)).eqTrans
    ((shift_identity z B N hB).eqTrans (qmul_congr (program_at z B N).eqSymm (.eqRefl _)))

theorem original_finite_Euler_head_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ shiftLaw (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (shift_identity _ _ _ Prf.hyp0))

theorem original_finite_Euler_returned_head_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ qmul (ofGaussian (var 0) (var 1)) (run (shifted (var 0) (var 1)) (var 1) (var 2)) ≐
      qmul (run (var 0) (var 1) (var 2)) (linear (var 0) (var 1) (succ (var 2)))) :=
  closeUniv 3 (.impI (returned_shift_identity _ _ _ Prf.hyp0))

theorem linear_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] linear z B zero ≐ ofGaussian z B :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
    (GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianGammaEulerHeadLower.translated_zero z B) (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hB)) (GaussianRationalHorner.ofGaussian_represents _ _ hB)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadShift
