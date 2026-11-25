import IPRADerivations.Analysis.GaussianGammaFiniteValueProperness

/-!
# Rescaling a finite Euler head's rational argument

Multiplying a native Gaussian numerator and its positive denominator by
the same positive integer preserves the canonical fraction at every
entry of the original Euler head, and hence preserves the returned head.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadRescaling

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianGammaEulerHead (factor factor_at factorBody data product run program_at)
open GaussianRationalFiniteProduct (product_congr_bounded)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents
  canonical_unique represents_rescale represents_congr positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRootAlgebra (equal_refl)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem fraction_rescale (z B t C : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hC : Γ ⊢[PRAAx] le one C) (h : Γ ⊢[PRAAx] B*t ≐ C) :
    Γ ⊢[PRAAx] ofGaussian (scale t z) C ≐ ofGaussian z B :=
  canonical_unique _ _ _ C (ofGaussian_canonical _ _ hC) (ofGaussian_canonical _ _ hB) hC
    (ofGaussian_represents _ _ hC)
    (represents_congr (.eqRefl _) (equal_refl _) h
      (represents_rescale _ _ _ _ (ofGaussian_represents _ _ hB)))

theorem factor_rescale (i z B t : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] le one t) :
    Γ ⊢[PRAAx] factor i (scale t z) (B*t) ≐ factor i z B :=
  qadd_congr (.eqRefl _) (fraction_rescale z (B*succ i) t ((B*t)*succ i)
    (positive_product _ _ hB (zero_lt_succ i))
    (positive_product _ _ (positive_product _ _ hB ht) (zero_lt_succ i)) (by ipra_ring))

theorem returned_rescale (z B t N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] le one t) :
    Γ ⊢[PRAAx] run (scale t z) (B*t) N ≐ run z B N := by
  have rows : Γ ⊢[PRAAx] termsEqual factorBody factorBody N (data (scale t z) (B*t)) (data z B) := by
    refine .allI (.impI ?_)
    let Z := Syn.shift z
    let E := Syn.shift B
    let T := Syn.shift t
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hb : Δ ⊢[PRAAx] le one E := by simpa [Δ,E,Fm.shift,Syn.shift,one] using hB.shift.wk
    have hu : Δ ⊢[PRAAx] le one T := by simpa [Δ,T,Fm.shift,Syn.shift,one] using ht.shift.wk
    have step := (factor_at (Γ := Δ) (var 0) (scale T Z) (E*T)).eqTrans
      ((factor_rescale (var 0) Z E T hb hu).eqTrans (factor_at (var 0) Z E).eqSymm)
    simpa [termsEqual,Δ,Z,E,T,Syn.shift] using step
  have hF := fraction_rescale z B t (B*t) hB (positive_product _ _ hB ht) (.eqRefl _)
  have pp : Γ ⊢[PRAAx] product (scale t z) (B*t) N ≐ product z B N :=
    product_congr_bounded _ _ _ _ _ rows
  exact (program_at (scale t z) (B*t) N).eqTrans
    ((qmul_congr hF pp).eqTrans (program_at z B N).eqSymm)

theorem original_Euler_head_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶
      run (scale (var 2) (var 0)) (var 1*var 2) (var 3) ≐ run (var 0) (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (returned_rescale _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadRescaling
