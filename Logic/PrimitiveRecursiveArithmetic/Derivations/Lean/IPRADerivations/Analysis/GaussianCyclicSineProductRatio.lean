import IPRADerivations.Analysis.GaussianCyclicOriginalSineProduct

/-!
# The exact ratio for the original finite sine product

A finite induction cancels one factor of two per original sine
observation. Thus the cofinal error for the actual sine product
has center the literal Gaussian rational `(N+1)/2^N`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicSineProductRatio

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale add mul normSq normSq_eval)
open GaussianCyclicOriginalSineProduct (originalF doubledF original_at doubled_at budget actual_doubled_product_error)
open GaussianCyclicSineProductNormalization (clock)
open GaussianCyclicSineProductSquare (data)
open GaussianCyclicFullHalfAngle (sineSample)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianRationalHorner (qmul qadd qmul_canonical qmul_represents qadd_represents ofGaussian
  ofGaussian_canonical ofGaussian_represents canonical_unique represents_rescale represents_congr positive_product)
open GaussianRationalReciprocal (qone)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents natural_product_value)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianRationalMetric (bounded distanceBounded bounded_of_cleared)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalPowerAlgebra (qmul_shuffle)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_mul im_mul re_one im_one re_scale im_scale re_add im_add)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def half (k : PTm n) : PTm n := ofGaussian oneCode (unit k)
def ratio (N : PTm n) : PTm n := ofGaussian (scale (succ N) oneCode) (unit N)
def halfPoint : PTm n := ofGaussian oneCode two

@[simp] theorem subst_half {L : ℕ} (σ : Fin n → PTm L) (k : PTm n) :
    Syn.subst σ (half k) = half (Syn.subst σ k) := by simp [half]

private theorem unit_succ (k : PTm n) : Γ ⊢[PRAAx] unit (succ k) ≐ unit k*two :=
  pw_succ _ _

private theorem half_zero : Γ ⊢[PRAAx] half (zero : PTm n) ≐ qone := by
  apply canonical_unique _ _ _ one (ofGaussian_canonical _ _ (unit_positive zero)) qone_canonical (le_refl one)
  · exact represents_congr (.eqRefl _) (equal_refl _) (pw_zero two) (ofGaussian_represents _ _ (unit_positive zero))
  · exact ofGaussian_represents _ _ (le_refl one)

private theorem half_succ (k : PTm n) : Γ ⊢[PRAAx] half (succ k) ≐ qmul (half k) halfPoint := by
  have h₂ : Γ ⊢[PRAAx] le one two := le_succ_self one
  have mk : Γ ⊢[PRAAx] equal (mul oneCode oneCode) oneCode := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one] <;> ring
  exact (canonical_unique _ _ _ (unit k*two) (qmul_canonical _ _)
    (ofGaussian_canonical _ _ (unit_positive (succ k))) (positive_product _ _ (unit_positive k) h₂)
    (represents_congr (.eqRefl _) mk (.eqRefl _)
      (qmul_represents _ _ _ _ _ _ (unit_positive k) h₂
        (ofGaussian_represents _ _ (unit_positive k)) (ofGaussian_represents _ _ h₂)))
    (represents_congr (.eqRefl _) (equal_refl _) (unit_succ k)
      (ofGaussian_represents _ _ (unit_positive (succ k))))).eqSymm

private theorem half_bound (k : PTm n) : Γ ⊢[PRAAx] bounded (half k) one one := by
  have h := unit_positive (Γ := Γ) k
  apply bounded_of_cleared _ _ _ _ _ h (le_refl one) (ofGaussian_represents _ _ h)
  have hn : Γ ⊢[PRAAx] normSq (oneCode : PTm n) ≐ one := by
    apply deriveNat
    rw [normSq_eval]
    simp only [re_one,im_one]
    ipra_simps
    ring
  exact le_congr ((congrMul (.eqRefl _) hn).eqTrans (by ipra_ring)).eqSymm
    (by ipra_ring) (le_mul_mono h h)

private theorem half_double (q : PTm n) (hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical q) :
    Γ ⊢[PRAAx] qmul halfPoint (qadd q q) ≐ q := by
  let a := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have h₂ : Γ ⊢[PRAAx] le one two := le_succ_self one
  have r := raw_represents (Γ := Γ) q
  have h := qmul_represents halfPoint (qadd q q) oneCode (add a a) two E h₂ hE
    (ofGaussian_represents _ _ h₂) (qadd_represents _ _ _ _ _ hE r r)
  have e : Γ ⊢[PRAAx] equal (mul oneCode (add a a)) (scale two a) := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one,re_add,im_add,re_scale,im_scale] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ (two*E) (qmul_canonical _ _) hc (positive_product _ _ h₂ hE)
    (represents_congr (.eqRefl _) e (.eqRefl _) h)
    (represents_congr (.eqRefl _) (equal_refl _) (mul_comm _ _) (represents_rescale _ _ _ two r))

private theorem half_natural (m k : PTm n) :
    Γ ⊢[PRAAx] qmul (half k) (naturalPoint m) ≐ ofGaussian (scale m oneCode) (unit k) := by
  have hk := unit_positive (Γ := Γ) k
  have e : Γ ⊢[PRAAx] equal (mul oneCode (scale m oneCode)) (scale m oneCode) := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one,re_scale,im_scale] <;> ring
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ hk) hk
    (represents_congr (.eqRefl _) e (by ipra_ring) (qmul_represents _ _ _ _ _ _ hk (le_refl one)
      (ofGaussian_represents _ _ hk) (natural_point_represents m))) (ofGaussian_represents _ _ hk)

private theorem unscale_row (p N x i : PTm n) :
    Γ ⊢[PRAAx] qmul halfPoint (ap3 doubledF p i (data N x)) ≐ ap3 originalF p i (data N x) := by
  let r := succ (GaussianCyclicSineProductSquare.index N i)
  let m := succ N
  let a := sineSample p r m x
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a := GaussianNamedSineFromExponential.sine_canonical
    GaussianCyclicExponentialRoots.angleF GaussianArctangentExponentialPeriod.fullTurnRadius
    (GaussianCyclicExponentialRoots.angleData r (two*m) x) p
  exact (qmul_congr (.eqRefl _) (doubled_at p N x i)).eqTrans
    ((half_double a hc).eqTrans (original_at p N x i).eqSymm)

private def law (p k d : PTm n) : Fm PTm n :=
  qmul (half k) (sample doubledF p k d) ≐ sample originalF p k d

@[simp] private theorem subst_law {L : ℕ} (σ : Fin n → PTm L) (p k d : PTm n) :
    (law p k d).subst σ = law (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ d) := by simp [law]

theorem unscale_product (p N x k : PTm n) :
    Γ ⊢[PRAAx] qmul (half k) (sample doubledF p k (data N x)) ≐ sample originalF p k (data N x) := by
  have all : Γ ⊢[PRAAx] .all (law (Syn.shift p) (var 0) (Syn.shift (data N x))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (qmul_congr half_zero (sample_zero doubledF p (data N x))).eqTrans
        ((qmul_one_right _ qone_canonical).eqTrans (sample_zero originalF p (data N x)).eqSymm)
    · simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift,GaussianCyclicSineProductSquare.subst_data]
      let P := Syn.shift p
      let M := Syn.shift N
      let X := Syn.shift x
      let j : PTm (n+1) := var 0
      let d := data M X
      let Δ := law P j d :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] law P j d := Prf.hyp0
      have result : Δ ⊢[PRAAx] law P (succ j) d :=
        (qmul_congr (half_succ j) (sample_succ doubledF P j d)).eqTrans
          ((qmul_shuffle _ _ _ _).eqTrans ((qmul_congr ih (unscale_row P M X j)).eqTrans
            (sample_succ originalF P j d).eqSymm))
      simpa [Δ,d,P,j,M,X,Syn.shift] using result
  change Γ ⊢[PRAAx] law p k (data N x)
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem original_product_error (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ratio N)
      (sample originalF (clock p (succ N)) N (data N x)) (budget N) (unit (clock p (succ N))) := by
  let q := clock p (succ N)
  exact distance_congr (half_natural (succ N) N) (unscale_product q N x N) (one_mul _) (.eqRefl _)
    (multiply_distance (half N) _ _ one (budget N) (unit q) (unit_positive q) (half_bound N)
      (actual_doubled_product_error p N x))

theorem original_cyclic_sine_product_ratio_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (ratio (var 1))
        (sample originalF (clock (var 2) (succ (var 1))) (var 1) (data (var 1) (var 0)))
        (budget (var 1)) (unit (clock (var 2) (succ (var 1))))) :=
  closeUniv 3 (original_product_error _ _ _)

end LeanProofs.IPRA.Analysis.GaussianCyclicSineProductRatio
