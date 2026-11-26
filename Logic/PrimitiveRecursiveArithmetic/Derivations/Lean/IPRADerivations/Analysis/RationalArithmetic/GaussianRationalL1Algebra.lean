import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalL1

/-!
# L1 estimates for actual Gaussian-rational arithmetic

Triangle, submultiplicativity and radius estimates concern the actual
normalized operations, with no common-denominator input guard. The shared
denominator used for addition is computed from the two actual inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalL1Algebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalL1
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (represents qadd qmul positive_product scalar_congr scalar_add_same)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE denominator_positive)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize normalize_preserves_value)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (scale add mul normSq)
open LeanProofs.IPRA.Analysis.GaussianL1 (norm1)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem add_of_representations (q r a b E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E) :
    Γ ⊢[PRAAx] rationalLE (qL1 (qadd q r)) (RationalArithmetic.add (qL1 q) (qL1 r)) := by
  have hl := qL1_represents (Γ := Γ) _ _ _ hE (GaussianRationalHorner.qadd_represents _ _ _ _ _ hE hq hr)
  have hsum := scalar_add_same _ _ _ _ _ hE (qL1_represents _ _ _ hE hq) (qL1_represents _ _ _ hE hr)
  have hs : Γ ⊢[PRAAx] RationalArithmetic.represents (RationalArithmetic.add (qL1 q) (qL1 r))
      (ZT.ofNat (norm1 a+norm1 b)) E := scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [ZT.toZ_add,ZT.toZ_ofNat,Q.mk_add,map_add]) (.eqRefl _) hsum
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ E E hE hE hl hs
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right E (GaussianL1.norm1_add a b)))

theorem multiply_of_representations (q r a b A B : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a A) (hr : Γ ⊢[PRAAx] represents r b B) :
    Γ ⊢[PRAAx] rationalLE (qL1 (qmul q r)) (RationalArithmetic.multiply (qL1 q) (qL1 r)) := by
  have hp := positive_product _ _ hA hB
  have hl := qL1_represents (Γ := Γ) _ _ _ hp (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hA hB hq hr)
  have hmul := RationalRepresentations.represents_multiply _ _ _ _ _ _
    (qL1_represents (Γ := Γ) _ _ _ hA hq) (qL1_represents _ _ _ hB hr)
  have hm : Γ ⊢[PRAAx] RationalArithmetic.represents (RationalArithmetic.multiply (qL1 q) (qL1 r))
      (ZT.ofNat (norm1 a*norm1 b)) (A*B) := scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]) (.eqRefl _) hmul
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ (A*B) (A*B) hp hp hl hm
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (A*B) (GaussianL1.norm1_multiply a b)))

theorem qL1_add (q r : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qadd q r)) (RationalArithmetic.add (qL1 q) (qL1 r)) := by
  have hq := GaussianRationalHorner.represents_rescale (Γ := Γ) q (rawGaussian q) (rawDen q) (rawDen r) (raw_represents q)
  have hr := GaussianRationalHorner.represents_rescale (Γ := Γ) r (rawGaussian r) (rawDen r) (rawDen q) (raw_represents r)
  exact add_of_representations q r _ _ _ (positive_product _ _ (raw_den_positive q) (raw_den_positive r)) hq
    (GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm _ _) hr)

theorem qL1_multiply (q r : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qmul q r)) (RationalArithmetic.multiply (qL1 q) (qL1 r)) :=
  multiply_of_representations q r _ _ _ _ (raw_den_positive q) (raw_den_positive r) (raw_represents q) (raw_represents r)

theorem qL1_negative (q : PTm n) : Γ ⊢[PRAAx]
    qL1 (GaussianRationalMetric.qnegative q) ≐ qL1 q := by
  have hl := qL1_represents (Γ := Γ) _ _ _ (raw_den_positive q)
    (GaussianRationalMetric.qnegative_represents q (rawGaussian q) (rawDen q) (raw_represents q))
  have hr := qL1_represents (Γ := Γ) _ _ _ (raw_den_positive q) (raw_represents q)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (qL1_guard _) (qL1_guard _) hl hr
    (raw_den_positive q) (raw_den_positive q)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  rw [natEq (GaussianL1.norm1_negative (Γ := Γ) (rawGaussian q))]

theorem qL1_sub (q r : PTm n) : Γ ⊢[PRAAx]
    rationalLE (qL1 (GaussianRationalMetric.qsub q r)) (RationalArithmetic.add (qL1 q) (qL1 r)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _)
    (RationalAlgebra.add_congr (.eqRefl _) (qL1_negative r)) (qL1_add q _)

/-- A rational Euclidean radius gives exactly twice that radius in L1,
including zero radius. The integer square comparison is proved after
positive denominator clearing. -/
theorem qL1_of_bounded (q A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianRationalMetric.bounded q A B) : Γ ⊢[PRAAx]
    rationalLE (qL1 q) (normalize (ZT.ofNat (two*A)) B) := by
  have raw := GaussianRationalMetric.bounded_to_cleared q (rawGaussian q) (rawDen q) A B
    (raw_den_positive q) hB (raw_represents q) h
  have l1 := le_mul_mono (le_refl (B*B)) (GaussianL1.norm1_square_le_two_normSq (Γ := Γ) (rawGaussian q))
  have eucl := le_mul_mono (le_refl two) raw
  have square : Γ ⊢[PRAAx] le ((B*norm1 (rawGaussian q))*(B*norm1 (rawGaussian q)))
      ((two*A*rawDen q)*(two*A*rawDen q)) := by
    have h1 : Γ ⊢[PRAAx] le ((B*norm1 (rawGaussian q))*(B*norm1 (rawGaussian q)))
        (two*(B*B*normSq (rawGaussian q))) := le_congr (by ipra_ring) (by ipra_ring) l1
    have h2 : Γ ⊢[PRAAx] le (two*(B*B*normSq (rawGaussian q)))
        (two*(A*A)*(rawDen q*rawDen q)) := le_congr (.eqRefl _) (by ipra_ring) eucl
    exact le_trans (le_trans h1 h2)
      (le_of_eq_add (d := two*(A*A)*(rawDen q*rawDen q)) (by ipra_ring))
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ (rawDen q) B
    (raw_den_positive q) hB
    (qL1_represents _ _ _ (raw_den_positive q) (raw_represents q))
    (normalize_preserves_value _ _ hB)
    (nat_sqrt_mono square)

theorem rational_l1_algebra_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (qL1 (qadd (var 0) (var 1))) (RationalArithmetic.add (qL1 (var 0)) (qL1 (var 1))) ⋏
      (rationalLE (qL1 (qmul (var 0) (var 1))) (RationalArithmetic.multiply (qL1 (var 0)) (qL1 (var 1))) ⋏
        (qL1 (GaussianRationalMetric.qnegative (var 0)) ≐ qL1 (var 0)))) :=
  closeUniv 2 (.andI (qL1_add _ _) (.andI (qL1_multiply _ _) (qL1_negative _)))

theorem rational_l1_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ GaussianRationalMetric.bounded (var 0) (var 1) (var 2) ⟶
      rationalLE (qL1 (var 0)) (normalize (ZT.ofNat (two*var 1)) (var 2))) :=
  closeUniv 3 (.impI (.impI (qL1_of_bounded _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalL1Algebra
