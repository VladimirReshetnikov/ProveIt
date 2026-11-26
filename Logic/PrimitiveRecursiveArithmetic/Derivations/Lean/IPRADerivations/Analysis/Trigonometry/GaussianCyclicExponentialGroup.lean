import IPRADerivations.Analysis.Trigonometry.GaussianCyclicExponentialRoots

/-!
# Addition and endpoint identities for the actual cyclic names

All cyclic angles have one fixed normalization clock. Sums with equal
integer indices have literally equal samples at that clock. Ordinary
exponential addition therefore identifies the corresponding root products,
including across the full-turn endpoint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicExponentialGroup

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicExponentialRoots (source coefficient angleF angleData angle_at angle_input angle_regular
  coefficient_bound rootF rootData root_regular)
open GaussianArctangentExponentialPeriod (fullTurnF fullTurnData fullTurnRadius original_full_turn_input)
open GaussianBoundedConstantProductName (clock)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianExponentialReference (add_sample add_input)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianNamedDiagonalRate (cross_of_diagonal_rate diagonalRate)
open GaussianGammaCanonicalExponent (constantF)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique
  qadd qadd_canonical qadd_represents qmul represents_rescale represents_congr)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (qone qone_represents_scaled qone_bounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianApproximateInverseDistance (multiply_distance)
open ComplexLogarithmRemainder (scale oneCode)
open GaussianRootAlgebra (equal_of_values re_add im_add re_scale im_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sumF : PR 2 := addF angleF angleF
def sumData (r s m x : PTm n) : PTm n := addData (angleData r m x) (angleData s m x)
def productF : PR 2 := multiplyF rootF rootF
def productData (r s m x : PTm n) : PTm n := multiplyData rootF rootF (rootData r m x) (rootData s m x)

@[simp] theorem subst_sumData {l : ℕ} (σ : Fin n → PTm l) (r s m x : PTm n) :
    Syn.subst σ (sumData r s m x) = sumData (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [sumData]
@[simp] theorem subst_productData {l : ℕ} (σ : Fin n → PTm l) (r s m x : PTm n) :
    Syn.subst σ (productData r s m x) =
      productData (Syn.subst σ r) (Syn.subst σ s) (Syn.subst σ m) (Syn.subst σ x) := by
  simp [productData]

theorem coefficient_add (r s m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] qadd (coefficient r m) (coefficient s m) ≐ coefficient (r+s) m := by
  let a := scale r oneCode
  let b := scale s oneCode
  let d := scale (r+s) oneCode
  have h := qadd_represents (coefficient r m) (coefficient s m) a b m hm
    (ofGaussian_represents _ _ hm) (ofGaussian_represents _ _ hm)
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add a b) d := by
    dsimp only [a,b,d]
    apply equal_of_values <;> simp only [re_add,im_add,re_scale,im_scale] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ _ (qadd_canonical _ _) (ofGaussian_canonical _ _ hm) hm
    (represents_congr (.eqRefl _) e (.eqRefl _) h) (ofGaussian_represents _ _ hm)

theorem coefficient_congr (m : PTm n) {r s : PTm n} (e : Γ ⊢[PRAAx] r ≐ s) :
    Γ ⊢[PRAAx] coefficient r m ≐ coefficient s m := by
  simpa only [GaussianCyclicExponentialRoots.subst_coefficient,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.tail_cons] using
      (Prf.eqCongr (coefficient (var 0) (var 1) : PTm 2) (σ := ![r,m]) (σ' := ![s,m])
        (fun j => by fin_cases j; exact e; exact .eqRefl m))

private theorem right_distribution (a b q : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul a q) (qmul b q) ≐ qmul (qadd a b) q :=
  (qadd_congr (qmul_commutative a q) (qmul_commutative b q)).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add q a b).eqSymm.eqTrans (qmul_commutative _ _))

theorem sum_at (p r s m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 sumF p (sumData r s m x) ≐
      qmul (coefficient (r+s) m)
        (ap2 fullTurnF (clock (GaussianFastValueCut.exponent two p) one) (fullTurnData x)) := by
  let t := GaussianFastValueCut.exponent two p
  exact (add_sample angleF angleF (angleData r m x) (angleData s m x) p).eqTrans
    ((qadd_congr (angle_at t r m x) (angle_at t s m x)).eqTrans
      ((right_distribution _ _ _).eqTrans (qmul_congr (coefficient_add r s m hm) (.eqRefl _))))

private theorem sum_equal_at (p r s u v m x : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (e : Γ ⊢[PRAAx] r+s ≐ u+v) :
    Γ ⊢[PRAAx] ap2 sumF p (sumData r s m x) ≐ ap2 sumF p (sumData u v m x) :=
  (sum_at p r s m x hm).eqTrans
    ((qmul_congr (coefficient_congr m e) (.eqRefl _)).eqTrans (sum_at p u v m x hm).eqSymm)

theorem sum_input (r s m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input sumF (fullTurnRadius+fullTurnRadius) (sumData r s m x) :=
  add_input _ _ fullTurnRadius _ _ (angle_input r m x hr) (angle_input s m x hs)

theorem sum_equal_cross (r s u v m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m)
    (hu : Γ ⊢[PRAAx] source u m) (hv : Γ ⊢[PRAAx] source v m) (e : Γ ⊢[PRAAx] r+s ≐ u+v) :
    Γ ⊢[PRAAx] crossEquivalent sumF sumF (sumData r s m x) (sumData u v m x) := by
  apply cross_of_diagonal_rate _ _ _ _ zero (sum_input r s m x hr hs).andE₁ (sum_input u v m x hu hv).andE₁
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have h' : Δ ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hr.andE₁.shift
  have e' : Δ ⊢[PRAAx] sh r+sh s ≐ sh u+sh v := by simpa [Fm.shift,Syn.shift,Δ,sh] using e.shift
  have close := distance_congr (sum_equal_at (var 0) (sh r) (sh s) (sh u) (sh v) (sh m) (sh x) h' e').eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero (ap2 sumF (var 0) (sumData (sh u) (sh v) (sh m) (sh x))) (unit (var 0)) (unit_positive (var 0)))
  simpa only [diagonalRate,Syn.shift,subst_sumData,ConciseIPRA.PTm.subst_zero,Δ,sh] using close

private theorem sum_index_at (p r s m x : PTm n) (hs : Γ ⊢[PRAAx] source (r+s) m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 sumF p (sumData r s m x)) (ap2 angleF p (angleData (r+s) m x)) two (unit p) := by
  let t := GaussianFastValueCut.exponent two p
  let a := clock t one
  let b := clock p one
  let d := fullTurnData x
  have h := common_late_distance (Γ := Γ) fullTurnF d p a b (original_full_turn_input x).andE₁
    (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)
  exact distance_congr (sum_at p r s m x hs.andE₁).eqSymm (angle_at p (r+s) m x).eqSymm
    (one_mul _) (.eqRefl _) (multiply_distance (coefficient (r+s) m) _ _ one two (unit p) (unit_positive p)
      (coefficient_bound (r+s) m hs) h)

theorem sum_index_cross (r s m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m)
    (ht : Γ ⊢[PRAAx] source (r+s) m) :
    Γ ⊢[PRAAx] crossEquivalent sumF angleF (sumData r s m x) (angleData (r+s) m x) := by
  apply cross_of_diagonal_rate _ _ _ _ two (sum_input r s m x hr hs).andE₁ (angle_regular (r+s) m x ht)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have ht' : Δ ⊢[PRAAx] source (sh r+sh s) (sh m) := by simpa [Fm.shift,Syn.shift,Δ,sh] using ht.shift
  simpa only [diagonalRate,Syn.shift,subst_sumData,GaussianCyclicExponentialRoots.subst_angleData,PTm.subst_add,
    two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Δ,sh] using
    sum_index_at (var 0) (sh r) (sh s) (sh m) (sh x) ht'

theorem product_sum_cross (r s m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m) :
    Γ ⊢[PRAAx] crossEquivalent productF (GaussianRadiusExponentialName.nameF sumF) (productData r s m x)
      (GaussianRadiusExponentialName.data (fullTurnRadius+fullTurnRadius) (sumData r s m x)) :=
  GaussianExponentialAddition.exponential_add_cross angleF angleF fullTurnRadius (angleData r m x) (angleData s m x)
    (by unfold fullTurnRadius GaussianArctangentExponentialPeriod.twiceRadius GaussianArctangentQuarterExponential.radius; ipra_le 7)
    (angle_input r m x hr) (angle_input s m x hs)

theorem product_equal_cross (r s u v m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m)
    (hu : Γ ⊢[PRAAx] source u m) (hv : Γ ⊢[PRAAx] source v m) (e : Γ ⊢[PRAAx] r+s ≐ u+v) :
    Γ ⊢[PRAAx] crossEquivalent productF productF (productData r s m x) (productData u v m x) := by
  have middle := GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
    (sum_input r s m x hr hs) (sum_input u v m x hu hv) (sum_equal_cross r s u v m x hr hs hu hv e)
  exact cross_trans _ _ _ _ _ _ (product_sum_cross r s m x hr hs)
    (cross_trans _ _ _ _ _ _ middle (cross_symm _ _ _ _ (product_sum_cross u v m x hu hv)))

theorem product_index_cross (r s m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m)
    (ht : Γ ⊢[PRAAx] source (r+s) m) :
    Γ ⊢[PRAAx] crossEquivalent productF rootF (productData r s m x) (rootData (r+s) m x) :=
  cross_trans _ _ _ _ _ _ (product_sum_cross r s m x hr hs)
    (GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
      (sum_input r s m x hr hs) (angle_input (r+s) m x ht) (sum_index_cross r s m x hr hs ht))

theorem coefficient_endpoint (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] coefficient m m ≐ qone :=
  canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hm) GaussianRationalSyntheticDivision.qone_canonical hm
    (ofGaussian_represents _ _ hm) (qone_represents_scaled m)

private theorem endpoint_angle_at (p m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 angleF p (angleData m m x)) (ap2 fullTurnF p (fullTurnData x)) two (unit p) := by
  let t := clock p one
  let d := fullTurnData x
  have recode : Γ ⊢[PRAAx] qmul qone (ap2 fullTurnF t d) ≐ ap2 fullTurnF t d :=
    GaussianPolynomialDeterminantTerms.one_mul_canonical _ (GaussianNameArithmetic.add_canonical
      GaussianArctangentExponentialPeriod.twiceF GaussianArctangentExponentialPeriod.twiceF
      (GaussianArctangentExponentialPeriod.twiceData x) (GaussianArctangentExponentialPeriod.twiceData x) t)
  exact distance_congr ((angle_at p m m x).eqTrans
      ((qmul_congr (coefficient_endpoint m hm) (.eqRefl _)).eqTrans recode)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (common_late_distance fullTurnF d p t p (original_full_turn_input x).andE₁ (le_add_right _ _) (le_refl p))

theorem endpoint_angle_cross (m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent angleF fullTurnF (angleData m m x) (fullTurnData x) := by
  apply cross_of_diagonal_rate _ _ _ _ two (angle_regular m m x (.andI hm (le_refl _))) (original_full_turn_input x).andE₁
  refine .allI ?_
  have hm' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hm.shift
  simpa [diagonalRate,Syn.shift,fullTurnData,GaussianArctangentExponentialPeriod.twiceData] using
    endpoint_angle_at (var 0) (Syn.shift m) (Syn.shift x) hm'

theorem endpoint_root_cross (m x : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] crossEquivalent rootF constantF (rootData m m x) qone :=
  cross_trans _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.independent_radii_proper _ _ _ _ _ _
      (angle_input m m x (.andI hm (le_refl _))) (original_full_turn_input x) (endpoint_angle_cross m x hm))
    (GaussianArctangentOriginalExponential.full_turn_cross x)

end LeanProofs.IPRA.Analysis.GaussianCyclicExponentialGroup
