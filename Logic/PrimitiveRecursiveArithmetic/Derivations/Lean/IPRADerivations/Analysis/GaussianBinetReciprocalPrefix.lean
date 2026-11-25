import IPRADerivations.Analysis.GaussianBinetLogCellComparison

/-!
# The logarithm–reciprocal comparison telescopes over the original prefix

Each horizontal unit cell contributes its telescoping real reciprocal
difference. Native quantifier-free induction sums the bounds for the
literal complex reciprocal prefix and the original logarithm samples.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetReciprocalPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLogCellComparison (budget budget_positive leftValue)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerHead (argument shifted_source)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum row_at rowBody)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data

def sample (p A B D neg N : PTm n) : PTm n := ap2 L p (ld (A+N*D) B D neg)

def increment (p A B D neg N : PTm n) : PTm n := qsub (sample p A B D neg N) (sample p A B D neg zero)

def denominator (p A D N : PTm n) : PTm n := A*(A+N*D)*unit p

def numerator (p A D N : PTm n) : PTm n := D*D*N*unit p+num 8*N*(A*(A+N*D))

def law (p A B D neg N : PTm n) : Fm PTm n :=
  distanceBounded (increment p A B D neg N) (reciprocalSum A B D neg N) (numerator p A D N) (denominator p A D N)

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p A B D neg N : PTm n) :
    Syn.subst σ (sample p A B D neg N) =
      sample (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ N) := by
  simp [sample]

@[simp] theorem subst_law {m : ℕ} (σ : Fin n → PTm m) (p A B D neg N : PTm n) :
    (law p A B D neg N).subst σ = law (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ N) := by
  simp [law,increment,numerator,denominator,reciprocalSum]

theorem denominator_positive (p A D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] le one (denominator p A D N) :=
  positive_product _ _ (positive_product _ _ h.andE₁.andE₁ (shifted_source N A D neg h).andE₁.andE₁) (unit_positive p)

private theorem code_congr (p A B D neg k j : PTm n) (h : Γ ⊢[PRAAx] k ≐ j) :
    Γ ⊢[PRAAx] sample p A B D neg k ≐ sample p A B D neg j := by
  have ed := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (ld (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![A+k*D,B,D,neg]) (σ' := ![A+j*D,B,D,neg])
    (fun i => by fin_cases i; exact congrAdd (.eqRefl A) (congrMul h (.eqRefl D)); exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
  exact congrAp2 L (.eqRefl p) (by simpa only [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using ed)

theorem base_sample (p A B D neg : PTm n) :
    Γ ⊢[PRAAx] sample p A B D neg zero ≐ ap2 L p (ld A B D neg) := by
  have eA : Γ ⊢[PRAAx] A+zero*D ≐ A := by ipra_ring
  have ed := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (ld (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![A+zero*D,B,D,neg]) (σ' := ![A,B,D,neg])
    (fun i => by fin_cases i; exact eA; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
  exact congrAp2 L (.eqRefl p) (by simpa only [GaussianRightHalfPlaneLogarithm.subst_data,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,
    Matrix.tail_cons] using ed)

private theorem cell (p A B D neg k : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    distanceBounded (qsub (sample p A B D neg (succ k)) (sample p A B D neg k)) (leftValue A B D neg k)
      (D*D*unit p+num 8*budget A D k) (budget A D k*unit p) := by
  let f := GaussianBinetLogCellComparison.nameF
  let x := GaussianBinetLogCellComparison.data A B D neg k
  let z := leftValue A B D neg k
  let E := budget A D k
  let U := unit p
  have he := budget_positive A D k neg h
  have hu := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ he hu
  have named := diagonal_rate f constantF x z (D*D) E p he (GaussianBinetLogCellComparison.independent_rate A B D neg k h)
  have obs := distance_congr (.eqRefl _) (constant_at p z) (.eqRefl _) (.eqRefl _) named
  let a := qsub (sample p A B D neg (k+one)) (sample p A B D neg k)
  let b := ap2 f p x
  have raw : Γ ⊢[PRAAx] distanceBounded b a (num 6) U := GaussianNamedDifference.sample_error L L _ _ p
    (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ (shifted_source (k+one) A D neg h))
    (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ (shifted_source k A D neg h))
  have first := distance_radius_mono a b _ U (num 6*E) (E*U) hu hD (by ipra_le 0)
    (distance_symmetric _ _ _ _ hu raw)
  have cast := code_congr (Γ := Γ) p A B D neg (k+one) (succ k) (by ipra_ring)
  exact distance_congr (qsub_congr cast (.eqRefl _)) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same a b z _ _ (E*U) hD first obs)

private theorem zero_case (p A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx] law p A B D neg zero := by
  let den := denominator p A D zero
  let z := qzero (n := n)
  have e := GaussianCoefficientNormOrder.qsub_self (Γ := Γ) (sample p A B D neg zero)
  have s := GaussianRationalFiniteSum.sum_zero (Γ := Γ) rowBody (argument A B D neg)
  exact distance_congr e.eqSymm s.eqSymm (by unfold numerator; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero z den (denominator_positive p A D neg zero h))

private theorem succ_case (p A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (ih : Γ ⊢[PRAAx] law p A B D neg N) : Γ ⊢[PRAAx] law p A B D neg (succ N) := by
  let U := unit p
  let X := A+N*D
  let Y := A+succ N*D
  let C := X*Y
  let P := denominator p A D N
  let Q := denominator p A D (succ N)
  let Z := P*Y
  let a := increment p A B D neg N
  let b := reciprocalSum A B D neg N
  let c := qsub (sample p A B D neg (succ N)) (sample p A B D neg N)
  let d := leftValue A B D neg N
  have hX := (shifted_source N A D neg h).andE₁.andE₁
  have hY := (shifted_source (succ N) A D neg h).andE₁.andE₁
  have hu := unit_positive (Γ := Γ) p
  have hp := denominator_positive p A D neg N h
  have hq := denominator_positive p A D neg (succ N) h
  have hz := positive_product P Y hp hY
  have hCell := cell p A B D neg N h
  have eY : Γ ⊢[PRAAx] A+(N+one)*D ≐ Y := by unfold Y; ipra_ring
  have close : Γ ⊢[PRAAx] distanceBounded c d (D*D*U+num 8*C) (C*U) :=
    distance_congr (.eqRefl _) (.eqRefl _)
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl X) eY)))
      (congrMul (congrMul (.eqRefl X) eY) (.eqRefl U)) hCell
  have left := distance_radius_mono a b (numerator p A D N) P (numerator p A D N*Y) Z hp hz
    (by dsimp only [Z]; ipra_le 0) ih
  have right := distance_radius_mono c d _ (C*U) ((D*D*U+num 8*C)*A) Z
    (positive_product _ _ (positive_product _ _ hX hY) hu) hz (by dsimp only [Z,P,denominator,X,C,U]; ipra_le 0) close
  have combined := GaussianNameArithmetic.sum_distance a b c d _ _ Z hz left right
  have small := distance_radius_mono _ _ _ Z (numerator p A D (succ N)) Q hz hq
    (by dsimp only [Z,P,Q,denominator,numerator,X,Y,C,U]; ipra_le 0) combined
  have leftEq : Γ ⊢[PRAAx] qadd a c ≐ increment p A B D neg (succ N) :=
    (GaussianReciprocalHorner.qadd_commutative a c).eqTrans
    (GaussianReconstructionRoots.difference_chain (sample p A B D neg (succ N)) (sample p A B D neg N) (sample p A B D neg zero))
  have rightEq := (GaussianRationalFiniteSum.sum_succ (Γ := Γ) rowBody N (argument A B D neg)).eqTrans
    (qadd_congr (.eqRefl b) (row_at (argument A B D neg) N))
  exact distance_congr leftEq rightEq.eqSymm (.eqRefl _) (.eqRefl _) small

theorem prefix_error (p A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx] law p A B D neg N := by
  let s (v : PTm n) := Syn.shift v
  have all : Γ ⊢[PRAAx] .all (law (s p) (s A) (s B) (s D) (s neg) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [s, subst_law, Syn.inst_zero, Syn.subst_var, Syn.subst_inst_shift]
      exact zero_case p A B D neg h
    · have hs : (law (s p) (s A) (s B) (s D) (s neg) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          source (s A) (s D) (s neg) :=
        by simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
      simp only [subst_law,Syn.subst_var,Syn.repl_zero,subst_repl_shift,s]
      exact
        succ_case (s p) (s A) (s B) (s D) (s neg) (var 0) hs Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,s] using all.allE N

theorem actual_complex_logarithm_reciprocal_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 3) (var 4) ⟶ law (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (prefix_error _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetReciprocalPrefix
