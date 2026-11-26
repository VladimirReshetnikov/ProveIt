import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalRoundedPower

/-!
# Independent observations of an actual affine name remainder

A same-query estimate for F-(G+cH), with |c|<=1, gives the exact
three-query estimate. The auxiliary query is the original rational
integer-gap program; no regularity of a replacement aggregate name is
assumed or used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedAffineRemainderRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qadd qmul positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def affine (G H : PR 2) (q r y z c : PTm n) : PTm n :=
  qadd (ap2 G q y) (qmul c (ap2 H r z))
def numerator (A B p q r : PTm n) : PTm n :=
  A*unit p*unit q*unit r+B*(unit q*unit r+unit p*unit r+unit p*unit q)
def denominator (B p q r : PTm n) : PTm n := B*unit p*unit q*unit r
def diagonalEnvelope (F G H : PR 2) (x y z c A B C : PTm n) : Fm PTm n := .all
  (distanceBounded (ap2 F (var 0) (Syn.shift x))
    (affine G H (var 0) (var 0) (Syn.shift y) (Syn.shift z) (Syn.shift c))
    (diagonalNumerator (Syn.shift A) (Syn.shift B) (Syn.shift C) (var 0))
    (diagonalDenominator (Syn.shift B) (var 0)))
def input (F G H : PR 2) (x y z c A B C : PTm n) : Fm PTm n :=
  le one B ⋏ (bounded c one one ⋏ (pointCN F x ⋏ (pointCN G y ⋏
    (pointCN H z ⋏ diagonalEnvelope F G H x y z c A B C))))

@[simp] theorem subst_affine {m : ℕ} (σ : Fin n → PTm m) (G H : PR 2) (q r y z c : PTm n) :
    Syn.subst σ (affine G H q r y z c) = affine G H (Syn.subst σ q) (Syn.subst σ r)
      (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ c) := by simp [affine]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (A B p q r : PTm n) :
    Syn.subst σ (numerator A B p q r) = numerator (Syn.subst σ A) (Syn.subst σ B)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ r) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (B p q r : PTm n) :
    Syn.subst σ (denominator B p q r) = denominator (Syn.subst σ B)
      (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ r) := by simp [denominator]
@[simp] theorem subst_diagonalEnvelope {m : ℕ} (σ : Fin n → PTm m) (F G H : PR 2) (x y z c A B C : PTm n) :
    (diagonalEnvelope F G H x y z c A B C).subst σ = diagonalEnvelope F G H (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ c) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) := by
  simp [diagonalEnvelope,Syn.subst_shift,Syn.shift_subst]

theorem denominator_positive (B p q r : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (denominator B p q r) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ hB (unit_positive p)) (unit_positive q)) (unit_positive r)

theorem diagonal_at (F G H : PR 2) (x y z c A B C t : PTm n)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G H x y z c A B C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F t x) (affine G H t t y z c)
      (diagonalNumerator A B C t) (diagonalDenominator B t) := by
  simpa only [diagonalEnvelope,GaussianRationalMetric.subst_distanceBounded,subst_ap2,subst_affine,
    GaussianNamedLipschitzRate.subst_diagonalNumerator,GaussianNamedLipschitzRate.subst_diagonalDenominator,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE t

theorem independent_slack (F G H : PR 2) (x y z c A B C p q r t : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] bounded c one one)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN H z)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G H x y z c A B C) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 F p x) (affine G H q r y z c))
      (numerator A B p q r) (denominator B p q r) (C+num 3) t := by
  let D := denominator B p q r*unit t
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (denominator_positive B p q r hB) (unit_positive t)
  have left := distance_radius_mono _ _ _ _ ((unit p+unit t)*(B*unit q*unit r)) D
    (positive_product _ _ (unit_positive p) (unit_positive t)) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring)) (GaussianNameEquivalence.point_at F x p t hf)
  have middle := distance_radius_mono _ _ _ _ ((A*unit t+C*B)*(unit p*unit q*unit r)) D
    (positive_product _ _ hB (unit_positive t)) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator,diagonalNumerator,diagonalDenominator]; ipra_ring))
    (diagonal_at F G H x y z c A B C t h)
  have rightG := distance_radius_mono _ _ _ _ ((unit t+unit q)*(B*unit p*unit r)) D
    (positive_product _ _ (unit_positive t) (unit_positive q)) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring)) (GaussianNameEquivalence.point_at G y t q hg)
  have rightH := distance_radius_mono _ _ _ _ ((unit t+unit r)*(B*unit p*unit q)) D
    (positive_product _ _ (unit_positive t) (unit_positive r)) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,denominator]; ipra_ring))
    (GaussianRationalRoundedPower.multiply_distance_bound c (ap2 H t z) (ap2 H r z)
      (unit t+unit r) (unit t*unit r) (positive_product _ _ (unit_positive t) (unit_positive r)) hc
      (GaussianNameEquivalence.point_at H z t r hh))
  have right := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd rightG rightH
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [numerator,denominator,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd left middle) right)

def gapQuery (F G H : PR 2) (x y z c A B C p q r : PTm n) : PTm n :=
  GaussianRationalSlackRemoval.precision (qsub (ap2 F p x) (affine G H q r y z c))
    (numerator A B p q r) (denominator B p q r) (C+num 3)

theorem independent_at (F G H : PR 2) (x y z c A B C p q r : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] bounded c one one)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) (hh : Γ ⊢[PRAAx] pointCN H z)
    (h : Γ ⊢[PRAAx] diagonalEnvelope F G H x y z c A B C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F p x) (affine G H q r y z c) (numerator A B p q r) (denominator B p q r) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (C+num 3) (denominator_positive B p q r hB)
    (independent_slack F G H x y z c A B C p q r (gapQuery F G H x y z c A B C p q r) hB hc hf hg hh h)

theorem actual_affine_remainder_independent_observations_closed (F G H : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input F G H (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (ap2 F (var 7) (var 0)) (affine G H (var 8) (var 9) (var 1) (var 2) (var 3))
        (numerator (var 4) (var 5) (var 7) (var 8) (var 9)) (denominator (var 5) (var 7) (var 8) (var 9))) :=
  closeUniv 10 (.impI (independent_at F G H _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedAffineRemainderRate
