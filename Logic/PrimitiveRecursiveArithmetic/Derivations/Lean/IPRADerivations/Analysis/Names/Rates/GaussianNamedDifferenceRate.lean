import IPRADerivations.Analysis.Names.GaussianNamedDifference
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate

/-!
# Exact independent rates for original normalized difference names

Two original endpoint rates A/B and C/E give the actual normalized
difference names the rate (A*E+C*B)/(B*E). Their actual negative/addition
readbacks supply a finite same-query envelope. Original regularity and
the existing rational finite-gap proof remove only its auxiliary error.
The requested output observations keep exactly their own dyadics.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDifferenceRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDifference (nameF data name_regular sample_error difference_distance)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator diagonalEnvelope)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leadingNumerator (A B C E : PTm n) : PTm n := A*E+C*B
def leadingDenominator (B E : PTm n) : PTm n := B*E
def source (F G H K : PR 2) (x y u v A B C E : PTm n) : Fm PTm n :=
  (le one B ⋏ le one E) ⋏ ((pointCN F x ⋏ pointCN G y) ⋏ ((pointCN H u ⋏ pointCN K v) ⋏
    (independentRate F H x u A B ⋏ independentRate G K y v C E)))

@[simp] theorem subst_leadingNumerator {m : ℕ} (σ : Fin n → PTm m) (A B C E : PTm n) :
    Syn.subst σ (leadingNumerator A B C E) = leadingNumerator (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ E) := by simp [leadingNumerator]
@[simp] theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (B E : PTm n) :
    Syn.subst σ (leadingDenominator B E) = leadingDenominator (Syn.subst σ B) (Syn.subst σ E) := by simp [leadingDenominator]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (F G H K : PR 2) (x y u v A B C E : PTm n) :
    (source F G H K x y u v A B C E).subst σ = source F G H K (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ u)
      (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ C) (Syn.subst σ E) := by simp [source]

theorem denominator_positive (B E : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    le one (leadingDenominator B E) := positive_product _ _ hB hE

theorem original_diagonal (F G H K : PR 2) (t x y u v A B C E : PTm n)
    (hs : Γ ⊢[PRAAx] source F G H K x y u v A B C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF F G) t (data x y)) (ap2 (nameF H K) t (data u v))
      (diagonalNumerator (leadingNumerator A B C E) (leadingDenominator B E) (num 16) t)
      (diagonalDenominator (leadingDenominator B E) t) := by
  let U := unit t
  let V := leadingDenominator B E
  let D := V*U
  have hB := hs.andE₁.andE₁
  have hE := hs.andE₁.andE₂
  have hU := unit_positive (Γ := Γ) t
  have hV : Γ ⊢[PRAAx] le one V := denominator_positive B E hB hE
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hV hU
  have leftEndpoint := GaussianNamedInverseRate.diagonal_rate F H x u A B t hB hs.andE₂.andE₂.andE₂.andE₁
  have rightEndpoint := GaussianNamedInverseRate.diagonal_rate G K y v C E t hE hs.andE₂.andE₂.andE₂.andE₂
  have left : Γ ⊢[PRAAx] distanceBounded (ap2 F t x) (ap2 H t u) ((A*U+two*B)*E) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hB hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,V,leadingDenominator]; ipra_ring)) leftEndpoint
  have right : Γ ⊢[PRAAx] distanceBounded (ap2 G t y) (ap2 K t v) ((C*U+two*E)*B) D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,V,leadingDenominator]; ipra_ring)) rightEndpoint
  have middle : Γ ⊢[PRAAx] distanceBounded (qsub (ap2 F t x) (ap2 G t y)) (qsub (ap2 H t u) (ap2 K t v))
      (leadingNumerator A B C E*U+num 4*V) D :=
    distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [leadingNumerator,V,leadingDenominator]; ipra_ring) (.eqRefl _)
      (difference_distance _ _ _ _ _ _ _ hD left right)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 (nameF F G) t (data x y)) (qsub (ap2 F t x) (ap2 G t y)) (num 6*V) D :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (sample_error F G x y t hs.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂)
  have last : Γ ⊢[PRAAx] distanceBounded (qsub (ap2 H t u) (ap2 K t v)) (ap2 (nameF H K) t (data u v)) (num 6*V) D :=
    distance_radius_mono _ _ _ _ _ _ hU hD (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (distance_symmetric _ _ _ _ hU (sample_error H K u v t hs.andE₂.andE₂.andE₁.andE₁ hs.andE₂.andE₂.andE₁.andE₂))
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,U,V]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD first (distance_triangle_same _ _ _ _ _ _ hD middle last))

theorem original_rate (F G H K : PR 2) (x y u v A B C E : PTm n)
    (hs : Γ ⊢[PRAAx] source F G H K x y u v A B C E) : Γ ⊢[PRAAx]
    independentRate (nameF F G) (nameF H K) (data x y) (data u v) (leadingNumerator A B C E) (leadingDenominator B E) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 16)
    (denominator_positive B E hs.andE₁.andE₁ hs.andE₁.andE₂)
    (name_regular F G x y hs.andE₂.andE₁.andE₁ hs.andE₂.andE₁.andE₂)
    (name_regular H K u v hs.andE₂.andE₂.andE₁.andE₁ hs.andE₂.andE₂.andE₁.andE₂)
  have ss : Γ.map Fm.shift ⊢[PRAAx] source F G H K (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v)
      (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hs.shift
  refine .allI ?_
  simpa only [diagonalEnvelope,GaussianNamedDifference.subst_data,subst_leadingNumerator,subst_leadingDenominator,PTm.subst_num,Syn.shift] using
    original_diagonal F G H K (var 0) (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v)
      (Syn.shift A) (Syn.shift B) (Syn.shift C) (Syn.shift E) ss

theorem original_observations (F G H K : PR 2) (p q x y u v A B C E : PTm n)
    (hs : Γ ⊢[PRAAx] source F G H K x y u v A B C E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF F G) p (data x y)) (ap2 (nameF H K) q (data u v))
      (rateNumerator (leadingNumerator A B C E) (leadingDenominator B E) p q)
      (rateDenominator (leadingDenominator B E) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate F G H K x y u v A B C E hs)

theorem self_rate (F : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) : Γ ⊢[PRAAx]
    independentRate F F x x zero one := by
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN F (Syn.shift (Syn.shift x)) := by simpa [Fm.shift,Syn.shift] using hf.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    distance_congr (.eqRefl _) (.eqRefl _)
      (by unfold rateNumerator; ipra_ring : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
        unit (var 1)+unit (var 0) ≐ rateNumerator zero one (var 1) (var 0))
      (by unfold rateDenominator; ipra_ring)
      (GaussianNameEquivalence.point_at F (Syn.shift (Syn.shift x)) (var 1) (var 0) ss)

theorem rate_parameters_congr (F G : PR 2) (x y A B A' B' : PTm n)
    (ha : Γ ⊢[PRAAx] A ≐ A') (hb : Γ ⊢[PRAAx] B ≐ B') (hr : Γ ⊢[PRAAx] independentRate F G x y A B) : Γ ⊢[PRAAx]
    independentRate F G x y A' B' := by
  simpa using Prf.eqSubst (independentRate F G (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    ![x,y,A,B] ![x,y,A',B'] (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact ha; exact hb) (by simpa using hr)

theorem same_right_rate (F H G : PR 2) (x u y A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H u) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hr : Γ ⊢[PRAAx] independentRate F H x u A B) : Γ ⊢[PRAAx]
    independentRate (nameF F G) (nameF H G) (data x y) (data u y) A B :=
  rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold leadingNumerator; ipra_ring) (by unfold leadingDenominator; ipra_ring)
    (original_rate F G H G x y u y A B zero one
      (.andI (.andI hB (le_refl one)) (.andI (.andI hf hg) (.andI (.andI hh hg) (.andI hr (self_rate G y hg))))))

theorem actual_original_named_difference_rate_closed (F G H K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source F G H K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate (nameF F G) (nameF H K) (data (var 0) (var 1)) (data (var 2) (var 3))
        (leadingNumerator (var 4) (var 5) (var 6) (var 7)) (leadingDenominator (var 5) (var 7))) :=
  closeUniv 8 (.impI (original_rate F G H K _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedDifferenceRate
