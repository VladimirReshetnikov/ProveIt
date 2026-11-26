import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasLogQuotient
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialDifferenceIdentity

/-!
# Recover the candidate value from the real Barnes logarithmic quotient

The actual exponential of the log quotient times the original Barnes
value recovers the candidate. Equivalence of quotients with the value at
one therefore yields proportionality with the candidate's value at one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasProportionality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHyperfactorial (barnesData barnes_regular)
open GaussianBarnesCanonicalPositiveLogarithm (default_source)
open GaussianBarnesCanonicalPositiveLogarithmRecurrence (exponential_barnes)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedExponentialDifferenceIdentity (ones_equivalent)
open GaussianNameRingLaws (negativeF negativeData oneF one_fast zeroF multiply_associative multiply_commutative
  multiply_one multiply_one_left)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "Log" => GaussianNamedPositiveLogarithm.nameF
local notation "logd" => GaussianNamedPositiveLogarithm.data
local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF
local notation "qd" => GaussianBarnesVignerasLogQuotient.data
local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "ereg" => GaussianRadiusExponentialName.name_regular

theorem exponential_clears (f : PR 2) (a b x P T : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (E (Q f)) G) f
      (multiplyData (E (Q f)) G (exponentialInputData (Q f) (qd a b x P)) (barnesData a b)) x := by
  let F := Log f
  let p := logd x P
  let l := ld a b (a+b)
  let q := qd a b x P
  let R := GaussianCompactLogarithmBounds.radius P T
  let S := U L l
  let u := ed R p
  let v := ed S (negativeData l)
  let w := ed S l
  let z := exponentialInputData (Q f) q
  have fr := GaussianNamedPositiveLogarithm.exponential_input f x P T hx
  have lr := exponential_input L l (GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ (default_source a b ha hb))
  have nr := GaussianExponentialInverse.negative_input L S l lr
  have qr := exponential_input (Q f) q (GaussianBarnesVignerasLogQuotient.regular f a b x P T ha hb hx)
  have addition := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent F (negativeF L) (Q f)
    R S (U (Q f) q) p (negativeData l) q fr nr qr (cross_refl _ _ qr.andE₁)
  have fu := ereg F R p fr
  have nv := ereg (negativeF L) S (negativeData l) nr
  have lw := ereg L S l lr
  have expanded := multiply_cross (E (Q f)) (multiplyF (E F) (E (negativeF L))) G (E L)
    z (multiplyData (E F) (E (negativeF L)) u v) (barnesData a b) w
    (ereg _ _ _ qr) (multiply_fast _ _ _ _ fu nv) (barnes_regular a b hb) lw
    (cross_symm _ _ _ _ addition) (cross_symm _ _ _ _ (exponential_barnes a b ha hb))
  have group := multiply_associative (E F) (E (negativeF L)) (E L) u v w fu nv lw
  have inverse := cross_trans _ _ _ _ _ _ (multiply_commutative (E (negativeF L)) (E L) v w nv lw)
    (cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse L S l lr) (ones_equivalent l u))
  have cancel := multiply_cross (E F) (E F) (multiplyF (E (negativeF L)) (E L)) oneF
    u u (multiplyData (E (negativeF L)) (E L) v w) u fu fu (multiply_fast _ _ _ _ nv lw) (one_fast _)
    (cross_refl _ _ fu) inverse
  exact cross_trans _ _ _ _ _ _ expanded (cross_trans _ _ _ _ _ _ group
    (cross_trans _ _ _ _ _ _ cancel (cross_trans _ _ _ _ _ _ (multiply_one _ _ fu)
      (GaussianNamedPositiveLogarithmExponential.original_recovery f x P T hx))))

private theorem barnes_at_one : Γ ⊢[PRAAx] crossEquivalent G oneF (barnesData (one : PTm n) one) zero := by
  let x := ld (one : PTm n) one (one+one)
  have h : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have r := GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ (default_source one one h h)
  have same := GaussianExponentialRadiusIndependence.independent_radii_proper L zeroF (U L x) one x zero
    (exponential_input _ _ r) (GaussianExponentialInverse.zero_input _ _)
    (GaussianBarnesCanonicalPositiveLogarithmRecurrence.normalization one h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_barnes one one h h))
    (cross_trans _ _ _ _ _ _ same (GaussianExponentialInverse.zero_exponential_cross one zero))

theorem proportional (f : PR 2) (a b x o P T M N : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T)
    (ho : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f o M N)
    (he : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (qd a b x P) (qd one one o M)) :
    Γ ⊢[PRAAx] crossEquivalent f (multiplyF f G) x (multiplyData f G o (barnesData a b)) := by
  let p := qd a b x P
  let q := qd one one o M
  let u := exponentialInputData (Q f) p
  let v := exponentialInputData (Q f) q
  let G1 := barnesData (one : PTm n) one
  let Gx := barnesData a b
  have h : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl _
  have ir := exponential_input _ _ (GaussianBarnesVignerasLogQuotient.regular f a b x P T ha hb hx)
  have is := exponential_input _ _ (GaussianBarnesVignerasLogQuotient.regular f one one o M N h h ho)
  have ur := ereg _ _ _ ir
  have vr := ereg _ _ _ is
  have atOne := exponential_clears f one one o M N h h ho
  have oneName : Γ ⊢[PRAAx] crossEquivalent G oneF G1 v :=
    cross_trans _ _ _ _ _ _ barnes_at_one (ones_equivalent (zero : PTm n) v)
  have reduce := multiply_cross (E (Q f)) (E (Q f)) G oneF v v G1 v vr vr (barnes_regular one one h) (one_fast v)
    (cross_refl _ _ vr) oneName
  have norm := cross_trans _ _ _ _ _ _ reduce (multiply_one _ _ vr)
  have fixed := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ norm) atOne
  have eq := GaussianExponentialRadiusIndependence.independent_radii_proper (Q f) (Q f) _ _ _ _ ir is he
  have scalar := cross_trans _ _ _ _ _ _ eq fixed
  have g := barnes_regular a b hb
  have product := multiply_cross (E (Q f)) f G G u o Gx Gx ur ho.andE₁ g g scalar (cross_refl _ _ g)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (exponential_clears f a b x P T ha hb hx)) product

theorem actual_Barnes_candidate_proportional_from_quotient_constancy_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let a := var 0
       let b := var 1
       let x := var 2
       let o := var 3
       let P := var 4
       let T := var 5
       let M := var 6
       let N := var 7
       ((le one a ⋏ le one b) ⋏
         (GaussianNamedPositiveLogarithm.source f x P T ⋏ GaussianNamedPositiveLogarithm.source f o M N)) ⟶
       crossEquivalent (Q f) (Q f) (qd a b x P) (qd one one o M) ⟶
       crossEquivalent f (multiplyF f G) x (multiplyData f G o (barnesData a b))) :=
  closeUniv 8 (.impI (.impI (proportional f _ _ _ _ _ _ _ _ Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

theorem normalized (f : PR 2) (a b x o P T M N : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T)
    (ho : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f o M N)
    (he : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (qd a b x P) (qd one one o M))
    (h₁ : Γ ⊢[PRAAx] crossEquivalent f oneF o o) : Γ ⊢[PRAAx] crossEquivalent f G x (barnesData a b) := by
  let v := barnesData a b
  have g := barnes_regular a b hb
  have unitValue := cross_trans _ _ _ _ _ _ h₁ (ones_equivalent o v)
  have moved := multiply_cross f oneF G G o v v v ho.andE₁ (one_fast _) g g unitValue (cross_refl _ _ g)
  exact cross_trans _ _ _ _ _ _ (proportional f a b x o P T M N ha hb hx ho he)
    (cross_trans _ _ _ _ _ _ moved (multiply_one_left _ _ g))

theorem actual_normalized_Barnes_candidate_from_quotient_constancy_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let a := var 0
       let b := var 1
       let x := var 2
       let o := var 3
       let P := var 4
       let T := var 5
       let M := var 6
       let N := var 7
       ((le one a ⋏ le one b) ⋏
         (GaussianNamedPositiveLogarithm.source f x P T ⋏ GaussianNamedPositiveLogarithm.source f o M N)) ⟶
       crossEquivalent (Q f) (Q f) (qd a b x P) (qd one one o M) ⟶
       crossEquivalent f oneF o o ⟶ crossEquivalent f G x (barnesData a b)) :=
  closeUniv 8 (.impI (.impI (.impI (normalized f _ _ _ _ _ _ _ _ Prf.hyp1.wk.andE₁.andE₁ Prf.hyp1.wk.andE₁.andE₂
    Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasProportionality
