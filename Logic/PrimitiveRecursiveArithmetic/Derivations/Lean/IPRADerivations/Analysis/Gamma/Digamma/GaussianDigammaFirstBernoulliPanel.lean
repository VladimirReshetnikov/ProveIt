import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanel

/-!
# The first literal Bernoulli panel for the digamma remainder

For H₁(t)=t(1-t), split the actual cubically weighted row into the
reciprocal, inverse-square, and inverse-cube terms. The panel offset,
mesh, and original centered Bernoulli sample all remain explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliPanel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open GaussianStirlingAllOrderFirstPanel (base first_sample)
open GaussianStirlingAllOrderKernel (row rowWeight offset_positive)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalAlgebra (multiply_congr)
open RationalArithmetic (add negative add_guard)
open RationalFiniteSum (canonical_equal)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalRepresentations (represents_add represents_negative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" x:max => Groth.ι (Q.mk Γ x)

def reciprocalPart (A B M k r : PTm n) : PTm n :=
  fraction (B*M) (base A B M k r)

def squarePart (A B M k r : PTm n) : PTm n :=
  let U := A+B*k
  let D := base A B M k r
  fraction ((two*U+B)*B*(M*M)) (D*D)

def cubePart (A B M k r : PTm n) : PTm n :=
  let U := A+B*k
  let D := base A B M k r
  fraction (U*(U+B)*B*(M*M*M)) (D*D*D)

def decomposed (A B M k r : PTm n) : PTm n :=
  add (add (negative (reciprocalPart A B M k r)) (squarePart A B M k r))
    (negative (cubePart A B M k r))

private theorem power_three (x : PTm n) :
    Γ ⊢[PRAAx] pw x (ConciseIPRA.PTm.succ two) ≐ x*x*x :=
  (pw_succ x two).eqTrans
    (congrMul ((pw_succ x one).eqTrans (congrMul (pw_one x) (.eqRefl x))) (.eqRefl x))

theorem literal_row (A B M k r : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] row 0 two A B M k r ≐ decomposed A B M k r := by
  let D := base A B M k r
  let P := B*M
  let U := A+B*k
  let X := (two*U+B)*B*(M*M)
  let Y := U*(U+B)*B*(M*M*M)
  have hD : Γ ⊢[PRAAx] le one D := le_trans (offset_positive A B M k hA hM) (le_add_right _ _)
  have hD2 := positive_product _ _ hD hD
  have hD3 := positive_product _ _ hD2 hD
  have hM2 := positive_product _ _ hM hM
  have v : Γ ⊢[PRAAx] rowWeight two A B M k r ≐ fraction (P*P*P) (D*D*D) :=
    fraction_congr (power_three P) (power_three D)
  refine (multiply_congr (first_sample r M hM hr) v).eqTrans ?_
  refine (fraction_multiply (r*monus M r) (M*M) (P*P*P) (D*D*D) hM2 hD3).eqTrans ?_
  have hE := positive_product _ _ hM2 hD3
  have hF := positive_product _ _ (positive_product _ _ hD hD2) hD3
  have p := represents_negative _ _ _ (fraction_represents P D hD)
  have q := fraction_represents (Γ := Γ) X (D*D) hD2
  have s := represents_negative _ _ _ (fraction_represents Y (D*D*D) hD3)
  have cert := represents_add _ _ _ _ _ _ (represents_add _ _ _ _ _ _ p q) s
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hE) (add_guard _ _)
    (fraction_represents _ _ hE) cert hE hF
  apply ZT.derive
  have e := natEq (eq_add_of_le hr)
  dsimp only [D,P,U,X,Y,base,GaussianStirlingAllOrderKernel.offset]
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -(𝔞 B)^3*𝔞 r*(𝔞 M)^3*
    ((𝔞 A+𝔞 B*𝔞 k)*𝔞 M+𝔞 B*𝔞 r)^6*e

theorem actual_first_digamma_Bernoulli_row_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 0) ⋏ (le one (var 2) ⋏ le (var 4) (var 2))) ⟶
        row 0 two (var 0) (var 1) (var 2) (var 3) (var 4) ≐
          decomposed (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (literal_row _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliPanel
