import IPRADerivations.Analysis.RationalArithmetic.RationalIntegerNormalization
import IPRADerivations.Analysis.Optimization.RationalArgmin
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Literal normalized midpoint cancellation for Minkowski cell centers

The doubled center of the integer cell `a` at mesh `m` is `(2a+1)/m`.
Negation and midpoint below are actual gcd-normalized rational operations.
From the integer equation `a-b=mz`, the computed midpoint of one doubled
center and the negation of the other is literally the canonical code of `z`.
This permits equality replacement in an arbitrary membership formula.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters

open_ipra
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (denominator_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def centerNumerator (a : ZT n) : ZT n := ZT.ofNat two*a+ZT.ofNat one
def center (a : ZT n) (m : PTm n) : PTm n := normalize (centerNumerator a) m
def opposite (c : PTm n) : PTm n := normalize (-numeratorOf c) (denominatorOf c)
def midpointNumerator (c d : PTm n) : ZT n :=
  numeratorOf c*ZT.ofNat (denominatorOf d)+numeratorOf d*ZT.ofNat (denominatorOf c)
def midpointDenominator (c d : PTm n) : PTm n := two*denominatorOf c*denominatorOf d
def midpoint (c d : PTm n) : PTm n := normalize (midpointNumerator c d) (midpointDenominator c d)

ipra_subst centerNumerator
ipra_subst center
ipra_subst opposite
ipra_subst midpointNumerator
ipra_subst midpointDenominator
ipra_subst midpoint

theorem midpoint_denominator_positive (c d : PTm n) :
    Γ ⊢[PRAAx] le one (midpointDenominator c d) := by
  have twoPos : Γ ⊢[PRAAx] le one two := le_of_eq_add (d := one) (by ipra_ring)
  have product : Γ ⊢[PRAAx] le ((one*one)*one) (two*denominatorOf c*denominatorOf d) :=
    le_mul_mono (le_mul_mono twoPos (denominator_positive c)) (denominator_positive d)
  exact le_congr (by ipra_ring) (.eqRefl _) product

theorem center_value (a : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ZT.eq (centerNumerator a*ZT.ofNat (denominatorOf (center a m)))
      (numeratorOf (center a m)*ZT.ofNat m) := normalize_preserves_value _ _ hm

theorem opposite_value (c : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (-numeratorOf c*ZT.ofNat (denominatorOf (opposite c)))
      (numeratorOf (opposite c)*ZT.ofNat (denominatorOf c)) :=
  normalize_preserves_value _ _ (denominator_positive c)

/-- Positive natural cancellation in an integer equation is derived from
ordinary natural multiplication cancellation, without a domain assumption. -/
theorem integer_cancel (c : PTm n) (u v : ZT n) (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat c*u) (ZT.ofNat c*v)) : Γ ⊢[PRAAx] ZT.eq u v := by
  have value := ZT.toZ_eq h
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at value
  have scaled : Γ ⊢[PRAAx] c*(u.pos+v.neg) ≐ c*(v.pos+u.neg) := by
    apply deriveNat
    simp only [ZT.toZ] at value
    ipra_simps
    linear_combination value
  exact Combinatorics.BinomialIdentities.mul_cancel (positive_form hc) scaled

theorem midpoint_input_integer (a b z : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] ZT.eq (a-b) (ZT.ofNat m*z)) :
    Γ ⊢[PRAAx] ZT.eq (midpointNumerator (center a m) (opposite (center b m)))
      (ZT.ofNat (midpointDenominator (center a m) (opposite (center b m)))*z) := by
  have positive : Γ ⊢[PRAAx] le one (m*denominatorOf (center b m)) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hm (denominator_positive _))
  apply integer_cancel (m*denominatorOf (center b m)) _ _ positive
  ipra_lc [centerNumerator, midpointNumerator, midpointDenominator] -(𝔞(denominatorOf (center b m))*𝔞(denominatorOf (opposite (center b m))))*ZT.toZ_eq (center_value (Γ := Γ) a m hm)+ (𝔞(denominatorOf (center a m))*𝔞(denominatorOf (opposite (center b m))))*ZT.toZ_eq (center_value (Γ := Γ) b m hm)- (𝔞 m*𝔞(denominatorOf (center a m)))*ZT.toZ_eq (opposite_value (Γ := Γ) (center b m))+ (2*𝔞(denominatorOf (center a m))*𝔞(denominatorOf (center b m))*𝔞(denominatorOf (opposite (center b m))))*ZT.toZ_eq h

/-- This conclusion is equality of actual natural codes. -/
theorem midpoint_code_integer (a b z : ZT n) (m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] ZT.eq (a-b) (ZT.ofNat m*z)) :
    Γ ⊢[PRAAx] midpoint (center a m) (opposite (center b m)) ≐ integerCode z :=
  normalize_integer _ z _ (midpoint_denominator_positive _ _) (midpoint_input_integer a b z m hm h)

def centerF : PR 3 := PTm.toPR (center (⟨var 0,var 1⟩ : ZT 3) (var 2))
def oppositeF : PR 1 := PTm.toPR (opposite (var 0))
def midpointF : PR 2 := PTm.toPR (midpoint (var 0) (var 1))

theorem center_at (p q m : PTm n) :
    Γ ⊢[PRAAx] ap3 centerF p q m ≐ center (⟨p,q⟩ : ZT n) m := by
  have h := toPR_eq (Γ := Γ) (center (⟨var 0,var 1⟩ : ZT 3) (var 2)) ![p,q,m]
  simpa [centerF, ap3, ZT.subst] using h

theorem opposite_at (c : PTm n) : Γ ⊢[PRAAx] ap1 oppositeF c ≐ opposite c := by
  simpa [oppositeF, ap1] using toPR_eq (Γ := Γ) (opposite (var 0) : PTm 1) ![c]

theorem midpoint_at (c d : PTm n) : Γ ⊢[PRAAx] ap2 midpointF c d ≐ midpoint c d := by
  simpa [midpointF, ap2] using toPR_eq (Γ := Γ) (midpoint (var 0) (var 1) : PTm 2) ![c,d]

theorem center_programs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap3 centerF (var 0) (var 1) (var 2) ≐ center (⟨var 0,var 1⟩ : ZT 3) (var 2)) ⋏
        ((ap1 oppositeF (var 0) ≐ opposite (var 0)) ⋏
          (ap2 midpointF (var 0) (var 1) ≐ midpoint (var 0) (var 1)))) :=
  closeUniv 3 (.andI (center_at _ _ _) (.andI (opposite_at _) (midpoint_at _ _)))

/-- All signed coordinates and the mesh are object-language inputs. -/
theorem center_cancellation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 6) ⟶
        ZT.eq ((⟨var 0,var 1⟩ : ZT 7)-(⟨var 2,var 3⟩ : ZT 7))
          (ZT.ofNat (var 6)*(⟨var 4,var 5⟩ : ZT 7)) ⟶
        (midpoint (center (⟨var 0,var 1⟩ : ZT 7) (var 6))
          (opposite (center (⟨var 2,var 3⟩ : ZT 7) (var 6))) ≐ integerCode (⟨var 4,var 5⟩ : ZT 7))) :=
  closeUniv 7 (.impI (.impI (midpoint_code_integer _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenters
