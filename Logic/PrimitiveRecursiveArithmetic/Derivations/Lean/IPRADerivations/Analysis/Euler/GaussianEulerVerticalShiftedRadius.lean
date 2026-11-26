import IPRADerivations.Analysis.Euler.GaussianEulerVerticalRealRadius
import IPRADerivations.Analysis.FiniteOperations.GaussianPositiveRadiusFiniteSum

/-!
# A signed observation shifted by its requested tolerance

The real observation of a nonnegative quantity can be negative at a coarse
query. Adding its own observation tolerance has a nonnegative numerator.
The same addition absorbs that tolerance from an upper comparison, with
the other rational allowance left in its original numerator and denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalShiftedRadius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerVerticalRealRadius (gap gap_identity denominator denominator_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open RationalGaussianEmbedding (scalarZero)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper)
open ComplexLogarithmRemainder (re)
open PolynomialBisection (slack)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def shiftedScalar (q U : PTm n) : PTm n := RationalArithmetic.add (fstT q) (fraction one U)

theorem shifted_represents (q U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (shiftedScalar q U) (ZT.ofNat (gap q U)) (denominator q U) := by
  have actual := RationalRepresentations.represents_add _ _ _ _ _ _ (raw_represents (Γ := Γ) q).andE₁ (fraction_represents one U hU)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) actual
  apply ZT.derive
  have e := natEq (gap_identity (Γ := Γ) q U h)
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination e

theorem upper_shift (s q U A B : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U)
    (hu : Γ ⊢[PRAAx] upper s (fstT q) (A*U+B) (B*U)) : Γ ⊢[PRAAx]
    upper s (shiftedScalar q U) A B := by
  let X := numeratorOf s
  let W := re (rawGaussian q)
  let P := denominatorOf s
  let D := rawDen q
  let L := left X D (B*U)
  let H := right W P D (A*U+B) (B*U)
  have hs := RationalRepresentations.represents_self (Γ := Γ) s
  have signed : Γ ⊢[PRAAx] zle L H := to_signed _ _ _ _ _ _ _ _ hs (raw_represents q).andE₁ hu
  apply from_signed _ _ X (ZT.ofNat (gap q U)) P (D*U) A B
    (RationalArgmin.denominator_positive s) (denominator_positive q U hU) hs (shifted_represents q U hU h)
  apply zle_of_toZ (slack L H)
  have e := natEq (gap_identity (Γ := Γ) q U h)
  have v := zle_toZ signed
  dsimp only [L,H,P,D,X,W,slack,left,right] at v ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at v ⊢
  simp only [ZT.toZ] at v ⊢
  ipra_simps
  linear_combination v+𝔞(P)*𝔞(B)*e

theorem enlarged_norm_after_shift (z r q U A B : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hr : Γ ⊢[PRAAx] GaussianPositiveRadiusFiniteSum.boundBy z r)
    (h : Γ ⊢[PRAAx] upper scalarZero (fstT q) one U)
    (hu : Γ ⊢[PRAAx] upper (fstT r) (fstT q) (A*U+B) (B*U)) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded z (gap q U*B+A*denominator q U) (denominator q U*B) :=
  GaussianPositiveRadiusFiniteSum.enlarge_radius z r (shiftedScalar q U) (gap q U) (denominator q U) A B hr
    (denominator_positive q U hU) hB (shifted_represents q U hU h) (upper_shift (fstT r) q U A B hU h hu)

theorem actual_enlarged_norm_after_signed_observation_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 3) ⋏ le one (var 5) ⋏ GaussianPositiveRadiusFiniteSum.boundBy (var 0) (var 1) ⋏
      upper scalarZero (fstT (var 2)) one (var 3) ⋏
      upper (fstT (var 1)) (fstT (var 2)) (var 4*var 3+var 5) (var 5*var 3)) ⟶
      GaussianRationalMetric.bounded (var 0)
        (gap (var 2) (var 3)*var 5+var 4*denominator (var 2) (var 3)) (denominator (var 2) (var 3)*var 5)) :=
  closeUniv 6 (.impI (enlarged_norm_after_shift _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalShiftedRadius
