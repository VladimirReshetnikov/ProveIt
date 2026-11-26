import IPRADerivations.Analysis.Inequalities.RationalNonnegativeFloor
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionTiltedNodes
import IPRADerivations.Analysis.RationalArithmetic.RationalUpperRepresentation

/-!
# The exact adjacent-width error of tilted original floor cuts

Two genuine original quotient errors and one affine tilt increment give
A/B+2/M. The displacement depends on a single adjacent step, not on the
number of nodes. Both raw scalar inputs may be signed and unreduced.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalTiltedFloorWidth

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionTiltedNodes (tilt tiltNumerator tilt_represents)
open RationalNonnegativeFloor (index quantized quantized_below quantized_upper_error)
open RationalConvexSecants (nonnegative)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalValueBounds (upper radius)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def difference (a b : PTm n) : PTm n := RationalArithmetic.add b (RationalArithmetic.negative a)
def width (a b i A B M : PTm n) : PTm n := monus (index (tilt b (succ i) A B) M) (index (tilt a i A B) M)

@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (difference a b) = difference (Syn.subst σ a) (Syn.subst σ b) := by simp [difference]
@[simp] theorem subst_width {m : ℕ} (σ : Fin n → PTm m) (a b i A B M : PTm n) :
    Syn.subst σ (width a b i A B M) = width (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ i)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ M) := by simp [width]

theorem original_width_error (a b i A B M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hM : Γ ⊢[PRAAx] le one M) (ha : Γ ⊢[PRAAx] nonnegative (tilt a i A B))
    (hb : Γ ⊢[PRAAx] nonnegative (tilt b (succ i) A B))
    (hOrder : Γ ⊢[PRAAx] le (index (tilt a i A B) M) (index (tilt b (succ i) A B) M)) : Γ ⊢[PRAAx]
    radius (fraction (width a b i A B M) M) (difference a b) (A*M+two*B) (M*B) := by
  let D := denominatorOf a
  let E := denominatorOf b
  let H := index (tilt a i A B) M
  let I := index (tilt b (succ i) A B) M
  let U := tiltNumerator a i A B
  let V := tiltNumerator b (succ i) A B
  let L₁ := ZT.ofNat (M*M)*U
  let R₁ := ZT.ofNat (M*(D*B))*ZT.ofNat H+ZT.ofNat (one*(D*B)*M)
  let L₂ := ZT.ofNat (one*(E*B))*ZT.ofNat I
  let R₂ := ZT.ofNat (one*M)*V+ZT.ofNat (zero*M*(E*B))
  let L₃ := ZT.ofNat (one*(D*B))*ZT.ofNat H
  let R₃ := ZT.ofNat (one*M)*U+ZT.ofNat (zero*M*(D*B))
  let L₄ := ZT.ofNat (M*M)*V
  let R₄ := ZT.ofNat (M*(E*B))*ZT.ofNat I+ZT.ofNat (one*(E*B)*M)
  have hD : Γ ⊢[PRAAx] le one D := RationalArgmin.denominator_positive a
  have hE : Γ ⊢[PRAAx] le one E := RationalArgmin.denominator_positive b
  have rep := RationalRepresentations.represents_add (Γ := Γ) b (RationalArithmetic.negative a) _ _ E D
    (RationalRepresentations.represents_self b) (RationalRepresentations.represents_negative a _ D (RationalRepresentations.represents_self a))
  have aError : Γ ⊢[PRAAx] zle L₁ R₁ := RationalUpperRepresentation.upper_from_representations _ _ (D*B) M one M U (ZT.ofNat H)
    (tilt_represents a i A B hB) (fraction_represents H M hM) (quantized_upper_error _ _ ha hM)
  have bBelow : Γ ⊢[PRAAx] zle L₂ R₂ := RationalUpperRepresentation.upper_from_representations _ _ M (E*B) zero one (ZT.ofNat I) V
    (fraction_represents I M hM) (tilt_represents b (succ i) A B hB)
    (RationalValueBounds.upper_of_order _ _ _ _ (quantized_below _ _ hb hM))
  have aBelow : Γ ⊢[PRAAx] zle L₃ R₃ := RationalUpperRepresentation.upper_from_representations _ _ M (D*B) zero one (ZT.ofNat H) U
    (fraction_represents H M hM) (tilt_represents a i A B hB)
    (RationalValueBounds.upper_of_order _ _ _ _ (quantized_below _ _ ha hM))
  have bError : Γ ⊢[PRAAx] zle L₄ R₄ := RationalUpperRepresentation.upper_from_representations _ _ (E*B) M one M V (ZT.ofNat I)
    (tilt_represents b (succ i) A B hB) (fraction_represents I M hM) (quantized_upper_error _ _ hb hM)
  have order := natEq (eq_add_of_le hOrder)
  apply RationalValueBounds.radius_of_upper
  · apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ M (E*D) _ _ hM (positive_product _ _ hE hD)
      (fraction_represents _ M hM) rep
    apply zle_of_toZ (E*PolynomialBisection.slack L₁ R₁+D*M*PolynomialBisection.slack L₂ R₂+M*B*D*E)
    have ae := zle_toZ aError
    have bb := zle_toZ bBelow
    dsimp only [L₁,R₁,L₂,R₂,U,V,D,E,H,I] at ae bb ⊢
    simp only [tiltNumerator,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,PolynomialBisection.slack] at ae bb ⊢
    dsimp only [difference,width]
    simp only [ZT.toZ] at ae bb ⊢
    ipra_simps
    linear_combination 𝔞 (denominatorOf b)*ae+𝔞 (denominatorOf a)*𝔞 M*bb-𝔞 M*𝔞 B*𝔞 (denominatorOf a)*𝔞 (denominatorOf b)*order
  · apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ (E*D) M _ _ (positive_product _ _ hE hD) hM
      rep (fraction_represents _ M hM)
    apply zle_of_toZ (E*M*PolynomialBisection.slack L₃ R₃+D*PolynomialBisection.slack L₄ R₄+two*A*M*M*D*E+M*B*D*E)
    have ab := zle_toZ aBelow
    have be := zle_toZ bError
    dsimp only [L₃,R₃,L₄,R₄,U,V,D,E,H,I] at ab be ⊢
    simp only [tiltNumerator,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,PolynomialBisection.slack] at ab be ⊢
    dsimp only [difference,width]
    simp only [ZT.toZ] at ab be ⊢
    ipra_simps
    linear_combination 𝔞 (denominatorOf b)*𝔞 M*ab+𝔞 (denominatorOf a)*be+𝔞 M*𝔞 B*𝔞 (denominatorOf a)*𝔞 (denominatorOf b)*order


theorem actual_adjacent_tilted_floor_width_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 4) ⋏ (le one (var 5) ⋏
      (nonnegative (tilt (var 0) (var 2) (var 3) (var 4)) ⋏
        (nonnegative (tilt (var 1) (succ (var 2)) (var 3) (var 4)) ⋏
          le (index (tilt (var 0) (var 2) (var 3) (var 4)) (var 5))
            (index (tilt (var 1) (succ (var 2)) (var 3) (var 4)) (var 5)))))) ⟶
      radius (fraction (width (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 5))
        (difference (var 0) (var 1)) (var 3*var 5+two*var 4) (var 5*var 4)) :=
  closeUniv 6 (.impI (original_width_error _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.RationalTiltedFloorWidth
