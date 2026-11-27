import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalValueBounds
import IPRADerivations.Analysis.RationalArithmetic.RationalArithmetic
import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.PolynomialBisection
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHorner

/-!
# Native signed comparison from an actual rational upper budget

The actual scalar upper comparison is transferred to arbitrary supplied
integer/denominator representations. Only the two decoded positive
scalar denominators are cancelled. All signs and observation error
terms remain explicit; no order law for represented outputs is input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalUpperRepresentation

open_ipra
open RationalSupMetric (denominatorOf)
open RationalValueBounds (upper crossLeft)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem upper_from_representations (a b P Q C D : PTm n) (u v : ZT n)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents a u P)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b v Q)
    (h : Γ ⊢[PRAAx] upper a b C D) : Γ ⊢[PRAAx]
    zle (ZT.ofNat (D*Q)*u) (ZT.ofNat (D*P)*v+ZT.ofNat (C*P*Q)) := by
  let da := denominatorOf a
  let db := denominatorOf b
  let gap := monus (D*crossLeft b a+C*da*db) (D*crossLeft a b)
  have ea := ZT.toZ_eq ha
  have eb := ZT.toZ_eq hb
  have eg := natEq (eq_add_of_le h)
  apply PolynomialBisection.zle_scale_cancel (c := da*db)
    (GaussianRationalHorner.positive_product _ _ (RationalValueBounds.denominator_positive a) (RationalValueBounds.denominator_positive b))
  apply zle_of_toZ (gap*P*Q)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at ea eb
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [ZT.toZ] at ea eb ⊢
  dsimp only [gap,da,db]
  unfold upper crossLeft at eg
  unfold crossLeft
  ipra_simps
  linear_combination (𝔞 D*𝔞 Q*𝔞(denominatorOf b))*ea -
    (𝔞 D*𝔞 P*𝔞(denominatorOf a))*eb - (𝔞 P*𝔞 Q)*eg

theorem original_scalar_upper_to_native_signed_representation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((RationalArithmetic.represents (var 0) ⟨var 2,var 3⟩ (var 6) ⋏
        RationalArithmetic.represents (var 1) ⟨var 4,var 5⟩ (var 7) ⋏
        upper (var 0) (var 1) (var 8) (var 9)) ⟶
          zle (ZT.ofNat (var 9*var 7)*⟨var 2,var 3⟩)
            (ZT.ofNat (var 9*var 6)*⟨var 4,var 5⟩+ZT.ofNat (var 8*var 6*var 7))) :=
  closeUniv 10 (.impI (upper_from_representations _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.RationalUpperRepresentation
