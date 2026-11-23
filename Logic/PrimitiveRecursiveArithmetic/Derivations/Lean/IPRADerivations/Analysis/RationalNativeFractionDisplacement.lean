import IPRADerivations.Analysis.GaussianEuclideanDistanceName

/-!
# Clearing displacement bounds between normalized native fractions

The absolute bound on the actual normalized scalar codes reflects back
to the absolute difference of the two native cross products. This
lets endpoint estimates be used with affine panels without any
assumption that their rational codes share a denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalNativeFractionDisplacement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalSupMetric (denominatorOf numeratorOf)
open RationalValueBounds (upper radius crossLeft positive_cancel upper_of_radius radius_symmetric)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul ad_le_of)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem native_upper (c d a E b H A B : PTm n)
    (hc : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat a) E)
    (hd : Γ ⊢[PRAAx] RationalArithmetic.represents d (ZT.ofNat b) H)
    (h : Γ ⊢[PRAAx] upper c d A B) : Γ ⊢[PRAAx] le (B*(H*a)) (B*(E*b)+A*(E*H)) := by
  let U := denominatorOf c
  let V := denominatorOf d
  let gap := monus (B*crossLeft d c+A*U*V) (B*crossLeft c d)
  have ec := ZT.toZ_eq hc
  have ed := ZT.toZ_eq hd
  have bound := natEq (eq_add_of_le h)
  apply positive_cancel (c := U*V)
    (positive_product _ _ (RationalValueBounds.denominator_positive c) (RationalValueBounds.denominator_positive d))
  refine le_of_eq_add (d := E*H*gap) ?_
  apply deriveNat
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at ec ed
  simp only [ZT.toZ] at ec ed
  dsimp [gap,U,V]
  unfold crossLeft at bound ⊢
  ipra_simps
  linear_combination 𝔞(E)*𝔞(denominatorOf c)*𝔞(B)*ed-𝔞(H)*𝔞(denominatorOf d)*𝔞(B)*ec+𝔞(E)*𝔞(H)*bound

theorem native_absolute (a E b H A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] radius (fraction a E) (fraction b H) A B) :
    Γ ⊢[PRAAx] le (B*ad (H*a) (E*b)) (A*(E*H)) := by
  have ha := fraction_represents a E hE
  have hb := fraction_represents b H hH
  have forward := native_upper _ _ a E b H A B ha hb (upper_of_radius _ _ _ _ h)
  have backward := native_upper _ _ b H a E A B hb ha (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ h))
  have corrected := le_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] B*(H*a)+A*(H*E) ≐ B*(H*a)+A*(E*H)) backward
  exact le_congr (ad_mul B (H*a) (E*b)) (.eqRefl _) (ad_le_of forward corrected)

theorem actual_normalized_rational_endpoint_displacement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 1) ⋏ (le one (var 3) ⋏ radius (fraction (var 0) (var 1)) (fraction (var 2) (var 3)) (var 4) (var 5))) ⟶
      le (var 5*ad (var 3*var 0) (var 1*var 2)) (var 4*(var 1*var 3))) :=
  closeUniv 6 (.impI (native_absolute _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.RationalNativeFractionDisplacement
