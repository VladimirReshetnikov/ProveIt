import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift

/-!
# Constant names on the right half-plane

Every original signed rational right-half-plane input supplies its own
named chart, with inverse real margin equal to its original denominator.
The generic late-observation decoder then certifies the identical rational
code in its own signed coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneConstant

open_ipra
open ComplexLogarithmRemainder (oneCode re eval_re_code)
open GaussianCoefficientNameBounds (unit)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRightHalfPlane (marginPoint radius threshold)
open GaussianNamedRightHalfPlaneLift (source)
open GaussianRationalHorner (ofGaussian_represents)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper_of_order)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "signedSource" => GaussianRightHalfPlaneLogarithm.source

theorem constant_real_order (x y : PTm n) (h : Γ ⊢[PRAAx] rationalLE (fstT x) (fstT y)) :
    Γ ⊢[PRAAx] realOrder constantF constantF x y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let s (a : PTm n) := Syn.shift (Syn.shift a)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have sh : Δ ⊢[PRAAx] rationalLE (fstT (s x)) (fstT (s y)) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,RationalArgmin.subst_rationalLE,subst_fstT] using h.shift.shift
  have order := rationalLE_congr (congrFst (constant_at p (s x))).eqSymm
    (congrFst (constant_at q (s y))).eqSymm sh
  exact upper_of_order _ _ (unit p + unit q) (unit p * unit q) order

theorem source_of_real_order (q M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] rationalLE (fstT (marginPoint M)) (fstT q)) :
    Γ ⊢[PRAAx] source constantF q M (radius constantF q) :=
  .andI (.andI (constant_regular q) (.andI hM (constant_real_order (marginPoint M) q h))) (le_refl _)

theorem signed_rational_source (A B D neg : PTm n) (h : Γ ⊢[PRAAx] signedSource A D neg) :
    Γ ⊢[PRAAx] source constantF (argument A B D neg) D (radius constantF (argument A B D neg)) := by
  let z := native A B neg
  refine source_of_real_order (argument A B D neg) D h.andE₂ ?_
  apply RationalArithmetic.order_of_representations _ _ (re oneCode) (re z) D D
    (ofGaussian_represents oneCode D h.andE₂).andE₁ (ofGaussian_represents z D h.andE₂).andE₁ h.andE₂ h.andE₂
  apply zle_of_toZ (D * monus A one)
  have e := natEq (eq_add_of_le h.andE₁.andE₁)
  simp only [z,native,eval_re_code,GaussianRootAlgebra.re_one,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -𝔞 D * e

theorem signed_rational_certificate (A B D neg : PTm n) (h : Γ ⊢[PRAAx] signedSource A D neg) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlaneSigned.certificate (argument A B D neg)
      (radius constantF (argument A B D neg)) (two*D) := by
  let z := argument A B D neg
  let R := radius constantF z
  let k := threshold D
  have cert := GaussianNamedRightHalfPlaneLift.late_certificate constantF z k D R
    (signed_rational_source A B D neg h) (le_refl k)
  let C : Fm PTm 3 := GaussianNamedRightHalfPlaneSigned.certificate (var 0) (var 1) (var 2)
  have eq := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) C ![ap2 constantF k z,R,two*D] ![z,R,two*D]
    (fun i => by fin_cases i <;> first | exact constant_at k z | exact .eqRefl _)
  simpa [C] using eq (by simpa [C] using cert)

theorem actual_signed_rational_named_right_half_plane_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (signedSource (var 0) (var 2) (var 3) ⟶
        source constantF (argument (var 0) (var 1) (var 2) (var 3)) (var 2)
          (radius constantF (argument (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (signed_rational_source _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneConstant
