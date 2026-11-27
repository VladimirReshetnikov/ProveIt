import IPRADerivations.Analysis.Trigonometry.Arctangent.Extension.GaussianArctangentNamedExtension
import IPRADerivations.Analysis.Trigonometry.Arctangent.Inverse.GaussianArctangentInverseForward
import IPRADerivations.Analysis.Trigonometry.Arctangent.Comparisons.GaussianArctangentSlope
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# The range of the actual named arctangent extension

Every clipped parameter sample has a nonnegative forward prefix. On
its physical mesh it lies below the full prefix at the same clearing
index. One original refinement and the exact quarter-turn comparison
give the independent-precision upper bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentExtensionRange

open_ipra
open ComplexLogarithmRemainder (zeroCode eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (prefixValue source total)
open GaussianArctangentInverseForward (imaginaryOrder input)
open GaussianArctangentInverseSampler (ordinate)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentNamedExtension (nameF clock numerator denominator sample_at denominator_positive
  numerator_le name_regular)
open GaussianArctangentPartialQuadrature (observation clearing mesh mesh_positive finite_refinement)
open GaussianArctangentPartialUnitEndpoint (unit_endpoint_cross)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (point_at cross_at)
open GaussianNameRingLaws (zeroF zero_at)
open GaussianNamedRealOrderTransport (upperSlack precision remove_upper_slack)
open GaussianRationalHorner (qzero positive_product scalar_congr ofGaussian_represents zero_represents)
open GaussianRationalMetric (comparison_of_cleared)
open GaussianRootAlgebra (im_scale)
open RationalArithmetic (represents)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_of_radius upper_order_left upper_triangle
  positive_cancel)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem prefix_represents (j M L : PTm n) :
    Γ ⊢[PRAAx] represents (sndT (prefixValue j M L)) (ZT.ofNat (two*total j M L)) (fact L) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (ofGaussian_represents _ _ (GaussianRationalPolynomialExponential.factorial_positive L)).andE₂
  apply ZT.derive
  simp only [im_scale, imaginaryCode, eval_im_code, ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem zero_ordinate_represents : Γ ⊢[PRAAx] represents (sndT qzero) (ZT.ofNat zero) one := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (zero_represents one).andE₂
  apply ZT.derive
  simp [zeroCode, eval_im_code, ZT.toZ_ofNat]

private theorem partial_nonnegative (p A B : PTm n) :
    Γ ⊢[PRAAx] rationalLE (sndT qzero) (GaussianArctangentNamedSlope.ordinate p A B) := by
  let N := mesh p
  let M := B*N
  let L := clearing M
  let j := A*N
  have core := comparison_of_cleared (Γ := Γ) (sndT qzero) (sndT (prefixValue j M L)) zero (two*total j M L) one (fact L)
    (le_refl one) (GaussianRationalPolynomialExponential.factorial_positive L) zero_ordinate_represents
    (prefix_represents j M L) (le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le _))
  exact rationalLE_congr (.eqRefl _) (congrSnd (GaussianArctangentPartialQuadrature.sample_at p A B)).eqSymm core

private theorem total_monotone_to_end (j M L : PTm n)
    (hsrc : Γ ⊢[PRAAx] source M L) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] le (total j M L) (total M M L) := by
  let k := monus M j
  have e : Γ ⊢[PRAAx] j+k ≐ M := (eq_add_of_le hj).eqSymm
  have h := (GaussianArctangentSlope.finite_slope j k M L hsrc (le_congr e.eqSymm (.eqRefl _) (le_refl M))).andE₁
  have te : Γ ⊢[PRAAx] total (j+k) M L ≐ total M M L :=
    congrAp2 (sumF BaselQuadrature.Qb) e (.eqRefl _)
  have order : Γ ⊢[PRAAx] le (two*M*total j M L) (two*M*total M M L) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) te)
      (le_trans (le_add_left (two*M*total j M L) (k*fact L)) h)
  exact positive_cancel (positive_product _ _ (le_succ_self one) hsrc.andE₁) order

private theorem unit_observation_at_mesh (M : PTm n) :
    Γ ⊢[PRAAx] prefixValue M M (clearing M) ≐ observation one one M := by
  have e := Prf.eqCongr (Γ := Γ) (prefixValue (var 0) (var 0) (clearing (var 0)) : PTm 1)
    (σ := fun _ => M) (σ' := fun _ => one*M) (fun _ => (one_mul _).eqSymm)
  change Γ ⊢[PRAAx] prefixValue M M (clearing M) ≐ prefixValue (one*M) (one*M) (clearing (one*M))
  simpa only [GaussianArctangentExponentialPrefix.subst_prefixValue,
    GaussianArctangentPartialQuadrature.subst_clearing, Syn.subst_var] using e

private theorem partial_unit_upper (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] upper (GaussianArctangentNamedSlope.ordinate p A B)
      (GaussianArctangentNamedSlope.ordinate p one one) one (unit p) := by
  let N := mesh p
  let M := B*N
  let L := clearing M
  let j := A*N
  let a := sndT (prefixValue j M L)
  let b := sndT (prefixValue M M L)
  let c := sndT (observation one one N)
  have hN := mesh_positive (Γ := Γ) p
  have hM := positive_product B N hB hN
  have hL : Γ ⊢[PRAAx] source M L := .andI hM (le_refl _)
  have hF := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) L
  have hj : Γ ⊢[PRAAx] le j M := le_mul_mono hA (le_refl N)
  have hc : Γ ⊢[PRAAx] le (fact L*(two*total j M L)) ((two*total M M L)*fact L) :=
    le_congr (.eqRefl _) (mul_comm _ _)
      (le_mul_mono (le_refl (fact L)) (le_mul_mono (le_refl two) (total_monotone_to_end j M L hL hj)))
  have order : Γ ⊢[PRAAx] rationalLE a b :=
    comparison_of_cleared _ _ _ _ _ _ hF hF (prefix_represents j M L) (prefix_represents M M L) hc
  have refined := finite_refinement one one N B (le_refl one) (le_refl one) hN hB
  have radius := imaginary_coordinate_radius _ _ _ _ hN refined
  have toward : Γ ⊢[PRAAx] upper b c one (unit p) :=
    upper_mono _ _ (num 4) N one (unit p) hN
      (upper_congr (congrSnd (unit_observation_at_mesh M)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (upper_of_radius _ _ _ _ radius))
      (le_congr (.eqRefl _) (one_mul N).eqSymm (le_refl N))
  have bound := upper_order_left a b c one (unit p) order toward
  exact upper_congr (congrSnd (GaussianArctangentPartialQuadrature.sample_at p A B)).eqSymm
    (congrSnd (GaussianArctangentPartialQuadrature.sample_at p one one)).eqSymm (.eqRefl _) (.eqRefl _) bound

theorem lower_at (f : PR 2) (p q x z : PTm n) :
    Γ ⊢[PRAAx] upper (ordinate zeroF p z) (ordinate (nameF f) q x) (unit p+unit q) (unit p*unit q) :=
  upper_of_order _ _ _ _
    (rationalLE_congr (congrSnd (zero_at p z)).eqSymm (congrSnd (sample_at f q x)).eqSymm
      (partial_nonnegative (clock q) (numerator f q x) (denominator f q x)))

private theorem clock_units_order (p : PTm n) :
    Γ ⊢[PRAAx] le (unit p) (unit (clock p)) :=
  GaussianExponentialReference.unit_monotone (le_add_right p two)

private theorem upper_slack_at (f : PR 2) (p q t x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] upperSlack (ordinate (nameF f) p x) (ordinate quarterF q z) (unit p+unit q) (unit p*unit q) (num 3) t := by
  let P := unit p
  let Q := unit q
  let T := unit t
  let V := unit (clock t)
  let a := ordinate (nameF f) p x
  let b := ordinate (nameF f) t x
  let c := GaussianArctangentNamedSlope.ordinate (clock t) one one
  let d := ordinate quarterF q z
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have ht := unit_positive (Γ := Γ) t
  have hv := unit_positive (Γ := Γ) (clock t)
  have hT := clock_units_order (Γ := Γ) t
  have hpt := positive_product _ _ hp ht
  have hVQ := positive_product _ _ hv hq
  have hTQ := positive_product _ _ ht hq
  have left : Γ ⊢[PRAAx] upper a b (P+T) (P*T) :=
    upper_of_radius _ _ _ _
      (imaginary_coordinate_radius _ _ _ _ hpt (point_at (nameF f) x p t (name_regular f x hf)))
  have mid : Γ ⊢[PRAAx] upper b c one T :=
    upper_mono _ _ one V one T hv
      (upper_congr (congrSnd (sample_at f t x)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (partial_unit_upper (clock t) (numerator f t x) (denominator f t x) (denominator_positive f t x)
          (numerator_le f t x)))
      (le_congr (one_mul T).eqSymm (one_mul V).eqSymm hT)
  have right : Γ ⊢[PRAAx] upper c d (T+Q) (T*Q) :=
    RationalValueBounds.upper_two_errors_retime hVQ hT (le_refl Q)
      (upper_of_radius _ _ _ _
        (imaginary_coordinate_radius _ _ _ _ hVQ
          (cross_at GaussianArctangentPartialQuadrature.nameF quarterF
            (GaussianArctangentPartialQuadrature.data one one) z (clock t) q (unit_endpoint_cross z))))
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ left mid) right
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hpt ht) hTQ) joined
  exact le_of_eq_add (d := zero) (by dsimp only [P,Q,T]; ipra_ring)

theorem upper_at (f : PR 2) (p q x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] upper (ordinate (nameF f) p x) (ordinate quarterF q z) (unit p+unit q) (unit p*unit q) :=
  remove_upper_slack _ _ _ _ (num 3)
    (upper_slack_at f p q (precision (ordinate (nameF f) p x) (ordinate quarterF q z) (unit p*unit q) (num 3)) x z hf)

theorem inverse_input (f : PR 2) (x z : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] input (nameF f) x z := by
  refine .andI (name_regular f x hf) (.andI (.allI (.allI ?_)) (.allI (.allI ?_)))
  · exact lower_at f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z))
  · have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
      simpa [Fm.shift, Syn.shift] using hf.shift.shift
    exact upper_at f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z)) hs

theorem actual_arctangent_extension_inverse_input_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (pointCN f (var 0) ⟶ input (nameF f) (var 0) (var 1)) :=
  closeUniv 2 (.impI (inverse_input f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentExtensionRange
