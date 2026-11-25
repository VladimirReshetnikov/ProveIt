import IPRADerivations.Analysis.GaussianStirlingAllOrderImproperName
import IPRADerivations.Analysis.GaussianStirlingAllOrderPanelPositivePrefix
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsCaps
import IPRADerivations.Analysis.GaussianNamedStrictOrderDifference

/-!
# Strict positivity of the actual periodic Bernoulli integral

The lower witness comes from an explicit positive block in the
original first panel. Enlarging each certified mesh by eight
preserves its approximation rate. The same positive rational
floor gives strict named positivity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperPositive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedRealOrderTransport (transport)
open GaussianNamedStrictOrderDifference (trans_weak)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGlobalBounds (steps)
open GaussianStirlingNames (source)
open GaussianStirlingAllOrderImproperName (original_improper_cross)
open GaussianStirlingAllOrderPanelPartsBinding (requiredMesh prefixAt radius actual_prefix_distance)
open GaussianStirlingAllOrderPanelPartsNames (nameF nameData name_regular)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix subst_panelPrefix)
open GaussianStirlingAllOrderPanelPositive (panelFloor panel_floor_den_positive)
open GaussianStirlingAllOrderPanelPositivePrefix (prefix_positive_lower)
open GaussianStirlingAllOrderPanelPositiveRows (boundDenominator)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open RationalArgmin (rationalLE rationalLE_congr eq_le transitive)
open RationalValueBounds (upper upper_congr upper_of_radius upper_of_order upper_order_left)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "fraction" => GaussianPositiveRationalLogarithm.fraction

def floorPoint (m : ℕ) (A B : PTm n) : PTm n :=
  fraction one (num 8*boundDenominator m (num (2*m+1)) A B)

@[simp] theorem subst_floorPoint {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (floorPoint m A B) = floorPoint m (Syn.subst σ A) (Syn.subst σ B) := by
  simp [floorPoint,boundDenominator,GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen,
    GaussianStirlingAllOrderCenteredBernoulli.denominator,pw,one]

private theorem mesh_positive (m : ℕ) (A B p : PTm n) : Γ ⊢[PRAAx] le one (requiredMesh m A B p) := by
  induction m with
  | zero => exact unit_positive _
  | succ m ih => exact le_trans ih (le_add_right _ _)

theorem prefix_floor (m : ℕ) (p A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] rationalLE (fstT (floorPoint m A B))
      (fstT (prefixAt m A B (requiredMesh m A B p*num 8) p)) := by
  let q := 2*m+1
  let K := requiredMesh m A B p
  let S := B*K
  let Q := K*num 8
  let L := steps p
  let a := panelPrefix m q A B (B*Q) L
  have hS : Γ ⊢[PRAAx] le one S := positive_product _ _ hs.andE₂ (mesh_positive m A B p)
  have hL : Γ ⊢[PRAAx] le one L := zero_lt_succ _
  have lo := prefix_positive_lower m q A B S L hs.andE₁ hs.andE₂ hS hL
  have eq : Γ ⊢[PRAAx] panelPrefix m q A B (S*num 8) L ≐ a := by
    simpa only [a,subst_panelPrefix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr (Γ := Γ) (panelPrefix m q (Syn.shift A) (Syn.shift B) (var 0) (Syn.shift L))
        (σ := Syn.inst (S*num 8)) (σ' := Syn.inst (B*Q))
        (fun i => Fin.cases (by dsimp [S,Q]; ipra_ring) (fun j => .eqRefl (var j)) i)
  have d := panel_floor_den_positive m (num q) A B hs.andE₁
  have floor : Γ ⊢[PRAAx] fstT (floorPoint m A B) ≐ panelFloor m (num q) A B :=
    fraction_real_part one _ d
  have last : Γ ⊢[PRAAx] fstT (prefixAt m A B Q p) ≐ RationalArithmetic.recode a := fst_pair _ _
  have mid := rationalLE_congr floor.eqSymm eq lo
  exact rationalLE_congr (.eqRefl _) last.eqSymm
    (transitive mid (eq_le (RationalArithmetic.recode_equal a).eqSymm))

theorem approximate_lower (m : ℕ) (p A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (floorPoint m A B)))
      (fstT (ap2 (nameF m) p (nameData m A B x))) (radius m B) (unit p) := by
  let K := requiredMesh m A B p
  let Q := K*num 8
  have hQ : Γ ⊢[PRAAx] le K Q := by dsimp [Q]; ipra_le 7*Groth.ι (IPRA.Q.mk Γ K)
  have dist := actual_prefix_distance m A B Q p x hs hQ
  have error := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive p) dist)
  exact upper_congr (congrFst (constant_at _ _)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_order_left _ _ _ _ _ (prefix_floor m p A B hs) error)

theorem named_lower (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] realOrder constantF (nameF m) (floorPoint m A B) (nameData m A B x) := by
  apply order_from_envelope _ _ _ _ (radius m B) (constant_regular _) (name_regular m A B x hs)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let c := Syn.shift x
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift
  simpa [envelope,a,b,c,Δ,Syn.shift] using approximate_lower m (var 0) a b c h

theorem original_improper_lower (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] realOrder constantF (GaussianStirlingAllOrderImproperName.nameF m) (floorPoint m A B)
      (GaussianStirlingAllOrderImproperName.data m A B) :=
  transport _ _ _ _ _ _ _ _ (cross_refl _ _ (constant_regular _))
    (cross_symm _ _ _ _ (original_improper_cross m A B x hs)) (named_lower m A B x hs)

private theorem floor_strict (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] strictOrder constantF constantF (fraction zero one) (floorPoint m A B) := by
  let D := num 8*boundDenominator m (num (2*m+1)) A B
  have hD := panel_floor_den_positive m (num (2*m+1)) A B hA
  have h : Γ ⊢[PRAAx] lt (D*zero) (one*one) := by
    change Γ ⊢[PRAAx] le (ConciseIPRA.PTm.succ (D*zero)) (one*one)
    ipra_le 0
  refine .andI ?_ (strict_fractions zero one one D (le_refl one) hD h)
  apply order_from_envelope _ _ _ _ zero (constant_regular _) (constant_regular _)
  refine .allI ?_
  let a := Syn.shift A
  let b := Syn.shift B
  let Δ := Γ.map Fm.shift
  have ha : Δ ⊢[PRAAx] le one a := by simpa [Δ,a,Fm.shift,Syn.shift] using hA.shift
  let E := num 8*boundDenominator m (num (2*m+1)) a b
  have hh := panel_floor_den_positive m (num (2*m+1)) a b ha
  have e : Δ ⊢[PRAAx] rationalLE (fstT (fraction zero one)) (fstT (floorPoint m a b)) :=
    rationalLE_congr (fraction_real_part _ _ (le_refl one)).eqSymm (fraction_real_part one E hh).eqSymm
      (GaussianEuclideanDistanceName.fraction_order zero one one E (le_refl _) hh (by ipra_le 1))
  have ho := upper_of_order _ _ zero (unit (var 0)) e
  simpa [envelope,Δ,a,b,Syn.shift,one] using
    upper_congr (congrFst (constant_at _ _)).eqSymm (congrFst (constant_at _ _)).eqSymm (.eqRefl _) (.eqRefl _) ho

theorem original_improper_positive (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF (GaussianStirlingAllOrderImproperName.nameF m) (fraction zero one)
      (GaussianStirlingAllOrderImproperName.data m A B) :=
  trans_weak _ _ _ _ _ _ (floor_strict m A B hs.andE₁) (original_improper_lower m A B x hs)

theorem actual_original_all_order_periodic_improper_positive_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (source (var 0) (var 1) ⟶
      strictOrder constantF (GaussianStirlingAllOrderImproperName.nameF m) (fraction zero one)
        (GaussianStirlingAllOrderImproperName.data m (var 0) (var 1))) :=
  closeUniv 3 (.impI (original_improper_positive m _ _ (var 2) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderImproperPositive
