import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliBaseAgreement
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderPanelPositivePrefix
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsCaps
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference

/-!
# Positive floor for the higher digamma Bernoulli names

The original weighted prefix has a fixed positive rational floor
from the first unit panel. One mesh enlargement by eight admits
that floor on every cofinal digamma observation. Passing through
the certified approximation gives strict named positivity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliPositive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDigammaBernoulliBaseAgreement (agreement prefix_from_agreement)
open GaussianDigammaBernoulliName (nameF nameData radius requiredMesh name_regular)
open GaussianDigammaBernoulliRecurrence (prefixAt)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedStrictOrderDifference (trans_weak)
open GaussianRationalHorner (positive_product)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix subst_panelPrefix)
open GaussianStirlingAllOrderPanelPositive (panelFloor panel_floor_den_positive)
open GaussianStirlingAllOrderPanelPositivePrefix (prefix_positive_lower)
open GaussianStirlingAllOrderPanelPositiveRows (boundDenominator)
open GaussianStirlingGlobalBounds (steps)
open GaussianStirlingMultiplicativeBoundsCaps (strict_fractions)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)
open GaussianStirlingNames (source)
open RationalArgmin (rationalLE rationalLE_congr eq_le transitive)
open RationalValueBounds (upper upper_congr upper_of_radius upper_order_left)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "fraction" => GaussianPositiveRationalLogarithm.fraction

def floorDenominator (m : ℕ) (A B : PTm n) : PTm n :=
  num 8*boundDenominator m (num (2*m+2)) A B

def floorPoint (m : ℕ) (A B : PTm n) : PTm n := fraction one (floorDenominator m A B)

@[simp] theorem subst_floorPoint {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (A B : PTm n) :
    Syn.subst σ (floorPoint m A B) = floorPoint m (Syn.subst σ A) (Syn.subst σ B) := by
  simp [floorPoint,floorDenominator,boundDenominator,GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen,
    GaussianStirlingAllOrderCenteredBernoulli.denominator,pw,one]

theorem floor_den_positive (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (floorDenominator m A B) :=
  panel_floor_den_positive m (num (2*m+2)) A B hA

theorem prefix_floor (m : ℕ) (p A B S : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (fstT (floorPoint m A B)) (fstT (prefixAt m A B (S*num 8) p)) := by
  let q := 2*m+2
  let M := B*S
  let L := steps p
  let v := panelPrefix m q A B (B*(S*num 8)) L
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hs.andE₂ hS
  have hL : Γ ⊢[PRAAx] le one L := zero_lt_succ _
  have lo := prefix_positive_lower m q A B M L hs.andE₁ hs.andE₂ hM hL
  have eq : Γ ⊢[PRAAx] panelPrefix m q A B (M*num 8) L ≐ v := by
    simpa only [v,subst_panelPrefix,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr (Γ := Γ) (panelPrefix m q (Syn.shift A) (Syn.shift B) (var 0) (Syn.shift L))
        (σ := Syn.inst (M*num 8)) (σ' := Syn.inst (B*(S*num 8)))
        (fun i => Fin.cases (by dsimp [M]; ipra_ring) (fun j => .eqRefl (var j)) i)
  have floor : Γ ⊢[PRAAx] fstT (floorPoint m A B) ≐ panelFloor m (num q) A B :=
    fraction_real_part one _ (floor_den_positive m A B hs.andE₁)
  have last : Γ ⊢[PRAAx] fstT (prefixAt m A B (S*num 8) p) ≐ RationalArithmetic.recode v := fst_pair _ _
  have mid := rationalLE_congr floor.eqSymm eq lo
  exact rationalLE_congr (.eqRefl _) last.eqSymm
    (transitive mid (eq_le (RationalArithmetic.recode_equal v).eqSymm))

theorem approximate_lower (initial : PR 2) (demand : PR 3) (m : ℕ) (p A B x cost : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hx : Γ ⊢[PRAAx] pointCN initial x)
    (base : Γ ⊢[PRAAx] agreement initial demand A B x cost) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (floorPoint m A B)))
      (fstT (ap2 (nameF initial m) p (nameData m A B x))) (radius m B cost) (unit p) := by
  let K := requiredMesh m A B p (ap3 demand p A B)
  let S := K+one
  let Q := S*num 8
  have hS : Γ ⊢[PRAAx] le one S := le_add_left _ _
  have hp : Γ ⊢[PRAAx] le one Q := positive_product _ _ hS (by ipra_le 7)
  have hQ : Γ ⊢[PRAAx] le K Q := by dsimp only [Q,S]; ipra_le 7*Groth.ι (IPRA.Q.mk Γ K)+8
  have dist := prefix_from_agreement initial demand m A B Q p x cost hs hx base hp hQ
  have error := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive p) dist)
  exact upper_congr (congrFst (constant_at _ _)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (upper_order_left _ _ _ _ _ (prefix_floor m p A B S hs hS) error)

theorem named_lower (initial : PR 2) (demand : PR 3) (m : ℕ) (A B x cost : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hx : Γ ⊢[PRAAx] pointCN initial x)
    (base : Γ ⊢[PRAAx] agreement initial demand A B x cost) :
    Γ ⊢[PRAAx] realOrder constantF (nameF initial m) (floorPoint m A B) (nameData m A B x) := by
  apply order_from_envelope _ _ _ _ (radius m B cost) (constant_regular _) (name_regular initial m A B x hx)
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have hS : Δ ⊢[PRAAx] source (sh A) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have hX : Δ ⊢[PRAAx] pointCN initial (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hx.shift
  have hB : Δ ⊢[PRAAx] agreement initial demand (sh A) (sh B) (sh x) (sh cost) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using base.shift
  simpa [envelope,Δ,sh,Syn.shift] using approximate_lower initial demand m (var 0) (sh A) (sh B) (sh x) (sh cost) hS hX hB

theorem floor_strict (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] strictOrder constantF constantF (fraction zero one) (floorPoint m A B) := by
  let D := floorDenominator m A B
  have hD := floor_den_positive m A B hA
  have h : Γ ⊢[PRAAx] lt (D*zero) (one*one) := by
    change Γ ⊢[PRAAx] le (succ (D*zero)) (one*one)
    ipra_le 0
  exact .andI (constant_order _ _ (fractions_order zero one one D (le_refl one) hD (by ipra_le 1)))
    (strict_fractions zero one one D (le_refl one) hD h)

theorem named_positive (initial : PR 2) (demand : PR 3) (m : ℕ) (A B x cost : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hx : Γ ⊢[PRAAx] pointCN initial x)
    (base : Γ ⊢[PRAAx] agreement initial demand A B x cost) :
    Γ ⊢[PRAAx] strictOrder constantF (nameF initial m) (fraction zero one) (nameData m A B x) :=
  trans_weak _ _ _ _ _ _ (floor_strict m A B hs.andE₁) (named_lower initial demand m A B x cost hs hx base)

theorem actual_generic_digamma_Bernoulli_positivity_closed (initial : PR 2) (demand : PR 3) (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (source (var 0) (var 1) ⟶ pointCN initial (var 2) ⟶
      agreement initial demand (var 0) (var 1) (var 2) (var 3) ⟶
        strictOrder constantF (nameF initial m) (fraction zero one) (nameData m (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (named_positive initial demand m _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliPositive
