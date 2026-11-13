import DiophantineConsistency.ModelThirteenRestoration
import DiophantineConsistency.ArithmeticThirteenSeed
import DiophantineConsistency.ArithmeticThirteenOuter
import DiophantineConsistency.ArithmeticPellFirstIndex
import FrontierBridge
import DiophantineConsistency.ModelThirteenCarrierPrelude
import DiophantineConsistency.ModelThirteenCoreInvariants
import DiophantineConsistency.ModelThirteenRankOrdinate
/-! # iPRA endpoint for the thirteen-variable 69/174 carrier form

In every model of `𝗜𝚺₁`, the 13-variable form `ThirteenCarrier.value69` and the
maintained 14-variable Carrier65 polynomial have zeros together:

* restoration (`ModelThirteenRestoration`) maps a positive 69-zero to a
  positive Carrier65 zero;
* completion (`complete`) maps a Carrier65 zero to a 69-zero. The outer data
  come from the internal soundness lemmas (`maintained_first_indices`,
  `ArithmeticThirteenOuter`), the strong seed from the internal pigeonhole
  (`ArithmeticThirteenSeed.strong_index`) and the auxiliary pair from
  `auxiliary_seed_of`; the independent coordinate `m` is solved exactly.

This is the internal counterpart of `CurrentCarrierArithmetic2011.positive_zero_65_iff_69`,
so the maintained all-model bridge transfers to the 69 form, giving native,
standard iPRA proofs of its no-zero sentence iff Foundation's
ZFC consistency predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ModelThirteenCarrier
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts FreshCarrierSpheres

/-! ### Completion in every model of `𝗜𝚺₁` -/

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticCarrierRadix2011 ArithmeticCurrentSentence2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Completion**: every model zero of the maintained equation gives a model
zero of the 13/69/174 form. -/
theorem complete (v : Fin 14 → V)
    (hz : InternalZero ObjectCurrentEquation2011.naturalExpression v) :
    ∃ u : Fin 13 → V, InternalZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) u := by
  set w : Fin 14 → V := fun j => v j + 1 with hwdef
  have hw : ∀ j, 0 < w j := fun j => lt_of_lt_of_le _root_.zero_lt_one le_add_self
  have hzw : ObjectCurrentEquation2011.expression.splitNatural.1.evalSemiring w =
      ObjectCurrentEquation2011.expression.splitNatural.2.evalSemiring w :=
    (ObjectCurrentEquation2011.internalZero_positiveShift ObjectCurrentEquation2011.expression v).mp hz
  have hpz : PositiveZero w := ⟨hw, hzw⟩
  -- ring-level zero and norms
  set x : Fin 14 → DiffRing V := fun j => ι (w j) with hxdef
  have hx : ∀ j, 0 < x j := fun j => ι_pos (hw j)
  have hz65 : Carrier65.value ringPorts x = 0 := by
    have := (internalZero_iff ObjectCurrentEquation2011.expression w).mp hzw
    rwa [ObjectCurrentEquation2011.expression, FreshModel106.evalRing_expressionAt65] at this
  have hb : (0 : DiffRing V) < ringPorts 0 := FreshModel106.beta_pos
  obtain ⟨hP, hQ, _, _, hW⟩ := (value65_zero_iff_norms modelFacts ringPorts x hb hx).mp hz65
  -- internal outer data
  obtain ⟨hβ, _, _⟩ := ArithmeticCarrierSoundness2011.current_bounds (V := V)
  have hβ0 : (0 : V) < (CurrentMasks2011.beta : V) := lt_of_lt_of_le (by norm_num) hβ
  have hcR := rank_ordinate v hz
  have hR4 := ArithmeticThirteenOuter.rank_mod_four w hpz
  have hqw := ArithmeticThirteenOuter.base_lt_shift w hpz
  obtain ⟨hαq, hFq⟩ := ArithmeticThirteenOuter.window_positive w hpz
  change (w 10 + w 11) * Y w + w 10 = ycoord (rank w) (X w * Y w + Y w) at hcR
  obtain ⟨eq_q, eq_Y, eq_E, eq_a, eq_c, eq_delta, eq_rank⟩ := core_invariants w hFq
  set aV := X w * Y w + Y w with haV
  set cV := (w 10 + w 11) * Y w + w 10 with hcV
  set RV := rank w with hRV
  have hc : cV = ycoord RV aV := hcR
  -- transport: G = b (z - 1) > 0 with b ∣ G
  have hbJ : 0 < (CurrentMasks2011.beta : V) * w 0 := mul_pos hβ0 (hw 0)
  have hG : 0 < transport ringPorts x := by
    have hC : 0 < (Carrier65.core ringPorts x).C := by
      change 0 < (Carrier65.core ringPorts x).q - x 1 - x 2
      rw [eq_q]
      have h1 := ι_lt_ι.mpr hαq
      rw [ArithmeticThirteenOuter.ι_tsub hFq.le] at h1
      linarith only [h1]
    have hC1 : 1 ≤ (Carrier65.core ringPorts x).C := model_discrete _ hC
    have hK : 0 ≤ ringPorts (V := V) 1 := by rw [port1]; exact ι_nonneg _
    have hwq : (Carrier65.core ringPorts x).q < x 8 := by rw [eq_q]; exact ι_lt_ι.mpr hqw
    have hFq' : x 1 < (Carrier65.core ringPorts x).q := by rw [eq_q]; exact ι_lt_ι.mpr hFq
    have hx8 : 0 ≤ x 8 := (hx 8).le
    have hmul : (ringPorts 1 + x 8) * 1 ≤ (ringPorts 1 + x 8) * (Carrier65.core ringPorts x).C :=
      mul_le_mul_of_nonneg_left hC1 (by linarith only [hK, hx8])
    unfold transport
    linarith only [hmul, hK, hwq, hFq']
  have hGb : transport ringPorts x = (ringPorts 0 * x 0) * (x 3 - 1) := by
    change (ringPorts 1 + x 8) * (Carrier65.core ringPorts x).C +
      ((Carrier65.core ringPorts x).q - x 1) - x 3 * (ringPorts 0 * x 0) = 1 at hW
    have hqshape : (Carrier65.core ringPorts x).q = ringPorts 0 * x 0 + 1 := rfl
    unfold transport
    rw [hqshape] at hW
    linear_combination hW
  -- fresh strong and auxiliary seeds
  have hcpos : 0 < cV := by
    have := ι_lt_ι.mp (show ι 0 < ι cV by rw [map_zero, ← eq_c]; exact c_pos modelFacts ringPorts x hb hx)
    exact this
  obtain ⟨t, j, _, hj, hyt⟩ := ArithmeticThirteenSeed.strong_index aV ((CurrentMasks2011.beta : V) * w 0) cV hbJ hcpos
  have hR3 : RV % 4 = 3 := hR4
  obtain ⟨T, u, y, hf, hT, hu, hy, hn, hyI, _, hlit, _, haux', hres⟩ :=
    ArithmeticThirteenSeed.auxiliary_seed_of aV RV t ((CurrentMasks2011.beta : V) * w 0 * j) hR3
      (mul_pos hbJ hj) (by rw [hyt, ← hc])
  rw [← hc] at hn hlit haux' hres
  -- ring-level fresh coordinates
  set fR := ι (xcoord t aV)
  set iR := ι j
  set TR := ι T
  set IV := delta aV * ((CurrentMasks2011.beta : V) * w 0 * j) * cV * cV with hIV
  have hstrongR : fR ^ 2 - (Carrier65.core ringPorts x).delta *
      (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) ^ 2 = 1 := by
    rw [eq_delta, eq_c, port0]
    have e := congrArg (ι : V →+* DiffRing V) hn
    simp only [map_add, map_mul, map_one] at e
    simp only [hxdef] at e ⊢
    linear_combination e
  have hVdef : ι u = fR ^ 2 * ((Carrier65.core ringPorts x).c * TR - (Carrier65.core ringPorts x).rank) -
      (Carrier65.core ringPorts x).c := by
    rw [eq_c, eq_rank]
    have e := congrArg (ι : V →+* DiffRing V) hlit
    simp only [map_add, map_mul] at e
    linear_combination -e
  -- the independent m
  obtain ⟨e4, he4⟩ : (4 * ((CurrentMasks2011.beta : V) * w 0)) ∣ y + 1 := by
    have h1 : 4 * IV * IV ∣ y + 1 := mod_eq_zero_iff_dvd.mp hres
    refine dvd_trans ⟨delta aV * j * cV * cV * IV, by ring⟩ h1
  set yR : DiffRing V := -ι y
  have hSR : (Carrier65.core ringPorts x).delta * (ringPorts 0 * x 0 * iR * (Carrier65.core ringPorts x).c ^ 2) = ι IV := by
    rw [eq_delta, eq_c, port0]; simp only [hxdef, map_mul, IV]; ring
  have hauxR : (ι IV) ^ 2 * ((ι u) ^ 2 - yR ^ 2) + yR ^ 2 = 1 := by
    have e := congrArg (ι : V →+* DiffRing V) haux'
    simp only [map_add, map_mul, map_one] at e
    simp only [yR]
    linear_combination e
  set bR := ringPorts 0 * x 0
  have hbR : bR = ι ((CurrentMasks2011.beta : V) * w 0) := by simp only [bR, port0, hxdef, map_mul]
  have hS2 : 2 ≤ ι IV := by
    rw [← hSR]
    have ha0 : 0 ≤ (Carrier65.core ringPorts x).a := by rw [eq_a]; exact ι_nonneg _
    have hδ3 : 3 ≤ (Carrier65.core ringPorts x).delta := by
      change 3 ≤ (Carrier65.core ringPorts x).a ^ 2 + (4 * (Carrier65.core ringPorts x).a + 3)
      linarith only [sq_nonneg (Carrier65.core ringPorts x).a, ha0]
    have hb1 : 1 ≤ bR := model_discrete _ (by rw [hbR]; exact ι_pos hbJ)
    have hi1 : 1 ≤ iR := model_discrete _ (ι_pos hj)
    have hc1 : 1 ≤ (Carrier65.core ringPorts x).c := model_discrete _ (c_pos modelFacts ringPorts x hb hx)
    have hc2 : 1 ≤ (Carrier65.core ringPorts x).c ^ 2 := one_le_pow₀ hc1
    have hbi : 1 ≤ bR * iR := one_le_mul_of_one_le_of_one_le hb1 hi1
    have hbic : 1 ≤ bR * iR * (Carrier65.core ringPorts x).c ^ 2 :=
      one_le_mul_of_one_le_of_one_le hbi hc2
    have := le_mul_of_one_le_right (by linarith only [hδ3] : (0 : DiffRing V) ≤ _) hbic
    linarith only [this, hδ3]
  obtain ⟨_, hsmall⟩ := ModelThirteenRestoration.auxiliary_estimates modelFacts hS2
    (show (ι IV) ^ 2 * (ι u) ^ 2 - ((ι IV) ^ 2 - 1) * yR ^ 2 = 1 by linear_combination hauxR)
  set gR := x 3 - 1
  have hgR : transport ringPorts x = bR * gR := hGb
  set mR : DiffRing V := -ι e4 + (1 + bR * (ι u) ^ 2) * gR
  have hym : yR = 1 + 4 * (bR * (mR - (ι u) ^ 2 * transport ringPorts x) - transport ringPorts x) := by
    have e := congrArg (ι : V →+* DiffRing V) he4
    simp only [map_add, map_mul, map_one, map_ofNat] at e
    simp only [yR, mR, hgR]
    rw [hbR]
    simp only [map_mul]
    linear_combination -e
  have hmpos : 0 < mR := by
    have hbpos : 0 < bR := by rw [hbR]; exact ι_pos hbJ
    have hsm : -2 * ι u < yR := by
      have := neg_abs_le yR
      have hu0 : |ι u| = ι u := abs_of_nonneg (ι_nonneg u)
      linarith only [this, hu0, hsmall]
    exact ModelThirteenRestoration.affine_carrier_pos modelFacts hbpos hG hsm hym
  -- the thirteen-coordinate ring zero
  have hzero : ThirteenCarrier.value69 ringPorts (replace x fR iR TR mR) = 0 := by
    apply replace_zero69 ringPorts x fR iR TR mR hP hQ hstrongR
    dsimp only
    rw [hSR, ← hVdef]
    have : 1 + 4 * (ringPorts 0 * x 0 * (mR - (ι u) ^ 2 * transport ringPorts x) - transport ringPorts x) = yR :=
      hym.symm
    rw [this]
    exact hauxR
  have hpos : ∀ k, 0 < replace x fR iR TR mR k :=
    replace_pos x hx fR iR TR mR (ι_pos hf) (ι_pos hj) (ι_pos hT) hmpos
  obtain ⟨u13, hu13⟩ := shifted_of_positive _ hpos
  refine ⟨u13, ?_⟩
  rw [internalZero_positiveShift, internalZero_iff, evalRing_expressionAt69]
  have hfun : (fun k => ι (u13 k + 1)) = replace x fR iR TR mR := funext fun k => (hu13 k).symm
  rw [hfun]
  exact hzero

end Model


/-! ### The 69 form has exactly the maintained zeros in every model, and its iPRA endpoints -/

section Bridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

theorem sameNoZero69 : HAExpressionNoZeroEquiv.SameNoZero
    (positiveShift (expressionAt69 CurrentWindowCarry2011.ports))
    ObjectCurrentEquation2011.naturalExpression := by
  intro V _ _
  constructor
  · intro h v hz
    obtain ⟨u, hu⟩ := complete v hz
    exact h u hu
  · intro h u hz
    have hz' := (internalZero_iff _ _).mp ((internalZero_positiveShift _ u).mp hz)
    rw [evalRing_expressionAt69] at hz'
    obtain ⟨w14, hpos, hval⟩ := ModelThirteenRestoration.restores_positive_zero69 modelFacts
      ringPorts (fun j => ι (u j + 1)) FreshModel106.beta_pos
      (fun j => ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self))
      ModelThirteenRestoration.modelSignedResidue hz'
    obtain ⟨v, hv⟩ := shifted_of_positive w14 hpos
    apply h v
    change InternalZero (positiveShift ObjectCurrentEquation2011.expression) v
    rw [internalZero_positiveShift, internalZero_iff, ObjectCurrentEquation2011.expression,
      FreshModel106.evalRing_expressionAt65]
    have hfun : (fun k => ι (v k + 1)) = w14 := funext fun k => (hv k).symm
    rw [hfun]
    exact hval

end Bridge

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem bridge69 : HAExpressionAssembly.PolynomialBridge
    (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) :=
  HAExpressionNoZeroEquiv.bridge _ _ sameNoZero69 HACurrentEquation2011.polynomialBridge

/-- **Native iPRA: the 13/69/174 form has no positive zero iff ZFC is consistent.** -/
theorem native_equivalence69 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge69

theorem standard_equivalence69 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift (expressionAt69 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence69


end DiophantineConsistency.ModelThirteenCarrier
