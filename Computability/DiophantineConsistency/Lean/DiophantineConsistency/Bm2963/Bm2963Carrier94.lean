import DiophantineConsistency.ArithmeticCarrier94Extraction
import DiophantineConsistency.Carrier94Value
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.Bm2963.Bm2963Soundness
import DiophantineConsistency.Bm2963.Bm2963Carrier118

/-! # iPRA endpoints for package 188's ordinary 14/67/94 companion

Package 188's `native/q67_d94.json` (14 positive unknowns, 67 operations, exact
degree 94) is `Carrier94Syntax.expressionAt94 p` at the block-mask2963 ports
`p = fun j => (Bm2963Ports.ports j : ℤ)`. This is the counterpart of the 2011-port
chain `ArithmeticCarrier94Soundness` + `ModelCarrier94`. In every model of `𝗜𝚺₁`:

* **soundness** (`halts_of_zero94`): a positive zero satisfies the five ordinary
  equations (the port-generic `ArithmeticCarrier94Extraction.expressionAt94_equations`).
  The power comes from the port-generic `ArithmeticCarrier94Soundness.ordinary_power`,
  the radix from `Bm2963CarrierRadix.radix_of_power`, the population lower bound from
  `ArithmeticCarrier94Indices.ordinary_first_indices` (a verbatim copy of
  `Bm2963HalfBinomial.population_of_equations` with that one call changed), and the
  window from the transport equation alone (`Bm2963WindowInterface.window_of_equations`).
  The block-mask2963 cell decoding then makes the machine halt;
* **completeness** (`zero94_of_zero`): a zero of the Carrier65 polynomial at the same
  ports gives a zero of this one, replacing only the strong multiplier `i` by
  `Delta i` (`Carrier94Value.zero94_of_maintained`, port-generic).

The Carrier65 bridge at these ports is the closed block-mask2963 calibration
(`Bm2963Carrier118.currentBridge`). The binding of the Lean syntax to the JSON is the
finite check `research/block-mask2963-calibration/tools/check_forms.py`. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Bm2963Carrier94
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrier94Soundness (OrdinaryEquations ordinary_power)
open Bm2963Carrier118 (intPorts)
attribute [local irreducible] Bm2963Ports.ports Bm2963Kernel.K Bm2963MaskData.radix
  Bm2963MaskData.beta Bm2963MaskData.lowPort Bm2963MaskData.highPort

/-- Package 188's ordinary companion: the 67/94 syntax at the block-mask2963 ports. -/
def expression94 : Expr (Fin 14) := Carrier94Syntax.expressionAt94 intPorts

/-- Its single positive shift. -/
def naturalExpression94 : Expr (Fin 14) := ObjectCurrentEquation2011.positiveShift expression94

/-! ### Soundness: the five ordinary equations make the machine halt -/

section Soundness
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section
open Bm2963CarrierRadix

/-- The five ordinary equations of a positive zero, at the block-mask2963 ports. -/
theorem ordinary_equations (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : expression94.splitNatural.1.evalSemiring v =
      expression94.splitNatural.2.evalSemiring v) :
    OrdinaryEquations (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V)
      (Bm2963MaskData.lowPort:V) ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V) v := by
  obtain ⟨hb, hl, hh⟩ := Bm2963Ports.current_bounds (V:=V)
  have h := ArithmeticCarrier94Extraction.expressionAt94_equations Bm2963Ports.ports v
    (by rw [Bm2963Ports.ports_zero]; exact lt_of_lt_of_le (by simp) hb)
    (by rw [Bm2963Ports.ports_zero, Bm2963Ports.ports_two]; exact hl)
    (by rw [Bm2963Ports.ports_zero, Bm2963Ports.ports_three]; exact hh) hv hz
  rwa [Bm2963Ports.ports_zero, Bm2963Ports.ports_one, Bm2963Ports.ports_two,
    Bm2963Ports.ports_three] at h

theorem power_of_ordinary (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (he : OrdinaryEquations (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V)
      (Bm2963MaskData.lowPort:V) ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V) v) :
    X v = Exp.exp (rank v) ∧ Exponential (rank v) (X v) ∧ Exp.exp (rank v) < Y v := by
  obtain ⟨hb, hl, hh⟩ := Bm2963Ports.current_bounds (V:=V)
  obtain ⟨ht, hn, hm, hf, hu⟩ := he
  exact ordinary_power
    (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V) (Bm2963MaskData.lowPort:V)
    ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) hb hl hh
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
    (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu

/-- The transport equation is the first ordinary equation. -/
theorem transport_of_ordinary (v : Fin 14 → V)
    (he : OrdinaryEquations (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V)
      (Bm2963MaskData.lowPort:V) ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V) v) :
    Bm2963WindowInterface.Transport v := by
  obtain ⟨ht, -, -, -, -⟩ := he
  exact ht

end

section
open ArithmeticPellRecurrence ArithmeticBinaryPopulation ArithmeticHalfBinomial
  Bm2963Ports Bm2963CarrierRadix

/-- `Bm2963HalfBinomial.population_of_equations` with the ordinary strong norm: only
the `first_indices` call changes. -/
theorem population_of_ordinary (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (he : OrdinaryEquations (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V)
      (Bm2963MaskData.lowPort:V) ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V) v)
    (hp : X v = Exp.exp (rank v)) (h : V) (hq : q v = Exp.exp h) :
    3*h+2 ≤ population (rank v) := by
  obtain ⟨hb, hl, hh⟩ := current_bounds (V:=V)
  have hb0 : (0:V) < (Bm2963MaskData.beta:V) := lt_of_lt_of_le (by simp) hb
  obtain ⟨ht, hn, hm, hf, hu⟩ := he
  obtain ⟨n, _, hn5, _, hnR, _, hk, _, hc, _, _, _, _⟩ :=
    ArithmeticCarrier94Indices.ordinary_first_indices
    (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V) (Bm2963MaskData.lowPort:V)
    ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V)
    (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
    (v 10) (v 11) (v 12) (v 13) hb0 hl hh
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4) (hv 5) (hv 6) (hv 7) (hv 8) (hv 9)
    (hv 10) (hv 11) (hv 12) (hv 13) ht hn hm hf hu
  change v 10+v 11=2*ycoord n (2*(X v*Y v*Y v-1)+1) at hk
  change (v 10+v 11)*Y v+v 10=ycoord (rank v) (X v*Y v+Y v) at hc
  change 2*n=rank v+1 at hnR
  obtain ⟨r, hrn, hr4, hR⟩ := half_index_of_ge_five n (rank v) hn5 hnR
  have hXe : X v = Exp.exp (2*r+1) := by rw [hp, hR]
  have hY : 1 ≤ Y v := by
    unfold Y
    have hq1 : 1 ≤ q v := by unfold q; exact le_add_of_nonneg_left (by simp)
    exact one_le_mul (pos_iff_one_le.mp (hv 7)) (by
      simpa only [show (q v)^3=q v*q v*q v by ring] using one_le_mul (one_le_mul hq1 hq1) hq1)
  have hck : ycoord (2*r+1) (Y v*(X v+1)) = 2*ycoord (r+1) (2*(X v*Y v*Y v-1)+1)*Y v+v 10 := by
    rw [show Y v*(X v+1)=X v*Y v+Y v by ring, ←hR, ←hc, hrn, ←hk]
  obtain ⟨w, hw⟩ := half_binomial (X v) (Y v) r (v 10) (v 11) hr4 hXe hY hck
    (by rw [hrn, ←hk]) (hv 10) (hv 11)
  have hYq : Exp.exp (3*h) ∣ Y v := by
    refine ⟨v 7, ?_⟩
    unfold Y
    rw [hq, show 3*h=h+h+h by ring, exp_add, exp_add]
    ring
  have h3 := Bm2963HalfBinomial.three_h_lt_rank v hv h hq
  rw [hR] at h3 ⊢
  exact population_lower (X v) (Y v) r w h hXe hw hYq h3

end

section
open SetTheory.BusyBeaver.ZFC ArithmeticCantor Bm2963CarrierRadix

/-- **Positive coordinates satisfying the five ordinary equations at the
block-mask2963 ports make the machine halt.** -/
theorem ordinary_halts (u : Fin 14 → V) (hu : ∀ j, 0 < u j)
    (he : OrdinaryEquations (Bm2963MaskData.beta:V) (Bm2963Kernel.K:V)
      (Bm2963MaskData.lowPort:V) ((Bm2963MaskData.highPort+Bm2963MaskData.beta:ℕ):V) u) :
    ∃ t : V, first (ArithmeticMachineRun215.run t) = 0 := by
  have hp := power_of_ordinary u hu he
  have hr := radix_of_power u (hu 0) hp.1
  obtain ⟨N, -, hw⟩ := Bm2963WindowInterface.window_of_equations u hu
    (transport_of_ordinary u he) hr
    (fun N hqN => population_of_ordinary u hu he hp.1 _ hqN)
  obtain ⟨t, -, ht⟩ := Bm2963CellWindow.window_halts hw
  exact ⟨t, ht⟩

end

end Soundness

/-! ### Soundness and completeness in every model, and the iPRA endpoints -/

section Model
open AdaptiveEquationSyntax2011 ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic
open SetTheory.BusyBeaver.ZFC
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- **Soundness.** A natural zero of the 67/94 equation makes the machine halt. -/
theorem halts_of_zero94 (w : Fin 14 → V) (hz : InternalZero naturalExpression94 w) :
    ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t) = 0 := by
  have hz' := (ObjectCurrentEquation2011.internalZero_positiveShift expression94 w).mp hz
  have hpos : ∀ j, 0 < w j + 1 := fun j =>
    lt_of_le_of_lt (Arithmetic.zero_le (w j)) (lt_add_one _)
  exact ordinary_halts _ hpos (ordinary_equations _ hpos hz')

/-- **Completeness.** A natural zero of the Carrier65 polynomial at the block-mask2963
ports gives one of the 67/94 equation, by `i ↦ Delta i`. -/
theorem zero94_of_zero (v : Fin 14 → V)
    (hz : InternalZero Bm2963Ports.naturalExpression v) :
    ∃ w : Fin 14 → V, InternalZero naturalExpression94 w := by
  have hz' : InternalZero Bm2963Ports.expression (fun j => v j + 1) :=
    (ObjectCurrentEquation2011.internalZero_positiveShift _ v).mp hz
  rw [internalZero_iff, Bm2963Ports.expression,
    ModelCarrierCurrent.evalRing_expressionAt65] at hz'
  let P : Fin 4 → DiffRing V := fun j => ((intPorts j : ℤ) : DiffRing V)
  let u : Fin 14 → DiffRing V := fun j => ι (v j + 1)
  have h94 := Carrier94Value.zero94_of_maintained model_discrete mod4 P u
    Bm2963Carrier118.beta_pos (ModelCarrierCurrent.shifted_pos v) hz'
  have hm := Carrier94Value.multiplier_pos model_discrete P u
    Bm2963Carrier118.beta_pos (ModelCarrierCurrent.shifted_pos v)
  obtain ⟨m, hm'⟩ := nonneg_iff.mp hm.le
  have hm0 : 0 < m := by
    rw [← ι_lt_ι, map_zero, ← hm']
    exact hm
  refine ⟨fun j => if j = 5 then m - 1 else v j, ?_⟩
  apply (ObjectCurrentEquation2011.internalZero_positiveShift _ _).mpr
  show InternalZero expression94 _
  rw [internalZero_iff, expression94, Carrier94Value.evalRing_expressionAt94]
  convert h94 using 2
  funext j
  by_cases hj : j = 5
  · subst hj
    simp only [Function.update_apply, ↓reduceIte]
    rw [tsub_add_cancel_of_le (pos_iff_one_le.mp hm0), hm']
  · simp only [Function.update_apply, hj, ↓reduceIte]
    rfl

end Model

section Bridge
open LO.Entailment
open scoped LO.FirstOrder
open AdaptiveEquationSyntax2011
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

/-- In every model of `𝗜𝚺₁` the two no-zero sentences agree. -/
theorem sameNoZero94 : HAExpressionNoZeroEquiv.SameNoZero naturalExpression94
    Bm2963Ports.naturalExpression := by
  intro V _ _
  constructor
  · intro h v hz
    obtain ⟨w, hw⟩ := zero94_of_zero v hz
    exact h w hw
  · intro h w hz
    obtain ⟨t, ht⟩ := halts_of_zero94 w hz
    have hno : (FoundationHANoZero.classicalNoZero
        Bm2963Ports.naturalExpression).Evalb (M := V) ![] := by
      rw [HAExpressionAssembly.classicalNoZero_iff]
      exact fun u hu => h u hu
    exact ((Bm2963Carrier118.currentBridge V).mp hno) ⟨t, ht⟩

theorem bridge94 : HAExpressionAssembly.PolynomialBridge naturalExpression94 :=
  HAExpressionNoZeroEquiv.bridge _ _ sameNoZero94 Bm2963Carrier118.currentBridge

/-- **Native iPRA: package 188's 67/94 form has no positive zero iff ZFC is
consistent.** -/
theorem native_equivalence94 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero naturalExpression94 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ bridge94

/-- **Standard iPRA.** -/
theorem standard_equivalence94 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero naturalExpression94 🡘
      ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence94

/-- **Equality-only iPRA.** -/
theorem reference_equivalence94 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero naturalExpression94) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference native_equivalence94

end Bridge

#print axioms ordinary_halts
#print axioms sameNoZero94
#print axioms native_equivalence94
#print axioms standard_equivalence94
#print axioms reference_equivalence94

end DiophantineConsistency.Bm2963Carrier94
