import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Nine121.N82p726Graph
import DiophantineConsistency.Nine121.N82Contract
import DiophantineConsistency.Nine121.Source31Converse

/-! # iPRA endpoints for package 82's nine-positive, 726-operation equation

The equation is `82-pell-congruences/nine_full_radical/laurent9_positive.json`: nine positive
unknowns `b g h s w C i j n`, 726 live operations, exact degree 1,158,228 (package claim), on
package 71's source65 prefix (the shared-tap layout of `N82Layout`, `L = bB¹⁹⁹¹`,
`N = 2^17079501 bB¹⁰⁵⁷`, height 1873) with package 71's Pell registers (Jones's `F`) and the
full-radical Laurent majorant `T = 4T₀` with scale `S = 2¹⁸C⁷`, at the wang943-mixed-121x8801 ports
`Mixed121Ports.ports` (package 55's payloads, which package 82's coefficient reconstruction
reproduces byte for byte). In every model of `𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* forward: `N82p726Graph.output_eval` reads a zero as a zero of `N82Finalizer.value` at the prefix
  `R, N, t`, which are model naturals with the finalizer's size hypotheses
  (`N82Contract.prefix_naturals`, including `R ≥ 2²⁰` and `N ≥ 32`); `N82Finalizer.sound` gives
  `N² ∣ C(2R, R)`, `b = 2ᵏ` and `g < 4t`; `N82Contract.contract` gives a digit vector `z` whose
  successors are a zero of the transformed parent rows; `N82Contract.source_of_code` and
  `Source31Facts.halts` give the halt;
* converse: `Source31Converse.converse` gives a positive parent zero, `N82Contract.code_of_source`
  the packed code `g` at a binary `b = 2ᵏ` with `0 < g < t`, the contract the calibration, and
  `N82Finalizer.complete` the remaining seven positive unknowns.

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard and equality-only iPRA
equivalences with the selected Foundation ZFC consistency predicate. The endpoints are about the
Lean graph; its correspondence with the JSON is the check
`research/nine-positive-p82-726-endpoint/tools/check_graph.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANine82p726
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open ModelDifferenceRing Nine121 Nine121.N82Prefix
open Nine121.N101Prefix (Bq)
attribute [local irreducible] Mixed121Ports.ports

def expression : Expr (Fin 9) :=
  N82p726Graph.n860 (fun j => (Mixed121Ports.ports j : ℤ))

theorem expression_def :
    expression = N82p726Graph.n860 (fun j => (Mixed121Ports.ports j : ℤ)) := rfl

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eval_expression (v : Fin 9 → V) :
    expression.evalRing (fun i => ι (v i)) = N82Finalizer.value
      (Rq (Source31Facts.portsR Mixed121Ports.ports) (ι (v 0)) (ι (v 1))) (Nq (ι (v 0)))
      (ι (v 0)) (ι (v 1)) (tq (ι (v 0))) (ι (v 2)) (ι (v 3)) (ι (v 4)) (ι (v 5)) (ι (v 6))
      (ι (v 7)) (ι (v 8)) :=
  N82p726Graph.output_eval (fun j => (Mixed121Ports.ports j : ℤ)) (fun i => ι (v i))

theorem forward (v : Fin 9 → V) (hv : ∀ j, 0 < v j) (hz : InternalZero expression v) :
    ∃ T : V, SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  rw [internalZero_iff, eval_expression] at hz
  obtain ⟨R, N, t, hR, hN, ht, hR8, hN8, hbR, hbN, ht0, hRB, hN32⟩ :=
    N82Contract.prefix_naturals (v 0) (v 1) (hv 0)
  rw [← hR, ← hN, ← ht] at hz
  obtain ⟨hdvd, ⟨k, hk⟩, hgt⟩ := N82Finalizer.sound hR8 hN32 hRB hbR (hv 0) hbN ht0 (hv 2) (hv 3)
    (hv 4) (hv 5) (hv 6) (hv 7) hz
  rw [hk] at hR hN ht
  obtain ⟨z, -, -, hrows⟩ := (N82Contract.contract k (v 1) R N t hgt hR hN ht).mp hdvd
  obtain ⟨x, hx, hxr⟩ := N82Contract.source_of_code z hrows
  exact Source31Facts.halts x hx hxr

theorem backward (T : V)
    (hT : SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 9 → V, (∀ j, 0 < v j) ∧ InternalZero expression v := by
  obtain ⟨x, hx, hxr⟩ := Source31Converse.converse T hT
  obtain ⟨k, z, hzk, hg0, hgt, hrows⟩ := N82Contract.code_of_source x hx hxr
  obtain ⟨g, hgd⟩ : ∃ g : V, g = ∑ i, z i * N101Contract.Bm (Exp.exp k) ^ N82Layout.weights i :=
    ⟨_, rfl⟩
  rw [← hgd] at hg0 hgt
  obtain ⟨R, N, t, hR, hN, ht, hR8, hN8, hbR, hbN, -, hRB, hN32⟩ :=
    N82Contract.prefix_naturals (Exp.exp k) g (exp_pos k)
  have htv : t = Exp.exp k * N101Contract.Bm (Exp.exp k) ^ 116 := by
    apply ι_injective
    rw [ht, map_mul, map_pow, N101Contract.ι_Bm, tq]
  have hgt' : g < t := by rw [htv]; exact hgt
  have h4 : g < 4 * t :=
    lt_of_lt_of_le hgt' (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hdvd := (N82Contract.contract k g R N t h4 hR hN ht).mpr ⟨z, hzk, hgd, hrows⟩
  obtain ⟨h, s, w, C, i, j, n, hh, hs, hw, hC, hi, hj, hn, hzero⟩ :=
    N82Finalizer.complete hR8 hN32 hRB hbR (exp_pos k) hbN hgt' hdvd ⟨k, rfl⟩
  refine ⟨![Exp.exp k, g, h, s, w, C, i, j, n], ?_, ?_⟩
  · intro j'
    fin_cases j'
    exacts [exp_pos k, hg0, hh, hs, hw, hC, hi, hj, hn]
  · rw [internalZero_iff, eval_expression]
    change N82Finalizer.value (Rq (Source31Facts.portsR Mixed121Ports.ports) (ι (Exp.exp k)) (ι g))
      (Nq (ι (Exp.exp k))) (ι (Exp.exp k)) (ι g) (tq (ι (Exp.exp k))) (ι h) (ι s) (ι w) (ι C)
      (ι i) (ι j) (ι n) = 0
    rw [← hR, ← hN, ← ht]
    exact hzero

end Model

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => forward v hv hz, fun ⟨T, hT⟩ => backward T hT⟩

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRANine82p726
