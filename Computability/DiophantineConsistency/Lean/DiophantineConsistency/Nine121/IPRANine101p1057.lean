import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Nine121.N101p1057Graph
import DiophantineConsistency.Nine121.N101Contract
import DiophantineConsistency.Nine121.Source31Converse

/-! # iPRA endpoints for package 101's nine-positive, 1,057-operation equation

The equation is `101-constructive-reductions/nine/equations/boundary_complete.json`: nine positive
unknowns `b g h s w C i j n`, 1,057 live operations, exact degree 997,810 (package claim), with the
complete-radical majorant `V₁ = Π(A, C, i, Z)` (333 terms) and `a₁ = DFI·(1024C⁵i)²`, at the
wang943-mixed-121x8801 ports `Mixed121Ports.ports` (package 31's payloads, translated original31
layout; prefix and contract unchanged from the 420 form). In every model of `𝗜𝚺₁` it has a
positive zero iff machine 215 halts:

* forward: `N101p1057Graph.output_eval` reads a zero as a zero of the complete-radical finalizer
  `N1057Finalizer.value` at the prefix `R, N, t`, which are model naturals with the finalizer's size
  hypotheses (`N101Contract.prefix_naturals`, and `N ≥ 32` from `N32`); `N1057Finalizer.sound`
  gives `N² ∣ C(2R, R)`, `b = 2ᵏ` and `g < 4t`; `N101Contract.contract` gives a digit vector `z`
  with vanishing gapN86 rows at `z + 1`; `N101Contract.source_of_code` and `Source31Facts.halts`
  give the halt;
* converse: `Source31Converse.converse` gives a positive parent zero, `N101Contract.code_of_source`
  the packed code `g` at a binary `b = 2ᵏ` with `0 < g < t`, the contract the calibration, and
  `N1057Finalizer.complete` the remaining seven positive unknowns.

The generic helpers of `IPRAOrdinary12Chain` turn this into native, standard and equality-only iPRA
equivalences with the selected Foundation ZFC consistency predicate. The endpoints are about the
Lean graph; its correspondence with the JSON is the check
`research/nine-positive-p101-1057-endpoint/tools/check_graph.py`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANine101p1057
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open ModelDifferenceRing Nine121 Nine121.N101Prefix
attribute [local irreducible] Mixed121Ports.ports

def expression : Expr (Fin 9) :=
  N101p1057Graph.n1385 (fun j => (Mixed121Ports.ports j : ℤ))

theorem expression_def :
    expression = N101p1057Graph.n1385 (fun j => (Mixed121Ports.ports j : ℤ)) := rfl

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The threshold register is at least 32 (`N = 2^16012032·B¹⁰⁵³ ≥ 8B`), as the complete-radical
majorant needs `A ≥ 2²⁰`. -/
theorem N32 {N b : V} (hN : ι N = Nq (ι b)) (hb : 0 < b) : 32 ≤ N := by
  obtain ⟨hH8, -⟩ := N101Contract.port_facts (V := V)
  obtain ⟨hB32, -, -, -⟩ := scale_facts (ι b) N101Contract.Hc (N101Contract.one_le_ι hb) hH8
    (N101Contract.hBb b)
  have hT : (8 : DiffRing V) ≤ ι (Exp.exp (16012032 : V)) := N101Contract.exp_ge_eight (by norm_num)
  have hB1 : (1 : DiffRing V) ≤ Bq (ι b) := by linarith
  have hBp : Bq (ι b) ≤ Bq (ι b) ^ 1053 := by
    have := pow_step _ hB1 1 1053 (by norm_num); rwa [pow_one] at this
  have h : (32 : DiffRing V) ≤ Nq (ι b) := by
    rw [Nq, N101Contract.thresholdScale_eq]
    calc (32 : DiffRing V) = 8 * 4 := by norm_num
      _ ≤ ι (Exp.exp (16012032 : V)) * Bq (ι b) ^ 1053 :=
          mul_le_mul hT (by linarith) (by norm_num) (by linarith)
  apply ι_le_ι.mp; rw [map_ofNat, hN]; exact h

theorem eval_expression (v : Fin 9 → V) :
    expression.evalRing (fun i => ι (v i)) = N1057Finalizer.value
      (Rq (Source31Facts.portsR Mixed121Ports.ports) (ι (v 0)) (ι (v 1))) (Nq (ι (v 0)))
      (ι (v 0)) (ι (v 1)) (tq (ι (v 0))) (ι (v 2)) (ι (v 3)) (ι (v 4)) (ι (v 5)) (ι (v 6))
      (ι (v 7)) (ι (v 8)) :=
  N101p1057Graph.output_eval (fun j => (Mixed121Ports.ports j : ℤ)) (fun i => ι (v i))

theorem forward (v : Fin 9 → V) (hv : ∀ j, 0 < v j) (hz : InternalZero expression v) :
    ∃ T : V, SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  rw [internalZero_iff, eval_expression] at hz
  obtain ⟨R, N, t, hR, hN, ht, hR8, hN8, hbR, hbN, ht0⟩ :=
    N101Contract.prefix_naturals (v 0) (v 1) (hv 0)
  rw [← hR, ← hN, ← ht] at hz
  obtain ⟨hdvd, ⟨k, hk⟩, hgt⟩ := N1057Finalizer.sound hR8 (N32 hN (hv 0)) hbR (hv 0) hbN ht0 (hv 2) (hv 3) (hv 4)
    (hv 5) (hv 6) (hv 7) hz
  rw [hk] at hR hN ht
  obtain ⟨z, -, -, hrows⟩ := (N101Contract.contract k (v 1) R N t hgt hR hN ht).mp hdvd
  obtain ⟨x, hx, hxr⟩ := N101Contract.source_of_code z hrows
  exact Source31Facts.halts x hx hxr

theorem backward (T : V)
    (hT : SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 9 → V, (∀ j, 0 < v j) ∧ InternalZero expression v := by
  obtain ⟨x, hx, hxr⟩ := Source31Converse.converse T hT
  obtain ⟨k, z, hzk, hg0, hgt, hrows⟩ := N101Contract.code_of_source x hx hxr
  obtain ⟨g, hgd⟩ : ∃ g : V, g = ∑ i, z i * N101Contract.Bm (Exp.exp k) ^ N101Layout.weights i :=
    ⟨_, rfl⟩
  rw [← hgd] at hg0 hgt
  obtain ⟨R, N, t, hR, hN, ht, hR8, hN8, hbR, hbN, -⟩ :=
    N101Contract.prefix_naturals (Exp.exp k) g (exp_pos k)
  have htv : t = Exp.exp k * N101Contract.Bm (Exp.exp k) ^ 115 := by
    apply ι_injective
    rw [ht, map_mul, map_pow, N101Contract.ι_Bm, tq]
  have hgt' : g < t := by rw [htv]; exact hgt
  have h4 : g < 4 * t :=
    lt_of_lt_of_le hgt' (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hdvd := (N101Contract.contract k g R N t h4 hR hN ht).mpr ⟨z, hzk, hgd, hrows⟩
  obtain ⟨h, s, w, C, i, j, n, hh, hs, hw, hC, hi, hj, hn, hzero⟩ :=
    N1057Finalizer.complete hR8 (N32 hN (exp_pos k)) hbR (exp_pos k) hbN hgt' hdvd ⟨k, rfl⟩
  refine ⟨![Exp.exp k, g, h, s, w, C, i, j, n], ?_, ?_⟩
  · intro j'
    fin_cases j'
    exacts [exp_pos k, hg0, hh, hs, hw, hC, hi, hj, hn]
  · rw [internalZero_iff, eval_expression]
    change N1057Finalizer.value (Rq (Source31Facts.portsR Mixed121Ports.ports) (ι (Exp.exp k)) (ι g))
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

end DiophantineConsistency.IPRANine101p1057
