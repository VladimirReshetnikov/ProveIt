import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Mixed121.P47p75Graph
import DiophantineConsistency.Mixed121.Short15Facts
import DiophantineConsistency.Mixed121.Short15Units
import DiophantineConsistency.Mixed121.Short15ConvData

/-! # iPRA endpoints for package 47's 15-positive, degree-44 equation

The equation is `47-sparse-support/minima/gap_minima75.json`: 15 positive
unknowns, 75 operations and exact degree 44, at the wang943-mixed-121x8801 ports
`Mixed121Ports.ports` (`minima/fixed_coefficients.json`). Its output is
`N0² + N1² + Na² + (Nk·Nt − 1)² + S² − 3` (`P47p75Graph`). In every model of
`𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* forward: `N0`, `N1` and `Na` are nonzero (`Short15Units`; `Na` because `S² ≤ 3`),
  so their squares are `1`, `S = 0` and `Nk·Nt = 1`. None of the three is `−1`,
  so `N0 = N1 = Na = 1` and `Nk = Nt = ±1`. The auxiliary norm at the old ordinate
  `V = c(Tf − 1) − Rf²` and `y = V + e` feeds `Short15Index.oracle_old`, and `Short15Facts.halts_core` gives the halt;
* converse: `Short15ConvData.canonical` with `i = Δ·i_halt`, `T = f·T_halt`
  (so that `c((fT)f − 1) − Rf² = f²(cT − R) − c` is the squared-modulus ordinate),
  `τ = τ_halt` and `e = y − w_aux` (positive since `y > w_aux`).

The generic helpers of `IPRAOrdinary12Chain` give native, standard and
equality-only iPRA equivalences with the selected Foundation ZFC consistency
predicate. The endpoints are about the Lean graph; its correspondence with the
JSON and the port binding is the check
`research/mixed121-calibration/tools/generate_short15.py --check`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.IPRAPositive47p75
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly ModelDifferenceRing
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open Short15Graph Short15Root
open Short15ConvData (intPorts)
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] Mixed121Ports.ports

def expression : Expr (Fin 15) := (P47p75Graph.graph intPorts).output

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem small5 {a b c d e : DiffRing V} (h : a * a + b * b + c * c + d * d + e * e - 3 = 0) :
    e * e ≤ 3 := by
  nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c, mul_self_nonneg d]

/-- A positive zero gives an internal halt of machine 215. -/
theorem halts (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hz : InternalZero expression v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hb, -, -, -⟩ := Mixed121Ports.leaf_bounds (V := V)
  have h := (internalZero_iff _ v).mp hz
  rw [expression, P47p75Graph.output_eval, P47p75Graph.N0_eval, P47p75Graph.N1_eval,
    P47p75Graph.Na_eval, P47p75Graph.Nk_eval, P47p75Graph.Nt_eval, P47p75Graph.Ns_eval] at h
  obtain ⟨h0, h1, ha, hu, hw⟩ := Short15Units.sos5_split h
    (Short15Units.n0_ne_zero Mixed121Ports.ports v hv hb _)
    (Short15Units.n1_ne_zero Mixed121Ports.ports v hv)
    (Short15Units.na_ne_zero Mixed121Ports.ports v hv hb _ (small5 h))
  have hN0 := h0.resolve_right (Short15Units.n0_ne_neg Mixed121Ports.ports v hv hb _)
  have hN1 := h1.resolve_right (Short15Units.n1_ne_neg _ _)
  have hNa := ha.resolve_right (Short15Units.na_ne_neg _ _ _ _)
  have hsign := Short15Units.sign_of_mul (sub_eq_zero.mp hu)
  have hτ := first Mixed121Ports.ports v (v 10) hN0
  have hstrong := strong Mixed121Ports.ports v (v 6) hw
  have hc0 : 0 < cV Mixed121Ports.ports v := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 11)
  exact Short15Facts.halts_core v hv _ hτ hN1
    (fun hF hR => Short15Index.oracle_old _ _ _ (v 4) (v 6) (v 7) (v 13) hc0 (hv 6) (hv 4) hR
      hstrong (aux_old Mixed121Ports.ports v hF (hv 4) hNa)) hsign

/-- An internal halt of machine 215 gives a positive zero. -/
theorem converse (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 15 → V, (∀ j, 0 < v j) ∧ InternalZero expression v := by
  obtain ⟨J, F, α, z, f, h, iH, TH, s, w, τ, η, ζ, y, wa, γ, ellM, ΔM, hJ, hF, hα, hz, hf, hh, hiH,
    hTH, hs, hw, hτ, hη, hζ, hy, hwy, hγ, hΔ, hellτ, hfacts⟩ := Short15ConvData.canonical T hT
  let v : Fin 15 → V := ![J, F, α, z, f, h, ΔM * iH, f * TH, s, w, τ, η, ζ, y - wa, γ]
  have hpos : ∀ j, 0 < v j := by
    intro j
    fin_cases j
    exacts [hJ, hF, hα, hz, hf, hh, mul_pos hΔ hiH, mul_pos hf hTH, hs, hw, hτ, hη, hζ, tsub_pos_of_lt hwy, hγ]
  refine ⟨v, hpos, ?_⟩
  obtain ⟨vell, vΔ, hNt, hNk, hN1, hN0, hnorm, hVn, hNa⟩ :=
    hfacts (fun j => ι (v j)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [internalZero_iff, expression, P47p75Graph.output_eval, P47p75Graph.N0_eval, P47p75Graph.N1_eval,
    P47p75Graph.Na_eval, P47p75Graph.Nk_eval, P47p75Graph.Nt_eval, P47p75Graph.Ns_eval]
  have e10 : ι (v 10) = ι τ := rfl
  have eVn : (vals intPorts (fun j => ι (v j))).Vo = ι wa := by
    rw [show (vals intPorts (fun j => ι (v j))).Vo = (vals intPorts (fun j => ι (v j))).c *
        (ι (v 7) * ι (v 4) - 1) - (vals intPorts (fun j => ι (v j))).RR * (ι (v 4) * ι (v 4)) from rfl,
      show ι (v 7) = ι (v 4) * ι TH from map_mul ι f TH, old_new]
    exact hVn
  have e13 : (vals intPorts (fun j => ι (v j))).Vo + ι (v 13) = ι y := by
    rw [eVn]
    show ι wa + ι (y - wa) = ι y
    rw [← map_add, add_tsub_cancel_of_le (le_of_lt hwy)]
  have hS : rS intPorts (fun j => ι (v j)) (ι (v 6)) = 0 := by
    rw [rS, show (vals intPorts (fun j => ι (v j))).Aaux =
        (vals intPorts (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) from rfl,
      show ι (v 6) = ι ΔM * ι iH from map_mul ι ΔM iH]
    rw [vΔ] at hnorm ⊢
    linear_combination (-(ι ΔM)) * hnorm
  rw [e10, hN0, hN1, e13, eVn, hNa, hNk, hNt, hS]
  ring

end Model

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := fun _ _ _ =>
  ⟨fun ⟨v, hv, hz⟩ => halts v hv hz, fun ⟨T, hT⟩ => converse T hT⟩

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

#print axioms halts
#print axioms converse
#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAPositive47p75
