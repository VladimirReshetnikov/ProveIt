import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.Mixed121.P54p71Graph
import DiophantineConsistency.Mixed121.Short15Facts
import DiophantineConsistency.Mixed121.Short15P54Split
import DiophantineConsistency.Mixed121.Short15ConvData

/-! # iPRA endpoints for package 54's 15-positive, degree-78 gate list at 121x8801

The gate list is `54-calibrated-carry/positive/p71_degree78.json`: 15 positive
unknowns, 71 operations and exact degree 78. **It is instantiated at the
wang943-mixed-121x8801 ports `Mixed121Ports.ports`** (package 55's payloads), not
at package 54's own c54 ports (`complemented-factorized-receiver-89x4831`,
base `2^429959`), which the tree does not calibrate. Its output is
`A² + B(B − 2) + C²` with `A = N0·N1`, `B = Na·Nk·Nt`, `C = S` (`P54p71Graph`). In
every model of `𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* forward: `N0`, `N1` are nonzero, so `A = ±1`, `B = 1`, `S = 0`, and the
  excluded values give `N0 = N1 = Na = 1`, `Nk = Nt = ±1` (`Short15P54Split`).
  The first norm holds at `τ = ℓ + r`, the strong norm at `i`, and the free
  partner `y` feeds `Short15Index.oracle_free`; `Short15Facts.halts_core` gives
  the halt;
* converse: `Short15ConvData.canonical` with `i = Δ·i_halt`, `T = T_halt`,
  `r = τ − ℓ` (positive since `τ² = ℓ(ℓ + k) + 1`) and `y = y_halt`, so
  `A = B = 1` and `C = 0`.

The generic helpers of `IPRAOrdinary12Chain` give native, standard and
equality-only iPRA equivalences with the selected Foundation ZFC consistency
predicate. The endpoints are about the Lean graph; its correspondence with the
JSON's gate list, and the port statement above, is the check
`research/mixed121-calibration/tools/generate_short15_p54.py --check`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.IPRAPositive54p71
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

def expression : Expr (Fin 15) := (P54p71Graph.graph intPorts).output

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive zero gives an internal halt of machine 215. -/
theorem halts (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hz : InternalZero expression v) :
    ∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0 := by
  obtain ⟨hb, -, -, -⟩ := Mixed121Ports.leaf_bounds (V := V)
  have h := (internalZero_iff _ v).mp hz
  rw [expression, P54p71Graph.output_eval, P54p71Graph.N0_eval, P54p71Graph.N1_eval,
    P54p71Graph.Na_eval, P54p71Graph.Nk_eval, P54p71Graph.Nt_eval, P54p71Graph.Ns_eval] at h
  obtain ⟨hN0, hN1, ha, hS, hsign⟩ := Short15P54Split.split h
    (Short15Units.n0_ne_zero Mixed121Ports.ports v hv hb _) (Short15Units.n1_ne_zero Mixed121Ports.ports v hv)
    (Short15Units.n0_ne_neg Mixed121Ports.ports v hv hb _) (Short15Units.n1_ne_neg _ _)
    (Short15Units.na_ne_neg _ _ _ _)
  have h0' : rN0 (fun j => (Mixed121Ports.ports j : ℤ)) (fun j => ι (v j))
      (ι (ellV Mixed121Ports.ports v + v 10)) = 1 := by
    rw [map_add, ← c_ell]; exact hN0
  have hτ := first Mixed121Ports.ports v _ h0'
  have hstrong := strong Mixed121Ports.ports v (v 6) hS
  have hc0 : 0 < cV Mixed121Ports.ports v := add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 11)
  exact Short15Facts.halts_core v hv _ hτ hN1
    (fun hF hR => Short15Index.oracle_free _ _ _ (v 4) (v 6) (v 7) (v 13) hc0 (hv 6) (hv 4) (hv 13) hR
      hstrong (aux_free Mixed121Ports.ports v hF (hv 4) ha)) hsign

/-- An internal halt of machine 215 gives a positive zero. -/
theorem converse (T : V) (hT : ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) :
    ∃ v : Fin 15 → V, (∀ j, 0 < v j) ∧ InternalZero expression v := by
  obtain ⟨J, F, α, z, f, h, iH, TH, s, w, τ, η, ζ, y, wa, γ, ellM, ΔM, hJ, hF, hα, hz, hf, hh, hiH,
    hTH, hs, hw, hτ, hη, hζ, hy, hwy, hγ, hΔ, hellτ, hfacts⟩ := Short15ConvData.canonical T hT
  let v : Fin 15 → V := ![J, F, α, z, f, h, ΔM * iH, TH, s, w, τ - ellM, η, ζ, y, γ]
  have hpos : ∀ j, 0 < v j := by
    intro j
    fin_cases j
    exacts [hJ, hF, hα, hz, hf, hh, mul_pos hΔ hiH, hTH, hs, hw, tsub_pos_of_lt hellτ, hη, hζ, hy, hγ]
  refine ⟨v, hpos, ?_⟩
  obtain ⟨vell, vΔ, hNt, hNk, hN1, hN0, hnorm, hVn, hNa⟩ :=
    hfacts (fun j => ι (v j)) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  rw [internalZero_iff, expression, P54p71Graph.output_eval, P54p71Graph.N0_eval, P54p71Graph.N1_eval,
    P54p71Graph.Na_eval, P54p71Graph.Nk_eval, P54p71Graph.Nt_eval, P54p71Graph.Ns_eval]
  have e10 : (vals intPorts (fun j => ι (v j))).ell + ι (v 10) = ι τ := by
    rw [vell]
    show ι ellM + ι (τ - ellM) = ι τ
    rw [← map_add, add_tsub_cancel_of_le (le_of_lt hellτ)]
  have eVn : (vals intPorts (fun j => ι (v j))).Vn = ι wa := hVn
  have e13 : ι (v 13) = ι y := rfl
  have hS : rS intPorts (fun j => ι (v j)) (ι (v 6)) = 0 := by
    rw [rS, show (vals intPorts (fun j => ι (v j))).Aaux =
        (vals intPorts (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) from rfl,
      show ι (v 6) = ι ΔM * ι iH from map_mul ι ΔM iH]
    rw [vΔ] at hnorm ⊢
    linear_combination (-(ι ΔM)) * hnorm
  rw [e10, hN0, hN1, eVn, e13, hNa, hNk, hNt, hS]
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

end DiophantineConsistency.IPRAPositive54p71
