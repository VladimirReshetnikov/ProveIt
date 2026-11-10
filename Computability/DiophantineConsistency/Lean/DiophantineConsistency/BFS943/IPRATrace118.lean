import DiophantineConsistency.BFS943.Trace118ModelIff
import DiophantineConsistency.BFS943.Trace118Syntax
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.IPRABoundedRhoZFC

/-! # iPRA endpoints for package 193's ten-positive 118-operation, degree-190 equation

The equation is `193-transport-and-pell-reuse/positive/whole190.json`: ten
positive unknowns `J, F, α, i, T, w, s, n, η, ζ`, 118 operations and exact
degree 190. It is package 172's 87/214 free-inverse chart with the folded
carrier gate `n - OmegaFold`, `OmegaFold = Ω + L B`, at package 178's
whole-product centre `Ω = U [2 S Rc + A (4 E V - θ Sc)]` (`θ = U² b`) and the new
transport weight `L = A U³ b²`, and the root-scale-four norm
`Q (Z² - 16 M² G V²) + (16 M² G - Z²)`. Its Lean literal is
`TenPositiveTrace118.expression` (`value118`, read in `Expr`), here at the same
direct-BFS943 ports as `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`.

`Trace118ModelIff.positive_model_iff` proves, in every model of `𝗜𝚺₁`, that
the circuit has a positive zero at these ports iff machine 215 halts.
Soundness: `Q - 1` is odd, so a zero has a carrier `4 Zh` with `Zh` a zero of
the 87 norm; with `Ω ≤ 5 A U E |V|` for every sign of `b` (`Trace118Estimate`,
`Trace118Omega`), `E ≤ U²` and `Δ ≥ 48` the weight dominates,
`2 (4 g y + Ω) < A U³ b²`, and the weight-`L` carrier `M (4 z + Ω)` gives
`B ≥ 0` (`Trace118Sign`); then the 87 soundness chain runs at the shifted
carrier `Z₈₇ - M (OmegaFold - b V B + 3 z)` (`Trace87Shift*`) to a
`BFS943FixedSource.FixedSource`, and `FixedSourceHalt.source_halts` gives
halting. Completeness: a positive 87 zero (`Trace87HaltGraph`) has `V > 0`,
`B ≥ 0`, `Ω ≥ 0` and root `z = ±g y`; moving `n` by `OmegaFold - b V B + 3 g y`
resp. `+ 5 g y` quadruples the carrier, and the moved `n` is positive since
`K < 2 g` and `-eclear < 2 g` (`Trace118Complete`). The iPRA wrappers are
those of `IPRATrace75`.

Scope: the endpoints are about the Lean literal at the symbolic ports. Its
correspondence with the JSON circuit is
`research/ten-positive-p193-118-endpoint/check_lean_graph.py`, and the binding
of the four ports to the coefficient hashes is
`reviews/bfs943-source-promotion/tools/check_ports.py`; both are finite
external checks, not Lean theorems about files. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.IPRATrace118
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAStandardTheory IPRAEqualityOnlyReference IPRAOrderErasure
open IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
attribute [local irreducible] CompactSymbolicKernel.rho DirectBFSSymbolicKernel.paramKernel
  CompactFixedBeta.betaNat Nat.ofDigits CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat

/-- The direct-BFS943 ports `![β, K0, MC, β + MF_native]`. -/
def fixedPorts : Fin 4 → ℕ :=
  CompactSymbolicPorts.ports CompactFixedBeta.betaNat
    (DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho)
    CompactSymbolicPorts.lowNat CompactSymbolicPorts.highNat

/-- Package 193's 118-operation circuit at the fixed ports. -/
def expression : Expr (Fin 10) := Trace118BFSSyntax.literal fixedPorts

theorem expression_def :
    expression = TenPositiveTrace118.expression (fun j => (fixedPorts j : ℤ)) := rfl

/-! Generic port projections, proved over arbitrary port values. -/

theorem ports_zero (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 0 = β := rfl
theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl
theorem ports_two (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 2 = L := rfl
theorem ports_three (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 3 = β + H := rfl

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  have h := Trace118ModelIff.positive_model_iff (V := V) fixedPorts
    (ports_zero _ _ _ _) (ports_one _ _ _ _) (ports_two _ _ _ _) (ports_three _ _ _ _)
  constructor
  · rintro ⟨v, hv, hz⟩
    exact h.mp ⟨v, hv, (Trace118BFSSyntax.literal_zero_iff fixedPorts v).mp hz⟩
  · intro hh
    obtain ⟨v, hv, hz⟩ := h.mpr hh
    exact ⟨v, hv, (Trace118BFSSyntax.literal_zero_iff fixedPorts v).mpr hz⟩

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

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := native_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

theorem reference_translated_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      IPRAOrderErasure.erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  refine IPRAReferenceInductionConversion.nativeToReference
    (σ := IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      (Semiformula.lMap embedding sourceSentence)ᴺ) ?_
  obtain ⟨h⟩ := native_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence
#print axioms standard_translated_equivalence
#print axioms reference_translated_equivalence

end DiophantineConsistency.IPRATrace118
