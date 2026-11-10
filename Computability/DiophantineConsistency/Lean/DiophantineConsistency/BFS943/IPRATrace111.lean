import DiophantineConsistency.BFS943.Trace111ModelIff
import DiophantineConsistency.BFS943.Trace111Syntax
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.IPRABoundedRhoZFC

/-! # iPRA endpoints for package 194's ten-positive 111-operation, degree-198 equation

The equation is `194-guarded-resultants-early-projection/positive/product2_radix67.json`
(mode `product2`): ten positive unknowns `J, F, α, i, T, w, s, n, η, ζ`,
111 operations and exact degree 198. It is package 172's 87/214 free-inverse
chart with the transport gate `(n - b V B) - Ω₂` at the first-product centre
`Ω₂ = U {2A [E V - θ (E² + S²)] + S [4 θ E - (b - c)]}`, `θ = U² b`
(weight `L = bV`), and the root-scale-two norm
`Q (Z² - 4 M² G V²) + (4 M² G - Z²)`. Its Lean literal is
`TenPositiveTrace111.expression` (`value111`, read in `Expr`), here at the same
direct-BFS943 ports as `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`.

`Trace111ModelIff.positive_model_iff` proves, in every model of `𝗜𝚺₁`, that
the circuit has a positive zero at these ports iff machine 215 halts.
Soundness: `Q - 1` is odd, so a zero has an even carrier `2 Zh` with `Zh` a
zero of the 87 norm; with `Ω₂ ≤ 3 A U E |V| < 5 g |V|` for every sign of `b`
(`Trace111Estimate`, `Trace111Omega`) and `|b| > 32 g` the 87 carrier
`M (2 z + Ω₂)` gives `B ≥ 0` (`Scaled87Sign`); then the 87 soundness chain runs
at the shifted carrier `Z₈₇ - M (Ω₂ + z)` (`Trace87Shift*`) to a
`BFS943FixedSource.FixedSource`, and `FixedSourceHalt.source_halts` gives
halting. Completeness: a positive 87 zero (`Trace87HaltGraph`) has `V > 0`,
hence `b > 0` and `Ω₂ ≥ 0`, and root `z = ±g y`; moving `n` by `Ω₂ + g y`
resp. `Ω₂ + 3 g y` doubles the carrier (`Scaled87Complete`). The iPRA wrappers
are those of `IPRATrace75`.

Scope: the endpoints are about the Lean literal at the symbolic ports. Its
correspondence with the JSON circuit is
`research/ten-positive-p194-111-endpoint/check_lean_graph.py`, and the binding
of the four ports to the coefficient hashes is
`reviews/bfs943-source-promotion/tools/check_ports.py`; both are finite
external checks, not Lean theorems about files. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.IPRATrace111
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

/-- Package 194's 111-operation circuit at the fixed ports. -/
def expression : Expr (Fin 10) := Trace111BFSSyntax.literal fixedPorts

theorem expression_def :
    expression = TenPositiveTrace111.expression (fun j => (fixedPorts j : ℤ)) := rfl

/-! Generic port projections, proved over arbitrary port values. -/

theorem ports_zero (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 0 = β := rfl
theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl
theorem ports_two (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 2 = L := rfl
theorem ports_three (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 3 = β + H := rfl

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  have h := Trace111ModelIff.positive_model_iff (V := V) fixedPorts
    (ports_zero _ _ _ _) (ports_one _ _ _ _) (ports_two _ _ _ _) (ports_three _ _ _ _)
  constructor
  · rintro ⟨v, hv, hz⟩
    exact h.mp ⟨v, hv, (Trace111BFSSyntax.literal_zero_iff fixedPorts v).mp hz⟩
  · intro hh
    obtain ⟨v, hv, hz⟩ := h.mpr hh
    exact ⟨v, hv, (Trace111BFSSyntax.literal_zero_iff fixedPorts v).mpr hz⟩

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

end DiophantineConsistency.IPRATrace111
