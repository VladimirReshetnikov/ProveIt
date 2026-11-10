import DiophantineConsistency.BFS943.Trace87ModelIff
import DiophantineConsistency.BFS943.Trace87Syntax
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.IPRABoundedRhoZFC

/-! # iPRA endpoints for package 172's ten-positive 87-operation, degree-214 equation

The equation is `172-pooled-powers-round21/part2/ConZFC_Pooled_Powers_Round21_2026-10-25/scalar/positive10/positive10_degree214_ops87.json`
(mode `free_inverse`): ten positive unknowns `J, F, α, i, T, w, s, n, η, ζ`,
87 operations and exact degree 214 (`X = q w`, free strip `c = k s + η`,
Pell scale `λ = q`: `A - 1 = q s (X + 1)`, transport base `w`,
`D = 6 q⁷`, inverse-Lucas offset `6 (e - q⁴ s) - v k (k² - 4)` with
`v = X (q s)²`; weight `L = bV`). Its Lean literal is
`TenPositiveTrace87.expression` (`value87`, read in `Expr`), here at the same
direct-BFS943 ports as `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`.

`Trace87ModelIff.positive_model_iff` proves, in every model of `𝗜𝚺₁`, that
the circuit has a positive zero at these ports iff machine 215 halts.
Soundness: a positive 87 zero is a `BFS943FixedSource.FixedSource`
(`Trace87Source`): the inverse-Lucas layer `InverseLucasCubic` (internal
second-order expansion of `ψ_{1+2v}`, the cubic split, `q^(m+1) ∣ 3x ⇒ q^m ∣ x`)
gives the first-index alignment `2 m = R + 1` (`Trace87Transport`,
`Trace87NormOffset`), then `X = 2^R`, `q³ ∣ s`, the natural transport
`(K0 + w) C = F + h t` and the half-binomial population bound, and
`FixedSourceHalt.source_halts` gives halting. Completeness builds a fresh 87
zero from the halting packing at scale `μ = q`, with a possibly negative
offset quotient `ρ` (`Trace87HaltGraph`, `Trace87ReverseGraph`,
`Trace87ReverseData`, `Trace87ParentMap`). The iPRA wrappers are those of
`IPRATrace75`.

Scope: the endpoints are about the Lean literal at the symbolic ports. Its
correspondence with the JSON circuit is
`research/ten-positive-p172-87-endpoint/check_lean_graph.py`, and the binding
of the four ports to the coefficient hashes is
`reviews/bfs943-source-promotion/tools/check_ports.py` (the 87 graph pins the
same four coefficient files as the 75 graph); both are finite external
checks, not Lean theorems about files. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.IPRATrace87
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

/-- Package 172's 87-operation circuit at the fixed ports. -/
def expression : Expr (Fin 10) := Trace87BFSSyntax.literal fixedPorts

theorem expression_def :
    expression = TenPositiveTrace87.expression (fun j => (fixedPorts j : ℤ)) := rfl

/-! Generic port projections, proved over arbitrary port values. -/

theorem ports_zero (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 0 = β := rfl
theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl
theorem ports_two (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 2 = L := rfl
theorem ports_three (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 3 = β + H := rfl

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  have h := Trace87ModelIff.positive_model_iff (V := V) fixedPorts
    (ports_zero _ _ _ _) (ports_one _ _ _ _) (ports_two _ _ _ _) (ports_three _ _ _ _)
  constructor
  · rintro ⟨v, hv, hz⟩
    exact h.mp ⟨v, hv, (Trace87BFSSyntax.literal_zero_iff fixedPorts v).mp hz⟩
  · intro hh
    obtain ⟨v, hv, hz⟩ := h.mpr hh
    exact ⟨v, hv, (Trace87BFSSyntax.literal_zero_iff fixedPorts v).mpr hz⟩

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

end DiophantineConsistency.IPRATrace87
