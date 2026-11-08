import DiophantineConsistency.BFS943.Q170Sound74
import DiophantineConsistency.BFS943.Q170Complete74
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.IPRABoundedRhoZFC

/-! # iPRA endpoints for package 170's 12-positive 74-operation, degree-438 rational carrier

The equation is
`170-quotient-carriers/compact/fixed_12_rational_74_degree438.json`
(`FIXED_CARRIER_PROOF.md` §7): twelve positive unknowns
`J, F, α, z, n, i, T, s, w, η, ζ, γ`, 74 operations and exact degree 438.
It deletes Carrier65's carrier, strong abscissa and auxiliary ordinate: with
`m = i (a+2) D`, `W = A Δ (m c²)²`, `F2 = 1 + W`, `Q = Δ W`, `G = A F2` and the
rational carrier `t = E n + (k - R - 1)`, the output is
`P = N1 · Nt · (3 B + 1) - 1`, `B = Q (t² - E² G V²) - t² + E² G`. Its Lean
literal is `Q170Form74.expression` (`value74`, read in `Expr`), here at the
direct-BFS943 ports of `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`.

In every model of `𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* soundness `Q170Sound74.zero_halts`: the units, explicit Bézout identities
  making `A` and `F2` coprime to `Q - 1` and `Q V² - 1`, the square of `A F2`
  and its split `A = τ²`, `F2 = f²`, the rational adjacent-Pell integrality
  `|t| = E τ f y`, hence `k ≡ R + 1 (mod E)`, and
  `Q170Residue.carrier_of_residue` give a positive solution of Carrier65's five
  equations (`i = τ m`, `n = (τ + R - k) / E`), and
  `Carrier65BFSSource.equations_halt` gives halting;
* completeness `Q170Complete74.zero_of_halt`: the outer data of
  `Carrier65BFSHalt.halt_outer`, a strong seed with multiplier divisible by
  `τ (a+2) D` and its fresh auxiliary seed, and `n = τ f y - (k - R - 1) / E`.

The iPRA wrappers are those of `IPRATrace75`. Scope: the endpoints are about
the Lean literal at the symbolic ports. Its correspondence with the JSON
circuit is `research/p170-74-endpoint/check_lean_graph.py`, and the binding
of the four ports to the coefficient hashes is
`reviews/bfs943-source-promotion/tools/check_ports.py` (`fixedPorts` is
textually that of `IPRATrace75`); both are finite external checks, not Lean
theorems about files. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.IPRAQuot170p74
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

/-- Package 170's 74-operation circuit at the fixed ports. -/
def expression : Expr (Fin 12) := Q170Syntax74.literal fixedPorts

theorem expression_def :
    expression = Q170Form74.expression (fun j => (fixedPorts j : ℤ)) := rfl

/-! Generic port projections, proved over arbitrary port values. -/

theorem ports_zero (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 0 = β := rfl
theorem ports_one (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 1 = K := rfl
theorem ports_two (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 2 = L := rfl
theorem ports_three (β K L H : ℕ) : CompactSymbolicPorts.ports β K L H 3 = β + H := rfl

/-- In every model of `𝗜𝚺₁`, a positive zero exists iff machine 215 halts. -/
theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  constructor
  · rintro ⟨v, hv, hz⟩
    exact Q170Sound74.zero_halts fixedPorts v (ports_zero _ _ _ _) (ports_one _ _ _ _)
      (ports_two _ _ _ _) (ports_three _ _ _ _) hv
      ((Q170Syntax74.literal_zero_iff fixedPorts v).mp hz)
  · rintro ⟨T, hT⟩
    obtain ⟨v, hv, hz⟩ := Q170Complete74.zero_of_halt fixedPorts T hT
      (Carrier65BFSHalt.port_values fixedPorts (ports_zero _ _ _ _) (ports_one _ _ _ _)
        (ports_two _ _ _ _) (ports_three _ _ _ _))
    exact ⟨v, hv, (Q170Syntax74.literal_zero_iff fixedPorts v).mpr hz⟩

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

end DiophantineConsistency.IPRAQuot170p74
