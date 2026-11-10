import DiophantineConsistency.BFS943.Q170Sound72
import DiophantineConsistency.BFS943.Q170Complete72
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.IPRABoundedRhoZFC

/-! # iPRA endpoints for package 170's 13-positive 72-operation, degree-154 q⁴ residue carrier

The equation is
`170-quotient-carriers/compact/fixed_13_residue_q4_72_degree154.json`
(`FIXED_CARRIER_PROOF.md` §6.1): thirteen positive unknowns
`J, F, α, z, f, n, i, T, s, w, η, ζ, γ`, 72 operations and exact degree 154.
It is Carrier65 with the carrier coordinate deleted: the strong multiplier is
`m = A q² i` and the auxiliary carrier is `t = q⁴ n - k + R`, with
`P = N1 · Nt · (3 B + 1) · Ns - 1`, `B = Q (t² - A V²) - t² + A`. Its Lean
literal is `Q170Form72.expression` (`value72`, read in `Expr`), here at the
direct-BFS943 ports of `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`.

In every model of `𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* soundness `Q170Sound72.zero_halts`: the units, the square extraction of `A`,
  the auxiliary ordinate's residue `±1 (mod 4 S²)`, read modulo `q⁴ > R + 2`, and
  the residue sign `Q170Residue.carrier_of_residue` (modulus `q⁴`) give a positive solution of Carrier65's five
  equations (`i = m`, `y = |t| / √A`, `n = (√A + R - k) / E`), and
  `Carrier65BFSSource.equations_halt` gives halting;
* completeness `Q170Complete72.zero_of_halt`: the outer data of
  `Carrier65BFSHalt.halt_outer`, a strong seed with multiplier divisible by
  `A q²` and its fresh auxiliary seed, and `n = (√A y + k - R) / q⁴`.

The iPRA wrappers are those of `IPRATrace75`. Scope: the endpoints are about
the Lean literal at the symbolic ports. Its correspondence with the JSON
circuit is `research/p170-72-endpoint/check_lean_graph.py`, and the binding
of the four ports to the coefficient hashes is
`reviews/bfs943-source-promotion/tools/check_ports.py` (`fixedPorts` is
textually that of `IPRATrace75`); both are finite external checks, not Lean
theorems about files. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.IPRAQuot170p72
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

/-- Package 170's 72-operation circuit at the fixed ports. -/
def expression : Expr (Fin 13) := Q170Syntax72.literal fixedPorts

theorem expression_def :
    expression = Q170Form72.expression (fun j => (fixedPorts j : ℤ)) := rfl

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
    exact Q170Sound72.zero_halts fixedPorts v (ports_zero _ _ _ _) (ports_one _ _ _ _)
      (ports_two _ _ _ _) (ports_three _ _ _ _) hv
      ((Q170Syntax72.literal_zero_iff fixedPorts v).mp hz)
  · rintro ⟨T, hT⟩
    obtain ⟨v, hv, hz⟩ := Q170Complete72.zero_of_halt fixedPorts T hT
      (Carrier65BFSHalt.port_values fixedPorts (ports_zero _ _ _ _) (ports_one _ _ _ _)
        (ports_two _ _ _ _) (ports_three _ _ _ _))
    exact ⟨v, hv, (Q170Syntax72.literal_zero_iff fixedPorts v).mpr hz⟩

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

end DiophantineConsistency.IPRAQuot170p72
