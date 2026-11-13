import DiophantineConsistency.BFS943.Carrier65BFSSource
import DiophantineConsistency.BFS943.Carrier65BFSHalt
import DiophantineConsistency.Compact44.IPRAOrdinary12Chain
import DiophantineConsistency.IPRABoundedRhoZFC

/-! # iPRA endpoints for the Carrier65 polynomial at the direct-BFS943 ports

The Carrier65 polynomial `ObjectCurrentEquation2011.expressionAt` (fourteen
positive unknowns `J, F, α, z, f, i, T, s, w, n, η, ζ, y, γ`, 65 operations,
exact degree 150; package 183's `equation/carrier65.json` circuit) is here
taken at the direct-BFS943 ports of `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`.

In every model of `𝗜𝚺₁` it has a positive zero iff machine 215 halts:

* soundness `Carrier65BFSSource.zero_halts`: the five Carrier65 equations
  (`ArithmeticCarrierSoundness2011.expressionAt_equations`) give a
  `BFS943FixedSource.FixedSource` (power by `maintained_power`, mask,
  transport `z - 1`, half-binomial population), and
  `FixedSourceHalt.source_halts` gives halting;
* completeness `Carrier65BFSHalt.halt_zero`: the direct-BFS943 halting packing
  and outer seed (`DirectBFSHaltPellSeed.halt_seeds_transport`), the auxiliary
  seed `ArithmeticPellAuxiliarySeed.auxiliary_seed`, the assembly
  `ArithmeticConstructionAssembly.equations_of` and
  `ArithmeticConstructionZero.equations_zero`.

The generic helpers of `IPRAOrdinary12Chain` give native, standard and
equality-only iPRA equivalences with the selected Foundation ZFC consistency
predicate; the `translated` variants use `IPRABoundedRhoZFC.zfcEquiv`.

Scope: the endpoints are about the Lean literal at the symbolic ports. Its
correspondence with the JSON circuit is
`research/bfs943-carrier65-calibration/check_lean_graph.py`, and the binding of
the four ports to the direct-BFS943 coefficient hashes is
`reviews/bfs943-source-promotion/tools/check_ports.py` (`fixedPorts` is
textually that of `IPRATrace75`); both are finite external checks, not Lean
theorems about files. -/
set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.IPRACarrier65BFS943
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

/-- The Carrier65 circuit at the fixed ports. -/
def expression : Expr (Fin 14) := ObjectCurrentEquation2011.expressionAt (fun j => (fixedPorts j : ℤ))

theorem expression_def :
    expression = ObjectCurrentEquation2011.expressionAt (fun j => (fixedPorts j : ℤ)) := rfl

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
    exact Carrier65BFSSource.zero_halts fixedPorts v (ports_zero _ _ _ _) (ports_one _ _ _ _)
      (ports_two _ _ _ _) (ports_three _ _ _ _) hv hz
  · rintro ⟨T, hT⟩
    exact Carrier65BFSHalt.halt_zero fixedPorts T hT (ports_zero _ _ _ _) (ports_one _ _ _ _)
      (ports_two _ _ _ _) (ports_three _ _ _ _)

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

end DiophantineConsistency.IPRACarrier65BFS943
