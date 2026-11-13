import DiophantineConsistency.Compact44.IPRAOrdinary12
import DiophantineConsistency.Compact44.FreeJSumSquares
import DiophantineConsistency.Compact44.Absorb89Halt

/-! # iPRA endpoints for the 94-, 92-, 91-, 90- and 89-operation 12-variable graphs

Each graph keeps the 12 positive witnesses and the four fixed compact44 ports
`CompactSymbolicModelIff.p` of the 95-operation free-J graph:

* 94 operations: `FreeJSumSquares.squareLiteral`, the sum of the three residual
  squares, has the same zeros as the 95-operation literal at every valuation
  (`FreeJSumSquares.zero_iff_literal`).
* 92, 91, 90 and 89 operations: `FreeJQCube92`, `FreeJXQ91`,
  `FreeJDirectMainGraph` and `FreeJAbsorb89`. Each of their `*Halt` modules
  proves, in every model of `𝗜𝚺₁`, that the graph has a positive zero iff
  machine 215 halts. The modules reach that statement by chaining
  positive-zero equivalences down to the 95-operation calibration.

`IPRAOrdinary12.bridge_of_positive` turns each of these all-model statements
into a polynomial bridge for the positive shift. The existing pipeline then
gives native, standard and equality-only iPRA equivalences with the selected
Foundation ZFC consistency predicate. As in `IPRAOrdinary12`, the endpoints
are about the Lean literals. Their correspondence with the JSON graphs is the
external `check_lean_graph.py`/`check-dag.py` checks of each candidate
directory. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAOrdinary12Chain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge bridge_of_positive)

theorem native_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e) :
    nativeTheory ⊢ IPRAExpressionNative.nativeNoZero (positiveShift e) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ (bridge_of_positive e h)

theorem standard_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e) :
    IPRAStandardTheory.standardTheory ⊢
      IPRAExpressionNative.nativeNoZero (positiveShift e) 🡘
        ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 (native_of_positive e h)

theorem reference_of_positive {n : ℕ} (e : Expr (Fin n)) (h : PositiveModelBridge e) :
    IPRAEqualityOnlyReference.referenceTheory ⊢
      IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift e)) 🡘
        ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference (native_of_positive e h)

/-! ## 94 operations: three residual squares -/

def expression94 : Expr (Fin 12) := FreeJSumSquares.squareLiteral CompactSymbolicModelIff.p

theorem positiveBridge94 : PositiveModelBridge expression94 := by
  intro V _ _
  refine Iff.trans ?_ (IPRAOrdinary12.positiveBridge V)
  constructor
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, hv, (FreeJSumSquares.zero_iff_literal _ v).1 hz⟩
  · rintro ⟨v, hv, hz⟩
    exact ⟨v, hv, (FreeJSumSquares.zero_iff_literal _ v).2 hz⟩

theorem native_equivalence94 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression94) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge94
theorem standard_equivalence94 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression94) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge94
theorem reference_equivalence94 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression94)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge94

/-! ## 92 operations: quotient coordinate `Y = q³ s` -/

def expression92 : Expr (Fin 12) := (FreeJQCube92.graph CompactSymbolicModelIff.p).output

theorem positiveBridge92 : PositiveModelBridge expression92 :=
  fun V _ _ => FreeJQCube92Halt.positive_model_iff (V := V)

theorem native_equivalence92 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression92) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge92
theorem standard_equivalence92 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression92) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge92
theorem reference_equivalence92 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression92)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge92

/-! ## 91 operations -/

def expression91 : Expr (Fin 12) := (FreeJXQ91.graph CompactSymbolicModelIff.p).output

theorem positiveBridge91 : PositiveModelBridge expression91 :=
  fun V _ _ => FreeJXQ91Halt.positive_model_iff (V := V)

theorem native_equivalence91 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression91) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge91
theorem standard_equivalence91 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression91) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge91
theorem reference_equivalence91 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression91)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge91

/-! ## 90 operations: direct main contribution -/

def expression90 : Expr (Fin 12) := (FreeJDirectMainGraph.graph CompactSymbolicModelIff.p).output

theorem positiveBridge90 : PositiveModelBridge expression90 :=
  fun V _ _ => DirectMainHalt.positive_model_iff (V := V)

theorem native_equivalence90 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression90) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge90
theorem standard_equivalence90 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression90) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge90
theorem reference_equivalence90 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression90)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge90

/-! ## 89 operations: first-root absorption -/

def expression89 : Expr (Fin 12) := (FreeJAbsorb89.graph CompactSymbolicModelIff.p).output

theorem positiveBridge89 : PositiveModelBridge expression89 :=
  fun V _ _ => Absorb89Halt.positive_model_iff (V := V)

theorem native_equivalence89 : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression89) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge89
theorem standard_equivalence89 : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression89) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge89
theorem reference_equivalence89 : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression89)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge89

#print axioms native_equivalence94
#print axioms standard_equivalence94
#print axioms reference_equivalence94
#print axioms native_equivalence92
#print axioms standard_equivalence92
#print axioms reference_equivalence92
#print axioms native_equivalence91
#print axioms standard_equivalence91
#print axioms reference_equivalence91
#print axioms native_equivalence90
#print axioms standard_equivalence90
#print axioms reference_equivalence90
#print axioms native_equivalence89
#print axioms standard_equivalence89
#print axioms reference_equivalence89

end DiophantineConsistency.IPRAOrdinary12Chain
