import PA194TemplateInternal
import PA194EqAtomCode
import PA194NumeralCode

/-! Primitive-recursive positive/negative pairs for source truth and atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194DualAtomCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PA194NumeralCode PA194BitTemplate PA194TemplateInternal
  PA194CanonicalVectorCode PA194EqAtomCode

/-- Both fixed truth values as a pair `(verum, falsum)`. -/
def dualTruthCode : Code 1 := bin pairCode (numeralCode 1 7) (numeralCode 1 13)

/-- Negate the single fixed bit formula syntactically at code-construction
 time, rather than applying a recursive negation code at runtime. -/
def negativeBitCode : Code 2 := formulaCode 0 (∼bitDef.val)
def dualBitCode : Code 2 := bin pairCode bitTemplateCode negativeBitCode

/-- Negated equality atom using the exact arity-two free-variable vector. -/
def negativeEqCode : Code 2 :=
  bin addCode
    (bin pairCode (numeralCode 2 1)
      (bin pairCode (numeralCode 2 2) (bin pairCode (.zero 2) vectorCode)))
    (numeralCode 2 1)
def dualEqCode : Code 2 := bin pairCode eqAtomCode negativeEqCode

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelDualTruth (n : M) : F dualTruthCode (fun _ => n) =
    pair (pair 2 0 + 1) (pair 3 0 + 1) := by
  rw [dualTruthCode,modelBin,modelNumeralCode,modelNumeralCode,modelPairCode]
  norm_num [pair]

theorem modelDualTruthInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (n : M) :
    F dualTruthCode (fun _ => n) = pair (qqVerum : M) (qqFalsum : M) := by
  rw [modelDualTruth,qqVerum,qqFalsum]

/-- Numeric structural meaning of the positive and negated fixed bit
formula, with no IΣ₁ assumption. -/
theorem modelDualBit (a b : M) : F dualBitCode ![a,b] =
    pair (formulaExpected 0 bitDef.val a b) (formulaExpected 0 (∼bitDef.val) a b) := by
  rw [dualBitCode,modelBin,modelPairCode,bitTemplateCode,modelFormulaCode,
      negativeBitCode,modelFormulaCode]

theorem modelDualBitInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : M) :
    F dualBitCode ![a,b] = pair
      (Bootstrapping.Semiformula.subst (substEnv a b 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val
      (Bootstrapping.Semiformula.subst (substEnv a b 0)
        (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelDualBit,formulaExpected_internal 0 bitDef.val a b,
      formulaExpected_internal 0 (∼bitDef.val) a b]

theorem modelNegativeEq (a b : M) : F negativeEqCode ![a,b] =
    pair 1 (pair 2 (pair 0 (F vectorCode ![a,b]))) + 1 := by
  rw [negativeEqCode,modelBin,modelBin,modelBin,modelBin,
    modelNumeralCode,modelNumeralCode,modelPairCode,modelPairCode,modelPairCode,
    PRAMultiplication.modelZero]
  simp only [Nat.cast_one,Nat.cast_ofNat]
  rfl

theorem modelDualEq (a b : M) : F dualEqCode ![a,b] =
    pair (F eqAtomCode ![a,b]) (pair 1 (pair 2 (pair 0 (F vectorCode ![a,b]))) + 1) := by
  rw [dualEqCode,modelBin,modelPairCode,modelNegativeEq]

theorem modelDualEqInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : M) : F dualEqCode ![a,b] =
    pair (qqRel 2 0 (matrixToVec ![qqFvar a,qqFvar b]))
         (qqNRel 2 0 (matrixToVec ![qqFvar a,qqFvar b])) := by
  rw [modelDualEq,modelEqAtomMatchesFoundation,modelVectorValue,matchesFoundationMatrix]
  rfl

#print axioms modelDualTruth
#print axioms modelDualTruthInternal
#print axioms modelDualBit
#print axioms modelDualBitInternal
#print axioms modelNegativeEq
#print axioms modelDualEq
#print axioms modelDualEqInternal
end models
end PA194DualAtomCode
