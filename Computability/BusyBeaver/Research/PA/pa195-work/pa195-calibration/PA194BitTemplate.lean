import PA194BVarCode
import PA194FVarCode
import PA194TagCode
import PA194QuadCode
import PA194NumeralCode

/-! A static compiler from a fixed closed arithmetic syntax template to a
binary PR code for its Foundation syntax encoding. Two outer bound variables
are replaced by source free labels; locally bound variables remain de Bruijn
indices. Structural agreement with an independent numeric specification is proved below;
its connection to the Foundation quote of substitution remains open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194BitTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRAHistoryPairCode PRALanguage PRATheory PRAAddOne
open PA194BVarCode PA194FVarCode PA194TagCode PA194QuadCode PA194NumeralCode

def applyUnary (c : Code 1) (x : Code 2) : Code 2 :=
  .comp c (.cons x (.nil 2))

def applyQuad (a b c d : Code 2) : Code 2 :=
  .comp quadCode (.cons a (.cons b (.cons c (.cons d (.nil 2)))))

def fixed (n : Nat) : Code 2 := numeralCode 2 n

def vectorCode {k : Nat} (v : Fin k → Code 2) : Code 2 :=
  Matrix.foldr (fun h t => bin tagCode h t) (.zero 2) v

def boundVariable (depth i : Nat) : Code 2 :=
  if i < depth then applyUnary bvarCode (fixed i)
  else if i = depth then applyUnary fvarCode (.proj 0)
  else applyUnary fvarCode (.proj 1)

def termCode (depth : Nat) {n : Nat} (t : ClosedSemiterm ℒₒᵣ n) : Code 2 :=
  match t with
  | .bvar i => boundVariable depth i.val
  | .fvar x => Empty.elim x
  | .func (arity := k) f v =>
    applyQuad (fixed 2) (fixed k) (fixed (Encodable.encode f))
      (vectorCode (fun i => termCode depth (v i)))
termination_by t.complexity

def binaryFormula (tag : Nat) (p q : Code 2) : Code 2 :=
  bin tagCode (fixed tag) (bin pairCode p q)

def unaryFormula (tag : Nat) (p : Code 2) : Code 2 := bin tagCode (fixed tag) p

def formulaCode (depth : Nat) {n : Nat} (φ : ArithmeticSemisentence n) : Code 2 :=
  match φ with
  | .verum => unaryFormula 2 (.zero 2)
  | .falsum => unaryFormula 3 (.zero 2)
  | .rel (arity := k) r v =>
    applyQuad (fixed 0) (fixed k) (fixed (Encodable.encode r)) (vectorCode (fun i => termCode depth (v i)))
  | .nrel (arity := k) r v =>
    applyQuad (fixed 1) (fixed k) (fixed (Encodable.encode r)) (vectorCode (fun i => termCode depth (v i)))
  | .and p q => binaryFormula 4 (formulaCode depth p) (formulaCode depth q)
  | .or p q => binaryFormula 5 (formulaCode depth p) (formulaCode depth q)
  | .all p => unaryFormula 6 (formulaCode (depth+1) p)
  | .exs p => unaryFormula 7 (formulaCode (depth+1) p)
termination_by φ.complexity

/-- This finite Code syntax is the candidate membership translator. Its
numeric structural correctness is proved below, but Foundation quote/substitution
correctness and feasible serialization are not established here. -/
def bitTemplateCode : Code 2 := formulaCode 0 bitDef.val

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := DiophantineConsistency.PRAModelIOpenPairing.standardModelIOpen

theorem modelApplyUnary (c : Code 1) (x : Code 2) (a b : M) :
    Structure.func (L := language) (applyUnary c x) ![a,b] =
      Structure.func (L := language) c (fun _ => Structure.func (L := language) x ![a,b]) := by
  rw [applyUnary,modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelApplyQuad (p q r s : Code 2) (a b : M) :
    Structure.func (L := language) (applyQuad p q r s) ![a,b] =
      pair (Structure.func (L := language) p ![a,b])
        (pair (Structure.func (L := language) q ![a,b])
          (pair (Structure.func (L := language) r ![a,b])
            (Structure.func (L := language) s ![a,b]))) + 1 := by
  rw [applyQuad,modelComposition]
  have hv : (fun i : Fin 4 => Structure.func (L := language)
      (getCode (.cons p (.cons q (.cons r (.cons s (.nil 2))))) i) ![a,b]) =
      ![Structure.func (L := language) p ![a,b],Structure.func (L := language) q ![a,b],
        Structure.func (L := language) r ![a,b],Structure.func (L := language) s ![a,b]] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  rw [hv,modelQuadValue]

theorem modelFixed (n : Nat) (a b : M) :
    Structure.func (L := language) (fixed n) ![a,b] = (n : M) := modelNumeralCode 2 n ![a,b]

theorem modelBoundVariable (depth i : Nat) (a b : M) :
    Structure.func (L := language) (boundVariable depth i) ![a,b] =
      if i < depth then pair 0 (i : M) + 1
      else if i = depth then pair 1 a + 1 else pair 1 b + 1 := by
  unfold boundVariable
  split
  · rw [modelApplyUnary,modelFixed,modelBvarValue]
  · split
    · rw [modelApplyUnary,modelProjection,modelFvarValue]
      rfl
    · rw [modelApplyUnary,modelProjection,modelFvarValue]
      rfl

theorem modelVectorCode {k : Nat} (v : Fin k → Code 2) (a b : M) :
    Structure.func (L := language) (vectorCode v) ![a,b] =
      Matrix.foldr (fun x y : M => pair x y + 1) 0
        (fun i => Structure.func (L := language) (v i) ![a,b]) := by
  induction k with
  | zero =>
    simp [vectorCode, PRAMultiplication.modelZero]
    rfl
  | succ k ih =>
    simp only [vectorCode, Matrix.foldr_succ, modelBin, modelTagValue]
    rw [←vectorCode]
    rw [ih]
    rfl

theorem modelUnaryFormula (tag : Nat) (p : Code 2) (a b : M) :
    Structure.func (L := language) (unaryFormula tag p) ![a,b] =
      pair (tag : M) (Structure.func (L := language) p ![a,b]) + 1 := by
  rw [unaryFormula, modelBin, modelFixed, modelTagValue]

theorem modelBinaryFormula (tag : Nat) (p q : Code 2) (a b : M) :
    Structure.func (L := language) (binaryFormula tag p q) ![a,b] =
      pair (tag : M) (pair (Structure.func (L := language) p ![a,b])
        (Structure.func (L := language) q ![a,b])) + 1 := by
  rw [binaryFormula, modelBin, modelFixed, modelBin, modelPairCode, modelTagValue]

/-- Direct numeric specification for a fixed term template with `depth`
internal binders and two outer placeholders. -/
noncomputable def termExpected (depth : Nat) {n : Nat}
    (t : ClosedSemiterm ℒₒᵣ n) (a b : M) : M :=
  match t with
  | .bvar i => if i.val < depth then pair 0 (i.val : M) + 1
      else if i.val = depth then pair 1 a + 1 else pair 1 b + 1
  | .fvar x => Empty.elim x
  | .func (arity := k) f v =>
    pair 2 (pair (k : M) (pair ((Encodable.encode f) : M)
      (Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => termExpected depth (v i) a b)))) + 1
termination_by t.complexity

theorem modelTermCode (depth : Nat) {n : Nat} (t : ClosedSemiterm ℒₒᵣ n) (a b : M) :
    Structure.func (L := language) (termCode depth t) ![a,b] = termExpected depth t a b := by
  induction t with
  | bvar i =>
    rw [termCode,termExpected]
    exact modelBoundVariable depth i.val a b
  | fvar x => exact Empty.elim x
  | @func k f v ih =>
    rw [termCode,termExpected,modelApplyQuad,modelFixed,modelFixed,modelFixed,modelVectorCode]
    congr 4
    congr 1
    funext i
    exact ih i


/-- Direct numeric semantics of the source formula template. -/
noncomputable def formulaExpected (depth : Nat) {n : Nat}
    (φ : ArithmeticSemisentence n) (a b : M) : M :=
  match φ with
  | .verum => pair 2 0 + 1
  | .falsum => pair 3 0 + 1
  | .rel (arity := k) r v =>
    pair 0 (pair (k : M) (pair ((Encodable.encode r) : M)
      (Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => termExpected depth (v i) a b)))) + 1
  | .nrel (arity := k) r v =>
    pair 1 (pair (k : M) (pair ((Encodable.encode r) : M)
      (Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => termExpected depth (v i) a b)))) + 1
  | .and p q => pair 4 (pair (formulaExpected depth p a b) (formulaExpected depth q a b)) + 1
  | .or p q => pair 5 (pair (formulaExpected depth p a b) (formulaExpected depth q a b)) + 1
  | .all p => pair 6 (formulaExpected (depth+1) p a b) + 1
  | .exs p => pair 7 (formulaExpected (depth+1) p a b) + 1
termination_by φ.complexity

theorem modelFormulaCode (depth : Nat) {n : Nat} (φ : ArithmeticSemisentence n) (a b : M) :
    Structure.func (L := language) (formulaCode depth φ) ![a,b] = formulaExpected depth φ a b := by
  induction φ generalizing depth with
  | verum =>
    rw [formulaCode,formulaExpected,modelUnaryFormula,PRAMultiplication.modelZero]
    rfl
  | falsum =>
    rw [formulaCode,formulaExpected,modelUnaryFormula,PRAMultiplication.modelZero]
    rfl
  | @rel n k r v =>
    rw [formulaCode,formulaExpected,modelApplyQuad,modelFixed,modelFixed,modelFixed,modelVectorCode]
    congr 4
    congr 1
    funext i
    exact modelTermCode depth (v i) a b
  | @nrel n k r v =>
    rw [formulaCode,formulaExpected,modelApplyQuad,modelFixed,modelFixed,modelFixed,modelVectorCode]
    simp only [Nat.cast_one]
    congr 4
    congr 1
    funext i
    exact modelTermCode depth (v i) a b
  | and p q ihp ihq =>
    rw [formulaCode,formulaExpected,modelBinaryFormula,ihp,ihq]
    rfl
  | or p q ihp ihq =>
    rw [formulaCode,formulaExpected,modelBinaryFormula,ihp,ihq]
    rfl
  | all p ih =>
    rw [formulaCode,formulaExpected,modelUnaryFormula,ih]
    rfl
  | exs p ih =>
    rw [formulaCode,formulaExpected,modelUnaryFormula,ih]
    rfl

end models
#print axioms modelFormulaCode
#print axioms modelUnaryFormula
#print axioms modelBinaryFormula
#print axioms modelTermCode
#print axioms modelApplyUnary
#print axioms modelApplyQuad
#print axioms modelFixed
#print axioms modelBoundVariable
#print axioms modelVectorCode

#print axioms termCode
#print axioms formulaCode
#print axioms bitTemplateCode
end PA194BitTemplate
