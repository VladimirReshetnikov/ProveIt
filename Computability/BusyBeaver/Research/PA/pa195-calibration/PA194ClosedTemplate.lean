import PA194CloseVariable
import PA194BitTemplate
import PA194CloseRew
import PA194TemplateRew

/-! Closing the two source labels inside a fixed formula template. The template
is external and finite; labels are arbitrary model elements. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ClosedTemplate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRAHistoryPairCode PRALanguage PRATheory PRAAddOne
open PA194BVarCode PA194FVarCode PA194TagCode PA194QuadCode PA194NumeralCode
open PA194CloseVariable

def fixed (n : Nat) : Code 3 := numeralCode 3 n

def unary (c : Code 1) (x : Code 3) : Code 3 := .comp c (.cons x (.nil 3))
def quad (a b c d : Code 3) : Code 3 :=
  .comp quadCode (.cons a (.cons b (.cons c (.cons d (.nil 3)))))
def vectorCode {k : Nat} (v : Fin k → Code 3) : Code 3 :=
  Matrix.foldr (fun h t => bin tagCode h t) (.zero 3) v

def closeOuter (which : Fin 3) (depth : Nat) : Code 3 :=
  .comp closeFreeCode (.cons (.proj 0) (.cons (.proj which) (.cons (fixed depth) (.nil 3))))

def boundVariable (depth i : Nat) : Code 3 :=
  if i < depth then unary bvarCode (fixed i)
  else if i = depth then closeOuter 1 depth else closeOuter 2 depth

def termCode (depth : Nat) {n : Nat} (t : ClosedSemiterm ℒₒᵣ n) : Code 3 :=
  match t with
  | .bvar i => boundVariable depth i.val
  | .fvar x => Empty.elim x
  | .func (arity := k) f v =>
    quad (fixed 2) (fixed k) (fixed (Encodable.encode f))
      (vectorCode (fun i => termCode depth (v i)))
termination_by t.complexity

def binaryFormula (tag : Nat) (p q : Code 3) : Code 3 :=
  bin tagCode (fixed tag) (bin pairCode p q)
def unaryFormula (tag : Nat) (p : Code 3) : Code 3 := bin tagCode (fixed tag) p

def formulaCode (depth : Nat) {n : Nat} (φ : ArithmeticSemisentence n) : Code 3 :=
  match φ with
  | .verum => unaryFormula 2 (.zero 3)
  | .falsum => unaryFormula 3 (.zero 3)
  | .rel (arity := k) r v =>
    quad (fixed 0) (fixed k) (fixed (Encodable.encode r)) (vectorCode (fun i => termCode depth (v i)))
  | .nrel (arity := k) r v =>
    quad (fixed 1) (fixed k) (fixed (Encodable.encode r)) (vectorCode (fun i => termCode depth (v i)))
  | .and p q => binaryFormula 4 (formulaCode depth p) (formulaCode depth q)
  | .or p q => binaryFormula 5 (formulaCode depth p) (formulaCode depth q)
  | .all p => unaryFormula 6 (formulaCode (depth+1) p)
  | .exs p => unaryFormula 7 (formulaCode (depth+1) p)
termination_by φ.complexity

def bitCloseCode : Code 3 := formulaCode 0 bitDef.val

def negativeBitCloseCode : Code 3 := formulaCode 0 (∼bitDef.val)

/-- Substitute the two labels and then close one label under the current depth. -/
def closedDepthRew (label a b depth : Nat) : Rew ℒₒᵣ Empty (depth+2) Nat (depth+1) :=
  (PA194CloseRew.closeDepthRew label depth).comp (PA194TemplateRew.depthRew a b depth)

theorem closedDepthRew_q (label a b depth : Nat) :
    closedDepthRew label a b (depth+1) = (closedDepthRew label a b depth).q := by
  simp only [closedDepthRew, PA194CloseRew.closeDepthRew, PA194TemplateRew.depthRew, Rew.q_comp]

theorem closedDepthRew_var (label a b depth : Nat) (i : Fin (depth+2)) :
    closedDepthRew label a b depth #i =
      if h : i.val < depth then #(Fin.castSucc ⟨i.val,h⟩)
      else if i.val = depth then (if a = label then #(Fin.last depth) else &a)
      else (if b = label then #(Fin.last depth) else &b) := by
  rw [closedDepthRew, Rew.comp_app, PA194TemplateRew.depthRew_var]
  split
  · rw [PA194CloseRew.closeDepthRew_bvar]
  · split <;> rw [PA194CloseRew.closeDepthRew_fvar]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

theorem modelUnary (c : Code 1) (x : Code 3) (e : Fin 3 → M) :
    F (unary c x) e = F c (fun _ => F x e) := by
  rw [unary,modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelQuad (p q r s : Code 3) (e : Fin 3 → M) :
    F (quad p q r s) e = pair (F p e) (pair (F q e) (pair (F r e) (F s e))) + 1 := by
  rw [quad,modelComposition]
  have hv : (fun i : Fin 4 => F (getCode (.cons p (.cons q (.cons r (.cons s (.nil 3))))) i) e) =
      ![F p e,F q e,F r e,F s e] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  rw [hv,modelQuadValue]

theorem modelFixed (n : Nat) (e : Fin 3 → M) : F (fixed n) e = (n : M) := modelNumeralCode 3 n e

theorem modelCloseOuter (which : Fin 3) (d : Nat) (e : Fin 3 → M) :
    F (closeOuter which d) e = if e 0 = e which then pair 0 (d : M) + 1 else pair 1 (e which) + 1 := by
  rw [closeOuter,modelComposition]
  have hv : (fun i : Fin 3 => F (getCode (.cons (.proj 0) (.cons (.proj which) (.cons (fixed d) (.nil 3)))) i) e) = ![e 0,e which,(d : M)] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection 0 e
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact modelProjection which e
      · exact Fin.cases (modelFixed d e) (fun l => Fin.elim0 l) k
  rw [hv,modelCloseFree]

theorem modelBoundVariable (depth i : Nat) (e : Fin 3 → M) :
    F (boundVariable depth i) e =
      if i < depth then pair 0 (i : M) + 1
      else if i = depth then (if e 0 = e 1 then pair 0 (depth : M) + 1 else pair 1 (e 1) + 1)
      else (if e 0 = e 2 then pair 0 (depth : M) + 1 else pair 1 (e 2) + 1) := by
  unfold boundVariable
  split
  · rw [modelUnary,modelFixed,modelBvarValue]
  · split <;> rw [modelCloseOuter]

theorem modelVectorCode {k : Nat} (v : Fin k → Code 3) (e : Fin 3 → M) :
    F (vectorCode v) e = Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => F (v i) e) := by
  induction k with
  | zero => simp [vectorCode, PRAMultiplication.modelZero]; rfl
  | succ k ih =>
    simp only [vectorCode, Matrix.foldr_succ, modelBin, modelTagValue]
    rw [←vectorCode, ih]
    rfl

noncomputable def termExpected (depth : Nat) {n : Nat}
    (t : ClosedSemiterm ℒₒᵣ n) (label a b : M) : M :=
  match t with
  | .bvar i => if i.val < depth then pair 0 (i.val : M) + 1
      else if i.val = depth then (if label = a then pair 0 (depth : M) + 1 else pair 1 a + 1)
      else (if label = b then pair 0 (depth : M) + 1 else pair 1 b + 1)
  | .fvar x => Empty.elim x
  | .func (arity := k) f v =>
    pair 2 (pair (k : M) (pair ((Encodable.encode f) : M)
      (Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => termExpected depth (v i) label a b)))) + 1
termination_by t.complexity

theorem modelTermCode (depth : Nat) {n : Nat} (t : ClosedSemiterm ℒₒᵣ n) (label a b : M) :
    F (termCode depth t) ![label,a,b] = termExpected depth t label a b := by
  induction t with
  | bvar i => rw [termCode,termExpected,modelBoundVariable]; rfl
  | fvar x => exact Empty.elim x
  | @func k f v ih =>
    rw [termCode,termExpected,modelQuad,modelFixed,modelFixed,modelFixed,modelVectorCode]
    congr 4
    congr 1
    funext i
    exact ih i

noncomputable def formulaExpected (depth : Nat) {n : Nat}
    (φ : ArithmeticSemisentence n) (label a b : M) : M :=
  match φ with
  | .verum => pair 2 0 + 1
  | .falsum => pair 3 0 + 1
  | .rel (arity := k) r v =>
    pair 0 (pair (k : M) (pair ((Encodable.encode r) : M)
      (Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => termExpected depth (v i) label a b)))) + 1
  | .nrel (arity := k) r v =>
    pair 1 (pair (k : M) (pair ((Encodable.encode r) : M)
      (Matrix.foldr (fun x y : M => pair x y + 1) 0 (fun i => termExpected depth (v i) label a b)))) + 1
  | .and p q => pair 4 (pair (formulaExpected depth p label a b) (formulaExpected depth q label a b)) + 1
  | .or p q => pair 5 (pair (formulaExpected depth p label a b) (formulaExpected depth q label a b)) + 1
  | .all p => pair 6 (formulaExpected (depth+1) p label a b) + 1
  | .exs p => pair 7 (formulaExpected (depth+1) p label a b) + 1
termination_by φ.complexity

theorem modelUnaryFormula (tag : Nat) (p : Code 3) (e : Fin 3 → M) :
    F (unaryFormula tag p) e = pair (tag : M) (F p e) + 1 := by
  rw [unaryFormula,modelBin,modelFixed,modelTagValue]
theorem modelBinaryFormula (tag : Nat) (p q : Code 3) (e : Fin 3 → M) :
    F (binaryFormula tag p q) e = pair (tag : M) (pair (F p e) (F q e)) + 1 := by
  rw [binaryFormula,modelBin,modelFixed,modelBin,modelPairCode,modelTagValue]

theorem modelFormulaCode (depth : Nat) {n : Nat} (φ : ArithmeticSemisentence n) (label a b : M) :
    F (formulaCode depth φ) ![label,a,b] = formulaExpected depth φ label a b := by
  induction φ generalizing depth with
  | verum => rw [formulaCode,formulaExpected,modelUnaryFormula,PRAMultiplication.modelZero]; rfl
  | falsum => rw [formulaCode,formulaExpected,modelUnaryFormula,PRAMultiplication.modelZero]; rfl
  | @rel n k r v =>
    rw [formulaCode,formulaExpected,modelQuad,modelFixed,modelFixed,modelFixed,modelVectorCode]
    congr 4
    congr 1
    funext i
    exact modelTermCode depth (v i) label a b
  | @nrel n k r v =>
    rw [formulaCode,formulaExpected,modelQuad,modelFixed,modelFixed,modelFixed,modelVectorCode]
    simp only [Nat.cast_one]
    congr 4
    congr 1
    funext i
    exact modelTermCode depth (v i) label a b
  | and p q ihp ihq =>
    rw [formulaCode,formulaExpected,modelBinaryFormula, ihp, ihq]
    simp only [Nat.cast_ofNat]
  | or p q ihp ihq =>
    rw [formulaCode,formulaExpected,modelBinaryFormula, ihp, ihq]
    simp only [Nat.cast_ofNat]
  | all p ih =>
    rw [formulaCode,formulaExpected,modelUnaryFormula, ih]
    simp only [Nat.cast_ofNat]
  | exs p ih =>
    rw [formulaCode,formulaExpected,modelUnaryFormula, ih]
    simp only [Nat.cast_ofNat]

/-- The positive bit case holds for arbitrary model-valued labels. -/
theorem modelBitCloseValue (label a b : M) :
    F bitCloseCode ![label,a,b] = formulaExpected 0 bitDef.val label a b :=
  modelFormulaCode 0 bitDef.val label a b

/-- The negative bit case also holds for arbitrary model-valued labels. -/
theorem modelNegativeBitCloseValue (label a b : M) :
    F negativeBitCloseCode ![label,a,b] = formulaExpected 0 (∼bitDef.val) label a b :=
  modelFormulaCode 0 (∼bitDef.val) label a b

/-- The fixed-template code quotes the exact closed rewrite for standard
labels in an IΣ₁ model. The numeric construction above needs only candidate PRA. -/
theorem termExpected_quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (d : Nat) (t : ClosedSemiterm ℒₒᵣ (d+2)) (label a b : Nat) :
    termExpected d t (label : M) (a : M) (b : M) =
      (⌜closedDepthRew label a b d t⌝ : M) := by
  induction t with
  | bvar i =>
    rw [termExpected,closedDepthRew_var]
    split
    · simp [Semiterm.quote_bvar,qqBvar]
    · split
      · rw [←modelCloseFree, PA194CloseRew.modelCloseFreeQuote]
        rw [PA194CloseRew.closeDepthRew_fvar]
      · rw [←modelCloseFree, PA194CloseRew.modelCloseFreeQuote]
        rw [PA194CloseRew.closeDepthRew_fvar]
  | fvar z => exact Empty.elim z
  | @func k f v ih =>
    rw [termExpected, Rew.func, Semiterm.quote_func]
    simp only [qqFunc]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact ih i

theorem formulaExpected_quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (d : Nat) (φ : ArithmeticSemisentence (d+2)) (label a b : Nat) :
    formulaExpected d φ (label : M) (a : M) (b : M) =
      (⌜closedDepthRew label a b d ▹ φ⌝ : M) := by
  cases φ with
  | verum =>
    rw [formulaExpected]
    change pair 2 0 + 1 = (⌜(⊤ : Semiproposition ℒₒᵣ (d+1))⌝ : M)
    simp [Semiformula.quote_verum, qqVerum]
  | falsum =>
    rw [formulaExpected]
    change pair 3 0 + 1 = (⌜(⊥ : Semiproposition ℒₒᵣ (d+1))⌝ : M)
    simp [Semiformula.quote_falsum, qqFalsum]
  | rel r v =>
    rw [formulaExpected, Semiformula.rew_rel, Semiformula.quote_rel]
    simp only [qqRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_quote d (v i) label a b
  | nrel r v =>
    rw [formulaExpected, Semiformula.rew_nrel, Semiformula.quote_nrel]
    simp only [qqNRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_quote d (v i) label a b
  | and p q =>
    rw [formulaExpected]
    change pair 4 (pair (formulaExpected d p (label : M) (a : M) (b : M))
        (formulaExpected d q (label : M) (a : M) (b : M))) + 1 =
      (⌜(closedDepthRew label a b d ▹ p) ⋏ (closedDepthRew label a b d ▹ q)⌝ : M)
    rw [Semiformula.quote_and]
    change pair 4 (pair (formulaExpected d p (label : M) (a : M) (b : M))
        (formulaExpected d q (label : M) (a : M) (b : M))) + 1 =
      pair 4 (pair (⌜closedDepthRew label a b d ▹ p⌝ : M)
        (⌜closedDepthRew label a b d ▹ q⌝ : M)) + 1
    rw [formulaExpected_quote d p label a b, formulaExpected_quote d q label a b]
  | or p q =>
    rw [formulaExpected]
    change pair 5 (pair (formulaExpected d p (label : M) (a : M) (b : M))
        (formulaExpected d q (label : M) (a : M) (b : M))) + 1 =
      (⌜(closedDepthRew label a b d ▹ p) ⋎ (closedDepthRew label a b d ▹ q)⌝ : M)
    rw [Semiformula.quote_or]
    change pair 5 (pair (formulaExpected d p (label : M) (a : M) (b : M))
        (formulaExpected d q (label : M) (a : M) (b : M))) + 1 =
      pair 5 (pair (⌜closedDepthRew label a b d ▹ p⌝ : M)
        (⌜closedDepthRew label a b d ▹ q⌝ : M)) + 1
    rw [formulaExpected_quote d p label a b, formulaExpected_quote d q label a b]
  | all p =>
    rw [formulaExpected]
    change pair 6 (formulaExpected (d+1) p (label : M) (a : M) (b : M)) + 1 =
      (⌜∀⁰ ((closedDepthRew label a b d).q ▹ p)⌝ : M)
    rw [Semiformula.quote_all]
    change pair 6 (formulaExpected (d+1) p (label : M) (a : M) (b : M)) + 1 =
      pair 6 (⌜(closedDepthRew label a b d).q ▹ p⌝ : M) + 1
    rw [←closedDepthRew_q, formulaExpected_quote (d+1) p label a b]
  | exs p =>
    rw [formulaExpected]
    change pair 7 (formulaExpected (d+1) p (label : M) (a : M) (b : M)) + 1 =
      (⌜∃⁰ ((closedDepthRew label a b d).q ▹ p)⌝ : M)
    rw [Semiformula.quote_ex]
    change pair 7 (formulaExpected (d+1) p (label : M) (a : M) (b : M)) + 1 =
      pair 7 (⌜(closedDepthRew label a b d).q ▹ p⌝ : M) + 1
    rw [←closedDepthRew_q, formulaExpected_quote (d+1) p label a b]
termination_by φ.complexity

/-- For standard labels and an IΣ₁ model, the generated positive bit
template is the quote of the actual capture-avoiding closing rewrite. -/
theorem modelBitCloseQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (label a b : Nat) :
    F bitCloseCode ![(label : M),(a : M),(b : M)] =
      (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew a b ▹ bitDef.val)⌝ : M) := by
  rw [bitCloseCode,modelFormulaCode,formulaExpected_quote]
  change (⌜((PA194CloseRew.closeDepthRew label 0).comp (PA194TemplateRew.outerRew a b)) ▹ bitDef.val⌝ : M) = _
  rw [TransitiveRewriting.comp_app]
  rfl

/-- The same quote theorem for the negated fixed bit template. -/
theorem modelNegativeBitCloseQuote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (label a b : Nat) :
    F negativeBitCloseCode ![(label : M),(a : M),(b : M)] =
      (⌜PA194BindTranslation.closeLabel label (PA194TemplateRew.outerRew a b ▹ (∼bitDef.val))⌝ : M) := by
  rw [negativeBitCloseCode,modelFormulaCode,formulaExpected_quote]
  change (⌜((PA194CloseRew.closeDepthRew label 0).comp (PA194TemplateRew.outerRew a b)) ▹ (∼bitDef.val)⌝ : M) = _
  rw [TransitiveRewriting.comp_app]
  rfl

#print axioms modelBitCloseValue
#print axioms modelNegativeBitCloseValue
#print axioms modelBitCloseQuote
#print axioms modelNegativeBitCloseQuote
#print axioms formulaExpected_quote
#print axioms termExpected_quote
#print axioms modelFormulaCode
#print axioms modelTermCode
#print axioms modelCloseOuter
end models
end PA194ClosedTemplate
