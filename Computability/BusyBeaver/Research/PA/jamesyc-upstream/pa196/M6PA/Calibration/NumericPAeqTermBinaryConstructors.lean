module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermBinaryTemplates
@[expose] public section

/-! Two actual existential value witnesses for the exact addition and
multiplication clauses. Inputs are child formula codes under two binders. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def binaryValue (p : Formula 3) (z left right : V) : V :=
  qqAnd (domainCode z) (qqExs (qqExs (qqAnd left (qqAnd right
    (templateThree p (qqBvar 1) (qqBvar 0) (termBShift language (termBShift language z)))))))
attribute [local irreducible] templateOneGraph templateThreeGraph
noncomputable def binaryValueGraph (p : Formula 3) : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “out z left right. ∃ d z1 z2 b1 b0 tail innermost inner ex2 ex1,
    !domainCodeGraph d z ∧ !(termBShiftGraph language) z1 z ∧ !(termBShiftGraph language) z2 z1 ∧
    !qqBvarDef b1 1 ∧ !qqBvarDef b0 0 ∧ !(templateThreeGraph p) tail b1 b0 z2 ∧
    !qqAndDef innermost right tail ∧ !qqAndDef inner left innermost ∧
    !qqExsDef ex2 inner ∧ !qqExsDef ex1 ex2 ∧ !qqAndDef out d ex1”
theorem binaryValue_graph (p : Formula 3) (out z left right : V) :
    (binaryValueGraph p).val.Evalb ![out,z,left,right] ↔ out=binaryValue p z left right := by
  simp [binaryValueGraph,binaryValue,domainCode,templateThree_graph,Matrix.comp_vecCons'']
instance binaryValue_defined (p : Formula 3) :
    𝚺ᴬ₁-Function₃ (binaryValue p : V → V → V → V) via binaryValueGraph p :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! binaryValue_graph p (v 0) (v 1) (v 2) (v 3)
theorem binaryValue_total_unique (p : Formula 3) (z left right : V) :
    ∃! out, (binaryValueGraph p).val.Evalb ![out,z,left,right] := by
  refine ⟨binaryValue p z left right,(binaryValue_graph _ _ _ _ _).mpr rfl,?_⟩
  intro out h; exact (binaryValue_graph _ _ _ _ _).mp h

theorem binaryValue_quote {m : Nat} (p : Formula 3) (z : Term m)
    (left right : Formula (m+2)) :
    binaryValue p (⌜z⌝ : V) ⌜left⌝ ⌜right⌝=⌜RelationalSource.Ordinal.domain z ⋏
      (∃¹ ∃¹ (left ⋏ (right ⋏ (p ⇜ ![.bvar 1,.bvar 0,Rew.bShift (Rew.bShift z)]))))⌝ := by
  have h0 : (qqBvar (0:V))=(⌜(.bvar 0 : Term (m+2))⌝ : V) := by simp
  have h1 : (qqBvar (1:V))=(⌜(.bvar 1 : Term (m+2))⌝ : V) := by simp
  have hs : termBShift language (termBShift language (⌜z⌝ : V))=⌜Rew.bShift (Rew.bShift z)⌝ := by
    simp [FFL.FirstOrder.Semiterm.quote_def]
  rw [binaryValue,domainCode_quote,h0,h1,hs,templateThree_quote]
  rfl

theorem binaryValue_isSemiformula (p : Formula 3) {n z left right : V}
    (hz : IsSemiterm language n z) (hl : IsSemiformula language ((n+1)+1) left)
    (hr : IsSemiformula language ((n+1)+1) right) :
    IsSemiformula language n (binaryValue p z left right) := by
  apply IsSemiformula.and.mpr
  refine ⟨domainCode_isSemiformula hz, IsSemiformula.exs.mpr (IsSemiformula.exs.mpr
    (IsSemiformula.and.mpr ⟨hl, IsSemiformula.and.mpr ⟨hr, ?_⟩⟩))⟩
  exact templateThree_isSemiformula p (by simp) (by simp) hz.termBShift.termBShift

noncomputable def additionValue (z left right : V) : V := binaryValue additionTemplate z left right
noncomputable def multiplicationValue (z left right : V) : V := binaryValue multiplicationTemplate z left right
noncomputable abbrev additionValueGraph : 𝚺ᴬ₁.Semisentence 4 := binaryValueGraph additionTemplate
noncomputable abbrev multiplicationValueGraph : 𝚺ᴬ₁.Semisentence 4 := binaryValueGraph multiplicationTemplate

theorem additionValue_forward {n m : Nat} (s t : ForwardRelational.SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    additionValue (⌜z⌝ : V)
      ⌜ForwardRelational.value s (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 1)⌝
      ⌜ForwardRelational.value t (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 0)⌝ =
    ⌜ForwardRelational.value (Presentation.add s t) b f z⌝ := by
  rw [additionValue,binaryValue_quote]
  congr 1
  change _ ⋏ (∃¹ ∃¹ (_ ⋏ (_ ⋏ _))) = _ ⋏ (∃¹ ∃¹ (_ ⋏ (_ ⋏ _)))
  rw [show (additionTemplate ⇜ ![.bvar 1,.bvar 0,Rew.bShift (Rew.bShift z)]) =
      RelationalSource.PairGraph.addResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)) from
    RelationalSource.PairGraph.addResult_rew _ _ _ _]
  rfl

theorem multiplicationValue_forward {n m : Nat} (s t : ForwardRelational.SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (z : Term m) :
    multiplicationValue (⌜z⌝ : V)
      ⌜ForwardRelational.value s (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 1)⌝
      ⌜ForwardRelational.value t (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv b))
        (ForwardRelational.shiftEnv (ForwardRelational.shiftEnv f)) (.bvar 0)⌝ =
    ⌜ForwardRelational.value (Presentation.mul s t) b f z⌝ := by
  rw [multiplicationValue,binaryValue_quote]
  congr 1
  change _ ⋏ (∃¹ ∃¹ (_ ⋏ (_ ⋏ _))) = _ ⋏ (∃¹ ∃¹ (_ ⋏ (_ ⋏ _)))
  rw [show (multiplicationTemplate ⇜ ![.bvar 1,.bvar 0,Rew.bShift (Rew.bShift z)]) =
      RelationalSource.PairGraph.mulResult (.bvar 1) (.bvar 0) (Rew.bShift (Rew.bShift z)) from
    RelationalSource.PairGraph.mulResult_rew _ _ _ _]
  rfl

#print axioms binaryValue_graph
#print axioms binaryValue_defined
#print axioms binaryValue_total_unique
#print axioms binaryValue_quote
#print axioms binaryValue_isSemiformula
#print axioms additionValue_forward
#print axioms multiplicationValue_forward
end M6.PA.NumericPAeqTerm

