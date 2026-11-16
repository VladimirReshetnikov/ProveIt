module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermCalibration
@[expose] public section

/-! Literal equality and strict-order presentation atoms. Strict order is the
positive-difference formula ∃z, x + S(z) = y, with both arguments shifted under
the new binder. These are syntax graphs, not interpreted-axiom proofs. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def equalityCode (s t : V) : V := qqRel 2 0 (s∷(t∷0))
noncomputable def lessCode (s t : V) : V := qqExs (equalityCode
  (qqFunc 2 2 (termBShift Presentation.language s∷(qqFunc 1 1 (qqBvar 0∷0)∷0)))
  (termBShift Presentation.language t))
noncomputable def equalityGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out s t. ∃ ts sts, !adjoinDef ts t 0 ∧ !adjoinDef sts s ts ∧ !qqRelDef out 2 0 sts”
noncomputable def lessGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out s t. ∃ ss tt b bs succ succs args add eq,
    !(termBShiftGraph Presentation.language) ss s ∧ !(termBShiftGraph Presentation.language) tt t ∧
    !qqBvarDef b 0 ∧ !adjoinDef bs b 0 ∧ !qqFuncDef succ 1 1 bs ∧
    !adjoinDef succs succ 0 ∧ !adjoinDef args ss succs ∧ !qqFuncDef add 2 2 args ∧
    !equalityGraph eq add tt ∧ !qqExsDef out eq”

theorem equality_graph (out s t : V) : equalityGraph.val.Evalb ![out,s,t] ↔ out=equalityCode s t := by
  simp [equalityGraph,equalityCode]
theorem less_graph (out s t : V) : lessGraph.val.Evalb ![out,s,t] ↔ out=lessCode s t := by
  simp [lessGraph,lessCode,equality_graph,Matrix.comp_vecCons'']

instance equality_defined : 𝚺ᴬ₁-Function₂ (equalityCode : V→V→V) via equalityGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! equality_graph (v 0) (v 1) (v 2)
instance less_defined : 𝚺ᴬ₁-Function₂ (lessCode : V→V→V) via lessGraph :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2]=v := by ext i; fin_cases i <;> rfl
    simpa only [hv] using! less_graph (v 0) (v 1) (v 2)

theorem equality_valid {n s t : V} (hs : IsSemiterm Presentation.language n s)
    (ht : IsSemiterm Presentation.language n t) :
    IsSemiformula Presentation.language n (equalityCode s t) := by
  simp [equalityCode,Presentation.source_relations,hs,ht]
theorem less_valid {n s t : V} (hs : IsSemiterm Presentation.language n s)
    (ht : IsSemiterm Presentation.language n t) :
    IsSemiformula Presentation.language n (lessCode s t) := by
  simp only [lessCode,IsSemiformula.exs]
  apply equality_valid
  · simp [Presentation.source_functions,hs.termBShift]
  · exact ht.termBShift

theorem equality_quote {n : Nat} (s t : SyntacticSemiterm Presentation.language n) :
    equalityCode (⌜s⌝ : V) ⌜t⌝=⌜Presentation.eq s t⌝ := by
  simp [equalityCode,Presentation.eq,SemitermVec.val]
  exact ⟨by rfl,rfl,rfl⟩
theorem less_quote {n : Nat} (s t : SyntacticSemiterm Presentation.language n) :
    lessCode (⌜s⌝ : V) ⌜t⌝=⌜Presentation.less s t⌝ := by
  change qqExs _ = qqExs (⌜Presentation.eq (Presentation.add (Rew.bShift s)
    (Presentation.succ (.bvar 0))) (Rew.bShift t)⌝ : V)
  rw [←equality_quote,quote_paeq_add,Presentation.quote_successor]
  simp [FFL.FirstOrder.Semiterm.quote_def]

#print axioms equality_graph
#print axioms less_graph
#print axioms equality_defined
#print axioms less_defined
#print axioms equality_valid
#print axioms less_valid
#print axioms equality_quote
#print axioms less_quote
end M6.PA.FoundationPAeqCode

