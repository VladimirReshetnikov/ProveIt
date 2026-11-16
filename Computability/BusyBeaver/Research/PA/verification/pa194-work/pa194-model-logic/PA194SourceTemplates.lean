import PA194UniformFullyClosed
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SourceTemplates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Substitute a model-valued target term code into one typed source template. -/
noncomputable def templateOne (p : Semiproposition SourceL 1) (z : V) : V :=
  substs1 SourceL z ⌜p⌝
noncomputable def templateOneGraph (p : Semiproposition SourceL 1) : 𝚺₁.Semisentence 2 :=
  .mkSigma “out z. !(substs1Graph SourceL) out z ↑(⌜p⌝ : Nat)”
theorem templateOne_graph (p : Semiproposition SourceL 1) (out z : V) :
    (templateOneGraph p).val.Evalb ![out,z] ↔ out = templateOne p z := by
  simp [templateOneGraph,templateOne, Semiformula.quote_eq_encode, numeral_eq_natCast]
instance templateOne_defined (p : Semiproposition SourceL 1) :
    𝚺₁-Function₁ (templateOne p : V → V) via templateOneGraph p := .mk fun v => by
  have hv : ![v 0,v 1] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  change (templateOneGraph p).val.Evalb v ↔ v 0 = templateOne p (v 1)
  simpa only [hv] using templateOne_graph p (v 0) (v 1)

theorem templateOne_valid (p : Semiproposition SourceL 1) {n z : V}
    (hz : IsSemiterm SourceL n z) : IsSemiformula SourceL n (templateOne p z) :=
  IsSemiformula.substs1 hz (by simpa using Semiformula.quote_isSemiformula (V := V) p)

theorem templateOne_quote {m : Nat} (p : Semiproposition SourceL 1)
    (z : Semiterm SourceL Nat m) :
    templateOne p (⌜z⌝ : V) = ⌜p ⇜ ![z]⌝ := by
  simp only [templateOne, substs1, Semiformula.quote_def, Semiformula.typed_quote_substs]
  rfl

/-- Simultaneous substitution into a two-variable source template. -/
noncomputable def templateTwo (p : Semiproposition SourceL 2) (x z : V) : V :=
  subst SourceL (?[x,z] : V) ⌜p⌝
noncomputable def templateTwoGraph (p : Semiproposition SourceL 2) : 𝚺₁.Semisentence 3 :=
  .mkSigma “out x z. ∃ zs xs, !adjoinDef zs z 0 ∧ !adjoinDef xs x zs ∧
    !(substsGraph SourceL) out xs ↑(⌜p⌝ : Nat)”
theorem templateTwo_graph (p : Semiproposition SourceL 2) (out x z : V) :
    (templateTwoGraph p).val.Evalb ![out,x,z] ↔ out = templateTwo p x z := by
  simp [templateTwoGraph,templateTwo, Semiformula.quote_eq_encode, numeral_eq_natCast]
instance templateTwo_defined (p : Semiproposition SourceL 2) :
    𝚺₁-Function₂ (templateTwo p : V → V → V) via templateTwoGraph p := .mk fun v => by
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  change (templateTwoGraph p).val.Evalb v ↔ v 0 = templateTwo p (v 1) (v 2)
  simpa only [hv] using templateTwo_graph p (v 0) (v 1) (v 2)

theorem templateTwo_valid (p : Semiproposition SourceL 2) {n x z : V}
    (hx : IsSemiterm SourceL n x) (hz : IsSemiterm SourceL n z) :
    IsSemiformula SourceL n (templateTwo p x z) := by
  apply IsSemiformula.subst (show IsSemiformula SourceL 2 (⌜p⌝ : V) by
    simpa using Semiformula.quote_isSemiformula (V := V) p)
  simp [hx,hz]

theorem templateTwo_quote {m : Nat} (p : Semiproposition SourceL 2)
    (x z : Semiterm SourceL Nat m) :
    templateTwo p (⌜x⌝ : V) ⌜z⌝ = ⌜p ⇜ ![x,z]⌝ := by
  simp only [templateTwo, Semiformula.quote_def, Semiformula.typed_quote_substs]
  rfl

#print axioms templateOne_graph
#print axioms templateOne_valid
#print axioms templateOne_quote
#print axioms templateTwo_graph
#print axioms templateTwo_valid
#print axioms templateTwo_quote
end generic
end PA194SourceTemplates
