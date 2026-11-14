import PA194ModelNeighborhoodCode
import PA194AtomShiftCodeModel

/-! Finite candidate-PRA codes decode positive and negative Foundation source equality
atoms and select labels from encoded bound/free environments. All model inputs may be
nonstandard. These results do not yet translate compound formula codes. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194AtomShiftCodeModel PA194VectorShiftCodeModel
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor



/-- Input: encoded source term, bound-label stack, free-label stack. -/
noncomputable def termLabelCode : Code 3 :=
  let d : Code 3 := unary predCode (.proj 0)
  let tag : Code 3 := unary firstProjection d
  let i : Code 3 := unary secondProjection d
  selectAmong tag (bin PA194TargetStep.lookup i (.proj 2)) (bin PA194TargetStep.lookup i (.proj 1))

/-- Input: a Foundation source equality-atom code, bound and free label stacks, and reserved label. -/
noncomputable def equalityAtomCode : Code 4 :=
  let d : Code 4 := unary predCode (.proj 0)
  let arityAndRest : Code 4 := unary secondProjection d
  let relAndTerms : Code 4 := unary secondProjection arityAndRest
  let terms : Code 4 := unary secondProjection relAndTerms
  let v : Code 4 := unary predCode terms
  let a : Code 4 := unary firstProjection v
  let tail : Code 4 := unary secondProjection v
  let b : Code 4 := unary firstProjection (unary predCode tail)
  let la : Code 4 := PA194TargetStep.app3 termLabelCode a (.proj 1) (.proj 2)
  let lb : Code 4 := PA194TargetStep.app3 termLabelCode b (.proj 1) (.proj 2)
  neighborhoodCode la lb (.proj 3)

/-- The same decoded equality atom with the source polarity negated. -/
noncomputable def negativeEqualityAtomCode : Code 4 := machineNeg equalityAtomCode

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termLabel_bound (i bound free : M) :
    F termLabelCode ![^#i,bound,free] = F PA194TargetStep.lookup ![i,bound] := by
  simp only [termLabelCode,modelSelectAmong,modelUnary,modelBin,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  have hp : F predCode (fun _ => ^#i) = pair 0 i := by
    simpa [qqBvar] using modelPredAddOne (pair (0 : M) i)
  rw [hp,pi₁_pair,pi₂_pair]
  change F selectCode ![(0 : M),F PA194TargetStep.lookup ![i,free],F PA194TargetStep.lookup ![i,bound]] = _
  exact modelSelectZero (M := M) _ _

theorem termLabel_free (i bound free : M) :
    F termLabelCode ![^&i,bound,free] = F PA194TargetStep.lookup ![i,free] := by
  simp only [termLabelCode,modelSelectAmong,modelUnary,modelBin,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  have hp : F predCode (fun _ => ^&i) = pair 1 i := by
    simpa [qqFvar] using modelPredAddOne (pair (1 : M) i)
  rw [hp,pi₁_pair,pi₂_pair]
  change F selectCode ![(1 : M),F PA194TargetStep.lookup ![i,free],F PA194TargetStep.lookup ![i,bound]] = _
  exact modelSelectOne (M := M) _ _

/-- The existing PA194 lookup code agrees with Foundation's nth operation. -/
theorem termLabel_bound_nth (i bound free : M) :
    F termLabelCode ![^#i,bound,free] = bound.[i] := by
  rw [termLabel_bound]
  exact PA194SearchVector.lookup_nth i bound

theorem termLabel_free_nth (i bound free : M) :
    F termLabelCode ![^&i,bound,free] = free.[i] := by
  rw [termLabel_free]
  exact PA194SearchVector.lookup_nth i free

theorem equalityAtom_model (a b bound free z : M) :
    F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,z] =
      neighborhoodValue (F termLabelCode ![a,bound,free]) (F termLabelCode ![b,bound,free]) z := by
  simp only [equalityAtomCode,neighborhoodCode_model,PA194TargetStep.app3_model,modelUnary,modelBin,
    modelProjection,modelSucc,modelPairCode,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [qqRel,modelPredAddOne,pi₁_pair,pi₂_pair]
  rfl

theorem termLabel_valid {t : M} (ht : IsUTerm M6.PA.RelationalSource.language t)
    (bound free : M) :
    (∃ i, t = ^#i ∧ F termLabelCode ![t,bound,free] = F PA194TargetStep.lookup ![i,bound]) ∨
    (∃ i, t = ^&i ∧ F termLabelCode ![t,bound,free] = F PA194TargetStep.lookup ![i,free]) := by
  rcases PA194TermShiftModel.term_cases ht with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact Or.inl ⟨i,rfl,termLabel_bound i bound free⟩
  · exact Or.inr ⟨i,rfl,termLabel_free i bound free⟩

theorem equalityAtom_complete {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (bound free z : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧
      IsUTerm M6.PA.RelationalSource.language b ∧
      F equalityAtomCode ![^rel (2 : M) (0 : M) v,bound,free,z] =
        neighborhoodValue (F termLabelCode ![a,bound,free]) (F termLabelCode ![b,bound,free]) z := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  refine ⟨a,b,ha,hb,?_⟩
  simpa [adjoin_def] using equalityAtom_model a b bound free z

theorem negativeEqualityAtom_model (a b bound free z : M) :
    F negativeEqualityAtomCode ![^nrel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,z] =
      negValue (neighborhoodValue (F termLabelCode ![a,bound,free]) (F termLabelCode ![b,bound,free]) z) := by
  simp only [negativeEqualityAtomCode,machineNeg_model,equalityAtomCode,neighborhoodCode_model,
    PA194TargetStep.app3_model,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [qqNRel,modelPredAddOne,pi₁_pair,pi₂_pair]
  rfl

theorem negativeEqualityAtom_complete {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (bound free z : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧
      IsUTerm M6.PA.RelationalSource.language b ∧
      F negativeEqualityAtomCode ![^nrel (2 : M) (0 : M) v,bound,free,z] =
        negValue (neighborhoodValue (F termLabelCode ![a,bound,free]) (F termLabelCode ![b,bound,free]) z) := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  refine ⟨a,b,ha,hb,?_⟩
  simpa [adjoin_def] using negativeEqualityAtom_model a b bound free z

theorem equalityAtomGraph (atom bound free z y : M) :
    (PA194CodeGraph.graph equalityAtomCode).val.Eval ![y,atom,bound,free,z] Empty.elim ↔
      y = F equalityAtomCode ![atom,bound,free,z] := by
  have h := (PA194CodeGraph.modelGraph (M := M) equalityAtomCode).defined ![y,atom,bound,free,z]
  have he : (fun i : Fin 4 => ![y,atom,bound,free,z] i.succ) = ![atom,bound,free,z] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  simp only [Matrix.cons_val_zero] at h
  rw [he] at h
  exact h

#print axioms negativeEqualityAtom_complete
#print axioms equalityAtomGraph
#print axioms termLabel_bound_nth
#print axioms termLabel_free_nth
#print axioms termLabel_valid
#print axioms equalityAtom_complete
#print axioms negativeEqualityAtom_model
#print axioms termLabel_bound
#print axioms termLabel_free
#print axioms equalityAtom_model
end models
end PA194ModelLogic
