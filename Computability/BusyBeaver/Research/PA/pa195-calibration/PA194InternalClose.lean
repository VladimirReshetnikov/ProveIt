import PA194TermWellFormedUnconditional
/-! Comparison of the candidate-PRA term-closing code with an internal
Foundation term-recursion construction. The two input parameters and every
term code may be nonstandard elements of the model. This construction is an
instance of Foundation's general TermRec interface; Foundation's existing
`termSubst` substitutes bound variables and is a different operation. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194InternalClose
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

/-- Closing a free label while inserting a binder at the given depth. For
arbitrary raw bound indices, those at or above the depth are shifted. -/
def blueprint : Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “y z label depth. (z < depth → !qqBvarDef y z) ∧ (¬z < depth → !qqBvarDef y (z + 1))”
  fvar := .mkSigma “y x label depth. (label = x → !qqBvarDef y depth) ∧ (¬label = x → !qqFvarDef y x)”
  func := .mkSigma “y k f v v' label depth. !qqFuncDef y k f v'”

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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def construction : Language.TermRec.Construction M blueprint where
  bvar p z := if z < p 1 then ^#z else ^#(z+1)
  fvar p x := if p 0 = x then ^#(p 1) else ^&x
  func _ k f _ v' := ^func k f v'
  bvar_defined := .mk fun v => by
    by_cases h : v 1 < v 3 <;> simp [blueprint,h]
  fvar_defined := .mk fun v => by
    by_cases h : v 2 = v 1 <;> simp [blueprint,h]
  func_defined := .mk fun v => by simp [blueprint]

/-- The Foundation internal term-recursion result, total on all codes. -/
noncomputable def close (label depth t : M) : M := construction.result ℒₒᵣ ![label,depth] t

theorem close_definable (label depth : M) : 𝚺₁-Function₁ (close label depth) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 3 → M => construction.result ℒₒᵣ (v ·.succ) (v 0)) :=
    HierarchySymbol.Defined.to_definable _ (construction.result_defined (L := ℒₒᵣ))
  have hi : ∀ j : Fin 3, 𝚺₁.DefinableFunction (fun v : Fin 1 → M => ![v 0,label,depth] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 0
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact HierarchySymbol.DefinableFunction.const label
      · exact Fin.cases (HierarchySymbol.DefinableFunction.const depth) (fun x => Fin.elim0 x) l
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  change 𝚺₁.DefinableFunction (fun v : Fin 1 → M => close label depth (v 0))
  convert h using 1
  funext v
  unfold close
  congr 1

/-- Equality on all model-internal semiterms. -/
theorem agree (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    F (PA194TermRecursion.closeCode first second) ![t,label,depth] = close label depth t := by
  have hdef : 𝚺₁-Predicate (fun t : M => F (PA194TermRecursion.closeCode first second) ![t,label,depth] = close label depth t) := by
    haveI := PA194CodeInstance.unary_of_three (PA194TermRecursion.closeCode first second) label depth
    haveI := close_definable label depth
    definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz
    simp only [qqBvar]
    rw [PA194TermRecursion.modelCloseBound first second hf hs]
    change (if z < depth then ^#z else ^#(z+1)) = construction.result ℒₒᵣ ![label,depth] (^#z)
    rw [Language.TermRec.Construction.result_bvar]
    simp [construction]
  · intro x
    simp only [qqFvar]
    rw [PA194TermRecursion.modelCloseFree first second hf hs]
    change (if label = x then ^#depth else ^&x) = construction.result ℒₒᵣ ![label,depth] (^&x)
    rw [Language.TermRec.Construction.result_fvar]
    simp [construction]
  · intro k f v hfunc hv ih
    have hk : k = 0 ∨ k = 2 := by
      rcases (Arithmetic.isFunc_iff_LOR (V := M)).mp hfunc with (⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩)
      all_goals simp_all
    rcases hk with rfl | rfl
    · have hv0 : v = 0 := IsSemitermVec.empty_iff.mp hv
      subst v
      change F (PA194TermRecursion.closeCode first second) ![pair 2 (pair 0 (pair f 0))+1,label,depth] = close label depth (^func 0 f 0)
      rw [PA194TermRecursion.modelCloseNullary first second hf hs]
      change (^func 0 f 0) = construction.result ℒₒᵣ ![label,depth] (^func 0 f 0)
      rw [Language.TermRec.Construction.result_func' construction hfunc hv.isUTerm]
      simp [construction]
    · obtain ⟨x,y,hx,hy,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
      have ihx : F (PA194TermRecursion.closeCode first second) ![x,label,depth] = close label depth x := by
        simpa using ih 0 (by norm_num)
      have ihy : F (PA194TermRecursion.closeCode first second) ![y,label,depth] = close label depth y := by
        simpa using ih 1 (by norm_num)
      change F (PA194TermRecursion.closeCode first second) ![pair 2 (pair 2 (pair f (pair x (pair y 0+1)+1)))+1,label,depth] = close label depth (^func 2 f ?[x,y])
      rw [PA194TermRecursion.modelCloseBinary first second hf hs, ihx, ihy]
      change (^func 2 f ?[close label depth x,close label depth y]) = construction.result ℒₒᵣ ![label,depth] (^func 2 f ?[x,y])
      rw [Language.TermRec.Construction.result_func' construction hfunc hv.isUTerm]
      change (^func 2 f ?[close label depth x,close label depth y]) =
        (^func 2 f (construction.resultVec ℒₒᵣ ![label,depth] 2 ?[x,y]))
      congr 1
      rw [show (2 : M) = 1+1 by norm_num,
        Language.TermRec.Construction.resultVec_cons _ _ _ (by simpa using hy) hx,
        show (1 : M) = 0+1 by simp,
        Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) hy]
      simp [close]

/-- A fixed certified choice of projections removes the certificate premises. -/
theorem canonical_agree (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    F (PA194TermRecursion.closeCode PA194TermWellFormedUnconditional.canonicalFirst
      PA194TermWellFormedUnconditional.canonicalSecond) ![t,label,depth] = close label depth t := by
  exact agree _ _
    (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
    (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2 label depth t ht

/-- The output of Foundation's construction is a term with one more bound
variable, for arbitrary internal depths and syntax codes. -/
theorem close_well_formed (label depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    IsSemiterm ℒₒᵣ (depth+1) (close label depth t) := by
  rw [← canonical_agree label depth t ht]
  exact PA194TermWellFormedUnconditional.canonical_internal label depth t ht

/-- A typed Foundation semiterm with standard external depth may itself have
an arbitrary, including nonstandard, internal code. -/
noncomputable def typedClose (label : M) (d : Nat)
    (t : Bootstrapping.Semiterm M ℒₒᵣ d) : Bootstrapping.Semiterm M ℒₒᵣ (d+1) :=
  ⟨close label (d : M) t.val, by
    simpa using close_well_formed label (d : M) t.val t.isSemiterm⟩

/-- The two internal operations agree as typed semiterms. -/
theorem typed_canonical_agree (label : M) (d : Nat)
    (t : Bootstrapping.Semiterm M ℒₒᵣ d) :
    (⟨F (PA194TermRecursion.closeCode PA194TermWellFormedUnconditional.canonicalFirst
      PA194TermWellFormedUnconditional.canonicalSecond) ![t.val,label,(d : M)], by
        simpa using PA194TermWellFormedUnconditional.canonical_internal label (d : M) t.val t.isSemiterm⟩ :
      Bootstrapping.Semiterm M ℒₒᵣ (d+1)) = typedClose label d t := by
  apply Bootstrapping.Semiterm.ext
  exact canonical_agree label (d : M) t.val t.isSemiterm

#print axioms typed_canonical_agree
#print axioms construction
#print axioms close_definable
#print axioms agree
#print axioms canonical_agree
#print axioms close_well_formed
end models
end PA194InternalClose
