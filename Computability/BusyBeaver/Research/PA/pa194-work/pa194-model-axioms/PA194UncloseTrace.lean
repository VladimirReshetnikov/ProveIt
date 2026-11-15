import PA194UncloseOnce
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance uncloseTraceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance uncloseTraceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance uncloseTraceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance uncloseTraceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance uncloseTraceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance uncloseTraceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fixed arithmetic graph for inverse opening, total even on invalid syntax. -/
noncomputable def uncloseStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. ∃ d, ((previous = 0 ∧ d = 0) ∨ previous = d+1) ∧
    ∃ p, !pi₂Def p d ∧ !(freeGraph SourceL) out p”
noncomputable def uncloseBlueprint : PR.Blueprint 1 where
  zero := sourceQVecZeroDef
  succ := uncloseStepDef
noncomputable def uncloseConstruction : PR.Construction M uncloseBlueprint where
  zero p := p 0
  succ _ _ previous := uncloseOnce previous
  zero_defined := .mk fun e => by simp [uncloseBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by
    rcases zero_or_succ (e 1) with h | ⟨a,h⟩
    · simp [uncloseBlueprint,uncloseStepDef,uncloseOnce,pi₂,h]
    · simp [uncloseBlueprint,uncloseStepDef,uncloseOnce,pi₂,h]

noncomputable def uncloseMany (n p : M) : M := (uncloseConstruction (M := M)).result ![p] n

theorem uncloseMany_zero (p : M) : uncloseMany 0 p = p := by
  simp [uncloseMany,uncloseConstruction]
theorem uncloseMany_succ (n p : M) : uncloseMany (n+1) p = uncloseOnce (uncloseMany n p) := by
  simp [uncloseMany,uncloseConstruction]

theorem uncloseMany_definable : 𝚺₁-Function₂ (uncloseMany : M → M → M) := by
  change 𝚺₁.Definable (fun v : Fin 3 → M => v 0 = uncloseMany (v 1) (v 2))
  simpa [uncloseMany, Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
    (uncloseConstruction (M := M)).result_defined.to_definable

theorem uncloseHistory_existsUnique (n p : M) :
    ∃! s : M, (uncloseConstruction (M := M)).CSeq ![p] s ∧ n+1 = lh s := by
  obtain ⟨s,hs,hl⟩ := PR.Construction.CSeq.exists (uncloseConstruction (M := M)) ![p] n
  refine ⟨s,⟨hs,hl⟩,?_⟩
  intro t ⟨ht,htl⟩
  have hlen : lh t = lh s := htl.symm.trans hl
  apply ht.seq.lh_ext hs.seq hlen
  intro i x y hx hy
  exact ht.unique hs (by rw [hlen]) (ht.seq.lt_lh_of_mem hx) hx hy

noncomputable def uncloseHistory (n p : M) : M := Classical.choose! (uncloseHistory_existsUnique n p)

theorem uncloseHistory_spec (n p : M) :
    (uncloseConstruction (M := M)).CSeq ![p] (uncloseHistory n p) ∧ n+1 = lh (uncloseHistory n p) :=
  Classical.choose!_spec (uncloseHistory_existsUnique n p)

noncomputable def uncloseHistoryGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “s n p. !(uncloseBlueprint.cseqDef) s p ∧ ∃ l, !lhDef l s ∧ l = n+1”

theorem uncloseHistoryGraph_iff (s n p : M) :
    uncloseHistoryGraph.val.Eval ![s,n,p] Empty.elim ↔ s = uncloseHistory n p := by
  have hu := uncloseHistory_existsUnique n p
  have hs := uncloseHistory_spec n p
  have hgraph : uncloseHistoryGraph.val.Eval ![s,n,p] Empty.elim ↔
      (uncloseConstruction (M := M)).CSeq ![p] s ∧ n+1 = lh s := by
    simp [uncloseHistoryGraph, (uncloseConstruction (M := M)).cseq_defined_iff, eq_comm, Matrix.constant_eq_singleton]
  rw [hgraph]
  constructor
  · intro h
    exact hu.unique h hs
  · rintro rfl
    exact hs

theorem uncloseHistory_entry_bound (n p i : M) (hi : i ≤ n) :
    uncloseMany i p < uncloseHistory n p := by
  have hs := (uncloseHistory_spec n p).1
  have hl := (uncloseHistory_spec n p).2
  have hlt : i < lh (uncloseHistory n p) := by rw [←hl]; exact lt_of_le_of_lt hi (lt_add_one n)
  obtain ⟨t,ht,htl,hm⟩ := (uncloseConstruction (M := M)).result_spec ![p] i
  have hm' := hs.seq.znth hlt
  have hle : lh t ≤ lh (uncloseHistory n p) := by rw [←htl,←hl]; exact (add_le_add_iff_right 1).mpr hi
  have hi' : i < lh t := by rw [←htl]; exact lt_add_one i
  have heq := ht.unique hs hle hi' hm hm'
  have hmem : ⟪i, uncloseMany i p⟫ ∈ uncloseHistory n p := by
    simpa only [uncloseMany,heq] using hm'
  exact lt_of_mem_rng hmem

/-- Internally iterated opening reverses internally iterated closure. -/
theorem uncloseMany_modelClose (n p : M) (hp : IsSemiformula SourceL 0 p) :
    uncloseMany n (modelClose n p) = p := by
  let K := n
  haveI : 𝚺₁-Function₂ (uncloseMany : M → M → M) := uncloseMany_definable
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  have hdef : 𝚺₁-Predicate (fun i : M => i ≤ K → ∀ j ≤ K, i+j ≤ K →
      uncloseMany i (modelClose (i+j) p) = modelClose j p) := by definability
  have hall : ∀ i : M, i ≤ K → ∀ j ≤ K, i+j ≤ K →
      uncloseMany i (modelClose (i+j) p) = modelClose j p := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _ j _ _
      simp [uncloseMany_zero]
    case succ i ih =>
      intro hi j hj hsum
      have hi' : i ≤ K := le_trans (le_of_lt (lt_add_one i)) hi
      have hj1 : j+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ i := zero_le
        simpa only [zero_add,add_comm,add_left_comm,add_assoc] using add_le_add_right hz (j+1)) (by
          simpa only [add_comm,add_left_comm,add_assoc] using hsum)
      have hsum' : i+(j+1) ≤ K := by simpa only [add_comm,add_left_comm,add_assoc] using hsum
      have hh := ih hi' (j+1) hj1 hsum'
      rw [uncloseMany_succ]
      have heq : (i+1)+j = i+(j+1) := by ac_rfl
      rw [heq,hh,uncloseOnce_modelClose_succ j p hp]
  have hn := hall n (le_refl n) 0 (zero_le) (by simp [K])
  simpa [modelClose_zero] using hn

theorem fullyClosedSeparation_property_bound (φ : M) (hφ : IsSemiformula SourceL 1 φ) :
    φ < uncloseHistory (fullyClosedSeparation φ) (fullyClosedSeparation φ) := by
  let n := formulaFreeBound (sepRoot φ)
  let q := fullyClosedSeparation φ
  have hq : q = modelClose n (sepRoot φ) := rfl
  have hn : n ≤ q := by
    rw [hq]
    have h := modelClose_separation_size n φ hφ
    exact le_trans (le_trans (le_of_lt (lt_add_one n)) (le_of_lt (lt_add_one (n+1)))) (le_of_lt h)
  have hentry := uncloseHistory_entry_bound q q n hn
  rw [hq,uncloseMany_modelClose n (sepRoot φ) (sepRoot_scoped φ hφ)] at hentry
  change φ < uncloseHistory q q
  rw [hq]
  exact lt_of_le_of_lt (sepRoot_contains_property φ) hentry

#print axioms uncloseMany_modelClose
#print axioms fullyClosedSeparation_property_bound
#print axioms uncloseHistory_existsUnique
#print axioms uncloseHistoryGraph_iff
#print axioms uncloseHistory_entry_bound
#print axioms uncloseMany_zero
#print axioms uncloseMany_succ
end models
end PA194BindSource
