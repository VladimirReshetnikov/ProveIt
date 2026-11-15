import PA194PAeqClosureComplexity
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def uncloseOnce (p : V) : V := unbindFormula 0 (pi₂ (p-1))
noncomputable def uncloseStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. ∃ d b, !subDef d previous 1 ∧ !pi₂Def b d ∧ !unbindFormulaGraph out 0 b”
noncomputable def uncloseBlueprint : PR.Blueprint 1 where
  zero := .mkSigma “out seed. out = seed”
  succ := uncloseStepDef
noncomputable def uncloseConstruction : PR.Construction V uncloseBlueprint where
  zero p := p 0
  succ _ _ previous := uncloseOnce previous
  zero_defined := .mk fun e => by simp [uncloseBlueprint]
  succ_defined := .mk fun e => by simp [uncloseBlueprint,uncloseStepDef,uncloseOnce,Matrix.comp_vecCons'']
noncomputable def uncloseMany (n p : V) : V := uncloseConstruction.result ![p] n
noncomputable def uncloseManyGraph : 𝚺₁.Semisentence 3 := uncloseBlueprint.resultDef
instance uncloseMany_defined : 𝚺₁-Function₂ (uncloseMany : V → V → V) via uncloseManyGraph := .mk fun v => by
  have h := (uncloseConstruction (V := V)).result_defined.defined v
  simpa [uncloseManyGraph,uncloseMany,Matrix.comp_vecCons',Matrix.constant_eq_singleton] using h
@[simp] theorem uncloseMany_zero (p : V) : uncloseMany 0 p = p := by simp [uncloseMany,uncloseConstruction]
@[simp] theorem uncloseMany_succ (n p : V) : uncloseMany (n+1) p = uncloseOnce (uncloseMany n p) := by simp [uncloseMany,uncloseConstruction]
theorem uncloseOnce_closeOne {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    uncloseOnce (closeOne p) = p := by
  simp [uncloseOnce,closeOne,qqAll,unbindFormula_bind hp.isUFormula 0 hp]
theorem uncloseOnce_close_succ (n : V) {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    uncloseOnce (close (n+1) p) = close n p := by
  rw [close_succ,uncloseOnce_closeOne (close_scope n hp)]

theorem uncloseMany_close (n p : V) (hp : IsSemiformula PA194PAeq.language 0 p) :
    uncloseMany n (close n p) = p := by
  let K := n
  haveI : 𝚺₁-Function₂ (uncloseMany : V → V → V) := uncloseMany_defined.to_definable
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun i : V => i ≤ K → ∀ j ≤ K, i+j ≤ K →
      uncloseMany i (close (i+j) p) = close j p) := by definability
  have hall : ∀ i : V, i ≤ K → ∀ j ≤ K, i+j ≤ K →
      uncloseMany i (close (i+j) p) = close j p := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero => intro _ j _ _; simp
    case succ i ih =>
      intro hi j hj hsum
      have hi' : i ≤ K := le_trans (le_of_lt (lt_add_one i)) hi
      have hj1 : j+1 ≤ K := le_trans (by
        have hz : (0 : V) ≤ i := zero_le
        simpa only [zero_add,add_comm,add_left_comm,add_assoc] using add_le_add_right hz (j+1)) (by
          simpa only [add_comm,add_left_comm,add_assoc] using hsum)
      have hsum' : i+(j+1) ≤ K := by simpa only [add_comm,add_left_comm,add_assoc] using hsum
      have hh := ih hi' (j+1) hj1 hsum'
      rw [uncloseMany_succ]
      have heq : (i+1)+j = i+(j+1) := by ac_rfl
      rw [heq,hh,uncloseOnce_close_succ j hp]
  have hn := hall n (le_refl n) 0 (zero_le) (by simp [K])
  simpa using hn

theorem uncloseHistory_existsUnique (n p : V) :
    ∃! s : V, (uncloseConstruction (V := V)).CSeq ![p] s ∧ n+1 = lh s := by
  obtain ⟨s,hs,hl⟩ := PR.Construction.CSeq.exists (uncloseConstruction (V := V)) ![p] n
  refine ⟨s,⟨hs,hl⟩,?_⟩
  intro t ⟨ht,htl⟩
  have hlen : lh t = lh s := htl.symm.trans hl
  apply ht.seq.lh_ext hs.seq hlen
  intro i x y hx hy
  exact ht.unique hs (by rw [hlen]) (ht.seq.lt_lh_of_mem hx) hx hy
noncomputable def uncloseHistory (n p : V) : V := Classical.choose! (uncloseHistory_existsUnique n p)
theorem uncloseHistory_spec (n p : V) :
    (uncloseConstruction (V := V)).CSeq ![p] (uncloseHistory n p) ∧ n+1 = lh (uncloseHistory n p) :=
  Classical.choose!_spec (uncloseHistory_existsUnique n p)
noncomputable def uncloseHistoryGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “s n p. !(uncloseBlueprint.cseqDef) s p ∧ ∃ l, !lhDef l s ∧ l = n+1”
theorem uncloseHistory_graph (s n p : V) :
    uncloseHistoryGraph.val.Evalb ![s,n,p] ↔ s = uncloseHistory n p := by
  have hu := uncloseHistory_existsUnique n p
  have hs := uncloseHistory_spec n p
  have hgraph : uncloseHistoryGraph.val.Evalb ![s,n,p] ↔
      (uncloseConstruction (V := V)).CSeq ![p] s ∧ n+1 = lh s := by
    simp [uncloseHistoryGraph,(uncloseConstruction (V := V)).cseq_defined_iff,eq_comm,Matrix.constant_eq_singleton]
  rw [hgraph]
  constructor
  · intro h; exact hu.unique h hs
  · rintro rfl; exact hs
instance uncloseHistory_defined : 𝚺₁-Function₂ (uncloseHistory : V → V → V) via uncloseHistoryGraph := .mk fun v => by
  change uncloseHistoryGraph.val.Evalb v ↔ v 0 = uncloseHistory (v 1) (v 2)
  have hv : ![v 0,v 1,v 2] = v := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
        rfl
  simpa only [hv] using uncloseHistory_graph (v 0) (v 1) (v 2)
theorem uncloseHistory_entry_bound (n p i : V) (hi : i ≤ n) :
    uncloseMany i p < uncloseHistory n p := by
  have hs := (uncloseHistory_spec n p).1
  have hl := (uncloseHistory_spec n p).2
  have hlt : i < lh (uncloseHistory n p) := by rw [←hl]; exact lt_of_le_of_lt hi (lt_add_one n)
  obtain ⟨t,ht,htl,hm⟩ := (uncloseConstruction (V := V)).result_spec ![p] i
  have hm' := hs.seq.znth hlt
  have hle : lh t ≤ lh (uncloseHistory n p) := by rw [←htl,←hl]; exact (add_le_add_iff_right 1).mpr hi
  have hi' : i < lh t := by rw [←htl]; exact lt_add_one i
  have heq := ht.unique hs hle hi' hm hm'
  have hmem : ⟪i, uncloseMany i p⟫ ∈ uncloseHistory n p := by simpa only [uncloseMany,heq] using hm'
  exact lt_of_mem_rng hmem
#print axioms uncloseOnce_closeOne
#print axioms uncloseMany_close
#print axioms uncloseHistory_graph
#print axioms uncloseHistory_entry_bound
end generic
end PA194PAeqBind
