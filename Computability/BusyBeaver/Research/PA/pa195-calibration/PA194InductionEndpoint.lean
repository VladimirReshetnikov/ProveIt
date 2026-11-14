import PA194OpeningShape
set_option autoImplicit false
set_option maxHeartbeats 700000
/-! Conditional model-length induction endpoint, and the one-binder case. -/
namespace PA194InductionEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma fvar_one : fvarVec (1 : V) = ?[^&0] := by
  rw [show (1 : V) = 0+1 by simp, fvarVec_succ, fvarVec_zero]
  simp
lemma opening_one {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) (hshift : shift ℒₒᵣ p = p)
    (h : Provable (𝗣𝗔 : ArithmeticTheory) (^∀ p)) :
    Provable (𝗣𝗔 : ArithmeticTheory) (subst ℒₒᵣ (fvarVec (1 : V)) p) := by
  have hfree := PA194IteratedFree.free_of_all hp h
  simpa [free,substs1,hshift,fvar_one] using hfree
lemma axiom_ind (p : V) (hp : IsFormula ℒₒᵣ p) (h : InductionUnivR p) :
    Provable (𝗣𝗔 : ArithmeticTheory) p := by
  apply Derivable.toProvable
  apply Derivable.by_axm (by simp [hp]) p (by simp)
  change (V ⊧/![p] (PeanoMinus.delta1.ch ⋎ InductionScheme.delta1_univ.ch).val)
  simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  right
  change (V ⊧/![p] chUniv.val)
  exact (InductionUnivR.defined (V := V)).df ![p] |>.mpr h

theorem induction_body_one (p K : V) (hp : IsSemiformula ℒₒᵣ 1 p)
    (hshift : shift ℒₒᵣ p = p) (hbv : bv ℒₒᵣ p = 1)
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hdecode : subst ℒₒᵣ (fvarVec (1 : V)) p = indBodyVal K) :
    Provable (𝗣𝗔 : ArithmeticTheory) (indBodyVal K) := by
  have he : qqAlls p (1 : V) = ^∀ p := by rw [show (1 : V) = 0+1 by simp,qqAlls_succ,qqAlls_zero]
  have haxiom : InductionUnivR (^∀ p) := by
    refine ⟨1,?_,p,?_,?_,hp.isUFormula,hshift,hbv,K,?_,hK,hdecode⟩
    · rw [←he]; exact index_le_qqAlls p 1
    · rw [←he]; exact le_qqAlls p 1
    · exact he.symm
    · rw [hdecode]; exact le_indBodyVal K
  have hformula : IsFormula ℒₒᵣ (^∀ p) := by
    have : IsSemiformula ℒₒᵣ ((0 : V)+1) p := by simpa using hp
    exact IsSemiformula.all.mpr this
  have h := opening_one hp hshift (axiom_ind _ hformula haxiom)
  simpa [hdecode] using h
theorem induction_body_model_length (p K n : V) (hp : IsSemiformula ℒₒᵣ n p)
    (hshift : shift ℒₒᵣ p = p) (hbv : bv ℒₒᵣ p = n)
    (hK : IsSemiformula ℒₒᵣ 1 K)
    (hdecode : subst ℒₒᵣ (fvarVec n) p = indBodyVal K)
    (hend : ∀ (s : V), Arithmetic.Seq s → lh s = n+1 → znth s 0 = qqAlls p n →
      (∀ i < n, znth s (i+1) = PA194OpeningHistory.opener (znth s i)) →
      znth s n = subst ℒₒᵣ (fvarVec n) p) :
    Provable (𝗣𝗔 : ArithmeticTheory) (indBodyVal K) := by
  have haxiom : InductionUnivR (qqAlls p n) := by
    refine ⟨n,index_le_qqAlls p n,p,le_qqAlls p n,rfl,hp.isUFormula,hshift,hbv,K,?_,hK,hdecode⟩
    rw [hdecode]; exact le_indBodyVal K
  have hformula : IsFormula ℒₒᵣ (qqAlls p n) := by
    have hh := IsSemiformula.qqAlls (n := (0 : V)) (k := n) (by simpa using hp)
    simpa using hh
  have hproof := axiom_ind _ hformula haxiom
  obtain ⟨s,hseq,hlen,hzero,hrec,hgood⟩ := PA194OpeningShape.open_block_provable p n hp hproof
  have hfinal := hgood n (lt_add_one n)
  rw [hend s hseq hlen hzero hrec,hdecode] at hfinal
  exact hfinal
#print axioms induction_body_model_length
#print axioms induction_body_one
#print axioms axiom_ind
end PA194InductionEndpoint
