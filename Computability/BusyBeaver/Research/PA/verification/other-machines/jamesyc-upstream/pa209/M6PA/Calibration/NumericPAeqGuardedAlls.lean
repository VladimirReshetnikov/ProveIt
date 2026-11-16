module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqGuardedAllsSyntax
@[expose] public section
namespace M6.PA.NumericPAeqGuardedAlls
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqGuardedUniversal
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem freeBound_alls {p:V} (hp:IsUFormula Presentation.language p) (k:V):
    NumericPAeqFormula.freeBound (qqAlls p k)=NumericPAeqFormula.freeBound p := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => rw [qqAlls_succ,freeBound_all (isUFormula_qqAlls.mpr hp),ih]
theorem freeSupported_alls {m p:V} (hs:FreeSupported m p) (k:V):FreeSupported m (qqAlls p k) :=
  ⟨isUFormula_qqAlls.mpr hs.1,by simpa only [freeBound_alls hs.1] using hs.2⟩

theorem matrixSupply_all {s p:V} (hp:IsSemiformula Presentation.language (s+1) p)
    (hs:FreeSupported 0 p) (h:MatrixSupply (s+1) p):MatrixSupply s (qqAll p) := by
  intro b f hb hf native lo z hc
  apply guarded_all_requested_certificate hb hf hp ⟨hs.1,le_trans hs.2 (by simp)⟩ native lo z hc
  intro g l r hc
  exact h (qqFvar 0∷targetShiftTerms b) (targetShiftTerms f)
    ((targetShiftTerms_valid hb).adjoin (by simp))
    (by simpa [targetShiftTerms_length hf] using targetShiftTerms_valid hf) g l r hc
attribute [local irreducible] matrixSupplyFormula freeSupportedGraph
noncomputable def closureInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ s p, !((isSemiformula Presentation.language).sigma) (s+k) p → !freeSupportedGraph 0 p →
    !matrixSupplyFormula (s+k) p → ∃ q,!qqAllsDef q p k ∧ !matrixSupplyFormula s q”
theorem closure_invariant (k:V):closureInvariant.Evalb ![k] ↔
    ∀s p:V,IsSemiformula Presentation.language (s+k) p→FreeSupported 0 p→
      MatrixSupply (s+k) p→MatrixSupply s (qqAlls p k) := by
  simp [closureInvariant,matrixSupply_formula,freeSupported_graph,Matrix.comp_vecCons'']
attribute [local irreducible] closureInvariant
theorem matrixSupply_alls {s k p:V} (hp:IsSemiformula Presentation.language (s+k) p)
    (hs:FreeSupported 0 p) (h:MatrixSupply (s+k) p):MatrixSupply s (qqAlls p k) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀s p:V,IsSemiformula Presentation.language (s+k) p→FreeSupported 0 p→
      MatrixSupply (s+k) p→MatrixSupply s (qqAlls p k) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀s p:V,
      IsSemiformula Presentation.language (s+k) p→FreeSupported 0 p→
      MatrixSupply (s+k) p→MatrixSupply s (qqAlls p k)) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb closureInvariant,by trivial,?_⟩
      intro k; simpa using (closure_invariant (V:=V) k).symm
    · intro s p hp hs h; simpa using h
    · intro k ih s p hp hs h
      rw [qqAlls_succ']
      have hp' : IsSemiformula Presentation.language ((s+k)+1) p := by simpa [add_assoc] using hp
      apply ih s (qqAll p) (IsSemiformula.all.mpr hp')
      · exact (freeSupported_all hp'.isUFormula).mpr hs
      · exact matrixSupply_all hp' hs (by simpa [add_assoc] using h)
  exact hall k s p hp hs h
#print axioms freeBound_alls
#print axioms freeSupported_alls
#print axioms matrixSupply_all
#print axioms closure_invariant
#print axioms freeBound_alls
#print axioms freeSupported_alls
#print axioms matrixSupply_alls
end M6.PA.NumericPAeqGuardedAlls

