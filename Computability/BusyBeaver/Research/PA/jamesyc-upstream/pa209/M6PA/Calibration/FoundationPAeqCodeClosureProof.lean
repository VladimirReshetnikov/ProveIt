module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeClosureOpening
@[expose] public section
/-! Model-count opening/closing of actual numerical proofs. Full PA induction
is applied to the explicit arithmetic invariant below, not a host callback. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language
local notation "U" => Presentation.ordinaryPAeq

noncomputable def closureProofInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ b, !((isSemiformula Presentation.language).sigma) k b →
    !(shiftGraph Presentation.language) b b →
    ∀ a w s, !qqAllsDef a b k → !fvarVecDef w k →
      !(substsGraph Presentation.language) s w b →
      (!(provable Presentation.ordinaryPAeq) a ↔ !(provable Presentation.ordinaryPAeq) s)”
theorem closureProofInvariant_eval (k : V) : closureProofInvariant.Evalb ![k] ↔
    ∀ b : V, IsSemiformula PAeq k b → shift PAeq b=b →
      (Provable U (qqAlls b k) ↔ Provable U (subst PAeq (fvarVec k) b)) := by
  simp only [closureProofInvariant]
  simp [Matrix.comp_vecCons'',eq_comm]
  constructor
  · intro h b hb hs; exact h b hb hs _ _ _ rfl rfl rfl
  · intro h b hb hs a w s ha hw hsub
    subst a; subst w; subst s
    exact h b hb hs

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem provable_alls_iff_open {k b : V} (hb : IsSemiformula PAeq k b)
    (hs : shift PAeq b=b) :
    Provable U (qqAlls b k) ↔ Provable U (subst PAeq (fvarVec k) b) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := FFL.Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ b : V, IsSemiformula PAeq k b → shift PAeq b=b →
      (Provable U (qqAlls b k) ↔ Provable U (subst PAeq (fvarVec k) b)) := by
    refine InductionScheme.succ_induction (C:=Set.univ)
      (P:=fun k : V=>∀ b : V, IsSemiformula PAeq k b → shift PAeq b=b →
        (Provable U (qqAlls b k) ↔ Provable U (subst PAeq (fvarVec k) b))) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb closureProofInvariant,by trivial,?_⟩
      intro k; simpa using (closureProofInvariant_eval (V:=V) k).symm
    · intro b hb _
      have he := subst_boundIdentity hb
      simpa using congrArg (Provable U) he.symm
    · intro k ih b hb hs
      have hab : IsSemiformula PAeq k (qqAll b) := by simpa using hb
      have hsh : shift PAeq (qqAll b)=qqAll b := by simp [hb.isUFormula,hs]
      have hw : IsSemitermVec PAeq (k+1) 1 (qVec PAeq (fvarVec k)) := by
        simpa using (target_fvarVec_valid k 0).qVec
      rw [qqAlls_succ',ih (qqAll b) hab hsh,substs_all hb.isUFormula,
        provable_all_iff_free (hb.subst hw),free_opening_succ hb hs]
  exact hall k b hb hs

#print axioms closureProofInvariant_eval
#print axioms provable_alls_iff_open
end M6.PA.FoundationPAeqCode

