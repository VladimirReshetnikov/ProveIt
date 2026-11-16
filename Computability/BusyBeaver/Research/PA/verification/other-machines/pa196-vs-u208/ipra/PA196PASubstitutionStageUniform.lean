import PA196PASubstitutionStageBounds

/-! Arithmetic substitution triples occur by an explicit iterated-majorant
fixpoint stage in all IΣ₁ models. This is a semantic stage bound, not yet a
candidate-PRA witness-bound proof. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA196PASubstitutionStageUniform
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA196PASubstitutionUniformGrowth PA196PASubstitutionStageBounds
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable abbrev arithmeticFix : Fixpoint.Construction V ((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ) :=
  (Substs.construction ℒₒᵣ).construction ℒₒᵣ
noncomputable def arithmeticStage (S : V) : V := arithmeticFix.limSeq ![] S

instance arithmeticStage_definable : 𝚺₁-Function₁ (arithmeticStage : V → V) := by
  have h := (arithmeticFix (V := V)).limSeq_definable' 𝚺 (m := 0)
  have e : (fun v : Fin 1 → V => arithmeticFix.limSeq (fun i => v i.succ) (v 0)) =
      (fun v => arithmeticStage (v 0)) := by
    funext v; unfold arithmeticStage; congr 1; funext i; exact i.elim0
  show HierarchySymbol.DefinableFunction 𝚺₁ (fun v : Fin 1 → V => arithmeticStage (v 0))
  rw [← e]; exact h

theorem mem_stage_of {x S : V} (hx : x + 1 ≤ S)
    (hΦ : ∀ s, S = s + 1 → (Substs.construction ℒₒᵣ).Phi ℒₒᵣ {z | z ∈ arithmeticFix.limSeq ![] s} x) :
    x ∈ arithmeticStage S := by
  obtain ⟨s, rfl⟩ : ∃ s, S = s + 1 :=
    ⟨S - 1, (tsub_add_cancel_of_le (le_trans le_add_self hx)).symm⟩
  exact arithmeticFix.mem_limSeq_succ_iff.mpr ⟨le_of_add_le_add_right hx, hΦ s rfl⟩

theorem mem_of_stage_lt {x S S' s : V} (hx : x ∈ arithmeticStage S) (hS : S < S') (hs : S' = s+1) :
    x ∈ arithmeticFix.limSeq ![] s :=
  arithmeticFix.limSeq_cumulative (lt_succ_iff_le.mp (hs ▸ hS)) hx

theorem triple_bound (p w : V) (hp : IsUFormula ℒₒᵣ p) :
    ⟪w,p,subst ℒₒᵣ w p⟫ + 1 ≤ stageBound w p :=
  triple_le_bound w p _ (subst_le_uniform p hp w)

/-- Every substitution result triple lies in the stated arithmetic fixpoint
stage, including for nonstandard formula and parameter codes. -/
theorem subst_stage : ∀ p : V, IsUFormula ℒₒᵣ p → ∀ w,
    ⟪w,p,subst ℒₒᵣ w p⟫ ∈ arithmeticStage (stageBound w p) := by
  refine IsUFormula.ISigma1.pi1_succ_induction (by definability) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k R v hR hv w
    have hP : IsUFormula ℒₒᵣ (^rel k R v) := by simp [hR, hv]
    refine mem_stage_of (triple_bound _ w hP) (fun s _ => ?_)
    exact ⟨w, ^rel k R v, _, rfl, hP, Or.inl ⟨k,R,v,rfl,by rw [substs_rel hR hv]; rfl⟩⟩
  · intro k R v hR hv w
    have hP : IsUFormula ℒₒᵣ (^nrel k R v) := by simp [hR, hv]
    refine mem_stage_of (triple_bound _ w hP) (fun s _ => ?_)
    exact ⟨w, ^nrel k R v, _, rfl, hP, Or.inr (Or.inl ⟨k,R,v,rfl,by rw [substs_nrel hR hv]; rfl⟩)⟩
  · intro w
    have hP : IsUFormula ℒₒᵣ (^⊤ : V) := by simp
    refine mem_stage_of (triple_bound _ w hP) (fun s _ => ?_)
    exact ⟨w, ^⊤, _, rfl, hP, Or.inr (Or.inr (Or.inl ⟨rfl,by rw [substs_verum]; rfl⟩))⟩
  · intro w
    have hP : IsUFormula ℒₒᵣ (^⊥ : V) := by simp
    refine mem_stage_of (triple_bound _ w hP) (fun s _ => ?_)
    exact ⟨w, ^⊥, _, rfl, hP, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,by rw [substs_falsum]; rfl⟩)))⟩
  · intro p q hp hq ihp ihq w
    have hP : IsUFormula ℒₒᵣ (p ^⋏ q) := by simp [hp,hq]
    refine mem_stage_of (triple_bound _ w hP) (fun s hs => ?_)
    refine ⟨w,p ^⋏ q,_,rfl,hP,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p,q,_,_,?_,?_,rfl,by rw [substs_and hp hq]; rfl⟩))))⟩
    · exact mem_of_stage_lt (ihp w) (same_child_lt w _ p (PRAWitnessCodeGrowth.add_two_le_and_left p q)) hs
    · exact mem_of_stage_lt (ihq w) (same_child_lt w _ q (PRAWitnessCodeGrowth.add_two_le_and_right p q)) hs
  · intro p q hp hq ihp ihq w
    have hP : IsUFormula ℒₒᵣ (p ^⋎ q) := by simp [hp,hq]
    refine mem_stage_of (triple_bound _ w hP) (fun s hs => ?_)
    refine ⟨w,p ^⋎ q,_,rfl,hP,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p,q,_,_,?_,?_,rfl,by rw [substs_or hp hq]; rfl⟩)))))⟩
    · exact mem_of_stage_lt (ihp w) (same_child_lt w _ p (PRAWitnessCodeGrowth.add_two_le_or_left p q)) hs
    · exact mem_of_stage_lt (ihq w) (same_child_lt w _ q (PRAWitnessCodeGrowth.add_two_le_or_right p q)) hs
  · intro p hp ihp w
    have hP : IsUFormula ℒₒᵣ (^∀ p) := by simp [hp]
    refine mem_stage_of (triple_bound _ w hP) (fun s hs => ?_)
    refine ⟨w,^∀ p,_,rfl,hP,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p,_,?_,rfl,by rw [substs_all hp]; rfl⟩))))))⟩
    exact mem_of_stage_lt (ihp (qVec ℒₒᵣ w)) (quant_child_lt w _ p (PRAWitnessCodeGrowth.add_two_le_all p)) hs
  · intro p hp ihp w
    have hP : IsUFormula ℒₒᵣ (^∃ p) := by simp [hp]
    refine mem_stage_of (triple_bound _ w hP) (fun s hs => ?_)
    refine ⟨w,^∃ p,_,rfl,hP,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨p,_,?_,rfl,by rw [substs_ex hp]; rfl⟩)))))))⟩
    exact mem_of_stage_lt (ihp (qVec ℒₒᵣ w)) (quant_child_lt w _ p (PRAWitnessCodeGrowth.add_two_le_exs p)) hs

/-- An arbitrary actual fixpoint element occurs at a stage bounded using
only its own code. -/
theorem subst_fixpoint_stage {x s : V} (hx : x ∈ arithmeticFix.limSeq ![] s) :
    x ∈ arithmeticStage (PA196PAQVecTowerAlgebra.iter (x+2) (4*x+1)) := by
  have hfix : arithmeticFix.Fixpoint ![] x := ⟨s,hx⟩
  obtain ⟨w,p,y,rfl,hp,_⟩ := arithmeticFix.case.mp hfix
  have hy : subst ℒₒᵣ w p = y := (Substs.construction ℒₒᵣ).result_eq_of_graph hfix
  subst hy
  have hstage := subst_stage p hp w
  have hw : w ≤ ⟪w,p,subst ℒₒᵣ w p⟫ := le_pair_left _ _
  have hp' : p ≤ ⟪w,p,subst ℒₒᵣ w p⟫ := le_trans (le_pair_left p _) (le_pair_right w _)
  have hs : seed w p ≤ 4*⟪w,p,subst ℒₒᵣ w p⟫+1 := by
    unfold seed
    calc
      w+3*p+1 ≤ ⟪w,p,subst ℒₒᵣ w p⟫ + 3*⟪w,p,subst ℒₒᵣ w p⟫ + 1 :=
        add_le_add (add_le_add hw (mul_le_mul' le_rfl hp')) le_rfl
      _ = 4*⟪w,p,subst ℒₒᵣ w p⟫+1 := by ring
  have hi : p+2 ≤ ⟪w,p,subst ℒₒᵣ w p⟫+2 := add_le_add hp' le_rfl
  apply arithmeticFix.limSeq_cumulative ?_ hstage
  exact le_trans (PA196PAQVecTowerAlgebra.iter_seed_mono _ _ _ hs)
    (PA196PAQVecTowerAlgebra.iter_index_mono _ _ _ hi)

#print axioms subst_fixpoint_stage
#print axioms subst_stage
end PA196PASubstitutionStageUniform
