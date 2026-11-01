import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegExtWitnessBound
import DiophantineConsistency.PRAExponentialWitnessBound
/-! Bound the negative Foundation Exponential.Seqₛ.def graph.
    Negative exponential and bit bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegSeqSWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] extDef ppow2Def

theorem neg_ext_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) (w : V) :
    (ω ▹ (∼extDef.val)).Evalb e →
      (bnd (ω ▹ (∼extDef.val))).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact PRARewritingWitnessBound.ternary_rew_bound_with (∼extDef.val) (fun _ _ _ => w)
    (fun x y z => PRANegExtWitnessBound.neg_ext_bound x y z w) ω e w le_rfl

private theorem neg_ext_rew_neg_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n)
    (e : Fin n → V) (w : V) :
    (∼(ω ▹ extDef.val)).Evalb e → (bnd (∼(ω ▹ extDef.val))).Evalb (Fin.snoc e w) := by
  have heq : (ω ▹ (∼extDef.val)) = ∼(ω ▹ extDef.val) := by
    exact LogicalConnective.HomClass.map_neg (Semiformula.rew ω) extDef.val
  rw [←heq]
  exact neg_ext_rew_bound ω e w

theorem negSeq_bound (y X Y : V) : (∼Exponential.Seqₛ.def.val).Evalb ![y,X,Y] →
    (bnd (∼Exponential.Seqₛ.def.val)).Evalb ![y,X,Y,2*y+1] := by
  intro h
  simp [Exponential.Seqₛ.def, Semiformula.ballLTSucc, Semiformula.ballLT,
    Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.ball, FirstOrder.bexs,
    DeMorgan.imply, bnd, bnd_open] at h ⊢
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rcases h with ⟨u,hu,hne,hpow,heven,hodd⟩
  have huy : u ≤ y := lt_succ_iff_le.mp hu
  have hy : y ≤ 2*y := by simp [two_mul]
  have hyw : y+1 ≤ 2*y+1 := by simpa [add_comm] using add_le_add_right hy 1
  have hp0 : 2*u ≤ 2*y := mul_le_mul_left huy
  have hpw : 2*u+1 ≤ 2*y+1 := by simpa [add_comm] using add_le_add_right hp0 1
  refine ⟨u,lt_of_lt_of_le hu hyw,hu,hne,?_,?_,?_⟩
  · let ω : Rew ℒₒᵣ Empty 1 Empty 4 := Rew.subst ![#0]
    have hf : (ω ▹ ppow2Def.val).Evalb ![u,y,X,Y] := by simpa [ω, Semiformula.eval_substs] using hpow
    have hw : 2*(ω #0).val ![u,y,X,Y] Empty.elim+1 ≤ 2*y+1 := hpw
    have hb := PRAExponentialWitnessBound.ppow2_rew_bound_at ω ![u,y,X,Y] (2*y+1) hw hf
    have hh : Fin.snoc ![u,y,X,Y] (2*y+1) = ![u,y,X,Y,2*y+1] := by simp
    rw [hh] at hb
    exact hb
  · rcases heven with hx | hy
    · left
      intro a
      rcases hx a with ha | ha1 | ha2
      · exact Or.inl ha
      · right; left
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#3]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha1)
        simpa using hr
      · right; right
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![‘(2 * #0)’,(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#3]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha2)
        simpa using hr
    · right
      intro a
      rcases hy a with ha | ha1 | ha2
      · exact Or.inl ha
      · right; left
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#4]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha1)
        simpa using hr
      · right; right
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#0],(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#4]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha2)
        simpa using hr
  · rcases hodd with hx | hy
    · left
      intro a
      rcases hx a with ha | ha1 | ha2
      · exact Or.inl ha
      · right; left
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#3]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha1)
        simpa using hr
      · right; right
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![‘((2 * #0) + 1)’,(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#3]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha2)
        simpa using hr
    · right
      intro a
      rcases hy a with ha | ha1 | ha2
      · exact Or.inl ha
      · right; left
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#4]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha1)
        simpa using hr
      · right; right
        let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![‘(2 * !!((Semiterm.Operator.npow ℒₒᵣ 2).operator ![#0]))’,(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#4]
        have hr := neg_ext_rew_neg_bound ω ![a,u,y,X,Y] (2*y+1)
          (by simpa [ω, Semiformula.eval_substs] using ha2)
        simpa using hr

def negSeq : ArithmeticSemisentence 3 := ∼Exponential.Seqₛ.def.val

def boundedNegSeq : ArithmeticSemisentence 4 := bnd negSeq

def negSeqBoundBody : ArithmeticSemisentence 3 :=
  “y X Y. !negSeq y X Y → !boundedNegSeq y X Y (2*y+1)”

theorem negSeqBoundBody_model (e : Fin 3 → V) : negSeqBoundBody.Eval e Empty.elim := by
  simp [negSeqBoundBody, boundedNegSeq, Semiformula.eval_substs]
  exact negSeq_bound (e 0) (e 1) (e 2)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negSeqBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negSeqBoundBody

theorem candidate_proves_negSeq_bound : PRA ⊢ negSeqBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negSeqBoundBody_model e
end DiophantineConsistency.PRANegSeqSWitnessBound
