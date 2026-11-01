import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRAUnaryRewritingBound
import DiophantineConsistency.PRANegPpow2WitnessBound
import DiophantineConsistency.PRAExtWitnessBound
/-! An explicit model-uniform bound for Foundation Exponential.Seqₛ.def.
    The complete exponential, bit membership and refutation bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRASeqSWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction DiophantineConsistency.PRAExtWitnessBound
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem ext_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) (w : V)
    (hw : (ω #2).val e Empty.elim + 1 ≤ w) :
    (ω ▹ extDef.val).Evalb e →
      (bnd (ω ▹ extDef.val)).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact PRARewritingWitnessBound.ternary_rew_bound_with extDef.val (fun _ _ z => z + 1)
    PRAExtWitnessBound.ext_bound ω e w hw

theorem neg_ppow2_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → V) (w : V)
    (hw : 2 * (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ (∼ppow2Def.val)).Evalb e →
      (bnd (ω ▹ (∼ppow2Def.val))).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact PRAUnaryRewritingBound.rew_bound_with (∼ppow2Def.val) (fun x => 2*x+1)
    PRANegPpow2WitnessBound.neg_ppow2_bound ω e w hw

attribute [local irreducible] extDef ppow2Def

theorem seqS_bound_of_common (y X Y w : V) (hX : X+1 ≤ w) (hY : Y+1 ≤ w) (hy : 2*y+1 ≤ w) :
    Exponential.Seqₛ.def.val.Evalb ![y,X,Y] →
      (bnd Exponential.Seqₛ.def.val).Evalb ![y,X,Y,w] := by
  intro h
  simp [Exponential.Seqₛ.def, Semiformula.ballLTSucc, Semiformula.ballLT,
    Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.ball, FirstOrder.bexs,
    DeMorgan.imply, bnd, bnd_open] at h ⊢
  intro u
  by_cases hu : y+1 ≤ u
  · exact Or.inl hu
  · have huy : u ≤ y := lt_succ_iff_le.mp (lt_of_not_ge hu)
    by_cases hu2 : u = 2
    · exact Or.inr (Or.inl hu2)
    · rcases h u with hb | he | hneg | hcases
      · exact (hu hb).elim
      · exact (hu2 he).elim
      · right; right; left
        let ω : Rew ℒₒᵣ Empty 1 Empty 4 := Rew.subst ![#0]
        have hf : (ω ▹ (∼ppow2Def.val)).Evalb ![u,y,X,Y] := by
          simpa [ω, Semiformula.eval_substs] using hneg
        have h2 : 2*u ≤ 2*y := mul_le_mul_left huy
        have hw : 2*(ω #0).val ![u,y,X,Y] Empty.elim + 1 ≤ w := by
          exact le_trans (by simpa [ω,add_comm] using add_le_add_right h2 1) hy
        have hb := neg_ppow2_rew_bound_at ω ![u,y,X,Y] w hw hf
        have hs : Fin.snoc ![u,y,X,Y] w = ![u,y,X,Y,w] := by simp
        rw [hs] at hb
        rw [show (ω ▹ (∼ppow2Def.val)) = ∼(ω ▹ ppow2Def.val) from
          LogicalConnective.HomClass.map_neg (Semiformula.rew ω) ppow2Def.val] at hb
        exact hb
      · right; right; right
        rcases hcases with ⟨⟨a,ha,ha1,ha2⟩,⟨b,hb,hb1,hb2⟩⟩ | ⟨⟨a,ha,ha1,ha2⟩,⟨b,hb,hb1,hb2⟩⟩
        · left
          constructor
          · refine ⟨a,lt_of_lt_of_le ha hX,ha,?_,?_⟩
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#3]
              have hf : (ω ▹ extDef.val).Evalb ![a,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using ha1
              have hw : (ω #2).val ![a,u,y,X,Y] Empty.elim + 1 ≤ w := hX
              have hr := ext_rew_bound_at ω ![a,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![a,u,y,X,Y] w = ![a,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![‘(2 * #0)’,(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#3]
              have hf : (ω ▹ extDef.val).Evalb ![a,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using ha2
              have hw : (ω #2).val ![a,u,y,X,Y] Empty.elim + 1 ≤ w := hX
              have hr := ext_rew_bound_at ω ![a,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![a,u,y,X,Y] w = ![a,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
          · refine ⟨b,lt_of_lt_of_le hb hY,hb,?_,?_⟩
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#4]
              have hf : (ω ▹ extDef.val).Evalb ![b,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using hb1
              have hw : (ω #2).val ![b,u,y,X,Y] Empty.elim + 1 ≤ w := hY
              have hr := ext_rew_bound_at ω ![b,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![b,u,y,X,Y] w = ![b,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#0],(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#4]
              have hf : (ω ▹ extDef.val).Evalb ![b,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using hb2
              have hw : (ω #2).val ![b,u,y,X,Y] Empty.elim + 1 ≤ w := hY
              have hr := ext_rew_bound_at ω ![b,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![b,u,y,X,Y] w = ![b,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
        · right
          constructor
          · refine ⟨a,lt_of_lt_of_le ha hX,ha,?_,?_⟩
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#3]
              have hf : (ω ▹ extDef.val).Evalb ![a,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using ha1
              have hw : (ω #2).val ![a,u,y,X,Y] Empty.elim + 1 ≤ w := hX
              have hr := ext_rew_bound_at ω ![a,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![a,u,y,X,Y] w = ![a,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![‘((2 * #0) + 1)’,(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#3]
              have hf : (ω ▹ extDef.val).Evalb ![a,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using ha2
              have hw : (ω #2).val ![a,u,y,X,Y] Empty.elim + 1 ≤ w := hX
              have hr := ext_rew_bound_at ω ![a,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![a,u,y,X,Y] w = ![a,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
          · refine ⟨b,lt_of_lt_of_le hb hY,hb,?_,?_⟩
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#0,#1,#4]
              have hf : (ω ▹ extDef.val).Evalb ![b,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using hb1
              have hw : (ω #2).val ![b,u,y,X,Y] Empty.elim + 1 ≤ w := hY
              have hr := ext_rew_bound_at ω ![b,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![b,u,y,X,Y] w = ![b,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr
            · let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![‘(2 * !!((Semiterm.Operator.npow ℒₒᵣ 2).operator ![#0]))’,(Semiterm.Operator.npow ℒₒᵣ 2).operator ![#1],#4]
              have hf : (ω ▹ extDef.val).Evalb ![b,u,y,X,Y] := by
                simpa [ω, Semiformula.eval_substs] using hb2
              have hw : (ω #2).val ![b,u,y,X,Y] Empty.elim + 1 ≤ w := hY
              have hr := ext_rew_bound_at ω ![b,u,y,X,Y] w hw hf
              have hs : Fin.snoc ![b,u,y,X,Y] w = ![b,u,y,X,Y,w] := by simp
              rw [hs] at hr
              exact hr

theorem seqS_bound (y X Y : V) : Exponential.Seqₛ.def.val.Evalb ![y,X,Y] →
      (bnd Exponential.Seqₛ.def.val).Evalb ![y,X,Y,X+Y+2*y+1] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hx0 : X ≤ X+Y := le_self_add
  have hy0 : Y ≤ X+Y := le_add_self
  have hx : X ≤ X+Y+2*y := le_trans hx0 le_self_add
  have hy : Y ≤ X+Y+2*y := le_trans hy0 le_self_add
  have hx' : X+1 ≤ X+Y+2*y+1 := by simpa [add_comm] using add_le_add_right hx 1
  have hy' : Y+1 ≤ X+Y+2*y+1 := by simpa [add_comm] using add_le_add_right hy 1
  have hz' : 2*y+1 ≤ X+Y+2*y+1 := by simp [add_comm]
  exact seqS_bound_of_common y X Y (X+Y+2*y+1) hx' hy' hz'

def actualSeqS : ArithmeticSemisentence 3 := Exponential.Seqₛ.def.val

def boundedSeqS : ArithmeticSemisentence 4 := bnd actualSeqS

def seqSBoundBody : ArithmeticSemisentence 4 :=
  “y X Y w. X+1 ≤ w ∧ Y+1 ≤ w ∧ 2*y+1 ≤ w ∧ !actualSeqS y X Y → !boundedSeqS y X Y w”

theorem seqSBoundBody_model (e : Fin 4 → V) : seqSBoundBody.Eval e Empty.elim := by
  simp [seqSBoundBody, boundedSeqS, Semiformula.eval_substs]
  exact seqS_bound_of_common (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def seqSBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqSBoundBody

theorem candidate_proves_seqS_bound : PRA ⊢ seqSBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact seqSBoundBody_model e
def seqSExplicitBoundBody : ArithmeticSemisentence 3 :=
  “y X Y. !actualSeqS y X Y → !boundedSeqS y X Y (X+Y+2*y+1)”

theorem seqSExplicitBoundBody_model (e : Fin 3 → V) : seqSExplicitBoundBody.Eval e Empty.elim := by
  simp [seqSExplicitBoundBody, boundedSeqS, Semiformula.eval_substs]
  exact seqS_bound (e 0) (e 1) (e 2)

def seqSExplicitBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding seqSExplicitBoundBody

theorem candidate_proves_seqS_explicit_bound : PRA ⊢ seqSExplicitBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact seqSExplicitBoundBody_model e
end DiophantineConsistency.PRASeqSWitnessBound
