import DiophantineConsistency.PRARewritingWitnessBound
import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegSeqSWitnessBound
/-! A polynomial model-uniform bound for negative Foundation exponentialDef.
    Negative expDef, bit and the refutation certificate remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRANegExponentialWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] extDef ppow2Def Exponential.Seqₛ.def

theorem negSeq_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 3 Empty n) (e : Fin n → V) (w : V)
    (hw : 2*(ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ (∼Exponential.Seqₛ.def.val)).Evalb e →
      (bnd (ω ▹ (∼Exponential.Seqₛ.def.val))).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  exact PRARewritingWitnessBound.ternary_rew_bound_with (∼Exponential.Seqₛ.def.val) (fun x _ _ => 2*x + 1)
    PRANegSeqSWitnessBound.negSeq_bound ω e w hw

theorem negExponential_bound_common (x y w : V)
    (hy : 2*y+1 ≤ w) (h2 : 2*(y^2)+1 ≤ w) :
    (∼exponentialDef.val).Evalb ![x,y] →
      (bnd (∼exponentialDef.val)).Evalb ![x,y,w] := by
  intro h
  simp [exponentialDef, Semiformula.bexsLTSucc, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open] at h ⊢
  constructor
  · exact h.1
  · intro A
    rcases h.2 A with hA | hA
    · exact Or.inl hA
    · right
      intro B
      rcases hA B with hB | (he1 | he2) | hseq | hu
      · exact Or.inl hB
      · right; left; left
        let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![Semiterm.numeral 1,Semiterm.numeral 4,#1]
        have hf : (ω ▹ (∼extDef.val)).Evalb ![B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he1
        simpa [LogicalConnective.HomClass.map_neg] using (PRANegSeqSWitnessBound.neg_ext_rew_bound ω ![B,A,x,y] w hf)
      · right; left; right
        let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![Semiterm.numeral 2,Semiterm.numeral 4,#0]
        have hf : (ω ▹ (∼extDef.val)).Evalb ![B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he2
        simpa [LogicalConnective.HomClass.map_neg] using (PRANegSeqSWitnessBound.neg_ext_rew_bound ω ![B,A,x,y] w hf)
      · right; right; left
        let ω : Rew ℒₒᵣ Empty 3 Empty 4 := Rew.subst ![#3,#1,#0]
        have hf : (ω ▹ (∼Exponential.Seqₛ.def.val)).Evalb ![B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using hseq
        have hw : 2*(ω #0).val ![B,A,x,y] Empty.elim+1 ≤ w := hy
        simpa [LogicalConnective.HomClass.map_neg] using (negSeq_rew_bound_at ω ![B,A,x,y] w hw hf)
      · right; right; right
        intro u
        by_cases hbig : y^2+1 ≤ u
        · exact Or.inl hbig
        · rcases hu u with hbig' | hu2 | hpow | he3 | he4
          · exact (hbig hbig').elim
          · exact Or.inr (Or.inl hu2)
          · right; right; left
            let ω : Rew ℒₒᵣ Empty 1 Empty 5 := Rew.subst ![#0]
            have hf : (ω ▹ (∼ppow2Def.val)).Evalb ![u,B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using hpow
            have hu0 : u ≤ y^2 := lt_succ_iff_le.mp (lt_of_not_ge hbig)
            have hp0 : 2*u ≤ 2*(y^2) := mul_le_mul_left hu0
            have hw : 2*(ω #0).val ![u,B,A,x,y] Empty.elim+1 ≤ w := le_trans (by simpa [ω,add_comm] using add_le_add_right hp0 1) h2
            simpa [LogicalConnective.HomClass.map_neg] using (PRASeqSWitnessBound.neg_ppow2_rew_bound_at ω ![u,B,A,x,y] w hw hf)
          · right; right; right; left
            let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#3,#0,#2]
            have hf : (ω ▹ (∼extDef.val)).Evalb ![u,B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he3
            simpa [LogicalConnective.HomClass.map_neg] using (PRANegSeqSWitnessBound.neg_ext_rew_bound ω ![u,B,A,x,y] w hf)
          · right; right; right; right
            let ω : Rew ℒₒᵣ Empty 3 Empty 5 := Rew.subst ![#4,#0,#1]
            have hf : (ω ▹ (∼extDef.val)).Evalb ![u,B,A,x,y] := by simpa [ω, Semiformula.eval_substs] using he4
            simpa [LogicalConnective.HomClass.map_neg] using (PRANegSeqSWitnessBound.neg_ext_rew_bound ω ![u,B,A,x,y] w hf)

def negExponentialMajorant (y : V) : V := (2*y+1)+(2*(y^2)+1)

theorem negExponential_bound (x y : V) :
    (∼exponentialDef.val).Evalb ![x,y] →
      (bnd (∼exponentialDef.val)).Evalb ![x,y,negExponentialMajorant y] := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h1 : 2*y+1 ≤ negExponentialMajorant y := le_self_add
  have h2 : 2*(y^2)+1 ≤ negExponentialMajorant y := le_add_self
  exact negExponential_bound_common x y (negExponentialMajorant y) h1 h2

def negExponential : ArithmeticSemisentence 2 := ∼exponentialDef.val

def boundedNegExponential : ArithmeticSemisentence 3 := bnd negExponential

def negExponentialBoundBody : ArithmeticSemisentence 2 :=
  “x y. !negExponential x y → !boundedNegExponential x y ((2*y+1)+(2*y²+1))”

theorem negExponentialBoundBody_model (e : Fin 2 → V) : negExponentialBoundBody.Eval e Empty.elim := by
  simp [negExponentialBoundBody, boundedNegExponential, Semiformula.eval_substs]
  exact negExponential_bound (e 0) (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negExponentialBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negExponentialBoundBody

theorem candidate_proves_negExponential_bound : PRA ⊢ negExponentialBoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negExponentialBoundBody_model e
end DiophantineConsistency.PRANegExponentialWitnessBound
