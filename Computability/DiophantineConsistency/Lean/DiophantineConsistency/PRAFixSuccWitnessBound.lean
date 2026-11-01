import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegBitFullWitnessBound
import DiophantineConsistency.PRABitFullWitnessBound
import DiophantineConsistency.PRARewritingWitnessBound
import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint
/-! Bind both membership polarities in Foundation succDef. The per-index
    bounded core sigma and negated-pi hypotheses remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAFixSuccWitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable (φ : Fixpoint.Blueprint 0)
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
attribute [local irreducible] bitDef

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] in
theorem bnd_rew_succ (ψ : ArithmeticSemisentence 2) (ω : Rew ℒₒᵣ Empty 2 Empty 4)
    (x u ih s w a b : V)
    (hv : (fun j => (ω #j).val ![x,u,ih,s] Empty.elim) = ![a,b])
    (hb : (bnd ψ).Evalb ![a,b,w]) :
    (bnd (ω ▹ ψ)).Evalb ![x,u,ih,s,w] := by
  have hn := PRABndRewriting.natural ψ ω ![x,u,ih,s] w
  have hs : Fin.snoc ![x,u,ih,s] w = ![x,u,ih,s,w] := by simp
  have hs' : Fin.snoc ![a,b] w = ![a,b,w] := by simp
  rw [hv,hs,hs'] at hn
  exact hn.mpr hb

theorem succ_bound_of_core (u ih s w : V)
    (hpos : PRABitFullWitnessBound.bitMajorant u ≤ w)
    (hneg : PRANegBitFullWitnessBound.negBitMajorant u ≤ w)
    (hcore : ∀ x, x < u+(s+1) → φ.core.sigma.val.Evalb ![x,ih] →
      (bnd φ.core.sigma.val).Evalb ![x,ih,w])
    (hcoreNeg : ∀ x, x < u+(s+1) → (∼φ.core.pi.val).Evalb ![x,ih] →
      (bnd (∼φ.core.pi.val)).Evalb ![x,ih,w]) :
    φ.succDef.val.Evalb ![u,ih,s] → (bnd φ.succDef.val).Evalb ![u,ih,s,w] := by
  intro h
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  simp [Fixpoint.Blueprint.succDef, Semiformula.ballLT, FirstOrder.ball, DeMorgan.imply, bnd, bnd_open] at h ⊢
  intro x
  by_cases hx : u+(s+1) ≤ x
  · exact Or.inl hx
  · right
    have hlt : x < u+(s+1) := lt_of_not_ge hx
    rcases h x with hx' | ⟨ha,hb⟩
    · exact (hx hx').elim
    · let coreRew : Rew ℒₒᵣ Empty 2 Empty 4 := Rew.subst ![#0,#2]
      have coreEnv : (fun j => (coreRew #j).val ![x,u,ih,s] Empty.elim) = ![x,ih] := by
        apply funext
        simp [Fin.forall_fin_succ, coreRew]
      constructor
      · rcases ha with hbit | ⟨hxs,hσ⟩
        · left
          have hf : (∼bitDef.val).Evalb ![x,u] := by
            simpa [Semiformula.Operator.val, operator_mem_def] using hbit
          let ω : Rew ℒₒᵣ Empty 2 Empty 4 := Rew.subst ![#0,#1]
          have hh := PRARewritingWitnessBound.binary_rew_bound_with (∼bitDef.val)
            (fun _ u => PRANegBitFullWitnessBound.negBitMajorant u)
            PRANegBitFullWitnessBound.negBit_bound ω ![x,u,ih,s] w
            (by simpa [ω] using hneg) (by simpa [ω, Semiformula.eval_substs] using hf)
          rw [show (ω ▹ (∼bitDef.val)) = ∼(ω ▹ bitDef.val) from
            LogicalConnective.HomClass.map_neg (Semiformula.rew ω) bitDef.val] at hh
          simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hh
        · right
          refine ⟨hxs,?_⟩
          exact bnd_rew_succ φ.core.sigma.val coreRew x u ih s w x ih coreEnv (hcore x hlt hσ)
      · rcases hb with (hxs | hπ) | hbit
        · exact Or.inl (Or.inl hxs)
        · left; right
          have hf : (∼φ.core.pi.val).Evalb ![x,ih] := by simpa using hπ
          simpa [LogicalConnective.HomClass.map_neg] using
            (bnd_rew_succ (∼φ.core.pi.val) coreRew x u ih s w x ih coreEnv (hcoreNeg x hlt hf))
        · right
          have hf : bitDef.val.Evalb ![x,u] := by
            simpa [Semiformula.Operator.val, operator_mem_def] using hbit
          let ω : Rew ℒₒᵣ Empty 2 Empty 4 := Rew.subst ![#0,#1]
          have hh := PRARewritingWitnessBound.binary_rew_bound_with bitDef.val
            (fun _ u => PRABitFullWitnessBound.bitMajorant u)
            PRABitFullWitnessBound.bit_bound ω ![x,u,ih,s] w
            (by simpa [ω] using hpos) (by simpa [ω, Semiformula.eval_substs] using hf)
          simpa [Semiformula.Operator.operator, operator_mem_def, Rewriting.emb] using hh

noncomputable def coreSigma : ArithmeticSemisentence 2 := φ.core.sigma.val
noncomputable def negCorePi : ArithmeticSemisentence 2 := ∼φ.core.pi.val
noncomputable def boundedCoreSigma : ArithmeticSemisentence 3 := bnd (coreSigma φ)
noncomputable def boundedNegCorePi : ArithmeticSemisentence 3 := bnd (negCorePi φ)
noncomputable def boundedSucc : ArithmeticSemisentence 4 := bnd φ.succDef.val
noncomputable def succBoundBody : ArithmeticSemisentence 4 :=
  “u ih s w.
    (((u⁴+1)+(u²+1)+(2*u²+1)+(u⁴+u⁴+2*u+1))+u+1) ≤ w ∧
    (((2*u+1)+(2*u²+1))+u+1) ≤ w ∧
    (∀ x < u+(s+1), !((coreSigma φ)) x ih → !((boundedCoreSigma φ)) x ih w) ∧
    (∀ x < u+(s+1), !((negCorePi φ)) x ih → !((boundedNegCorePi φ)) x ih w) ∧
    !φ.succDef u ih s → !((boundedSucc φ)) u ih s w”

theorem succBoundBody_model (e : Fin 4 → V) : (succBoundBody φ).Eval e Empty.elim := by
  simp [succBoundBody, boundedCoreSigma, boundedNegCorePi, boundedSucc, Semiformula.eval_substs]
  exact succ_bound_of_core φ (e 0) (e 1) (e 2) (e 3)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

noncomputable def succBoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding (succBoundBody φ)

theorem candidate_proves_succ_bound : PRA ⊢ succBoundSentence φ := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact succBoundBody_model φ e
end DiophantineConsistency.PRAFixSuccWitnessBound
