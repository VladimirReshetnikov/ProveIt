import DiophantineConsistency.PRAIOpenCompleteness
import DiophantineConsistency.PRANegSppow2WitnessBound
/-! The negative Foundation ppow2Def graph has a model-uniform bound.
    The full exponential, membership and refutation obligations remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegPpow2WitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem neg_sppow2_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → V) (w : V)
    (hw : (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ (∼sppow2Def.val)).Evalb e →
      (bnd (ω ▹ (∼sppow2Def.val))).Evalb (Fin.snoc e w) := by
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  intro h
  let g : Fin 1 → V := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0] = g := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hs : Fin.snoc g (g 0+1) = ![g 0,g 0+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hw' : g 0+1 ≤ w := hw
  have hb := PRANegSppow2WitnessBound.neg_sppow2_bound (g 0) (by simpa [hv] using h)
  have hb' : (bnd (∼sppow2Def.val)).Evalb (Fin.snoc g w) := by
    apply eval_bnd_mono (∼sppow2Def.val) g (Empty.elim : Empty → V) hw'
    rw [hs]
    exact hb
  exact (PRABndRewriting.natural (∼sppow2Def.val) ω e w).mpr hb'
attribute [local irreducible] sppow2Def

theorem neg_ppow2_bound (i : V) : (∼ppow2Def.val).Evalb ![i] →
      (bnd (∼ppow2Def.val)).Evalb ![i,2*i+1] := by
  intro h
  simp [ppow2Def, Semiformula.bexsLT, FirstOrder.bexs, bnd, bnd_open] at h ⊢
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hi : i ≤ 2*i := by simp [two_mul]
  have hiw : i+1 ≤ 2*i+1 := by simpa [add_comm] using add_le_add_right hi 1
  rcases h with hpow | hall
  · left
    have hf : (∼pow2Def.val).Evalb ![i] := by simpa using hpow
    have hb := PRANegPow2WitnessBound.neg_pow2_bound i hf
    exact eval_bnd_mono (∼pow2Def.val) ![i] (Empty.elim : Empty → V) hiw hb
  · right
    intro m
    by_cases hm : 2*i ≤ m
    · exact Or.inl hm
    · have hmw : m+1 ≤ 2*i+1 := by simpa [add_comm] using add_le_add_right (le_of_lt (lt_of_not_ge hm)) 1
      rcases hall m with hm' | hspp | hlen
      · exact (hm hm').elim
      · right; left
        let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#0]
        have hf : (ω ▹ (∼sppow2Def.val)).Evalb ![m,i] := by simpa [ω, Semiformula.eval_substs] using hspp
        have hb := neg_sppow2_rew_bound_at ω ![m,i] (2*i+1) hmw hf
        have hs : Fin.snoc ![m,i] (2*i+1) = ![m,i,2*i+1] := by simp
        rw [hs] at hb
        rw [show (ω ▹ (∼sppow2Def.val)) = ∼(ω ▹ sppow2Def.val) from
          LogicalConnective.HomClass.map_neg (Semiformula.rew ω) sppow2Def.val] at hb
        exact hb
      · right; right
        let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
        have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![m,i] := by simpa [ω, Semiformula.eval_substs] using hlen
        have hb := PRANegLenbitRewritingBound.neg_lenbit_rew_bound ω ![m,i] hf
        exact eval_bnd_mono (ω ▹ (∼lenbitDef.val)) ![m,i] (Empty.elim : Empty → V) hmw hb
def negPpow2 : ArithmeticSemisentence 1 := ∼ppow2Def.val

def boundedNegPpow2 : ArithmeticSemisentence 2 := bnd negPpow2

def negPpow2BoundBody : ArithmeticSemisentence 1 := “i. !negPpow2 i → !boundedNegPpow2 i (2*i+1)”

theorem negPpow2BoundBody_model (e : Fin 1 → V) : negPpow2BoundBody.Eval e Empty.elim := by
  simp [negPpow2BoundBody, boundedNegPpow2, Semiformula.eval_substs]
  intro h
  apply neg_ppow2_bound (e 0)
  have hv : ![e 0] = e := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]
  exact h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negPpow2BoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negPpow2BoundBody

theorem candidate_proves_negPpow2_bound : PRA ⊢ negPpow2BoundSentence := by
  apply PRAIOpenCompleteness.proves_allClosure
  intro M _ _ e
  exact negPpow2BoundBody_model e
end DiophantineConsistency.PRANegPpow2WitnessBound
