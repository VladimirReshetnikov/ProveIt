import DiophantineConsistency.PRASppow2WitnessBound
import DiophantineConsistency.PRAPow2WitnessBound
/-! A model-uniform graph bound for Foundation ppow2Def. The current
    exponentiation, membership and refutation bounds remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRAPpow2WitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem sppow2_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → V) (w : V)
    (hw : (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ sppow2Def.val).Evalb e →
      (bnd (ω ▹ sppow2Def.val)).Evalb (Fin.snoc e w) := by
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
  have hb := PRASppow2WitnessBound.sppow2_bound (g 0) (by simpa [hv] using h)
  have hb' : (bnd sppow2Def.val).Evalb (Fin.snoc g w) := by
    apply eval_bnd_mono sppow2Def.val g (Empty.elim : Empty → V) hw'
    rw [hs]
    exact hb
  exact (PRABndRewriting.natural sppow2Def.val ω e w).mpr hb'
attribute [local irreducible] sppow2Def

theorem ppow2_bound (i : V) : ppow2Def.val.Evalb ![i] →
      (bnd ppow2Def.val).Evalb ![i,2*i+1] := by
  intro h
  simp [ppow2Def, Semiformula.bexsLT,
    FirstOrder.bexs, bnd, bnd_open] at h ⊢
  have hi : i ≤ 2*i := by simp [two_mul]
  have hiw : i+1 ≤ 2*i+1 := by simpa [add_comm] using add_le_add_right hi 1
  letI : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have hpow : pow2Def.val.Evalb ![i] := by simpa using h.1
  have hpowb := PRAPow2WitnessBound.pow2_bound i hpow
  constructor
  · exact eval_bnd_mono pow2Def.val ![i] (Empty.elim : Empty → V) hiw hpowb
  · rcases h.2 with ⟨m,hm,hspp,hlen⟩
    have hmw : m+1 ≤ 2*i+1 := by simpa [add_comm] using add_le_add_right (le_of_lt hm) 1
    refine ⟨m,lt_trans hm (lt_succ_iff_le.mpr (le_refl (2*i))),hm,?_,?_⟩
    · let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#0]
      have hf : (ω ▹ sppow2Def.val).Evalb ![m,i] := by
        simpa [ω, Semiformula.eval_substs] using hspp
      have hb := sppow2_rew_bound_at ω ![m,i] (2*i+1) hmw hf
      have hs : Fin.snoc ![m,i] (2*i+1) = ![m,i,2*i+1] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      rw [hs] at hb
      exact hb
    · let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#1,#0]
      have hf : (ω ▹ lenbitDef.val).Evalb ![m,i] := by simpa [ω, Semiformula.eval_substs] using hlen
      have hb := PRASppow2WitnessBound.pos_lenbit_rew_bound ω ![m,i] hf
      exact eval_bnd_mono (ω ▹ lenbitDef.val) ![m,i] (Empty.elim : Empty → V) hmw hb
def boundedPpow2 : ArithmeticSemisentence 2 := bnd ppow2Def.val

def ppow2BoundBody : ArithmeticSemisentence 1 := “i. !ppow2Def i → !boundedPpow2 i (2*i+1)”

theorem ppow2BoundBody_model (e : Fin 1 → V) : ppow2BoundBody.Eval e Empty.elim := by
  simp [ppow2BoundBody, boundedPpow2, Semiformula.eval_substs]
  intro h
  apply ppow2_bound (e 0)
  have hv : ![e 0] = e := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]
  exact h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def ppow2BoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding ppow2BoundBody

theorem candidate_proves_ppow2_bound : PRA ⊢ ppow2BoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, ppow2BoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact ppow2BoundBody_model e
end DiophantineConsistency.PRAPpow2WitnessBound
