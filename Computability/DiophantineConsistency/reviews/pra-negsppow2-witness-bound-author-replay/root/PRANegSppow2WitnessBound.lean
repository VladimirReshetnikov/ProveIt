import DiophantineConsistency.PRASppow2WitnessBound
import DiophantineConsistency.PRAPow2WitnessBound
/-! Bound the negative Foundation sppow2Def graph in IOpen. The negative
    ppow2Def, exponential and refutation obligations remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace DiophantineConsistency.PRANegSppow2WitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem pow2_rew_bound_at {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → V) (w : V)
    (hw : (ω #0).val e Empty.elim + 1 ≤ w) :
    (ω ▹ pow2Def.val).Evalb e →
      (bnd (ω ▹ pow2Def.val)).Evalb (Fin.snoc e w) := by
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
  have hb := PRAPow2WitnessBound.pow2_bound (g 0) (by simpa [hv] using h)
  have hb' : (bnd pow2Def.val).Evalb (Fin.snoc g w) := by
    apply eval_bnd_mono pow2Def.val g (Empty.elim : Empty → V) hw'
    rw [hs]
    exact hb
  exact (PRABndRewriting.natural pow2Def.val ω e w).mpr hb'

theorem neg_sppow2_bound (m : V) : (∼sppow2Def.val).Evalb ![m] →
      (bnd (∼sppow2Def.val)).Evalb ![m,m+1] := by
  intro h
  simp [sppow2Def, Semiformula.ballLTSucc, Semiformula.ballLT, Semiformula.bexsLTSucc,
    Semiformula.bexsLT, FirstOrder.ball, FirstOrder.bexs, DeMorgan.imply, bnd, bnd_open] at h ⊢
  rcases h with hfirst | hsecond | ⟨x,hx,hpow,hx2,hiff⟩
  · left
    let ω : Rew ℒₒᵣ Empty 2 Empty 1 := Rew.subst ![Semiterm.numeral 1,#0]
    have hf : (ω ▹ lenbitDef.val).Evalb ![m] := by simpa [ω, Semiformula.eval_substs] using hfirst
    exact PRASppow2WitnessBound.pos_lenbit_rew_bound ω ![m] hf
  · right; left
    let ω : Rew ℒₒᵣ Empty 2 Empty 1 := Rew.subst ![Semiterm.numeral 2,#0]
    have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![m] := by simpa [ω, Semiformula.eval_substs] using hsecond
    exact PRANegLenbitRewritingBound.neg_lenbit_rew_bound ω ![m] hf
  · right; right
    have hxm : x ≤ m := lt_succ_iff_le.mp hx
    refine ⟨x,hx,?_,hx2,?_⟩
    · let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#0]
      have hf : (ω ▹ pow2Def.val).Evalb ![x,m] := by simpa [ω, Semiformula.eval_substs] using hpow
      have hw : (ω #0).val ![x,m] Empty.elim + 1 ≤ m+1 := by simpa [ω, add_comm] using add_le_add_right hxm 1
      have hb := pow2_rew_bound_at ω ![x,m] (m+1) hw hf
      have hs : Fin.snoc ![x,m] (m+1) = ![x,m,m+1] := by
        funext j
        refine Fin.cases rfl (fun k => ?_) j
        refine Fin.cases rfl (fun k => ?_) k
        exact Fin.cases rfl (fun k => Fin.elim0 k) k
      rw [hs] at hb
      exact hb
    · simp [LogicalConnective.iff, DeMorgan.imply, bnd, bnd_open]
      let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#0,#1]
      by_cases hl : LenBit x m
      · left
        constructor
        · have hf : (ω ▹ lenbitDef.val).Evalb ![x,m] := by simpa [ω, Semiformula.eval_substs] using hl
          exact PRASppow2WitnessBound.pos_lenbit_rew_bound ω ![x,m] hf
        · have hn : ¬(√x < x+1 ∧ √x * √x = x ∧ LenBit (√x) m) := by
            intro hp
            exact hiff ⟨fun _ => hp, fun _ => hl⟩
          have hf : PRANegSqrtLenbitBound.negSqrtLenbit.Evalb ![x,m] := by
            simp [PRANegSqrtLenbitBound.negSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs]
            intro s
            by_cases hs : x+1 ≤ s
            · exact Or.inl hs
            · by_cases heq : s = √x
              · subst s
                right; right
                by_cases hsquare : √x * √x = x
                · right
                  intro hlen
                  exact hn ⟨lt_of_not_ge hs, hsquare, hlen⟩
                · exact Or.inl hsquare
              · exact Or.inr (Or.inl heq)
          have hb := PRANegSqrtLenbitBound.negSqrtLenbit_bound x m hf
          simpa [PRANegSqrtLenbitBound.negSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs, bnd, bnd_open] using hb
      · right
        constructor
        · have hp : √x < x+1 ∧ √x * √x = x ∧ LenBit (√x) m := by
            by_contra hn
            exact hiff ⟨fun ha => (hl ha).elim, fun hb => (hn hb).elim⟩
          have hf : PRAPosSqrtLenbitBound.posSqrtLenbit.Evalb ![x,m] := by
            simpa [PRAPosSqrtLenbitBound.posSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs] using hp
          have hb := PRAPosSqrtLenbitBound.posSqrtLenbit_bound x m hxm hf
          simpa [PRAPosSqrtLenbitBound.posSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs, bnd, bnd_open] using hb
        · have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![x,m] := by simpa [ω, Semiformula.eval_substs] using hl
          exact PRANegLenbitRewritingBound.neg_lenbit_rew_bound ω ![x,m] hf
def negSppow2 : ArithmeticSemisentence 1 := ∼sppow2Def.val

def boundedNegSppow2 : ArithmeticSemisentence 2 := bnd negSppow2

def negSppow2BoundBody : ArithmeticSemisentence 1 := “m. !negSppow2 m → !boundedNegSppow2 m (m+1)”

theorem negSppow2BoundBody_model (e : Fin 1 → V) : negSppow2BoundBody.Eval e Empty.elim := by
  simp [negSppow2BoundBody, boundedNegSppow2, Semiformula.eval_substs]
  intro h
  apply neg_sppow2_bound (e 0)
  have hv : ![e 0] = e := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]
  exact h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def negSppow2BoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding negSppow2BoundBody

theorem candidate_proves_negSppow2_bound : PRA ⊢ negSppow2BoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, negSppow2BoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact negSppow2BoundBody_model e
end DiophantineConsistency.PRANegSppow2WitnessBound
