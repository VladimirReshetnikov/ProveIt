import DiophantineConsistency.PRANegLenbitRewritingBound
import DiophantineConsistency.PRANegPow2WitnessBound
import DiophantineConsistency.PRANegSqrtLenbitBound
import DiophantineConsistency.PRAPosSqrtLenbitBound
/-! A model-uniform bound for Foundation sppow2Def, assembled from
    local positive and negative graph bounds in IOpen. The ppow2Def and
    downstream exponential and refutation obligations remain open. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRASppow2WitnessBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.StrictSigmaOneInduction
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
theorem pos_lenbit_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 2 Empty n) (e : Fin n → V) :
    (ω ▹ lenbitDef.val).Evalb e →
      (bnd (ω ▹ lenbitDef.val)).Evalb (Fin.snoc e (((ω #1).val e Empty.elim)+1)) := by
  intro h
  let g : Fin 2 → V := fun i => (ω #i).val e Empty.elim
  have hf : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.fvar) =
      (Empty.elim : Empty → V) := Subsingleton.elim _ _
  have hg : (Semiterm.val e Empty.elim ∘ ω ∘ Semiterm.bvar) = g := rfl
  simp only [Semiformula.eval_rew] at h
  rw [hg,hf] at h
  have hv : ![g 0,g 1] = g := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hs : Fin.snoc g (g 1+1) = ![g 0,g 1,g 1+1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j
  have hb := PRALenbitWitnessBound.lenbit_bound (g 0) (g 1) (by simpa [hv] using h)
  have hn := PRABndRewriting.natural lenbitDef.val ω e (g 1+1)
  rw [hs] at hn
  exact hn.mpr hb

theorem neg_pow2_rew_bound {n : ℕ} (ω : Rew ℒₒᵣ Empty 1 Empty n) (e : Fin n → V) :
    (ω ▹ (∼pow2Def.val)).Evalb e →
      (bnd (ω ▹ (∼pow2Def.val))).Evalb (Fin.snoc e (((ω #0).val e Empty.elim)+1)) := by
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
  have hb := PRANegPow2WitnessBound.neg_pow2_bound (g 0) (by simpa [hv] using h)
  have hn := PRABndRewriting.natural (∼pow2Def.val) ω e (g 0+1)
  rw [hs] at hn
  exact hn.mpr hb
theorem sppow2_bound (m : V) : sppow2Def.val.Evalb ![m] →
      (bnd sppow2Def.val).Evalb ![m,m+1] := by
  intro h
  simp [sppow2Def, Semiformula.ballLTSucc, Semiformula.ballLT, Semiformula.bexsLTSucc,
    Semiformula.bexsLT, FirstOrder.ball, FirstOrder.bexs, DeMorgan.imply, bnd, bnd_open] at h ⊢
  constructor
  · have hf : PRANegLenbitRewritingBound.negFirst.Evalb ![m] := by
      simpa [PRANegLenbitRewritingBound.negFirst, Semiformula.eval_substs] using h.1
    exact PRANegLenbitRewritingBound.negFirst_bound m hf
  constructor
  · let ω : Rew ℒₒᵣ Empty 2 Empty 1 := Rew.subst ![Semiterm.numeral 2,#0]
    have hf : (ω ▹ lenbitDef.val).Evalb ![m] := by simpa [ω, Semiformula.eval_substs] using h.2.1
    have hb := pos_lenbit_rew_bound ω ![m] hf
    exact hb
  intro x
  by_cases hx : m+1 ≤ x
  · exact Or.inl hx
  · have hxm : x ≤ m := lt_succ_iff_le.mp (lt_of_not_ge hx)
    by_cases hp : Pow2 x
    · by_cases hx2 : x ≤ 2
      · exact Or.inr (Or.inr (Or.inl hx2))
      · have hi : LenBit x m ↔ (√x < x+1 ∧ √x * √x = x ∧ LenBit (√x) m) := by
          rcases h.2.2 x with hb | hn | ht | hi
          · exact (hx hb).elim
          · exact (hn hp).elim
          · exact (hx2 ht).elim
          · exact hi
        right; right; right
        let ω : Rew ℒₒᵣ Empty 2 Empty 2 := Rew.subst ![#0,#1]
        by_cases hl : LenBit x m
        · constructor
          · right
            have hf : PRAPosSqrtLenbitBound.posSqrtLenbit.Evalb ![x,m] := by
              simpa [PRAPosSqrtLenbitBound.posSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs] using hi.mp hl
            have hb := PRAPosSqrtLenbitBound.posSqrtLenbit_bound x m hxm hf
            simpa [PRAPosSqrtLenbitBound.posSqrtLenbit, Semiformula.bexsLTSucc, Semiformula.bexsLT, FirstOrder.bexs, bnd, bnd_open] using hb
          · right
            have hf : (ω ▹ lenbitDef.val).Evalb ![x,m] := by simpa [ω, Semiformula.eval_substs] using hl
            exact pos_lenbit_rew_bound ω ![x,m] hf
        · constructor
          · left
            have hf : (ω ▹ (∼lenbitDef.val)).Evalb ![x,m] := by simpa [ω, Semiformula.eval_substs] using hl
            exact PRANegLenbitRewritingBound.neg_lenbit_rew_bound ω ![x,m] hf
          · left
            have hn : ¬(√x < x+1 ∧ √x * √x = x ∧ LenBit (√x) m) := fun hh => hl (hi.mpr hh)
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
            exact hb
    · right; left
      let ω : Rew ℒₒᵣ Empty 1 Empty 2 := Rew.subst ![#0]
      have hf : (ω ▹ (∼pow2Def.val)).Evalb ![x,m] := by simpa [ω, Semiformula.eval_substs] using hp
      have hb := neg_pow2_rew_bound ω ![x,m] hf
      have hle : x+1 ≤ m+1 := by simpa [add_comm] using add_le_add_right hxm 1
      exact eval_bnd_mono (ω ▹ (∼pow2Def.val)) ![x,m] (Empty.elim : Empty → V) hle hb
def boundedSppow2 : ArithmeticSemisentence 2 := bnd sppow2Def.val

def sppow2BoundBody : ArithmeticSemisentence 1 := “m. !sppow2Def m → !boundedSppow2 m (m+1)”

theorem sppow2BoundBody_model (e : Fin 1 → V) : sppow2BoundBody.Eval e Empty.elim := by
  simp [sppow2BoundBody, boundedSppow2, Semiformula.eval_substs]
  intro h
  apply sppow2_bound (e 0)
  have hv : ![e 0] = e := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hv]
  exact h
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing

def sppow2BoundSentence : Sentence language := ∀⁰* Semiformula.lMap embedding sppow2BoundBody

theorem candidate_proves_sppow2_bound : PRA ⊢ sppow2BoundSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ hM
  letI : M↓[language] ⊧* PRA := hM
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [models_iff, sppow2BoundSentence, Semiformula.eval_allClosure]
  intro e
  rw [Semiformula.eval_lMap, reduct_eq_standard]
  exact sppow2BoundBody_model e
end DiophantineConsistency.PRASppow2WitnessBound
