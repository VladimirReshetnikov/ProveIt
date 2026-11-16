import IPRABridge.Syntax
import DiophantineConsistency.IPRATheoryHilbertBridge

set_option autoImplicit false

/-!
# Transport from Foundation's intuitionistic Hilbert calculus to natural deduction

The proof is uniform in the images of free variables. A Hilbert generalization can
therefore assign the newly opened variable to the fresh variable of the natural
deduction scope and shift all earlier assignments. Only the theory axioms need a
separate arithmetic translation.
-/

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting
open LeanProofs.ConciseIPRA
open DiophantineConsistency.IPRAEqualityOnlyReference (EqualityRel language)

local notation "L" => language

local instance forwardReferenceDecidableEq : language.DecidableEq where
  func k := by
    change DecidableEq (DiophantineConsistency.PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (EqualityRel k)
    infer_instance

private abbrev propImage {n : ℕ} (free : ℕ → PTm n) (p : Propositionᵢ L) :
    Fm PTm n :=
  toConciseFormula Fin.elim0 free p

private abbrev bodyImage {n : ℕ} (free : ℕ → PTm n) (p : Semipropositionᵢ L 1) :
    Fm PTm (n + 1) :=
  toConciseFormula (Syn.up (Fin.elim0 : Fin 0 → PTm n)) (fun i => Syn.shift (free i)) p

private theorem image_instance {n : ℕ} (free : ℕ → PTm n)
    (p : Semipropositionᵢ L 1) (term : SyntacticTerm L) :
    propImage free (p/[term]) =
      (bodyImage free p).subst (Syn.inst (toConciseTerm Fin.elim0 free term)) := by
  simp only [propImage, bodyImage, toConciseFormula_rew, toConciseFormula_subst,
    Rew.subst_bvar, Rew.subst_fvar, toConciseTerm, Syn.subst_inst_shift]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp

private theorem image_weaken {n : ℕ} (free : ℕ → PTm n) (p : Propositionᵢ L) :
    bodyImage free (p/[]) = (propImage free p).shift := by
  simp only [bodyImage, propImage, Fm.shift, toConciseFormula_rew, toConciseFormula_subst,
    Rew.subst_fvar, toConciseTerm]
  congr 1
  exact funext isEmptyElim

private def underBinder {n : ℕ} (free : ℕ → PTm n) : ℕ → PTm (n + 1)
  | 0 => Syn.var 0
  | i + 1 => Syn.shift (free i)

private theorem image_free {n : ℕ} (free : ℕ → PTm n) (p : Semipropositionᵢ L 1) :
    propImage (underBinder free) (Rewriting.free p) = bodyImage free p := by
  simp only [propImage, bodyImage, toConciseFormula_rew, Rew.free_fvar, toConciseTerm,
    underBinder]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [toConciseTerm, underBinder]

/-- A Hilbert derivation translates into a natural deduction derivation, given
derivations of the extra Hilbert axioms under every free-variable assignment. -/
theorem hilbertToConcise {Ax : LeanProofs.ConciseIPRA.Theory PTm} {H : Hilbertᵢ L}
    (axiomImage : ∀ {n : ℕ} (p : Propositionᵢ L), p ∈ H → ∀ free : ℕ → PTm n,
      Prf Ax [] (toConciseFormula Fin.elim0 free p))
    {p : Propositionᵢ L} (proof : HilbertProofᵢ H p) :
    ∀ {n : ℕ} (free : ℕ → PTm n), Prf Ax [] (toConciseFormula Fin.elim0 free p) := by
  induction proof with
  | eaxm h => intro n free; exact axiomImage _ h free
  | mdp _ _ ih₁ ih₂ => intro n free; exact .impE (ih₁ free) (ih₂ free)
  | gen proof ih =>
    intro n free
    apply Prf.allI
    simpa only [List.map_nil, image_free, bodyImage] using ih (underBinder free)
  | verum => intro n free; exact .impI Prf.hyp0
  | implyK p q => intro n free; exact .impI (.impI Prf.hyp1)
  | implyS p q r =>
    intro n free
    exact .impI (.impI (.impI
      (.impE (.impE Prf.hyp1.wk Prf.hyp0) (.impE Prf.hyp1 Prf.hyp0))))
  | and₁ p q => intro n free; exact .impI (.andE₁ Prf.hyp0)
  | and₂ p q => intro n free; exact .impI (.andE₂ Prf.hyp0)
  | and₃ p q => intro n free; exact .impI (.impI (.andI Prf.hyp1 Prf.hyp0))
  | or₁ p q => intro n free; exact .impI (.orI₁ Prf.hyp0)
  | or₂ p q => intro n free; exact .impI (.orI₂ Prf.hyp0)
  | or₃ p q r =>
    intro n free
    exact .impI (.impI (.impI
      (.orE Prf.hyp0 (.impE Prf.hyp1.wk.wk Prf.hyp0)
        (.impE Prf.hyp1.wk Prf.hyp0))))
  | all₁ p term =>
    intro n free
    change Prf Ax [] (.imp (.all (bodyImage free p)) (propImage free (p/[term])))
    rw [image_instance]
    exact .impI (.allE (toConciseTerm Fin.elim0 free term) Prf.hyp0)
  | all₂ p q =>
    intro n free
    let a := propImage free p
    let b := bodyImage free q
    change Prf Ax [] (.imp (.all (.imp (bodyImage free (p/[])) b)) (.imp a (.all b)))
    rw [image_weaken]
    have premise : Prf Ax [a, .all (.imp a.shift b)] (.all (.imp a.shift b)) := Prf.hyp1
    exact .impI (.impI (.allI (.impE premise.allOpen Prf.hyp0)))
  | ex₁ term p =>
    intro n free
    change Prf Ax [] (.imp (propImage free (p/[term])) (.ex (bodyImage free p)))
    rw [image_instance]
    exact .impI (.exI (toConciseTerm Fin.elim0 free term) Prf.hyp0)
  | ex₂ p q =>
    intro n free
    let a := bodyImage free p
    let b := propImage free q
    change Prf Ax [] (.imp (.all (.imp a (bodyImage free (q/[])))) (.imp (.ex a) b))
    rw [image_weaken]
    have premise : Prf Ax [.ex a, .all (.imp a b.shift)] (.all (.imp a b.shift)) := Prf.hyp1
    exact .impI (.impI (.exE Prf.hyp0 (.impE premise.allOpen.wk Prf.hyp0)))

private theorem image_emb {n : ℕ} (free : ℕ → PTm n) (p : Sentenceᵢ L) :
    propImage free (Rewriting.emb p) =
      (toConciseClosed p).subst (Fin.elim0 : Fin 0 → PTm n) := by
  simp only [propImage, toConciseClosed, toConciseFormula_rew, toConciseFormula_subst]
  congr 1 <;> exact funext isEmptyElim

/-- Translate an open reference proposition under an arbitrary assignment,
given closed Concise derivations of the theory axioms. -/
theorem extendedToConcise {Ax : LeanProofs.ConciseIPRA.Theory PTm}
    (T : Theoryᵢ L (𝗜𝗻𝘁¹ : Hilbertᵢ L))
    (axiomImage : ∀ p ∈ T.theory, Prf Ax [] (toConciseClosed p))
    {p : Propositionᵢ L} (proof : DiophantineConsistency.IPRATheoryHilbertBridge.extended T ⊢! p)
    {n : ℕ} (free : ℕ → PTm n) : Prf Ax [] (toConciseFormula Fin.elim0 free p) := by
  let H := DiophantineConsistency.IPRATheoryHilbertBridge.extended T
  have map_axiom {n : ℕ} (q : Propositionᵢ L) (hq : q ∈ H)
      (free : ℕ → PTm n) : Prf Ax [] (propImage free q) := by
    rcases hq with hq | ⟨q, hq, rfl⟩
    · obtain ⟨r, rfl⟩ := hq
      exact .impI (.botE _ Prf.hyp0)
    · rw [image_emb]
      exact (axiomImage q hq).subst Fin.elim0
  exact hilbertToConcise map_axiom proof free

/-- A Foundation theory proof gives a Concise derivation of its closed image
once each theory axiom has a closed Concise derivation. -/
theorem theoryToConcise {Ax : LeanProofs.ConciseIPRA.Theory PTm}
    (T : Theoryᵢ L (𝗜𝗻𝘁¹ : Hilbertᵢ L))
    (axiomImage : ∀ p ∈ T.theory, Prf Ax [] (toConciseClosed p))
    {p : Sentenceᵢ L} (h : T ⊢ p) : Prf Ax [] (toConciseClosed p) := by
  obtain ⟨proof⟩ := h
  let free : ℕ → PTm 0 := fun _ => PTm.zero
  have result : Prf Ax [] (propImage free (Rewriting.emb p)) :=
    extendedToConcise T axiomImage
      (DiophantineConsistency.IPRATheoryHilbertBridge.theoryToExtended T proof) free
  rw [image_emb] at result
  have hEmpty : (Fin.elim0 : Fin 0 → PTm 0) = Syn.var := funext isEmptyElim
  simpa only [hEmpty, Fm.subst_id] using result

end IPRABridge
