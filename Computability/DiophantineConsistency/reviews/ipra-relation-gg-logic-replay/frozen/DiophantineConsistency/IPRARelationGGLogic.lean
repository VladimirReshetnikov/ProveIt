import DiophantineConsistency.IPRATwoImpLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
set_option autoImplicit false
namespace DiophantineConsistency.IPRARelationGGLogic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRAQuantifierFree
open IPRANativeTheory IPRANativeAxiomImage IPRANativeEquationImages IPRANativeBasicImages IPRATwoImpLogic
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
theorem nnConj (p q : Propositionᵢ L) : Λ ⊢ (∼∼p ⋏ ∼∼q) 🡒 ∼∼(p ⋏ q) := by
  have h : [∼∼p ⋏ ∼∼q] ⊢[Λ] ∼∼(p ⋏ q) := by
    apply FiniteContext.deduct!
    let Γ : List (Propositionᵢ L) := [∼(p ⋏ q), ∼∼p ⋏ ∼∼q]
    have hn : Γ ⊢[Λ]! ∼(p ⋏ q) := FiniteContext.byAxm₀
    have hnn : Γ ⊢[Λ]! ∼∼p ⋏ ∼∼q := FiniteContext.byAxm₁
    have hnp : Γ ⊢[Λ]! ∼∼p := Entailment.K_left hnn
    have hnq : Γ ⊢[Λ]! ∼∼q := Entailment.K_right hnn
    have hnp' : Γ ⊢[Λ] ∼p := by
      apply FiniteContext.deduct!
      let Δ : List (Propositionᵢ L) := [p, ∼(p ⋏ q), ∼∼p ⋏ ∼∼q]
      have hp : Δ ⊢[Λ]! p := FiniteContext.byAxm₀
      have hneg : Δ ⊢[Λ]! ∼(p ⋏ q) := FiniteContext.byAxm₁
      have hboth : Δ ⊢[Λ]! ∼∼p ⋏ ∼∼q := FiniteContext.byAxm₂
      have hnnq : Δ ⊢[Λ]! ∼∼q := Entailment.K_right hboth
      have hpq : Δ ⊢[Λ] q 🡒 (p ⋏ q) := by
        apply FiniteContext.deduct!
        let Ω : List (Propositionᵢ L) := [q, p, ∼(p ⋏ q), ∼∼p ⋏ ∼∼q]
        have hq : Ω ⊢[Λ]! q := FiniteContext.byAxm₀
        have hp' : Ω ⊢[Λ]! p := FiniteContext.byAxm₁
        exact ⟨Entailment.K_intro hp' hq⟩
      have hnq' : Δ ⊢[Λ]! ∼q := Entailment.mdp (Entailment.contra (Classical.choice hpq)) hneg
      exact ⟨Entailment.mdp hnnq hnq'⟩
    exact ⟨Entailment.mdp hnp (Classical.choice hnp')⟩
  have hi := FiniteContext.toDef (Classical.choice (FiniteContext.deduct! h))
  apply Nonempty.intro
  simpa using (Entailment.mdp hi (Entailment.verum : Λ ⊢! ⊤))

omit [L.DecidableEq] in
theorem curried_conj (p q r s : Propositionᵢ L) :
    Λ ⊢ (p 🡒 q 🡒 r 🡒 s) 🡒 ((p ⋏ (q ⋏ ⊤)) 🡒 r 🡒 s) := by
  have h : [p 🡒 q 🡒 r 🡒 s] ⊢[Λ] (p ⋏ (q ⋏ ⊤)) 🡒 r 🡒 s := by
    apply FiniteContext.deduct!
    apply FiniteContext.deduct!
    let Γ : List (Propositionᵢ L) := [r, p ⋏ (q ⋏ ⊤), p 🡒 q 🡒 r 🡒 s]
    have hr : Γ ⊢[Λ]! r := FiniteContext.byAxm₀
    have hpq : Γ ⊢[Λ]! p ⋏ (q ⋏ ⊤) := FiniteContext.byAxm₁
    have hf : Γ ⊢[Λ]! p 🡒 q 🡒 r 🡒 s := FiniteContext.byAxm₂
    have hp : Γ ⊢[Λ]! p := Entailment.K_left hpq
    have hq : Γ ⊢[Λ]! q := Entailment.K_left (Entailment.K_right hpq)
    exact ⟨((hf ⨀ hp) ⨀ hq) ⨀ hr⟩
  have hi := FiniteContext.toDef (Classical.choice (FiniteContext.deduct! h))
  apply Nonempty.intro
  simpa using (Entailment.mdp hi (Entailment.verum : Λ ⊢! ⊤))

theorem nnConjTop (p q : Propositionᵢ L) :
    Λ ⊢ (∼∼p ⋏ (∼∼q ⋏ ⊤)) 🡒 ∼∼(p ⋏ (q ⋏ ⊤)) := by
  obtain ⟨hqt⟩ := nnConj (Λ := Λ) q ⊤
  obtain ⟨hpt⟩ := nnConj (Λ := Λ) p (q ⋏ ⊤)
  have hb : Λ ⊢! (∼∼q ⋏ ⊤) 🡒 ∼∼(q ⋏ ⊤) :=
    Entailment.C_trans (Entailment.CKK_of_C_of_C Entailment.C_id Entailment.dni) hqt
  exact ⟨Entailment.C_trans
    (Entailment.CKK_of_C_of_C Entailment.C_id hb) hpt⟩
theorem nnConjAny (p q x : Propositionᵢ L) :
    Λ ⊢ (∼∼p ⋏ (∼∼q ⋏ x)) 🡒 ∼∼(p ⋏ (q ⋏ ⊤)) := by
  obtain ⟨hqt⟩ := nnConj (Λ := Λ) q ⊤
  obtain ⟨hpt⟩ := nnConj (Λ := Λ) p (q ⋏ ⊤)
  have htt : Λ ⊢! ∼∼(⊤ : Propositionᵢ L) := Entailment.mdp Entailment.dni Entailment.verum
  have hx : Λ ⊢! x 🡒 ∼∼(⊤ : Propositionᵢ L) :=
    Entailment.mdp (HilbertProofᵢ.implyK _ _) htt
  have hb : Λ ⊢! (∼∼q ⋏ x) 🡒 ∼∼(q ⋏ ⊤) :=
    Entailment.C_trans (Entailment.CKK_of_C_of_C Entailment.C_id hx) hqt
  exact ⟨Entailment.C_trans
    (Entailment.CKK_of_C_of_C Entailment.C_id hb) hpt⟩
omit [L.DecidableEq] in
theorem openAllC_and (n : ℕ) (p q : Semiproposition L n) :
    openAllC n (p ⋏ q) = (openAllC n p ⋏ openAllC n q) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [openAllC, LogicalConnective.HomClass.map_and, ih]

omit [L.DecidableEq] in
theorem openAllC_top (n : ℕ) : openAllC n (⊤ : Semiproposition L n) = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [openAllC] using ih

omit [L.DecidableEq] in
theorem openAll_top (n : ℕ) : openAll n (⊤ : Semipropositionᵢ L n) = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [openAll] using ih

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem atomic_relation_image (n : ℕ) {k j l m : ℕ} (ra : language.Rel k)
    (rb : language.Rel j) (rr : language.Rel l) (rs : language.Rel m)
    (a : Fin k → Semiterm language ℕ n) (b : Fin j → Semiterm language ℕ n)
    (v : Fin l → Semiterm language ℕ n) (w : Fin m → Semiterm language ℕ n) :
    (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
      openAll n ((Semiformulaᵢ.rel ra a) 🡒 (Semiformulaᵢ.rel rb b) 🡒
        (Semiformulaᵢ.rel rr v) 🡒 Semiformulaᵢ.rel rs w) 🡒
      openAll n ((((Semiformula.rel ra a) ⋏ ((Semiformula.rel rb b) ⋏ ⊤)) 🡒
        (Semiformula.rel rr v) 🡒 Semiformula.rel rs w)ᴺ) := by
  let A := openAll n (Semiformulaᵢ.rel ra a)
  let B := openAll n (Semiformulaᵢ.rel rb b)
  let R := openAll n (Semiformulaᵢ.rel rr v)
  let S := openAll n (Semiformulaᵢ.rel rs w)
  let AC := openAllC n (Semiformula.rel ra a)
  let BC := openAllC n (Semiformula.rel rb b)
  let RC := openAllC n (Semiformula.rel rr v)
  let SC := openAllC n (Semiformula.rel rs w)
  have ha : ACᴺ = ∼∼A := by
    dsimp [AC, A]; rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hb : BCᴺ = ∼∼B := by
    dsimp [BC, B]; rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hr : RCᴺ = ∼∼R := by
    dsimp [RC, R]; rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hs : SCᴺ = ∼∼S := by
    dsimp [SC, S]; rw [←openAll_gg]; simp only [Semiformula.doubleNegation_rel, openAll_neg]
  have hg := gg_two_implications (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) (AC ⋏ (BC ⋏ ⊤)) RC SC
  rw [Semiformula.doubleNegation_and, Semiformula.doubleNegation_and,
    Semiformula.doubleNegation_verum, ha, hb, hr, hs] at hg
  obtain ⟨hg⟩ := hg
  obtain ⟨hc⟩ := curried_conj (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) A B R S
  obtain ⟨hd⟩ := twoImp_dni (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) (A ⋏ (B ⋏ ⊤)) R S
  obtain ⟨hn⟩ := nnConjAny (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) A B (∼⊥)
  have h := Entailment.C_trans hc (Entailment.C_trans hd
    (Entailment.C_trans (Entailment.CCC_of_C_left hn) (Entailment.K_left hg)))
  apply Nonempty.intro
  exact Entailment.cast h (by
    simp only [openAll_imp, openAll_gg, openAllC_imp, openAllC_and, openAllC_top,
      A, B, R, S, AC, BC, RC, SC])
theorem atomic_relation_closure {n k j l m : ℕ} (ra : language.Rel k)
    (rb : language.Rel j) (rr : language.Rel l) (rs : language.Rel m)
    (a : Fin k → TermN n) (b : Fin j → TermN n)
    (v : Fin l → TermN n) (w : Fin m → TermN n) : nativeTheory ⊢
      (∀⁰* ((Semiformulaᵢ.rel ra a) 🡒 (Semiformulaᵢ.rel rb b) 🡒
        (Semiformulaᵢ.rel rr v) 🡒 Semiformulaᵢ.rel rs w)) 🡒
      (∀⁰* (((Semiformula.rel ra a) ⋏ ((Semiformula.rel rb b) ⋏ ⊤)) 🡒
        (Semiformula.rel rr v) 🡒 Semiformula.rel rs w))ᴺ := by
  have h := atomic_relation_image n ra rb rr rs (fun i => Rew.emb (a i))
    (fun i => Rew.emb (b i)) (fun i => Rew.emb (v i)) (fun i => Rew.emb (w i))
  have hh := allClosure_imp n _ _ h
  obtain ⟨hh⟩ := hh
  apply Nonempty.intro
  apply Theoryᵢ.ofHilbert
  simpa [gg_allClosure, LogicalConnective.HomClass.map_imply, Rewriting.emb,
    Semiformula.rew_doubleNegation, Semiformulaᵢ.rew_rel, Function.comp_def] using hh
def relCongruenceI (r : language.Rel 2) : Sentenceᵢ language := ∀⁰ ∀⁰ ∀⁰ ∀⁰
  ((Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#2]) 🡒
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#1,#3]) 🡒
      (Semiformulaᵢ.rel r ![#0,#1]) 🡒 Semiformulaᵢ.rel r ![#2,#3])

theorem binary_relExt_adapter (r : language.Rel 2) :
    nativeTheory ⊢ relCongruenceI r 🡒 (Theory.Eq.relExt r)ᴺ := by
  have h := atomic_relation_closure (n := 4) Language.ORing.Rel.eq Language.ORing.Rel.eq r r
    ![#0,#2] ![#1,#3] ![#0,#1] ![#2,#3]
  have hv1 : (fun i : Fin 2 => (Semiterm.bvar (Fin.addCast 2 i) : TermN 4)) = ![#0,#1] := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have hv2 : (fun i : Fin 2 => (Semiterm.bvar (i.addNat 2) : TermN 4)) = ![#2,#3] := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  simp only [relCongruenceI, Theory.Eq.relExt, Matrix.conj, Matrix.vecTail,
    hv1, hv2, allClosure_succ] at h ⊢
  convert h using 1; simp [Fin.addCast, Fin.addNat]
  congr 1
end DiophantineConsistency.IPRARelationGGLogic
