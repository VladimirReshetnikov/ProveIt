import DiophantineConsistency.FoundationHAArithmetic
import DiophantineConsistency.FoundationPAHFLogic
import DiophantineConsistency.HAEqualityDecidable

/-! # Actual Foundation equality axioms in conventional HA

The endpoint handles the nine equality-theory cases of the ordered-ring
language. Only equality is made stable using the proved HA decision formula.
The encoded order relation remains double-negated and is transported by
Leibniz equality. Source implications use Foundation's existing GG equivalence;
no translation recursion or order axiom is introduced here.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAEquality
open LO LO.FirstOrder
open scoped LO.FirstOrder
open FoundationPAHFSyntax
open SetTheory.PA HA

/-- Equality-specific double-negation elimination, from actual HA decidability. -/
theorem equality_stable (s t : Term) : Proves (.imp (doubleNeg (.eq s t)) (.eq s t)) := by
  apply Relative.imp_intro
  apply Relative.or_elim ((EqualityDecidable.eq_decidable s t).weaken (by simp))
  · exact Relative.hypothesis List.mem_cons_self
  · have hn : Relative Formula.Ax_s
        [neg (.eq s t), doubleNeg (.eq s t)] (neg (.eq s t)) :=
      Relative.hypothesis List.mem_cons_self
    have hnn : Relative Formula.Ax_s
        [neg (.eq s t), doubleNeg (.eq s t)] (doubleNeg (.eq s t)) :=
      Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨L,hL,h⟩ := hnn.mp hn
    exact ⟨L,hL,.botE _ _ h⟩

private theorem recover {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (doubleNeg (.eq s t))) :
    Relative Formula.Ax_s G (.eq s t) :=
  ((equality_stable s t).weaken (by simp)).mp h

private theorem dni {G : List Formula} {a : Formula}
    (h : Relative Formula.Ax_s G a) : Relative Formula.Ax_s G (doubleNeg a) :=
  (relative_of_derives (Derives.doubleNeg_intro G a)).mp h

/-- Reuse the existing Foundation implication equivalence through the checked
logical proof map. The arbitrary finite HA context is retained. -/
theorem translated_imp {G : List Formula} (φ ψ : Proposition ℒₒᵣ)
    (h : Relative Formula.Ax_s G (.imp (formula φᴺ) (formula ψᴺ))) :
    Relative Formula.Ax_s G (formula (φ 🡒 ψ)ᴺ) := by
  obtain ⟨p⟩ := (LO.FirstOrder.Derivation.imply_doubleNegation
    (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ)) φ ψ)
  have hi := FoundationPAHFLogic.intuitionistic_proof p
  change Derives [] (.and
    (.imp (.imp (formula φᴺ) (formula ψᴺ)) (formula (φ 🡒 ψ)ᴺ))
    (.imp (formula (φ 🡒 ψ)ᴺ) (.imp (formula φᴺ) (formula ψᴺ)))) at hi
  exact ((relative_of_derives hi).and_left.weaken (by simp)).mp h

private def eqAtom (s t : SyntacticTerm ℒₒᵣ) : Proposition ℒₒᵣ :=
  .rel .eq ![s,t]
private def inputEqs : Proposition ℒₒᵣ :=
  eqAtom (.fvar 0) (.fvar 2) ⋏ (eqAtom (.fvar 1) (.fvar 3) ⋏ ⊤)

private theorem inputs {G : List Formula}
    (h : Relative Formula.Ax_s G (formula inputEqsᴺ)) :
    Relative Formula.Ax_s G (.eq (.var 0) (.var 2)) ∧
    Relative Formula.Ax_s G (.eq (.var 1) (.var 3)) := by
  exact ⟨recover h.and_left, recover h.and_right.and_left⟩

theorem refl : Proves (sentence (Theory.Eq.refl ℒₒᵣ)ᴺ) := by
  change Proves (Formula.closeN 1 (doubleNeg (.eq (.var 0) (.var 0))))
  exact Arithmetic.reclose 1 (dni (Relative.eq_refl (.var 0)))

theorem symm : Proves (sentence (Theory.Eq.symm ℒₒᵣ)ᴺ) := by
  change Proves (Formula.closeN 2 (formula
    (eqAtom (.fvar 1) (.fvar 0) 🡒 eqAtom (.fvar 0) (.fvar 1))ᴺ))
  apply Arithmetic.reclose 2
  apply translated_imp
  apply Relative.imp_intro
  exact dni (recover (Relative.hypothesis List.mem_cons_self)).eq_symm

theorem trans : Proves (sentence (Theory.Eq.trans ℒₒᵣ)ᴺ) := by
  change Proves (Formula.closeN 3 (formula
    (eqAtom (.fvar 2) (.fvar 1) 🡒
      (eqAtom (.fvar 1) (.fvar 0) 🡒 eqAtom (.fvar 2) (.fvar 0)))ᴺ))
  apply Arithmetic.reclose 3
  apply translated_imp
  apply Relative.imp_intro
  apply translated_imp
  apply Relative.imp_intro
  have h₁ : Relative Formula.Ax_s
      [formula (eqAtom (.fvar 1) (.fvar 0))ᴺ,
       formula (eqAtom (.fvar 2) (.fvar 1))ᴺ] (.eq (.var 2) (.var 1)) :=
    recover (Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
  exact dni (h₁.eq_trans (recover (Relative.hypothesis List.mem_cons_self)))

/-- Both nullary cases retain the source empty conjunction as an antecedent. -/
theorem funcZero : Proves (sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .zero)ᴺ) := by
  change Proves (formula ((⊤ : Proposition ℒₒᵣ) 🡒
    eqAtom (.func .zero Fin.elim0) (.func .zero Fin.elim0))ᴺ)
  apply translated_imp
  apply Relative.imp_intro
  exact dni (Relative.eq_refl .zero)

theorem funcOne : Proves (sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .one)ᴺ) := by
  change Proves (formula ((⊤ : Proposition ℒₒᵣ) 🡒
    eqAtom (.func .one Fin.elim0) (.func .one Fin.elim0))ᴺ)
  apply translated_imp
  apply Relative.imp_intro
  exact dni (Relative.eq_refl (.succ .zero))

theorem funcAdd : Proves (sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .add)ᴺ) := by
  change Proves (Formula.closeN 4 (formula (inputEqs 🡒 eqAtom
    (.func .add ![.fvar 0,.fvar 1]) (.func .add ![.fvar 2,.fvar 3]))ᴺ))
  apply Arithmetic.reclose 4
  apply translated_imp
  apply Relative.imp_intro
  obtain ⟨h₁,h₂⟩ := inputs (Relative.hypothesis List.mem_cons_self)
  exact dni ((h₁.eq_add_left (.var 1)).eq_trans (h₂.eq_add_right (.var 2)))

theorem funcMul : Proves (sentence (Theory.Eq.funcExt (L := ℒₒᵣ) .mul)ᴺ) := by
  change Proves (Formula.closeN 4 (formula (inputEqs 🡒 eqAtom
    (.func .mul ![.fvar 0,.fvar 1]) (.func .mul ![.fvar 2,.fvar 3]))ᴺ))
  apply Arithmetic.reclose 4
  apply translated_imp
  apply Relative.imp_intro
  obtain ⟨h₁,h₂⟩ := inputs (Relative.hypothesis List.mem_cons_self)
  exact dni ((h₁.eq_mul_left (.var 1)).eq_trans (h₂.eq_mul_right (.var 2)))

theorem relEq : Proves (sentence (Theory.Eq.relExt (L := ℒₒᵣ) .eq)ᴺ) := by
  change Proves (Formula.closeN 4 (formula (inputEqs 🡒
    (eqAtom (.fvar 0) (.fvar 1) 🡒 eqAtom (.fvar 2) (.fvar 3)))ᴺ))
  apply Arithmetic.reclose 4
  apply translated_imp
  apply Relative.imp_intro
  apply translated_imp
  apply Relative.imp_intro
  obtain ⟨h₁,h₂⟩ := inputs (Relative.hypothesis
    (List.mem_cons_of_mem _ List.mem_cons_self))
  exact dni ((h₁.eq_symm.eq_trans (recover
    (Relative.hypothesis List.mem_cons_self))).eq_trans h₂)

/-- This transports a double-negated existential order formula. It never
extracts its witness or assumes that order itself is decidable or stable. -/
theorem lt_transport {G : List Formula} {s t u v : Term}
    (hs : Relative Formula.Ax_s G (.eq s u))
    (ht : Relative Formula.Ax_s G (.eq t v))
    (h : Relative Formula.Ax_s G (doubleNeg (ltFormula s t))) :
    Relative Formula.Ax_s G (doubleNeg (ltFormula u v)) := by
  have h₀ : Relative Formula.Ax_s G (Formula.subst (Formula.instTerm s)
      (doubleNeg (ltFormula (.var 0) (Term.rename Nat.succ t)))) := by
    simpa only [doubleNeg, neg, Formula.subst, subst_ltFormula, Term.subst,
      Formula.instTerm, Formula.term_subst_instTerm_rename_succ] using h
  have h₁ := Relative.eq_elim
    (doubleNeg (ltFormula (.var 0) (Term.rename Nat.succ t))) hs h₀
  have h₂ : Relative Formula.Ax_s G (Formula.subst (Formula.instTerm t)
      (doubleNeg (ltFormula (Term.rename Nat.succ u) (.var 0)))) := by
    simpa only [doubleNeg, neg, Formula.subst, subst_ltFormula, Term.subst,
      Formula.instTerm, Formula.term_subst_instTerm_rename_succ] using h₁
  have h₃ := Relative.eq_elim
    (doubleNeg (ltFormula (Term.rename Nat.succ u) (.var 0))) ht h₂
  simpa only [doubleNeg, neg, Formula.subst, subst_ltFormula, Term.subst,
    Formula.instTerm, Formula.term_subst_instTerm_rename_succ] using h₃

theorem relLt : Proves (sentence (Theory.Eq.relExt (L := ℒₒᵣ) .lt)ᴺ) := by
  change Proves (Formula.closeN 4 (formula (inputEqs 🡒
    ((Semiformula.rel .lt ![.fvar 0,.fvar 1] : Proposition ℒₒᵣ) 🡒
     (Semiformula.rel .lt ![.fvar 2,.fvar 3] : Proposition ℒₒᵣ)))ᴺ))
  apply Arithmetic.reclose 4
  apply translated_imp
  apply Relative.imp_intro
  apply translated_imp
  apply Relative.imp_intro
  obtain ⟨h₁,h₂⟩ := inputs (Relative.hypothesis
    (List.mem_cons_of_mem _ List.mem_cons_self))
  exact lt_transport h₁ h₂ (Relative.hypothesis List.mem_cons_self)

/-- Every actual equality axiom of the ordered-ring source language has its
literal GG image proved in conventional HA. No image-axiom premise remains. -/
theorem equality_axiom {σ : Sentence ℒₒᵣ} (h : σ ∈ Theory.eqAxiom ℒₒᵣ) :
    Proves (sentence σᴺ) := by
  cases h with
  | refl => exact refl
  | symm => exact symm
  | trans => exact trans
  | funcExt f => cases f with
    | zero => exact funcZero
    | one => exact funcOne
    | add => exact funcAdd
    | mul => exact funcMul
  | relExt r => cases r with
    | eq => exact relEq
    | lt => exact relLt

end DiophantineConsistency.FoundationHAEquality
