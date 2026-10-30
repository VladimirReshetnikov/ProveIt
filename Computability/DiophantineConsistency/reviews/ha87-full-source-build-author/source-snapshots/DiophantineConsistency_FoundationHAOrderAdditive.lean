import DiophantineConsistency.FoundationHAOrderBase

/-! # Two additive order axioms translated into conventional HA

Order witnesses are transported by actual HA equality and additive proofs.
The GG premise stays double-negated. Only a literal negative conclusion
uses intuitionistic stability; no order/equality DNE or model oracle occurs.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderAdditive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAEquality FoundationHAOrderBase
open SetTheory.PA HA

private theorem dni {B : Formula → Prop} {G : List Formula} {a : Formula}
    (h : Relative B G a) : Relative B G (doubleNeg a) :=
  (relative_of_derives (Derives.doubleNeg_intro G a)).mp h

/-- The existing finite axiom list is retained through a purely logical map. -/
theorem map_doubleNeg {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (h : Relative B G (.imp a b)) :
    Relative B G (.imp (doubleNeg a) (doubleNeg b)) := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, hL, hp.doubleNeg_map⟩

/-- Stability is supplied only for a syntactically negative conclusion. -/
theorem apply_negative {G : List Formula} {a b : Formula} (hb : Negative b)
    (h : Relative Formula.Ax_s G (.imp a b))
    (ha : Relative Formula.Ax_s G (doubleNeg a)) : Relative Formula.Ax_s G b :=
  (relative_of_derives (hb.stable G)).mp ((map_doubleNeg h).mp ha)

/-- An actual existential implies its literal GG-style negative encoding.
The fresh witness shifts the entire finite context and is never extracted
from a double-negated premise. -/
theorem encoded_exists {G : List Formula} {a : Formula}
    (h : Relative Formula.Ax_s G (.ex a)) :
    Relative Formula.Ax_s G (neg (.all (neg (doubleNeg a)))) := by
  apply Relative.imp_intro
  apply Relative.ex_elim Formula.Ax_s_sentences
    (h.prepend (.all (neg (doubleNeg a))))
  have hf : Relative Formula.Ax_s
      (a :: (.all (neg (doubleNeg a)) :: G).map (Formula.rename Nat.succ))
      (Formula.rename Nat.succ (.all (neg (doubleNeg a)))) := by
    apply Relative.hypothesis
    exact List.mem_cons_of_mem _ (by simp)
  have hn := Relative.all_elim (.var 0) hf
  have hn' : Relative Formula.Ax_s
      (a :: (.all (neg (doubleNeg a)) :: G).map (Formula.rename Nat.succ))
      (neg (doubleNeg a)) := by
    simpa only [Formula.rename, Formula.subst_instTerm_var_zero_rename_up_succ] using hn
  exact hn'.mp (dni (Relative.hypothesis List.mem_cons_self))

def addWitnessBody (s t : Term) : Formula :=
  .eq (.add (Term.rename Nat.succ s) (.var 0)) (Term.rename Nat.succ t)

def addWitness (s t : Term) : Formula := .ex (addWitnessBody s t)

theorem subst_addWitness (σ : Nat → Term) (s t : Term) :
    Formula.subst σ (addWitness s t) =
      addWitness (Term.subst σ s) (Term.subst σ t) := by
  simp only [addWitness, addWitnessBody, Formula.subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_addWitness (r : Nat → Nat) (s t : Term) :
    Formula.rename r (addWitness s t) =
      addWitness (Term.rename r s) (Term.rename r t) := by
  rw [← Formula.subst_var_rename, subst_addWitness]
  simp only [Formula.term_subst_var_rename]

/-- A predecessor witness d for s<t supplies the actual sum witness S d. -/
theorem add_witness {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (ltFormula s t)) :
    Relative Formula.Ax_s G (addWitness s t) := by
  apply Relative.ex_elim Formula.Ax_s_sentences h
  rw [rename_addWitness]
  apply Relative.ex_intro _ (.succ (.var 0))
  simp only [addWitnessBody, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ]
  exact Relative.hypothesis List.mem_cons_self

/-- Addition on the right retains the very same strict-order witness.
Every ambient term is shifted under that witness binder. -/
theorem add_lt_add {G : List Formula} {s t : Term} (u : Term)
    (h : Relative Formula.Ax_s G (ltFormula s t)) :
    Relative Formula.Ax_s G (ltFormula (.add s u) (.add t u)) := by
  apply Relative.ex_elim Formula.Ax_s_sentences h
  rw [rename_ltFormula]
  apply Relative.ex_intro _ (.var 0)
  simp only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ]
  let ss := Term.rename Nat.succ s
  let ts := Term.rename Nat.succ t
  let us := Term.rename Nat.succ u
  have he : Relative Formula.Ax_s
      (.eq (.add ss (.succ (.var 0))) ts :: G.map (Formula.rename Nat.succ))
      (.eq (.add ss (.succ (.var 0))) ts) :=
    Relative.hypothesis List.mem_cons_self
  have h₁ := (Arithmetic.add_assoc ss us (.succ (.var 0))).weaken
    (G' := .eq (.add ss (.succ (.var 0))) ts :: G.map (Formula.rename Nat.succ)) (by simp)
  have h₂ := ((Arithmetic.add_comm us (.succ (.var 0))).eq_add_right ss).weaken
    (G' := .eq (.add ss (.succ (.var 0))) ts :: G.map (Formula.rename Nat.succ)) (by simp)
  have h₃ := (Arithmetic.add_assoc ss (.succ (.var 0)) us).eq_symm.weaken
    (G' := .eq (.add ss (.succ (.var 0))) ts :: G.map (Formula.rename Nat.succ)) (by simp)
  exact ((h₁.eq_trans h₂).eq_trans h₃).eq_trans (he.eq_add_left us)

/-- The negative existential conclusion is stable; order itself is not
asserted stable and no witness is extracted from its double negation. -/
theorem negative_add_witness {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (doubleNeg (ltFormula s t))) :
    Relative Formula.Ax_s G (neg (.all (neg (doubleNeg (addWitnessBody s t))))) := by
  have hp : Proves (.imp (ltFormula s t)
      (neg (.all (neg (doubleNeg (addWitnessBody s t)))))) := by
    apply Relative.imp_intro
    exact encoded_exists (add_witness (Relative.hypothesis List.mem_cons_self))
  exact apply_negative (.neg _) (hp.weaken (by simp)) h

theorem negative_add_lt_add {G : List Formula} {s t : Term} (u : Term)
    (h : Relative Formula.Ax_s G (doubleNeg (ltFormula s t))) :
    Relative Formula.Ax_s G (doubleNeg (ltFormula (.add s u) (.add t u))) := by
  have hp : Proves (.imp (ltFormula s t) (ltFormula (.add s u) (.add t u))) := by
    apply Relative.imp_intro
    exact add_lt_add u (Relative.hypothesis List.mem_cons_self)
  exact (map_doubleNeg (hp.weaken (by simp))).mp h

/-- Literal GG image of the existing two-variable source axiom. -/
theorem addEqOfLt : Proves (sentence PeanoMinus.Axiom.addEqOfLtᴺ) := by
  change Proves (Formula.closeN 2 (formula
    (“&1 < &0 → ∃ z, &1 + z = &0” : Proposition ℒₒᵣ)ᴺ))
  apply Arithmetic.reclose 2
  apply translated_imp
  apply Relative.imp_intro
  exact negative_add_witness (Relative.hypothesis List.mem_cons_self)

/-- Literal GG image with source quantifier order x,y,z and target slots2,1,0. -/
theorem addLtAdd : Proves (sentence PeanoMinus.Axiom.addLtAddᴺ) := by
  change Proves (Formula.closeN 3 (formula
    (“&2 < &1 → &2 + &0 < &1 + &0” : Proposition ℒₒᵣ)ᴺ))
  apply Arithmetic.reclose 3
  apply translated_imp
  apply Relative.imp_intro
  exact negative_add_lt_add (.var 0) (Relative.hypothesis List.mem_cons_self)

end DiophantineConsistency.FoundationHAOrderAdditive
