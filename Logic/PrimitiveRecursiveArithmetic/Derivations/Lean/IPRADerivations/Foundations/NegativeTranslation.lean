import IPRADerivations.Core.Order

/-!
# The atom-preserving negative translation of classical PRA into iPRA

Packets: `ipra_kifc_framework_2026-11-16` (`paper/sections/11b_retained_transfer.tex`: Theorems
`thm:negative-stability` "Negative stability", `thm:proof-translation` "Proof translation" and
`thm:qf-recovery` "Quantifier-free recovery") and `ipra_pfig_framework_2026-11-15` (the same retained-transfer
statements). The translation keeps atoms and `⊥`, commutes with `∧`, `→`, `∀`, and sends
`A ∨ B` to `¬(¬A^N ∧ ¬B^N)` and `∃x A` to `¬∀x ¬A^N`. Because natural-number equality is decidable in
iPRA (`Core/Order.eq_or_ne`), no double negation is needed at the atoms.

* `trN`, `trN_subst`, `trN_shift`, `trN_QF`: the translation, its commutation with substitution, and that it
  keeps quantifier-free formulas quantifier-free;
* `stable` (`thm:negative-stability`): for every formula `A`, iPRA proves `¬¬A^N → A^N`;
* `qf_dec`, `qf_recovery` (`thm:qf-recovery`): every quantifier-free formula is decidable, and
  `A^N ↔ A` for quantifier-free `A`;
* `CPRAAx`: classical PRA, the axioms of iPRA together with every instance of `A ∨ ¬A`;
* `proof_translation` (`thm:proof-translation`): `Γ ⊢_{CPRA} A` gives `Γ^N ⊢_{iPRA} A^N`, by induction on
  the classical derivation;
* `qf_conservative`: a quantifier-free theorem of classical PRA is a theorem of iPRA;
* `Retained`, `retained_equivalence` (`thm:retained-equivalence`), `lift_classical` and `retained_transfer`
  (`thm:retained-transfer`): on sequents of retained formulas (quantifier-free formulas closed under `∧`, `→`,
  `∀`) classical and intuitionistic PRA prove the same.
-/

namespace LeanProofs.IPRA.Foundations.NegativeTranslation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm

/-- The atom-preserving negative translation. -/
def trN : {n : ℕ} → Fm PTm n → Fm PTm n
  | _, .eq s t => .eq s t
  | _, .bot => .bot
  | _, .and φ ψ => .and (trN φ) (trN ψ)
  | _, .or φ ψ => neg (.and (neg (trN φ)) (neg (trN ψ)))
  | _, .imp φ ψ => .imp (trN φ) (trN ψ)
  | _, .all φ => .all (trN φ)
  | _, .ex φ => neg (.all (neg (trN φ)))

theorem neg_subst {n m : ℕ} (φ : Fm PTm n) (σ : Fin n → PTm m) : (neg φ).subst σ = neg (φ.subst σ) := rfl

theorem trN_subst : {n m : ℕ} → (φ : Fm PTm n) → (σ : Fin n → PTm m) → trN (φ.subst σ) = (trN φ).subst σ
  | _, _, .eq s t, σ => rfl
  | _, _, .bot, σ => rfl
  | _, _, .and φ ψ, σ => by simp only [Fm.subst_and, trN, trN_subst φ σ, trN_subst ψ σ]
  | _, _, .or φ ψ, σ => by simp only [Fm.subst_or, trN, neg_subst, Fm.subst_and, trN_subst φ σ, trN_subst ψ σ]
  | _, _, .imp φ ψ, σ => by simp only [Fm.subst_imp, trN, trN_subst φ σ, trN_subst ψ σ]
  | _, _, .all φ, σ => by simp only [Fm.subst_all, trN, trN_subst φ (Syn.up σ)]
  | _, _, .ex φ, σ => by simp only [Fm.subst_ex, trN, neg_subst, Fm.subst_all, trN_subst φ (Syn.up σ)]

theorem trN_shift {n : ℕ} (φ : Fm PTm n) : trN φ.shift = (trN φ).shift := trN_subst φ _

theorem map_trN_shift {n : ℕ} (Γ : List (Fm PTm n)) :
    (Γ.map Fm.shift).map trN = (Γ.map trN).map Fm.shift := by
  simp only [List.map_map]
  congr 1
  funext φ
  exact trN_shift φ

theorem trN_QF : {n : ℕ} → (φ : Fm PTm n) → φ.QF → (trN φ).QF
  | _, .eq _ _, _ => trivial
  | _, .bot, _ => trivial
  | _, .and φ ψ, h => ⟨trN_QF φ h.1, trN_QF ψ h.2⟩
  | _, .or φ ψ, h => ⟨⟨⟨trN_QF φ h.1, trivial⟩, ⟨trN_QF ψ h.2, trivial⟩⟩, trivial⟩
  | _, .imp φ ψ, h => ⟨trN_QF φ h.1, trN_QF ψ h.2⟩
  | _, .all _, h => h.elim
  | _, .ex _, h => h.elim

/-! ## Stability -/

theorem hyp2 {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ χ : Fm PTm n} : (χ :: ψ :: φ :: Γ) ⊢[PRAAx] φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem hyp3 {n : ℕ} {Γ : List (Fm PTm n)} {φ ψ χ ω : Fm PTm n} : (ω :: χ :: ψ :: φ :: Γ) ⊢[PRAAx] φ :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- Instantiating the bound variable of a shifted body at the new variable gives the body back. -/
theorem shift_up_inst {n : ℕ} (φ : Fm PTm (n + 1)) :
    (φ.subst (Syn.up (fun i => Syn.var i.succ))).subst (Syn.inst (Syn.var 0)) = φ := by
  rw [Fm.subst_subst]
  conv_rhs => rw [← Fm.subst_id φ]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Syn.shift]

/-- Negations are stable: `¬¬¬X → ¬X`. -/
theorem neg_stable {n : ℕ} {Γ : List (Fm PTm n)} (X : Fm PTm n) :
    Γ ⊢[PRAAx] neg (neg (neg X)) ⟶ neg X :=
  .impI (.impI (.impE Prf.hyp1 (.impI (.impE Prf.hyp0 Prf.hyp1))))

/-- `thm:negative-stability`: `¬¬A^N → A^N` for every formula `A`. -/
theorem stable : {n : ℕ} → (φ : Fm PTm n) → {Γ : List (Fm PTm n)} → Γ ⊢[PRAAx] neg (neg (trN φ)) ⟶ trN φ
  | _, .eq s t, Γ => by
    refine .impI (.orE (eq_or_ne s t) Prf.hyp0 (.botE _ (.impE Prf.hyp1 Prf.hyp0)))
  | _, .bot, Γ => .impI (.impE Prf.hyp0 (.impI Prf.hyp0))
  | _, .and φ ψ, Γ => by
    refine .impI (.andI (.impE (stable φ) (.impI ?_)) (.impE (stable ψ) (.impI ?_)))
    · exact .impE Prf.hyp1 (.impI (.impE Prf.hyp1 (.andE₁ Prf.hyp0)))
    · exact .impE Prf.hyp1 (.impI (.impE Prf.hyp1 (.andE₂ Prf.hyp0)))
  | _, .or φ ψ, Γ => neg_stable _
  | _, .imp φ ψ, Γ => by
    refine .impI (.impI (.impE (stable ψ) (.impI ?_)))
    exact .impE hyp2 (.impI (.impE Prf.hyp1 (.impE Prf.hyp0 hyp2)))
  | _, .all φ, Γ => by
    refine .impI (.allI (.impE (stable φ) (.impI ?_)))
    have nn : (neg (trN φ) :: (neg (neg (Fm.all (trN φ))) :: Γ).map Fm.shift) ⊢[PRAAx]
        (neg (neg (Fm.all (trN φ)))).shift := .hyp (by simp)
    refine .impE nn (.impI ?_)
    have f : (Fm.all ((trN φ).subst (Syn.up (fun i => Syn.var i.succ))) ::
        neg (trN φ) :: (neg (neg (Fm.all (trN φ))) :: Γ).map Fm.shift) ⊢[PRAAx]
        Fm.all ((trN φ).subst (Syn.up (fun i => Syn.var i.succ))) := Prf.hyp0
    have g := Prf.allE (Syn.var 0) f
    rw [shift_up_inst] at g
    exact .impE Prf.hyp1 g
  | _, .ex φ, Γ => neg_stable _

/-! ## Quantifier-free formulas -/

/-- Every quantifier-free formula is decidable in iPRA. -/
theorem qf_dec : {n : ℕ} → (φ : Fm PTm n) → φ.QF → {Γ : List (Fm PTm n)} → Γ ⊢[PRAAx] φ ⋎ neg φ
  | _, .eq s t, _, Γ => eq_or_ne s t
  | _, .bot, _, Γ => .orI₂ (.impI Prf.hyp0)
  | _, .and φ ψ, h, Γ => by
    refine .orE (qf_dec φ h.1) (.orE (qf_dec ψ h.2) (.orI₁ (.andI Prf.hyp1 Prf.hyp0)) ?_) ?_
    · exact .orI₂ (.impI (.impE Prf.hyp1 (.andE₂ Prf.hyp0)))
    · exact .orI₂ (.impI (.impE Prf.hyp1 (.andE₁ Prf.hyp0)))
  | _, .or φ ψ, h, Γ => by
    refine .orE (qf_dec φ h.1) (.orI₁ (.orI₁ Prf.hyp0)) ?_
    refine .orE (qf_dec ψ h.2) (.orI₁ (.orI₂ Prf.hyp0)) ?_
    exact .orI₂ (.impI (.orE Prf.hyp0 (.impE hyp3 Prf.hyp0) (.impE hyp2 Prf.hyp0)))
  | _, .imp φ ψ, h, Γ => by
    refine .orE (qf_dec ψ h.2) (.orI₁ (.impI Prf.hyp1)) ?_
    refine .orE (qf_dec φ h.1) ?_ (.orI₁ (.impI (.botE _ (.impE Prf.hyp1 Prf.hyp0))))
    exact .orI₂ (.impI (.impE hyp2 (.impE Prf.hyp0 Prf.hyp1)))
  | _, .all _, h, _ => h.elim
  | _, .ex _, h, _ => h.elim

/-- `thm:qf-recovery`: `A^N ↔ A` for quantifier-free `A`. -/
theorem qf_recovery : {n : ℕ} → (φ : Fm PTm n) → φ.QF → {Γ : List (Fm PTm n)} →
    (Γ ⊢[PRAAx] trN φ ⟶ φ) ∧ (Γ ⊢[PRAAx] φ ⟶ trN φ)
  | _, .eq s t, _, Γ => ⟨.impI Prf.hyp0, .impI Prf.hyp0⟩
  | _, .bot, _, Γ => ⟨.impI Prf.hyp0, .impI Prf.hyp0⟩
  | _, .and φ ψ, h, Γ =>
    ⟨.impI (.andI (.impE (qf_recovery φ h.1).1 (.andE₁ Prf.hyp0)) (.impE (qf_recovery ψ h.2).1 (.andE₂ Prf.hyp0))),
     .impI (.andI (.impE (qf_recovery φ h.1).2 (.andE₁ Prf.hyp0)) (.impE (qf_recovery ψ h.2).2 (.andE₂ Prf.hyp0)))⟩
  | _, .or φ ψ, h, Γ => by
    refine ⟨.impI ?_, .impI ?_⟩
    · refine .orE (qf_dec φ h.1) (.orI₁ Prf.hyp0) ?_
      refine .orE (qf_dec ψ h.2) (.orI₂ Prf.hyp0) ?_
      refine .botE _ (.impE hyp2 (.andI (.impI ?_) (.impI ?_)))
      · exact .impE hyp2 (.impE (qf_recovery φ h.1).1 Prf.hyp0)
      · exact .impE Prf.hyp1 (.impE (qf_recovery ψ h.2).1 Prf.hyp0)
    · refine .impI (.orE Prf.hyp1 ?_ ?_)
      · exact .impE (.andE₁ Prf.hyp1) (.impE (qf_recovery φ h.1).2 Prf.hyp0)
      · exact .impE (.andE₂ Prf.hyp1) (.impE (qf_recovery ψ h.2).2 Prf.hyp0)
  | _, .imp φ ψ, h, Γ =>
    ⟨.impI (.impI (.impE (qf_recovery ψ h.2).1 (.impE Prf.hyp1 (.impE (qf_recovery φ h.1).2 Prf.hyp0)))),
     .impI (.impI (.impE (qf_recovery ψ h.2).2 (.impE Prf.hyp1 (.impE (qf_recovery φ h.1).1 Prf.hyp0))))⟩
  | _, .all _, h, _ => h.elim
  | _, .ex _, h, _ => h.elim

/-! ## Translation of classical derivations -/

/-- Classical PRA: the axioms of iPRA and every instance of excluded middle. -/
def CPRAAx : Theory PTm := fun k φ => PRAAx k φ ∨ ∃ ψ : Fm PTm k, φ = (ψ ⋎ neg ψ)

theorem trN_axiom {k : ℕ} {φ : Fm PTm k} (h : PRAAx k φ) : PRAAx k (trN φ) := by
  cases h with
  | proj i => exact .proj i
  | comp f gs => exact .comp f gs
  | precZero f g => exact .precZero f g
  | precSucc f g => exact .precSucc f g
  | succNeZero => exact .succNeZero
  | succInj => exact .succInj
  | ind φ hφ =>
    have e : trN (φ.subst (Syn.inst ConciseIPRA.PTm.zero) ⟶
        Fm.all (φ ⟶ φ.subst (Syn.repl (ConciseIPRA.PTm.succ (Syn.var 0)))) ⟶ Fm.all φ) =
        ((trN φ).subst (Syn.inst ConciseIPRA.PTm.zero) ⟶
        Fm.all (trN φ ⟶ (trN φ).subst (Syn.repl (ConciseIPRA.PTm.succ (Syn.var 0)))) ⟶ Fm.all (trN φ)) := by
      simp only [trN, trN_subst]
    rw [e]
    exact .ind (trN φ) (trN_QF φ hφ)

/-- `thm:proof-translation`: a classical derivation translates into an iPRA derivation. -/
theorem proof_translation {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm n} (h : Γ ⊢[CPRAAx] φ) :
    Γ.map trN ⊢[PRAAx] trN φ := by
  induction h with
  | hyp h => exact .hyp (List.mem_map_of_mem h)
  | ax h σ =>
    rw [trN_subst]
    rcases h with h | ⟨ψ, rfl⟩
    · exact .ax (trN_axiom h) σ
    · simp only [trN, neg_subst, Fm.subst_and]
      exact .impI (.impE (.andE₂ Prf.hyp0) (.andE₁ Prf.hyp0))
  | botE φ _ ih => exact .botE _ ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .impI (.impE (.andE₁ Prf.hyp0) ih.wk)
  | orI₂ _ ih => exact .impI (.impE (.andE₂ Prf.hyp0) ih.wk)
  | @orE n Γ φ ψ χ _ _ _ ih ih₁ ih₂ =>
    refine .impE (stable χ) (.impI (.impE ih.wk (.andI (.impI ?_) (.impI ?_))))
    · exact .impE Prf.hyp1 (ih₁.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _)))
    · exact .impE Prf.hyp1 (ih₂.weaken (List.cons_subset_cons _ (List.subset_cons_self _ _)))
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | allI _ ih =>
    rw [map_trN_shift] at ih
    exact .allI ih
  | allE t _ ih =>
    rw [trN_subst]
    exact .allE t ih
  | exI t _ ih =>
    rw [trN_subst] at ih
    exact .impI (.impE (.allE t Prf.hyp0) ih.wk)
  | @exE n Γ φ ψ _ _ ih₁ ih₂ =>
    simp only [List.map_cons, map_trN_shift, trN_shift] at ih₂
    refine .impE (stable ψ) (.impI (.impE ih₁.wk (.allI (.impI ?_))))
    have nψ : (trN φ :: (neg (trN ψ) :: Γ.map trN).map Fm.shift) ⊢[PRAAx] (neg (trN ψ)).shift := .hyp (by simp)
    exact .impE nψ (ih₂.weaken (List.cons_subset_cons _ (by simp)))
  | eqRefl t => exact .eqRefl t
  | eqSubst φ σ σ' _ _ ih₁ ih₂ =>
    rw [trN_subst] at ih₂ ⊢
    exact .eqSubst (trN φ) σ σ' ih₁ ih₂

/-- A quantifier-free theorem of classical PRA is a theorem of iPRA. -/
theorem qf_conservative {n : ℕ} {φ : Fm PTm n} (hφ : φ.QF) (h : ([] : List (Fm PTm n)) ⊢[CPRAAx] φ) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] φ :=
  .impE (qf_recovery φ hφ).1 (proof_translation h)


/-! ## The retained class -/

/-- `Retained`: the least class containing the quantifier-free formulas and closed under `∧`, `→`, `∀`. -/
inductive Retained : {n : ℕ} → Fm PTm n → Prop
  | qf {n : ℕ} {φ : Fm PTm n} (h : φ.QF) : Retained φ
  | and {n : ℕ} {φ ψ : Fm PTm n} (h₁ : Retained φ) (h₂ : Retained ψ) : Retained (φ ⋏ ψ)
  | imp {n : ℕ} {φ ψ : Fm PTm n} (h₁ : Retained φ) (h₂ : Retained ψ) : Retained (φ ⟶ ψ)
  | all {n : ℕ} {φ : Fm PTm (n + 1)} (h : Retained φ) : Retained (Fm.all φ)

/-- `thm:retained-equivalence`: `A^N ↔ A` for retained `A`. -/
theorem retained_equivalence {n : ℕ} {φ : Fm PTm n} (h : Retained φ) :
    ∀ {Γ : List (Fm PTm n)}, (Γ ⊢[PRAAx] trN φ ⟶ φ) ∧ (Γ ⊢[PRAAx] φ ⟶ trN φ) := by
  induction h with
  | qf h => exact fun {Γ} => qf_recovery _ h
  | and _ _ ih₁ ih₂ =>
    exact fun {Γ} =>
      ⟨.impI (.andI (.impE ih₁.1 (.andE₁ Prf.hyp0)) (.impE ih₂.1 (.andE₂ Prf.hyp0))),
       .impI (.andI (.impE ih₁.2 (.andE₁ Prf.hyp0)) (.impE ih₂.2 (.andE₂ Prf.hyp0)))⟩
  | imp _ _ ih₁ ih₂ =>
    exact fun {Γ} =>
      ⟨.impI (.impI (.impE ih₂.1 (.impE Prf.hyp1 (.impE ih₁.2 Prf.hyp0)))),
       .impI (.impI (.impE ih₂.2 (.impE Prf.hyp1 (.impE ih₁.1 Prf.hyp0))))⟩
  | all _ ih =>
    exact fun {Γ} =>
      ⟨.impI (.allI (.impE ih.1 (Prf.allOpen Prf.hyp0))), .impI (.allI (.impE ih.2 (Prf.allOpen Prf.hyp0)))⟩

/-- Every iPRA derivation is a derivation of classical PRA. -/
theorem lift_classical {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm n} (h : Γ ⊢[PRAAx] φ) : Γ ⊢[CPRAAx] φ := by
  induction h with
  | hyp h => exact .hyp h
  | ax h σ => exact .ax (Or.inl h) σ
  | botE φ _ ih => exact .botE φ ih
  | andI _ _ ih₁ ih₂ => exact .andI ih₁ ih₂
  | andE₁ _ ih => exact .andE₁ ih
  | andE₂ _ ih => exact .andE₂ ih
  | orI₁ _ ih => exact .orI₁ ih
  | orI₂ _ ih => exact .orI₂ ih
  | orE _ _ _ ih ih₁ ih₂ => exact .orE ih ih₁ ih₂
  | impI _ ih => exact .impI ih
  | impE _ _ ih₁ ih₂ => exact .impE ih₁ ih₂
  | allI _ ih => exact .allI ih
  | allE t _ ih => exact .allE t ih
  | exI t _ ih => exact .exI t ih
  | exE _ _ ih₁ ih₂ => exact .exE ih₁ ih₂
  | eqRefl t => exact .eqRefl t
  | eqSubst φ σ σ' _ _ ih₁ ih₂ => exact .eqSubst φ σ σ' ih₁ ih₂

/-- `thm:retained-transfer`: on retained sequents classical and intuitionistic PRA prove the same. -/
theorem retained_transfer {n : ℕ} {Γ : List (Fm PTm n)} {φ : Fm PTm n} (hΓ : ∀ ψ ∈ Γ, Retained ψ)
    (hφ : Retained φ) (h : Γ ⊢[CPRAAx] φ) : Γ ⊢[PRAAx] φ := by
  have t := (proof_translation h).trans (Δ := Γ) (by
    intro χ hχ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ
    exact .impE (retained_equivalence (hΓ ψ hψ)).2 (.hyp hψ))
  exact .impE (retained_equivalence hφ).1 t

end LeanProofs.IPRA.Foundations.NegativeTranslation
