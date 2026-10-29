import ZFCinPA.BufferedTemplateProofCompiler
import BoundedPAConsistency.SizedDerivation

/-!
# The buffered template compiler, with an explicit size bound

`BufferedTemplateProofCompiler.compileDerivation` compiles a fixed meta-level
derivation `d : T₁ ⟹₂ Γ` into an internal derivation of the translated
sequent. Its axiom leaves come from a supplied `axiomProof`, which in the
`L` application is chosen with `Classical.choose`, so its code is
unconstrained.

This module proves the bounded counterpart directly, by meta induction on
`d`: if every translated formula of every sequent of `d` (at every buffer up
to `B`) is below `F`, the translated terms and axiom proofs are below `2^e`,
and `F ≤ e`, then the translated conclusion has an internal derivation with
code at most `2^(1024^(height d) · e)` (`sized_compile`). The derivation is
built from the bounded primitive rules of `SizedDerivation` and need not
coincide with `compileDerivation`'s code.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedTemplateCompiler

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.BufferedTemplateProofCompiler
open LeanProofs.BoundedPAConsistency.SizedDerivation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L₁ L₂ : Language} [L₁.DecidableEq] [L₂.Encodable] [L₂.LORDefinable]
variable {T₁ : Theory L₁} {T₂ : InternalTheory V L₂}

/-! ## Stages and heights -/

/-- `stg n e = 1024ⁿ · e`. -/
def stg : ℕ → V → V
  | 0, e => e
  | n + 1, e => 1024 * stg n e

theorem le_stg (n : ℕ) (e : V) : e ≤ stg n e := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact le_trans ih DerivableLe.le_1024

theorem stg_mono {n m : ℕ} (h : n ≤ m) (e : V) : stg n e ≤ stg m e := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih DerivableLe.le_1024

theorem four_le_stg {e : V} (he : 4 ≤ e) (n : ℕ) : 4 ≤ stg n e := le_trans he (le_stg n e)

/-- The height of a meta-level derivation. -/
def height : {Γ : Finset (Proposition L₁)} → T₁ ⟹₂ Γ → ℕ
  | _, .closed _ _ _ _ => 1
  | _, .axm _ _ _ => 1
  | _, .verum _ => 1
  | _, .and _ d₁ d₂ => max (height d₁) (height d₂) + 1
  | _, .or _ d => height d + 1
  | _, .all _ d => height d + 1
  | _, .exs _ _ d => height d + 1
  | _, .wk d _ => height d + 1
  | _, .shift d => height d + 1
  | _, .cut d₁ d₂ => max (height d₁) (height d₂) + 1

/-! ## The hypotheses, recursively over the fixed derivation -/

variable (tr : BufferedTranslation V L₁ L₂)

/-- The translated members of `Γ`, at every buffer up to `B`, are below `F`. -/
def Here (F : V) (B : ℕ) (Γ : Finset (Proposition L₁)) : Prop :=
  ∀ b ≤ B, ∀ p ∈ Γ, (tr.formula b p).val < F

/-- Every sequent, term and axiom leaf of `d` is bounded. -/
def Good (U : InternalTheory V L₂) (F e : V) (B : ℕ) :
    {Γ : Finset (Proposition L₁)} → T₁ ⟹₂ Γ → Prop
  | Γ, d => Here tr F B Γ ∧
    match d with
    | .closed _ _ _ _ => True
    | .axm σ _ _ => ∀ b ≤ B,
        DerivableLe U.theory (insert (tr.formula b (Rewriting.emb σ)).val ∅) (Exp.exp e)
    | .verum _ => True
    | .and _ d₁ d₂ => Good U F e B d₁ ∧ Good U F e B d₂
    | .or _ d => Good U F e B d
    | .all _ d => Good U F e B d
    | .exs _ t d => (tr.term t).val ≤ Exp.exp e ∧ Good U F e B d
    | .wk d _ => Good U F e B d
    | .shift d => Good U F e B d
    | .cut d₁ d₂ => Good U F e B d₁ ∧ Good U F e B d₂

theorem Good.here {F e : V} {B : ℕ} {Γ : Finset (Proposition L₁)} {d : T₁ ⟹₂ Γ}
    (h : Good tr T₂ F e B d) : Here tr F B Γ := by
  unfold Good at h
  exact h.1

/-- The translated sequent at buffer `b` is below `2^e`. -/
theorem seq_bound {F e : V} {B b : ℕ} {Γ : Finset (Proposition L₁)} (hb : b ≤ B)
    (hh : Here tr F B Γ) (hFe : F ≤ e) :
    (translateSequent (tr.formula b) Γ).val ≤ Exp.exp e := by
  refine DerivableLe.seq_le hFe ?_
  intro y hy
  obtain ⟨p, hp, rfl⟩ := (mem_translateSequent_iff (f := tr.formula b)).mp hy
  exact hh b hb p hp

/-! ## The bounded compiler -/

/-- **The bounded buffered compiler.** -/
theorem sized_compile {F e : V} {B : ℕ} (he : 4 ≤ e) (hFe : F ≤ e) :
    ∀ {Γ : Finset (Proposition L₁)} (d : T₁ ⟹₂ Γ) (b : ℕ), bufferBound d ≤ b →
      b + height d ≤ B → Good tr T₂ F e B d →
      DerivableLe T₂.theory (translateSequent (tr.formula b) Γ).val
        (Exp.exp (stg (height d) e)) := by
  have translated_mem {b : ℕ} {Γ : Finset (Proposition L₁)} {p : Proposition L₁}
      (hp : p ∈ Γ) : (tr.formula b p).val ∈ (translateSequent (tr.formula b) Γ).val :=
    Bootstrapping.Sequent.mem_iff.mp (formula_mem_translateSequent (tr.formula b) hp)
  have child_heights {b h₁ h₂ B : ℕ} (h : b + (max h₁ h₂ + 1) ≤ B) :
      b + h₁ ≤ B ∧ b + h₂ ≤ B := by
    constructor <;> omega
  intro Γ d
  induction d with
  | closed Δ p hp hn =>
      intro b _ hbB hg
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      refine DerivableLe.em he (seq_bound tr hb (Good.here tr hg) hFe) (translateSequent (tr.formula b) Δ).val_formulaSet
        (tr.formula b p).val (translated_mem hp) ?_
      have := translated_mem (b := b) hn
      rw [tr.neg] at this
      simpa using this
  | axm σ hT hΓ =>
      intro b _ hbB hg
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      unfold Good at hg
      refine DerivableLe.wk he (seq_bound tr hb hg.1 hFe)
        (translateSequent (tr.formula b) _).val_formulaSet ?_ (hg.2 b hb)
      intro y hy
      rcases mem_bitInsert_iff.mp hy with rfl | hy
      · exact translated_mem hΓ
      · simp at hy
  | verum h =>
      intro b _ hbB hg
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      refine DerivableLe.verum he (seq_bound tr hb (Good.here tr hg) hFe)
        (translateSequent (tr.formula b) _).val_formulaSet ?_
      have := translated_mem (b := b) h
      rw [tr.verum] at this
      simpa using this
  | @and Δ φ ψ h dp dq ihp ihq =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, gp, gq⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound, max_le_iff] at hbb
      have hhgt := child_heights hbB
      have hp := ihp b hbb.1 hhgt.1 gp
      have hq := ihq b hbb.2 hhgt.2 gq
      rw [translateSequent_insert] at hp hq
      simp only [Bootstrapping.Sequent.val_insert] at hp hq
      have hm : (tr.formula b φ).val ^⋏ (tr.formula b ψ).val ∈
          (translateSequent (tr.formula b) Δ).val := by
        have := translated_mem (b := b) h
        rw [tr.and] at this
        simpa using this
      exact DerivableLe.and_m (four_le_stg he _)
        (le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e)) hm
        (hp.mono (exp_monotone_le.mpr (stg_mono (le_max_left _ _) e)))
        (hq.mono (exp_monotone_le.mpr (stg_mono (le_max_right _ _) e)))
  | @or Δ φ ψ h dp ih =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, gp⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound] at hbb
      have hp := ih b hbb (le_trans (Nat.add_le_add_left (Nat.le_succ _) b) hbB) gp
      rw [translateSequent_insert, translateSequent_insert] at hp
      simp only [Bootstrapping.Sequent.val_insert] at hp
      have hm : (tr.formula b φ).val ^⋎ (tr.formula b ψ).val ∈
          (translateSequent (tr.formula b) Δ).val := by
        have := translated_mem (b := b) h
        rw [tr.or] at this
        simpa using this
      exact DerivableLe.or_m (four_le_stg he _)
        (le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e)) hm hp
  | @all Δ φ h dp ih =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, gp⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound] at hbb
      have hp := ih (b + 1) (le_trans hbb (Nat.le_succ b))
        (by rw [Nat.add_right_comm]; exact hbB) gp
      rw [translateSequent_insert, tr.free, tr.sequent_shift] at hp
      simp only [Bootstrapping.Sequent.val_insert, Semiformula.free_val] at hp
      have hm : ^∀ (tr.formula b φ).val ∈ (translateSequent (tr.formula b) Δ).val := by
        have := translated_mem (b := b) h
        rw [tr.all] at this
        simpa using this
      exact DerivableLe.all_m (four_le_stg he _)
        (le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e)) hm hp
  | @exs Δ φ h t dp ih =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, ht, gp⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound] at hbb
      have hp := ih b hbb (le_trans (Nat.add_le_add_left (Nat.le_succ _) b) hbB) gp
      rw [translateSequent_insert, tr.subst₁] at hp
      simp only [Bootstrapping.Sequent.val_insert, Semiformula.val_substs] at hp
      have hm : ^∃ (tr.formula b φ).val ∈ (translateSequent (tr.formula b) Δ).val := by
        have := translated_mem (b := b) h
        rw [tr.exs] at this
        simpa using this
      exact DerivableLe.ex_m (four_le_stg he _)
        (le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e))
        (le_exp_of_le ht (le_stg _ e)) hm (tr.term t).isSemiterm
        (by simpa [substs1] using hp)
  | wk dp hsub ih =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, gp⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound] at hbb
      have hp := ih b hbb (le_trans (Nat.add_le_add_left (Nat.le_succ _) b) hbB) gp
      exact DerivableLe.wk (four_le_stg he _)
        (le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e))
        (translateSequent (tr.formula b) _).val_formulaSet
        (Bootstrapping.Sequent.subset_iff.mp (translateSequent_mono (tr.formula b) hsub)) hp
  | @shift Δ dp ih =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, gp⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound] at hbb
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hp := ih b' (by omega) (by omega) gp
      have hS := tr.sequent_shift b' Δ
      have hsb : setShift L₂ (translateSequent (tr.formula b') Δ).val ≤
          Exp.exp (stg (height dp) e) := by
        have := congrArg Bootstrapping.Sequent.val hS
        simp only [Bootstrapping.Sequent.shift] at this
        rw [← this]
        exact le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e)
      have hD := DerivableLe.shift (four_le_stg he _) hsb hp
      have := congrArg Bootstrapping.Sequent.val hS
      simp only [Bootstrapping.Sequent.shift] at this
      rw [← this] at hD
      exact hD
  | @cut Δ φ dp dq ihp ihq =>
      intro b hbb hbB hg
      unfold Good at hg
      obtain ⟨hh, gp, gq⟩ := hg
      simp only [height] at hbB ⊢
      have hb : b ≤ B := le_trans (Nat.le_add_right b _) hbB
      simp only [bufferBound, max_le_iff] at hbb
      have hhgt := child_heights hbB
      have hp := ihp b hbb.1 hhgt.1 gp
      have hq := ihq b hbb.2 hhgt.2 gq
      have hφ := (Good.here tr gp) b hb _ (Finset.mem_insert_self _ _)
      rw [translateSequent_insert] at hp hq
      rw [tr.neg] at hq
      simp only [Bootstrapping.Sequent.val_insert, Semiformula.val_neg] at hp hq
      exact DerivableLe.cut (four_le_stg he _)
        (le_exp_of_le (seq_bound tr hb hh hFe) (le_stg _ e)) _
        (le_exp_of_le_self (le_trans (le_of_lt hφ) (le_trans hFe (le_stg _ e))))
        (hp.mono (exp_monotone_le.mpr (stg_mono (le_max_left _ _) e)))
        (hq.mono (exp_monotone_le.mpr (stg_mono (le_max_right _ _) e)))

end LeanProofs.ZFCinPA.SizedTemplateCompiler
