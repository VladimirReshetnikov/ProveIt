import ZFCinPA.SizedSchemaLeaves
import ZFCinPA.LTemplate

/-!
# Bounded template compilation over the full template theory

`LTemplate.compileT` turns a fixed source derivation over `templTheory`
(lifted `𝗭𝗙`, the equality axioms of the enlarged language, and every
separation/replacement instance) into an internal `𝗭𝗙` proof of its
translation at the placeholders `Ks`. Its axiom leaves use chosen codes.

This module proves the bounded counterpart, `sized_compileT`. Every axiom
leaf is bounded uniformly (`templ_leaf`):
* lifted axioms by one `axm` rule;
* placeholder congruence by `SizedPlaceholderCongruence.cong_leaf`;
* schema instances by `SizedSchemaLeaves.sep_leaf`/`rep_leaf`.
`sized_open_compile` then compiles the derivation itself. Placeholders are
shift-fixed (the `SetPlaceholders` convention) with arity at most `3`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedLTemplate

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LeanProofs.ZFCinPA.BufferedTemplateProofCompiler
open LeanProofs.ZFCinPA.TemplateTranslateLevel LeanProofs.ZFCinPA.SizedTemplateAxioms
open LeanProofs.ZFCinPA.SizedTemplateCompiler LeanProofs.ZFCinPA.SizedOpenTemplate
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence LeanProofs.ZFCinPA.SizedSchemaLeaves
open LeanProofs.ZFCinPA.SizedCongruence (le_of_add_eq)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : ℕ} {arities : Fin k → ℕ}

/-! ## `tA` of a universal closure -/

theorem tA_allClosure : ∀ (n : ℕ) (φ : Semiproposition (setTemplateLanguage k arities) n),
    tA (∀⁰* φ) = tA φ + 2 * n
  | 0, φ => by simp
  | n + 1, φ => by
      show tA (∀⁰* (∀⁰ φ)) = _
      rw [tA_allClosure n (∀⁰ φ)]
      simp only [tA]
      ring

theorem tA_univCl_eq (q : Proposition (setTemplateLanguage k arities)) :
    tA (Rewriting.emb q.univCl : Proposition (setTemplateLanguage k arities)) =
      tA (OpenTemplateClosure.sourceClosure q) + 2 * (0 + q.fvSup) := by
  rw [FirstOrder.Semiformula.coe_univCl_eq_univCl', FirstOrder.Semiformula.univCl', tA_allClosure]
  rfl

theorem tA_univCl (q : Proposition (setTemplateLanguage k arities)) :
    2 * (0 + q.fvSup) ≤ tA (Rewriting.emb q.univCl : Proposition (setTemplateLanguage k arities)) := by
  rw [tA_univCl_eq]
  omega

/-! ## Every template axiom leaf, bounded -/

/-- The uniform level of a template axiom leaf. -/
def leafW (σ : Sentence (setTemplateLanguage k arities)) (u : V) : V :=
  (tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) * (u + 2) + congL u + 5

theorem leafW_ge (σ : Sentence (setTemplateLanguage k arities)) (u : V) :
    (tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) * (u + 1) + 5 +
        (tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) ≤ leafW σ u :=
  le_of_add_eq (y := congL u) (by unfold leafW; ring)

/-- A lifted ZF axiom requires one bounded axiom rule. -/
theorem lifted_leaf (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u) (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ Theory.lMap (setHom k arities) (𝗭𝗙 : SetTheory)) :
    DLv 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb σ)).val ∅)
      ((tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) * (u + 1) + 5) := by
  have hx := translate_level (Rewriting.emb σ) u Ks hK
  have hw4 : (4 : V) ≤ (tA (Rewriting.emb σ : Proposition _) : V) * (u + 1) + 4 := le_add_self
  refine (DLv.by_axm hw4 ((SeqLt.empty _).insert (lt_lvB_of hx (_root_.add_le_add le_rfl
    (by norm_num)))) (singleton_formulaSet _) (translateFormula Ks (Rewriting.emb σ)).val
    (by simp) ?_).mono (le_of_eq (by ring))
  rcases h with ⟨τ, hτ, rfl⟩
  rw [translateFormula_lMap_set_emb]
  exact (Bootstrapping.Δ₁Class.mem_iff'' (T := (𝗭𝗙 : SetTheory))).mpr hτ

/-- **Every template axiom leaf is bounded.** -/
theorem templ_leaf (harity : ∀ i, arities i ≤ 3) (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ LTemplate.templTheory k arities)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) {u : V} (hu : 2 ≤ u) (hK : ∀ i, (Ks i).val ≤ lvB u) :
    DLv 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb σ)).val ∅) (leafW σ u) := by
  set t : V := (tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) with ht
  have hge := leafW_ge σ u
  rcases templ_lifted_or_congruence σ h with hl | ⟨i, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · -- a lifted `𝗭𝗙` axiom: one `axm` rule
    exact (lifted_leaf Ks hK σ hl).mono (le_trans le_self_add hge)
  · -- placeholder congruence
    rw [SetCongruence.translate_setPlaceholderCongruenceSentence]
    exact (cong_leaf (arities i) (harity i) (Ks i) hu (hK i)).mono
      (le_of_add_eq (y := t * (u + 2) + 5) (by unfold leafW; ring))
  · -- separation
    refine (sep_leaf Ks hKs hK p).mono (le_trans ?_ hge)
    refine _root_.add_le_add le_rfl ?_
    exact_mod_cast tA_univCl (OpenSchemaTemplates.sepBodySource p)
  · -- replacement
    refine (rep_leaf Ks hKs hK p).mono (le_trans ?_ hge)
    refine _root_.add_le_add le_rfl ?_
    exact_mod_cast tA_univCl (OpenSchemaTemplates.repBodySource p)

/-! ## The axiom leaves of a derivation -/

theorem axOK_of {T₁ : Theory (setTemplateLanguage k arities)}
    (P : Sentence (setTemplateLanguage k arities) → Prop) {A : ℕ}
    (hP : ∀ σ, σ ∈ T₁ → tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) ≤ A → P σ) :
    ∀ {Γ : Finset (Proposition (setTemplateLanguage k arities))} (d : T₁ ⟹₂ Γ),
      derMax d ≤ A → AxOK P d := by
  intro Γ d
  induction d <;> intro hA <;> simp only [AxOK] <;> simp only [derMax, max_le_iff] at hA
  case axm σ hσ hΓ => exact hP σ hσ (le_trans (le_seqMax hΓ) hA.1)
  case and _ _ _ ihp ihq => exact ⟨ihp hA.2.1, ihq hA.2.2⟩
  case or _ _ ih => exact ih hA.2
  case all _ _ ih => exact ih hA.2
  case exs _ _ _ ih => exact ih hA.2.2
  case wk _ _ ih => exact ih hA.2
  case shift _ ih => exact ih hA.2
  case cut _ _ ihp ihq => exact ⟨ihp hA.2.1, ihq hA.2.2⟩

/-! ## Bounded compilation -/

/-- The exponent level of the compiler's leaves and sequents. -/
def cExp (A B : ℕ) (u : V) : V :=
  10 * ((A : V) * (u + B + 1) + 1) + 3 + (A : V) * (u + 2) + congL u + 5

/-- The leaf bound `e` fed to `sized_open_compile`. -/
def cE (A B : ℕ) (u : V) : V := lvB (cExp A B u) + 1

/-- **Bounded template compilation over `templTheory`.** A fixed source
derivation of `σ` over the template theory compiles, at shift-fixed
placeholders of arity at most `3` and level `u ≥ 2`, to an internal `𝗭𝗙`
derivation of the translation with code at most
`2^(stg (4·b₀) (stg h (cE A B u)))`. Here `A`, `B`, `b₀` and `h` are
meta-level numbers read off the fixed derivation; `cE` is a double
exponential in `u`. -/
theorem sized_compileT (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (hKs : ∀ i, (Ks i).shift = Ks i) {u : V} (hu : 2 ≤ u) (hK : ∀ i, (Ks i).val ≤ lvB u)
    {σ : Sentence (setTemplateLanguage k arities)}
    (d : LTemplate.templTheory k arities ⟹₂
      ({(Rewriting.emb σ : Proposition (setTemplateLanguage k arities))} : Finset _)) :
    DerivableLe 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb σ)).val ∅)
      (Exp.exp (stg (4 * bufferBound d) (stg (height d)
        (cE (derMax d) (bufferBound d + height d) u)))) := by
  set A := derMax d with hAd
  set B := bufferBound d + height d with hBd
  set E := cExp A B u with hE
  have hX : (A : V) * (u + B + 1) ≤ 10 * ((A : V) * (u + B + 1) + 1) :=
    le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hcanE : 10 * ((A : V) * (u + B + 1) + 1) + 3 ≤ E :=
    le_of_add_eq (y := (A : V) * (u + 2) + congL u + 5) (by rw [hE]; unfold cExp; ring)
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hcanE)
  have he : (4 : V) ≤ cE A B u := le_trans (four_le_lvB hE1) le_self_add
  have hFe : lvB ((A : V) * (u + B + 1)) + 1 ≤ cE A B u :=
    _root_.add_le_add (lvB_mono (le_trans hX (le_trans le_self_add hcanE))) le_rfl
  have hAE : (A : V) ≤ E := by
    refine le_trans ?_ (le_trans hX (le_trans le_self_add hcanE))
    exact le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self
  have hT : lvB (A : V) ≤ Exp.exp (cE A B u) :=
    le_trans (lvB_mono hAE) (le_trans le_self_add (le_of_lt (lt_exp _)))
  have hcan : lvB (10 * ((A : V) * (u + B + 1) + 1) + 3) + 1 ≤ cE A B u :=
    _root_.add_le_add (lvB_mono hcanE) le_rfl
  have hax : AxOK (fun σ' ↦ ∀ b ≤ B, DerivableLe ((𝗭𝗙 : SetTheory).internalize V).theory
      (insert (translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ')).val ∅)
      (Exp.exp (cE A B u))) d := by
    refine axOK_of _ (A := A) ?_ d le_rfl
    intro σ' hσ' htA b _
    rw [shiftedPredicates_fixed Ks hKs b]
    refine DerivableLe.mono (templ_leaf harity σ' hσ' Ks hKs hu hK) (exp_monotone_le.mpr ?_)
    refine le_trans (lvB_mono ?_) le_self_add
    have htA' : (tA (Rewriting.emb σ' : Proposition (setTemplateLanguage k arities)) : V) ≤ A := by
      exact_mod_cast htA
    unfold leafW
    calc (tA (Rewriting.emb σ' : Proposition (setTemplateLanguage k arities)) : V) * (u + 2) + congL u + 5
        ≤ (A : V) * (u + 2) + congL u + 5 :=
          _root_.add_le_add (_root_.add_le_add (mul_le_mul_of_nonneg_right htA' (Arithmetic.zero_le _))
            le_rfl) le_rfl
      _ ≤ E := le_of_add_eq (y := 10 * ((A : V) * (u + B + 1) + 1) + 3) (by rw [hE]; unfold cExp; ring)
  exact sized_open_compile (U := (𝗭𝗙 : SetTheory).internalize V) Ks hK d le_rfl he hFe hT hcan hax

end LeanProofs.ZFCinPA.SizedLTemplate
