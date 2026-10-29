import ZFCinPA.SizedOpenAxiom
import ZFCinPA.SizedLTemplate

/-!
# Template schema leaves at arbitrary placeholders

`SizedSchemaLeaves` bounds the separation/replacement leaves for shift-fixed
placeholders. The `L` inductions also compile templates at placeholders with
free variables (`rel K` in `LSepBase.sep_base`), so this module removes the
premise. The translated sentence `∀^N T` is opened at `&0 … &(N-1)` into an
open schema instance, which `SizedOpenAxiom.open_sep_le`/`open_rep_le`
derive. `strip_gen` then restores the `N` binders. `templ_leaf_gen` and
`sized_compileT_gen` repeat `SizedLTemplate` for arbitrary placeholders.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedOpenTemplateLeaves

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LeanProofs.ZFCinPA.OpenTemplateClosure
open LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedPlaceholderCongruence LeanProofs.ZFCinPA.SizedCongruenceAtoms
open LeanProofs.ZFCinPA.SizedCongruence (le_of_add_eq)
open LeanProofs.ZFCinPA.SizedOpenAxiom

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Stripping `n` binders -/

/-- The member level of the general binder-stripping step. -/
def sβc (c x : V) : V := 10 * (x + 3) + c

theorem strip_gen {c : V} (hc : 1 ≤ c) : ∀ (n : ℕ) (φ : Bootstrapping.Semiformula V ℒₛₑₜ n) (u W : V),
    (∀ j : ℕ, j ≤ n → (^&(j : V) : V) ≤ lvB c) → 2 ≤ u →
    φ.val ≤ lvB u → 4 ≤ W → sβc c (u + 3 * n) + 1 ≤ W →
    DLv 𝗭𝗙 (insert ((shs n φ).subst (fvVec n)).val ∅) W →
    DLv 𝗭𝗙 (insert (∀⁰* φ).val ∅) (W + 2 * n)
  | 0, φ, u, W, _, _, _, _, _, h => by
      simpa [shs, Bootstrapping.Semiformula.subst_nil_eq_self] using h
  | n + 1, φ, u, W, hfv, hu, hφ, hW4, hW, h => by
      have hfv' : ∀ j : ℕ, j ≤ n → (^&(j : V) : V) ≤ lvB c := fun j hj => hfv j (by omega)
      have hent1 : ∀ j, ((fvVec (V := V) (n + 1)) j).val ≤ lvB c := fun j => by
        simpa [fvVec] using hfv j (by omega)
      have hent : ∀ j, ((fvVec (V := V) n) j).val ≤ lvB c := fun j => by
        simpa [fvVec] using hfv' j (by omega)
      set χ := (shs n φ).subst (fvVec n).q
      have hAφ : (∀⁰ φ).val ≤ lvB (u + 2) := by
        have : (∀⁰ φ).val = ^∀ φ.val := by simp
        rw [this]
        exact pair_lvB hu (tag_le_lvB (by norm_num) hu) hφ
      have hcast : ((n + 1 : ℕ) : V) = (n : V) + 1 := by push_cast; rfl
      have hFv : χ.free.val ≤ lvB (sβc c (u + n) + 1) := by
        rw [free_fvVec]
        refine lift_lvB (tsubst_le _ _ (shs_level φ hφ (n + 1)) hc hent1) ?_
        unfold sβc
        rw [hcast]
        exact le_of_add_eq (y := 11) (by ring)
      have hAv : (∀⁰ χ).val ≤ lvB (sβc c (u + n)) := by
        have e : ∀⁰ χ = (shs n (∀⁰ φ)).subst (fvVec n) := by
          rw [shs_all, Bootstrapping.Semiformula.substs_all]
        rw [e]
        refine lift_lvB (tsubst_le _ _ (shs_level _ hAφ n) hc hent) ?_
        unfold sβc
        exact le_of_eq (by ring)
      have hmW : sβc c (u + n) + 1 + 1 ≤ W := by
        refine le_trans ?_ hW
        unfold sβc
        rw [hcast]
        exact le_of_add_eq (y := 20 * (n : V) + 29) (by ring)
      have d1 := all_step hW4 hAv hFv hmW (by rw [free_fvVec]; exact h)
      have e2 : ∀⁰ χ = (shs n (∀⁰ φ)).subst (fvVec n) := by
        rw [shs_all, Bootstrapping.Semiformula.substs_all]
      rw [e2] at d1
      have ih := strip_gen hc n (∀⁰ φ) (u + 2) (W + 1 + 1) hfv' (le_trans hu le_self_add) hAφ
        (le_trans hW4 (le_trans le_self_add le_self_add)) (by
          refine le_trans ?_ (le_trans hW (le_trans le_self_add le_self_add))
          unfold sβc
          rw [hcast]
          exact le_of_add_eq (y := 10) (by ring)) d1
      have e3 : W + 1 + 1 + 2 * (n : V) = W + 2 * ((n + 1 : ℕ) : V) := by rw [hcast]; ring
      rw [e3] at ih
      exact ih

theorem shs_eq_shifts {n : ℕ} (φ : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    ∀ k : ℕ, shs k φ = shifts k φ
  | 0 => rfl
  | k + 1 => by rw [shs_succ, shs_eq_shifts φ k]; rfl

theorem fvVec_eq_freshTuple (n : ℕ) : fvVec (V := V) n = freshTuple (V := V) (L := ℒₛₑₜ) n := rfl

theorem fvar_le_of_le {N : ℕ} : ∀ j : ℕ, j ≤ N → (^&(j : V) : V) ≤ lvB ((N : V) + 4) := by
  intro j hj
  have h2 : (2 : V) ≤ (N : V) + 2 := le_add_self
  have hjN : (j : V) ≤ lvB ((N : V) + 2) :=
    le_trans (by exact_mod_cast hj) (le_trans (le_lvB_self _) (lvB_mono le_self_add))
  have := pair_lvB h2 (show (1 : V) ≤ lvB ((N : V) + 2) from le_trans (by norm_num) (two_le_lvB _)) hjN
  rw [show (N : V) + 2 + 2 = (N : V) + 4 by ring] at this
  show ⟪(1 : V), (j : V)⟫ + 1 ≤ _
  exact this

/-! ## Monotonicity of the level functions -/

theorem spcW_mono {a a' c c' R R' : V} (ha : a ≤ a') (hc : c ≤ c') (hR : R ≤ R') :
    spcW a c R ≤ spcW a' c' R' := by
  unfold spcW
  refine _root_.add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) le_rfl
  exact _root_.add_le_add (_root_.add_le_add (_root_.add_le_add
    (mul_le_mul_of_nonneg_left (_root_.add_le_add ha le_rfl) (by norm_num)) hc)
    (mul_le_mul_of_nonneg_left hR (by norm_num))) le_rfl

theorem openL_mono {u u' : V} (h : u ≤ u') : openL u ≤ openL u' := by
  unfold openL
  exact _root_.add_le_add (_root_.add_le_add
    (mul_le_mul_of_nonneg_left (_root_.add_le_add h le_rfl) (by norm_num)) h) le_rfl

theorem openW_mono {u u' : V} (h : u ≤ u') : openW u ≤ openW u' := by
  unfold openW
  have hl := openL_mono h
  exact _root_.add_le_add (spcW_mono hl (_root_.add_le_add hl le_rfl) (lvB_mono hl))
    (mul_le_mul_of_nonneg_left (lvB_mono hl) (by norm_num))

/-! ## The open schema leaf -/

variable {k : ℕ} {arities : Fin k → ℕ}

/-- The level of a schema leaf with translation constant `t` at level `u`. -/
def oschW (t : ℕ) (u : V) : V :=
  openW (10 * ((t : V) * (u + 1) + t + 1) + t + 4) + sβc ((t : V) + 4) ((t : V) * (u + 1) + 3 * t) +
    1 + 2 * t

theorem tA_univCl_eq (q : Proposition (setTemplateLanguage k arities)) :
    tA (Rewriting.emb q.univCl : Proposition (setTemplateLanguage k arities)) =
      tA (sourceClosure q) + 2 * (0 + q.fvSup) := by
  rw [FirstOrder.Semiformula.coe_univCl_eq_univCl', FirstOrder.Semiformula.univCl',
    SizedLTemplate.tA_allClosure]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The schema leaf at arbitrary placeholders.** -/
theorem oschema_leaf {a : ℕ}
    (src : Semiproposition (setTemplateLanguage k arities) a → Proposition (setTemplateLanguage k arities))
    (body : Bootstrapping.Semiformula V ℒₛₑₜ a → Bootstrapping.Formula V ℒₛₑₜ)
    (htr : ∀ (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) p,
      translateFormula Ks (src p) = body (translateFormula Ks p))
    (hopen : ∀ (K : Bootstrapping.Semiformula V ℒₛₑₜ a) {u : V}, (body K).val ≤ lvB u → 2 ≤ u →
      DLv 𝗭𝗙 (insert (body K).val ∅) (openW u))
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) {u : V} (hu : 2 ≤ u)
    (hK : ∀ i, (Ks i).val ≤ lvB u) (p : Semiproposition (setTemplateLanguage k arities) a) :
    DLv 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb (src p).univCl)).val ∅)
      (oschW (tA (Rewriting.emb (src p).univCl : Proposition (setTemplateLanguage k arities))) u) := by
  set σ := src p with hσ
  set N : ℕ := 0 + σ.fvSup with hNd
  set t : ℕ := tA (Rewriting.emb σ.univCl : Proposition (setTemplateLanguage k arities)) with htd
  set T := translateFormula Ks (sourceClosure σ) with hTd
  have hteq : t = tA (sourceClosure σ) + 2 * N := tA_univCl_eq σ
  have hNt : (N : V) ≤ t := by exact_mod_cast (show N ≤ t by omega)
  have htC : (tA (sourceClosure σ) : V) ≤ t := by exact_mod_cast (show tA (sourceClosure σ) ≤ t by omega)
  have ht2 : (2 : V) ≤ t := by exact_mod_cast two_le_tA (Rewriting.emb σ.univCl : Proposition _)
  have hT : T.val ≤ lvB ((t : V) * (u + 1)) :=
    lift_lvB (translate_level (sourceClosure σ) u Ks hK)
      (mul_le_mul_of_nonneg_right htC (Arithmetic.zero_le _))
  have htu2 : (2 : V) ≤ (t : V) * (u + 1) :=
    le_trans ht2 (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self)
  -- the opening
  have hO : (shs N T).subst (fvVec N) = body (translateFormula (shiftedPredicates Ks N) p) := by
    rw [shs_eq_shifts, fvVec_eq_freshTuple]
    exact (closure_opening Ks σ).trans (htr _ p)
  have hc4 : (1 : V) ≤ (N : V) + 4 := le_trans (by norm_num) le_add_self
  have lO : ((shs N T).subst (fvVec N)).val ≤ lvB (10 * ((t : V) * (u + 1) + N + 1) + (N + 4)) :=
    tsubst_le _ _ (shs_level T hT N) hc4 (fun j => by simpa [fvVec] using fvar_le_of_le j (le_of_lt j.isLt))
  set U : V := 10 * ((t : V) * (u + 1) + t + 1) + t + 4 with hU
  have hlev : 10 * ((t : V) * (u + 1) + N + 1) + (N + 4) ≤ U := by
    calc 10 * ((t : V) * (u + 1) + N + 1) + (N + 4) ≤ 10 * ((t : V) * (u + 1) + t + 1) + (t + 4) :=
          _root_.add_le_add (mul_le_mul_of_nonneg_left (_root_.add_le_add
            (_root_.add_le_add le_rfl hNt) le_rfl) (by norm_num)) (_root_.add_le_add hNt le_rfl)
      _ = U := by rw [hU]; ring
  have hO' : (body (translateFormula (shiftedPredicates Ks N) p)).val ≤
      lvB (10 * ((t : V) * (u + 1) + N + 1) + (N + 4)) := hO ▸ lO
  have hu' : (2 : V) ≤ 10 * ((t : V) * (u + 1) + N + 1) + (N + 4) :=
    le_trans (by norm_num : (2 : V) ≤ 4) (le_trans le_add_self le_add_self)
  have dO := hopen _ hO' hu'
  set W : V := openW U + sβc ((t : V) + 4) ((t : V) * (u + 1) + 3 * t) + 1 with hW
  have hsβ : sβc ((N : V) + 4) ((t : V) * (u + 1) + 3 * N) ≤ sβc ((t : V) + 4) ((t : V) * (u + 1) + 3 * t) := by
    unfold sβc
    exact _root_.add_le_add (mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hNt (by norm_num))) le_rfl) (by norm_num)) (_root_.add_le_add hNt le_rfl)
  have hWs : sβc ((N : V) + 4) ((t : V) * (u + 1) + 3 * N) + 1 ≤ W :=
    le_trans (_root_.add_le_add hsβ le_rfl) (by rw [hW, add_assoc]; exact le_add_self)
  have h4s : (4 : V) ≤ sβc ((N : V) + 4) ((t : V) * (u + 1) + 3 * N) :=
    le_trans (le_add_self : (4 : V) ≤ (N : V) + 4) le_add_self
  have hW4 : (4 : V) ≤ W := le_trans h4s (le_trans le_self_add hWs)
  have hdO : DLv 𝗭𝗙 (insert ((shs N T).subst (fvVec N)).val ∅) W := by
    rw [hO]
    refine dO.mono (le_trans (openW_mono hlev) ?_)
    rw [hW, add_assoc]
    exact le_self_add
  have hstrip := strip_gen hc4 N T ((t : V) * (u + 1)) W (fun j hj => fvar_le_of_le j hj) htu2 hT
    hW4 hWs hdO
  rw [translate_univCl Ks σ]
  have hosch : oschW t u = W + 2 * (t : V) := by rw [hW, hU]; rfl
  rw [hosch]
  exact hstrip.mono (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left hNt (by norm_num)))


/-! ## Every template axiom leaf, at arbitrary placeholders -/

/-- The uniform leaf level at arbitrary placeholders. -/
def leafG (t : ℕ) (u : V) : V := (t : V) * (u + 2) + congL u + 5 + oschW t u

theorem congL_mono {u u' : V} (h : u ≤ u') : congL u ≤ congL u' := by
  have e : congL u' + 1130 * u = congL u + 1130 * u' := by
    unfold congL lW₁ coreL SizedCongruence.cW sW mBig; ring
  have h2 : congL u + 1130 * u ≤ congL u' + 1130 * u := by
    rw [e]; exact _root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h (by norm_num))
  exact (add_le_add_iff_right _).mp h2

theorem oschW_mono {t A : ℕ} {u U : V} (ht : t ≤ A) (hu : u ≤ U) : oschW t u ≤ oschW A U := by
  have htA : (t : V) ≤ A := by exact_mod_cast ht
  have hm : (t : V) * (u + 1) ≤ (A : V) * (U + 1) :=
    mul_le_mul htA (_root_.add_le_add hu le_rfl) (Arithmetic.zero_le _) (Arithmetic.zero_le _)
  unfold oschW sβc
  refine _root_.add_le_add (_root_.add_le_add (_root_.add_le_add (openW_mono ?_) ?_) le_rfl)
    (mul_le_mul_of_nonneg_left htA (by norm_num))
  · exact _root_.add_le_add (_root_.add_le_add (mul_le_mul_of_nonneg_left
      (_root_.add_le_add (_root_.add_le_add hm htA) le_rfl) (by norm_num)) htA) le_rfl
  · exact _root_.add_le_add (mul_le_mul_of_nonneg_left (_root_.add_le_add (_root_.add_le_add hm
      (mul_le_mul_of_nonneg_left htA (by norm_num))) le_rfl) (by norm_num)) (_root_.add_le_add htA le_rfl)

theorem leafG_mono {t A : ℕ} {u U : V} (ht : t ≤ A) (hu : u ≤ U) : leafG t u ≤ leafG A U := by
  have htA : (t : V) ≤ A := by exact_mod_cast ht
  unfold leafG
  exact _root_.add_le_add (_root_.add_le_add (_root_.add_le_add (mul_le_mul htA
    (_root_.add_le_add hu le_rfl) (Arithmetic.zero_le _) (Arithmetic.zero_le _)) (congL_mono hu))
    le_rfl) (oschW_mono ht hu)

/-- **Every template axiom leaf is bounded, at arbitrary placeholders.** -/
theorem templ_leaf_gen (harity : ∀ i, arities i ≤ 3) (σ : Sentence (setTemplateLanguage k arities))
    (h : σ ∈ LTemplate.templTheory k arities)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {u : V} (hu : 2 ≤ u) (hK : ∀ i, (Ks i).val ≤ lvB u) :
    DLv 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb σ)).val ∅)
      (leafG (tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities))) u) := by
  set t : V := (tA (Rewriting.emb σ : Proposition (setTemplateLanguage k arities)) : V) with ht
  have hx := translate_level (Rewriting.emb σ) u Ks hK
  have hge1 : t * (u + 1) + 5 ≤ leafG (tA (Rewriting.emb σ : Proposition _)) u := by
    unfold leafG
    rw [← ht]
    refine le_trans ?_ (le_self_add)
    refine le_trans ?_ (_root_.add_le_add (_root_.add_le_add le_rfl (Arithmetic.zero_le (congL u)))
      le_rfl)
    exact _root_.add_le_add (le_trans (mul_le_mul_of_nonneg_left (_root_.add_le_add le_rfl
      (by norm_num : (1 : V) ≤ 2)) (Arithmetic.zero_le _)) (by simp)) le_rfl
  rcases SizedTemplateAxioms.templ_lifted_or_congruence σ h with hl | ⟨i, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · have hw4 : (4 : V) ≤ t * (u + 1) + 4 := le_add_self
    refine (DLv.by_axm hw4 ((SeqLt.empty _).insert (lt_lvB_of hx (_root_.add_le_add le_rfl
      (by norm_num)))) (SizedTemplateAxioms.singleton_formulaSet _)
      (translateFormula Ks (Rewriting.emb σ)).val (by simp) ?_).mono
      (le_trans (le_of_eq (by ring)) hge1)
    rcases hl with ⟨τ, hτ, rfl⟩
    rw [translateFormula_lMap_set_emb]
    exact (Bootstrapping.Δ₁Class.mem_iff'' (T := (𝗭𝗙 : SetTheory))).mpr hτ
  · rw [SetCongruence.translate_setPlaceholderCongruenceSentence]
    refine (cong_leaf (arities i) (harity i) (Ks i) hu (hK i)).mono ?_
    unfold leafG
    exact le_trans (le_add_self : congL u ≤ _ + congL u)
      (le_trans le_self_add le_self_add)
  · refine (oschema_leaf OpenSchemaTemplates.sepBodySource sepBody
      (fun Ks p => OpenSchemaTemplates.translate_sepBodySource Ks p)
      (fun K _ hK hu => open_sep_le K hK hu) Ks hu hK p).mono ?_
    unfold leafG; exact le_add_self
  · refine (oschema_leaf OpenSchemaTemplates.repBodySource repBody
      (fun Ks p => OpenSchemaTemplates.translate_repBodySource Ks p)
      (fun K _ hK hu => open_rep_le K hK hu) Ks hu hK p).mono ?_
    unfold leafG; exact le_add_self

/-! ## Bounded compilation at arbitrary placeholders -/

/-- The exponent level of the general compiler. -/
def cExpG (A B : ℕ) (u : V) : V := 10 * ((A : V) * (u + B + 1) + 1) + 3 + leafG A (u + B)

/-- The leaf bound `e` of the general compiler. -/
def cEG (A B : ℕ) (u : V) : V := lvB (cExpG A B u) + 1

/-- **Bounded template compilation over `templTheory`, at arbitrary
placeholders** of arity at most `3` and level `u ≥ 2`. -/
theorem sized_compileT_gen (harity : ∀ i, arities i ≤ 3)
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) {u : V} (hu : 2 ≤ u)
    (hK : ∀ i, (Ks i).val ≤ lvB u) {σ : Sentence (setTemplateLanguage k arities)}
    (d : LTemplate.templTheory k arities ⟹₂
      ({(Rewriting.emb σ : Proposition (setTemplateLanguage k arities))} : Finset _)) :
    DerivableLe 𝗭𝗙 (insert (translateFormula Ks (Rewriting.emb σ)).val ∅)
      (Exp.exp (SizedTemplateCompiler.stg (4 * BufferedTemplateProofCompiler.bufferBound d)
        (SizedTemplateCompiler.stg (SizedTemplateCompiler.height d)
          (cEG (SizedOpenTemplate.derMax d)
            (BufferedTemplateProofCompiler.bufferBound d + SizedTemplateCompiler.height d) u)))) := by
  set A := SizedOpenTemplate.derMax d with hAd
  set B := BufferedTemplateProofCompiler.bufferBound d + SizedTemplateCompiler.height d with hBd
  set E := cExpG A B u with hE
  have hX : (A : V) * (u + B + 1) ≤ 10 * ((A : V) * (u + B + 1) + 1) :=
    le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hcanE : 10 * ((A : V) * (u + B + 1) + 1) + 3 ≤ E := by rw [hE]; unfold cExpG; exact le_self_add
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self hcanE)
  have he : (4 : V) ≤ cEG A B u := le_trans (four_le_lvB hE1) le_self_add
  have hFe : lvB ((A : V) * (u + B + 1)) + 1 ≤ cEG A B u :=
    _root_.add_le_add (lvB_mono (le_trans hX (le_trans le_self_add hcanE))) le_rfl
  have hAE : (A : V) ≤ E := by
    refine le_trans ?_ (le_trans hX (le_trans le_self_add hcanE))
    exact le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self
  have hT : lvB (A : V) ≤ Exp.exp (cEG A B u) :=
    le_trans (lvB_mono hAE) (le_trans le_self_add (le_of_lt (lt_exp _)))
  have hcan : lvB (10 * ((A : V) * (u + B + 1) + 1) + 3) + 1 ≤ cEG A B u :=
    _root_.add_le_add (lvB_mono hcanE) le_rfl
  have hax : SizedOpenTemplate.AxOK (fun σ' ↦ ∀ b ≤ B,
      DerivableLe ((𝗭𝗙 : SetTheory).internalize V).theory
        (insert (translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ')).val ∅)
        (Exp.exp (cEG A B u))) d := by
    refine SizedLTemplate.axOK_of _ (A := A) ?_ d le_rfl
    intro σ' hσ' htA b hb
    have hub : (2 : V) ≤ u + b := le_trans hu le_self_add
    refine DerivableLe.mono (templ_leaf_gen harity σ' hσ' (shiftedPredicates Ks b) hub
      (SizedOpenTemplate.shifted_level Ks hK b)) (exp_monotone_le.mpr ?_)
    refine le_trans (lvB_mono ?_) le_self_add
    have hbB : u + (b : V) ≤ u + B := _root_.add_le_add le_rfl (by exact_mod_cast hb)
    exact le_trans (leafG_mono htA hbB) (by unfold cExpG; exact le_add_self)
  exact SizedOpenTemplate.sized_open_compile (U := (𝗭𝗙 : SetTheory).internalize V) Ks hK d le_rfl
    he hFe hT hcan hax

end LeanProofs.ZFCinPA.SizedOpenTemplateLeaves
