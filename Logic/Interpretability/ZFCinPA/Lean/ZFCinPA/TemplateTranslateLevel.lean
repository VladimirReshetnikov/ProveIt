import ZFCinPA.SetPlaceholders
import ZFCinPA.SetCodeLevels

/-!
# Levels of translated template formulas

For a fixed meta-level template formula `φ` with placeholders, a meta-level
constant `tA φ : ℕ` is computed by recursion on `φ`. In every model of `𝗜𝚺₁`:
if every placeholder formula `Ks i` has level `u` (`(Ks i).val ≤ lvB u`), then

`(translateFormula Ks φ).val ≤ lvB (tA φ · (u + 1))` (`translate_level`).

So translation multiplies levels by a fixed constant of the template. The
placeholder atoms go through `SetCodeLevels.subst_level`; their argument
vectors are translated variables, bounded by the meta constants `termA`/`vecA`.
Negated placeholder atoms additionally go through `neg_level`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.TemplateTranslateLevel

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.SetCodeLevels
open LeanProofs.BoundedPAConsistency.SubstBound

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : ℕ} {arities : Fin k → ℕ}

/-! ## Meta-level constants -/

/-- The level constant of a translated template term. -/
def termA {n : ℕ} : SyntacticSemiterm (setTemplateLanguage k arities) n → ℕ
  | .bvar i => i + 4
  | .fvar x => x + 4
  | .func _ _ => 4

/-- The level constant of a translated term vector. -/
def vecA {n : ℕ} : {ℓ : ℕ} → (Fin ℓ → SyntacticSemiterm (setTemplateLanguage k arities) n) → ℕ
  | 0, _ => 4
  | _ + 1, v => termA (v 0) + vecA (fun j ↦ v j.succ) + 2

/-- The level constant of a translated template formula. -/
def tA : {n : ℕ} → Semiproposition (setTemplateLanguage k arities) n → ℕ
  | _, ⊤ => 4
  | _, ⊥ => 4
  | _, .rel (Sum.inl _) v => vecA v + 10
  | _, .rel (Sum.inr r) v => vecA (fun j ↦ v (Fin.cast r.2 j)) + 10
  | _, .nrel (Sum.inl _) v => vecA v + 10
  | _, .nrel (Sum.inr r) v => 10 * (vecA (fun j ↦ v (Fin.cast r.2 j)) + 11)
  | _, p ⋏ q => tA p + tA q + 4
  | _, p ⋎ q => tA p + tA q + 4
  | _, ∀⁰ p => tA p + 2
  | _, ∃⁰ p => tA p + 2

theorem two_le_termA {n : ℕ} (t : SyntacticSemiterm (setTemplateLanguage k arities) n) :
    2 ≤ termA t := by
  cases t <;> simp [termA]

theorem four_le_vecA {n : ℕ} : ∀ {ℓ : ℕ}
    (v : Fin ℓ → SyntacticSemiterm (setTemplateLanguage k arities) n), 4 ≤ vecA v
  | 0, _ => by simp [vecA]
  | _ + 1, v => by
      have := four_le_vecA (fun j ↦ v j.succ)
      simp only [vecA]
      omega

theorem two_le_tA {n : ℕ} (φ : Semiproposition (setTemplateLanguage k arities) n) : 2 ≤ tA φ := by
  induction φ with
  | verum => simp [tA]
  | falsum => simp [tA]
  | rel r v => rcases r with r | r <;> simp [tA]
  | nrel r v => rcases r with r | r <;> simp [tA] <;> omega
  | and p q => simp [tA]
  | or p q => simp [tA]
  | all p => simp [tA]
  | exs p => simp [tA]

/-! ## Terms and term vectors -/

theorem cast_le {a b : ℕ} (h : a ≤ b) : (a : V) ≤ b := Nat.mono_cast h

theorem var_code_le {t z : V} (ht : t = ⟪0, z⟫ + 1 ∨ t = ⟪1, z⟫ + 1) : t ≤ lvB (z + 4) := by
  have hz2 : (2 : V) ≤ z + 2 := le_add_self
  have h0 : (0 : V) ≤ lvB (z + 2) := Arithmetic.zero_le _
  have h1 : (1 : V) ≤ lvB (z + 2) := le_trans (by norm_num) (four_le_lvB (le_trans (by norm_num) hz2))
  have hz : z ≤ lvB (z + 2) := lift_lvB (le_lvB_self z) le_self_add
  rcases ht with rfl | rfl
  · exact le_trans (pair_lvB hz2 h0 hz) (lvB_mono (le_of_eq (by ring)))
  · exact le_trans (pair_lvB hz2 h1 hz) (lvB_mono (le_of_eq (by ring)))

theorem translateTerm_le {n : ℕ} (t : SyntacticSemiterm (setTemplateLanguage k arities) n) :
    (translateTerm (V := V) t).val ≤ lvB (termA t : V) := by
  cases t with
  | bvar i =>
      simp only [translateTerm, Semiterm.bvar_val, termA]
      push_cast
      exact var_code_le (Or.inl rfl)
  | fvar x =>
      simp only [translateTerm, Semiterm.fvar_val, termA]
      push_cast
      exact var_code_le (Or.inr rfl)
  | func f v => rcases f with f | f <;> exact f.elim

theorem translateVec_le {n : ℕ} : ∀ (ℓ : ℕ)
    (v : Fin ℓ → SyntacticSemiterm (setTemplateLanguage k arities) n),
    SemitermVec.val (fun j ↦ translateTerm (V := V) (v j)) ≤ lvB (vecA v : V)
  | 0, v => by simp
  | ℓ + 1, v => by
      rw [SemitermVec.val_succ]
      have h0 := translateTerm_le (V := V) (v 0)
      have hr := translateVec_le ℓ (fun j ↦ v j.succ)
      have h2 := two_le_termA (v 0)
      have hL2 : (2 : V) ≤ ((termA (v 0) + vecA (fun j ↦ v j.succ) : ℕ) : V) := by
        have h' : (2 : ℕ) ≤ termA (v 0) + vecA (fun j ↦ v j.succ) := le_trans h2 (Nat.le_add_right _ _)
        have := cast_le (V := V) h'
        simpa using this
      have ha : (translateTerm (V := V) (v 0)).val ≤
          lvB ((termA (v 0) + vecA (fun j ↦ v j.succ) : ℕ) : V) :=
        lift_lvB h0 (cast_le (Nat.le_add_right _ _))
      have hb : SemitermVec.val (Matrix.vecTail fun j ↦ translateTerm (V := V) (v j)) ≤
          lvB ((termA (v 0) + vecA (fun j ↦ v j.succ) : ℕ) : V) :=
        lift_lvB hr (cast_le (Nat.le_add_left _ _))
      simp only [adjoin_def]
      refine le_trans (pair_lvB hL2 ha hb) (lvB_mono (le_of_eq ?_))
      simp only [vecA]
      push_cast
      ring

/-! ## Formulas -/

theorem le_mul_succ (x u : V) : x ≤ x * (u + 1) :=
  le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self

theorem isVar_of_term {t : V} (ht : IsUTerm ℒₛₑₜ t) : IsVarTerm t := by
  rcases term_var ht with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact ⟨z, lt_succ_iff_le.mpr (le_pair_right 0 z), Or.inl rfl⟩
  · exact ⟨z, lt_succ_iff_le.mpr (le_pair_right 1 z), Or.inr rfl⟩

/-- A set atom with an argument vector at level `c` has level `c + 6`. -/
theorem setAtom_le {t R w c : V} (hc : 2 ≤ c) (ht : t ≤ 1) (hR : R ≤ 1) (hw : w ≤ lvB c) :
    ⟪t, 2, R, w⟫ + 1 ≤ lvB (c + 6) := by
  have h1 : (1 : V) ≤ lvB c := le_trans (by norm_num) (four_le_lvB (le_trans (by norm_num) hc))
  have s1 := pair_lvB' hc (le_trans hR h1) hw
  have s2 := pair_lvB' (le_trans hc le_self_add) (tag_le_lvB (k := 2) (by norm_num) (le_trans hc le_self_add)) s1
  have s3 := pair_lvB (le_trans hc (le_trans le_self_add le_self_add))
    (lift_lvB (le_trans ht h1) (le_trans le_self_add le_self_add)) s2
  exact le_trans s3 (lvB_mono (le_of_eq (by ring)))

theorem setRel_le {m n : ℕ} (r : (ℒₛₑₜ).Rel m) (w : SemitermVec V ℒₛₑₜ m n) {c : V} (hc : 2 ≤ c)
    (hw : w.val ≤ lvB c) : (Semiformula.rel r w).val ≤ lvB (c + 6) := by
  have hF := (Semiformula.rel r w).isSemiformula.isUFormula
  rw [Semiformula.rel_val] at hF ⊢
  obtain ⟨hk, hR⟩ := isRel_set (IsUFormula.rel.mp hF).1
  rw [hk]
  exact setAtom_le hc (by simp) (by rcases hR with h | h <;> rw [h] <;> simp) hw

theorem setNRel_le {m n : ℕ} (r : (ℒₛₑₜ).Rel m) (w : SemitermVec V ℒₛₑₜ m n) {c : V} (hc : 2 ≤ c)
    (hw : w.val ≤ lvB c) : (Semiformula.nrel r w).val ≤ lvB (c + 6) := by
  have hF := (Semiformula.nrel r w).isSemiformula.isUFormula
  rw [Semiformula.nrel_val] at hF ⊢
  obtain ⟨hk, hR⟩ := isRel_set (IsUFormula.nrel.mp hF).1
  rw [hk]
  exact setAtom_le hc le_rfl (by rcases hR with h | h <;> rw [h] <;> simp) hw

/-- A placeholder atom: substitution of translated variables into `K`. -/
theorem placeholder_le {a n : ℕ} (K : Bootstrapping.Semiformula V ℒₛₑₜ a)
    (w : SemitermVec V ℒₛₑₜ a n) {u c₀ : V} (hc₀ : 1 ≤ c₀) (hK : K.val ≤ lvB u)
    (hw : w.val ≤ lvB c₀) : (K.subst w).val ≤ lvB (10 * (u + 1) + c₀) := by
  rw [Semiformula.val_substs]
  refine subst_level u K.val hK K.isSemiformula.isUFormula c₀ (a : V) (n : V) w.val hc₀
    w.isSemitermVec (fun i _ => le_trans (nth_le _ _) hw) (fun i hi => ?_)
  exact isVar_of_term (w.isUTermVec.2 i hi)

/-- **Translated template formulas multiply levels by `tA φ`.** -/
theorem translate_level : ∀ {n : ℕ} (φ : Semiproposition (setTemplateLanguage k arities) n)
    (u : V) (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)),
    (∀ i, (Ks i).val ≤ lvB u) → (translateFormula Ks φ).val ≤ lvB ((tA φ : V) * (u + 1)) := by
  intro n φ
  induction φ with
  | verum =>
      intro u Ks _
      simp only [translateFormula, Semiformula.val_verum, tA]
      refine le_trans (pair_lvB le_rfl (tag_le_lvB (by norm_num) le_rfl) (Arithmetic.zero_le _))
        (lvB_mono ?_)
      push_cast
      exact le_trans (by norm_num) (le_mul_succ 4 u)
  | falsum =>
      intro u Ks _
      simp only [translateFormula, Semiformula.val_falsum, tA]
      refine le_trans (pair_lvB le_rfl (tag_le_lvB (by norm_num) le_rfl) (Arithmetic.zero_le _))
        (lvB_mono ?_)
      push_cast
      exact le_trans (by norm_num) (le_mul_succ 4 u)
  | rel r v =>
      intro u Ks hK
      rcases r with r | r
      · simp only [translateFormula, tA]
        have hc : (2 : V) ≤ (vecA v : V) := by
          have := cast_le (V := V) (le_trans (by norm_num : 2 ≤ 4) (four_le_vecA v))
          simpa using this
        refine le_trans (setRel_le r _ hc (translateVec_le _ v)) (lvB_mono ?_)
        push_cast
        exact le_trans (_root_.add_le_add le_rfl (by norm_num)) (le_mul_succ _ u)
      · simp only [translateFormula, tA]
        have hc : (1 : V) ≤ (vecA (fun j ↦ v (Fin.cast r.2 j)) : V) := by
          have := cast_le (V := V) (le_trans (by norm_num : 1 ≤ 4) (four_le_vecA (fun j ↦ v (Fin.cast r.2 j))))
          simpa using this
        refine le_trans (placeholder_le (Ks r.1) _ hc (hK r.1) (translateVec_le _ _)) (lvB_mono ?_)
        push_cast
        calc 10 * (u + 1) + (vecA (fun j ↦ v (Fin.cast r.2 j)) : V)
            ≤ 10 * (u + 1) + (vecA (fun j ↦ v (Fin.cast r.2 j)) : V) * (u + 1) :=
              _root_.add_le_add le_rfl (le_mul_succ _ u)
          _ = ((vecA (fun j ↦ v (Fin.cast r.2 j)) : V) + 10) * (u + 1) := by ring
  | nrel r v =>
      intro u Ks hK
      rcases r with r | r
      · simp only [translateFormula, tA]
        have hc : (2 : V) ≤ (vecA v : V) := by
          have := cast_le (V := V) (le_trans (by norm_num : 2 ≤ 4) (four_le_vecA v))
          simpa using this
        refine le_trans (setNRel_le r _ hc (translateVec_le _ v)) (lvB_mono ?_)
        push_cast
        exact le_trans (_root_.add_le_add le_rfl (by norm_num)) (le_mul_succ _ u)
      · simp only [translateFormula, tA, Semiformula.val_neg]
        have hc : (1 : V) ≤ (vecA (fun j ↦ v (Fin.cast r.2 j)) : V) := by
          have := cast_le (V := V) (le_trans (by norm_num : 1 ≤ 4) (four_le_vecA (fun j ↦ v (Fin.cast r.2 j))))
          simpa using this
        have hS := placeholder_le (Ks r.1) (fun j ↦ translateTerm (v (Fin.cast r.2 j))) hc (hK r.1)
          (translateVec_le _ _)
        have hN := neg_level _ _ hS ((Ks r.1).subst _).isSemiformula.isUFormula
        refine le_trans hN (lvB_mono ?_)
        push_cast
        set c := (vecA (fun j ↦ v (Fin.cast r.2 j)) : V)
        calc 10 * (10 * (u + 1) + c + 1) = 100 * (u + 1) + (10 * c + 10) := by ring
          _ ≤ 100 * (u + 1) + (10 * c + 10) * (u + 1) := _root_.add_le_add le_rfl (le_mul_succ _ u)
          _ = 10 * (c + 11) * (u + 1) := by ring
  | and p q ihp ihq =>
      intro u Ks hK
      simp only [translateFormula, Semiformula.val_and, tA]
      have hp := ihp u Ks hK
      have hq := ihq u Ks hK
      have hL : (2 : V) ≤ ((tA p : V) + tA q) * (u + 1) := by
        have h2 := cast_le (V := V) (two_le_tA p)
        simp only [Nat.cast_ofNat] at h2
        exact le_trans (le_trans h2 le_self_add) (le_mul_succ _ u)
      have ap := lift_lvB hp (mul_le_mul_of_nonneg_right (le_self_add : (tA p : V) ≤ tA p + tA q) (Arithmetic.zero_le (u + 1)))
      have aq := lift_lvB hq (mul_le_mul_of_nonneg_right (le_add_self : (tA q : V) ≤ tA p + tA q) (Arithmetic.zero_le (u + 1)))
      refine le_trans (pair_lvB (le_trans hL le_self_add)
        (tag_le_lvB (by norm_num) (le_trans hL le_self_add)) (pair_lvB' hL ap aq)) (lvB_mono ?_)
      push_cast
      calc ((tA p : V) + tA q) * (u + 1) + 2 + 2 = ((tA p : V) + tA q) * (u + 1) + 4 := by ring
        _ ≤ ((tA p : V) + tA q) * (u + 1) + 4 * (u + 1) := _root_.add_le_add le_rfl (le_mul_succ _ u)
        _ = ((tA p : V) + tA q + 4) * (u + 1) := by ring
  | or p q ihp ihq =>
      intro u Ks hK
      simp only [translateFormula, Semiformula.val_or, tA]
      have hp := ihp u Ks hK
      have hq := ihq u Ks hK
      have hL : (2 : V) ≤ ((tA p : V) + tA q) * (u + 1) := by
        have h2 := cast_le (V := V) (two_le_tA p)
        simp only [Nat.cast_ofNat] at h2
        exact le_trans (le_trans h2 le_self_add) (le_mul_succ _ u)
      have ap := lift_lvB hp (mul_le_mul_of_nonneg_right (le_self_add : (tA p : V) ≤ tA p + tA q) (Arithmetic.zero_le (u + 1)))
      have aq := lift_lvB hq (mul_le_mul_of_nonneg_right (le_add_self : (tA q : V) ≤ tA p + tA q) (Arithmetic.zero_le (u + 1)))
      refine le_trans (pair_lvB (le_trans hL le_self_add)
        (tag_le_lvB (by norm_num) (le_trans hL le_self_add)) (pair_lvB' hL ap aq)) (lvB_mono ?_)
      push_cast
      calc ((tA p : V) + tA q) * (u + 1) + 2 + 2 = ((tA p : V) + tA q) * (u + 1) + 4 := by ring
        _ ≤ ((tA p : V) + tA q) * (u + 1) + 4 * (u + 1) := _root_.add_le_add le_rfl (le_mul_succ _ u)
        _ = ((tA p : V) + tA q + 4) * (u + 1) := by ring
  | all p ih =>
      intro u Ks hK
      simp only [translateFormula, Semiformula.val_all, tA]
      have hp := ih u Ks hK
      have hL : (2 : V) ≤ (tA p : V) * (u + 1) := by
        have h2 := cast_le (V := V) (two_le_tA p)
        simp only [Nat.cast_ofNat] at h2
        exact le_trans h2 (le_mul_succ _ u)
      refine le_trans (pair_lvB hL (tag_le_lvB (by norm_num) hL) hp) (lvB_mono ?_)
      push_cast
      calc (tA p : V) * (u + 1) + 2 ≤ (tA p : V) * (u + 1) + 2 * (u + 1) :=
            _root_.add_le_add le_rfl (le_mul_succ _ u)
        _ = ((tA p : V) + 2) * (u + 1) := by ring
  | exs p ih =>
      intro u Ks hK
      simp only [translateFormula, Semiformula.val_exs, tA]
      have hp := ih u Ks hK
      have hL : (2 : V) ≤ (tA p : V) * (u + 1) := by
        have h2 := cast_le (V := V) (two_le_tA p)
        simp only [Nat.cast_ofNat] at h2
        exact le_trans h2 (le_mul_succ _ u)
      refine le_trans (pair_lvB hL (tag_le_lvB (by norm_num) hL) hp) (lvB_mono ?_)
      push_cast
      calc (tA p : V) * (u + 1) + 2 ≤ (tA p : V) * (u + 1) + 2 * (u + 1) :=
            _root_.add_le_add le_rfl (le_mul_succ _ u)
        _ = ((tA p : V) + 2) * (u + 1) := by ring

end LeanProofs.ZFCinPA.TemplateTranslateLevel
