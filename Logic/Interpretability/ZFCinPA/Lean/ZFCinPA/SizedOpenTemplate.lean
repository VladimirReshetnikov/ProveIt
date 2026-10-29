import ZFCinPA.OpenSetTemplateCompiler
import ZFCinPA.SizedShiftCancel
import ZFCinPA.TemplateTranslateLevel

/-!
# Open template compilation with an explicit size bound

`OpenSetTemplateCompiler.compileOpenTemplate` compiles a fixed meta-level
template derivation at internal placeholder formulas `Ks`. This module proves
the bounded counterpart, `sized_open_compile`. In every model of `𝗜𝚺₁`: if the
placeholders have level `u` and the axiom leaves used by the template
derivation have derivations below `2^e`, then the translated conclusion has an
internal derivation with an explicit bound. That bound is a fixed-height tower
in `u` whose constants are meta-level numbers computed from the template
derivation alone, so they are the same in every model.

Ingredients:
* `TemplateTranslateLevel.translate_level` bounds every translated formula of
  every sequent, and `SetCodeLevels.shift_level` the buffered placeholders
  `shiftedPredicates Ks b`;
* `SizedTemplateCompiler.sized_compile` compiles at the buffer `bufferBound d`;
* `SizedShiftCancel.cancelShiftNLe` cancels that buffer.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedOpenTemplate

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.SetCodeLevels
open LeanProofs.ZFCinPA.BufferedTemplateProofCompiler LeanProofs.ZFCinPA.OpenSetTemplateCompiler
open LeanProofs.ZFCinPA.SizedTemplateCompiler LeanProofs.ZFCinPA.SizedShiftCancel
open LeanProofs.ZFCinPA.TemplateTranslateLevel LeanProofs.ZFCinPA.ModelCodedShiftCancellation
open LeanProofs.BoundedPAConsistency.SizedDerivation

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {k : ℕ} {arities : Fin k → ℕ}
variable {T₁ : Theory (setTemplateLanguage k arities)}

/-! ## Meta-level maxima over a fixed derivation -/

theorem le_foldr_max : ∀ (l : List ℕ) {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | [], _, h => absurd h (List.not_mem_nil)
  | a :: l, x, h => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max l h) (le_max_right _ _)

/-- The largest translation constant of a sequent. -/
def seqMax (Γ : Finset (Proposition (setTemplateLanguage k arities))) : ℕ :=
  (Γ.toList.map tA).foldr max 0

theorem le_seqMax {Γ : Finset (Proposition (setTemplateLanguage k arities))} {p}
    (hp : p ∈ Γ) : tA p ≤ seqMax Γ :=
  le_foldr_max _ (List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hp, rfl⟩)

/-- The largest translation constant over all sequents of a derivation. -/
def derMax : {Γ : Finset (Proposition (setTemplateLanguage k arities))} → T₁ ⟹₂ Γ → ℕ
  | Γ, d => max (seqMax Γ) (
    match d with
    | .closed _ _ _ _ => 0
    | .axm _ _ _ => 0
    | .verum _ => 0
    | .and _ d₁ d₂ => max (derMax d₁) (derMax d₂)
    | .or _ d => derMax d
    | .all _ d => derMax d
    | .exs _ t d => max (termA t) (derMax d)
    | .wk d _ => derMax d
    | .shift d => derMax d
    | .cut d₁ d₂ => max (derMax d₁) (derMax d₂))

theorem seqMax_le_derMax {Γ : Finset (Proposition (setTemplateLanguage k arities))}
    (d : T₁ ⟹₂ Γ) : seqMax Γ ≤ derMax d := by
  unfold derMax
  exact le_max_left _ _

/-- Every axiom leaf of `d` satisfies `P`. -/
def AxOK (P : Sentence (setTemplateLanguage k arities) → Prop) :
    {Γ : Finset (Proposition (setTemplateLanguage k arities))} → T₁ ⟹₂ Γ → Prop
  | _, .closed _ _ _ _ => True
  | _, .axm σ _ _ => P σ
  | _, .verum _ => True
  | _, .and _ d₁ d₂ => AxOK P d₁ ∧ AxOK P d₂
  | _, .or _ d => AxOK P d
  | _, .all _ d => AxOK P d
  | _, .exs _ _ d => AxOK P d
  | _, .wk d _ => AxOK P d
  | _, .shift d => AxOK P d
  | _, .cut d₁ d₂ => AxOK P d₁ ∧ AxOK P d₂

/-! ## Buffered placeholders -/

theorem shifted_level (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) {u : V}
    (hK : ∀ i, (Ks i).val ≤ lvB u) : ∀ b : ℕ, ∀ i, (shiftedPredicates Ks b i).val ≤ lvB (u + b)
  | 0, i => by simpa [shiftedPredicates] using hK i
  | b + 1, i => by
      simp only [shiftedPredicates, Semiformula.val_shift]
      have := shift_level (shifted_level Ks hK b i)
      push_cast
      rw [← add_assoc]
      exact this

/-! ## The compiler hypotheses for the open translation -/

variable {U : InternalTheory V ℒₛₑₜ}

theorem good_open (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i)) {u : V}
    (hK : ∀ i, (Ks i).val ≤ lvB u) {e : V} {B A : ℕ} (hT : lvB (A : V) ≤ Exp.exp e) :
    ∀ {Γ : Finset (Proposition (setTemplateLanguage k arities))} (d : T₁ ⟹₂ Γ),
      derMax d ≤ A →
      AxOK (fun σ ↦ ∀ b ≤ B, DerivableLe U.theory
        (insert (translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ)).val ∅) (Exp.exp e)) d →
      Good (openTranslation Ks) U (lvB ((A : V) * (u + B + 1)) + 1) e B d := by
  have here : ∀ (Γ : Finset (Proposition (setTemplateLanguage k arities))),
      seqMax Γ ≤ A → Here (openTranslation Ks) (lvB ((A : V) * (u + B + 1)) + 1) B Γ := by
    intro Γ hΓ b hb p hp
    have hl := translate_level p (u + b) (shiftedPredicates Ks b) (shifted_level Ks hK b)
    refine lt_of_le_of_lt (le_trans hl (lvB_mono ?_)) (lt_add_one _)
    have htA : (tA p : V) ≤ A := cast_le (le_trans (le_seqMax hp) hΓ)
    have hbB : (b : V) ≤ B := cast_le hb
    exact mul_le_mul htA (_root_.add_le_add (_root_.add_le_add le_rfl hbB) le_rfl)
      (Arithmetic.zero_le _) (Arithmetic.zero_le _)
  intro Γ d
  induction d <;> intro hA hax <;>
    simp only [derMax, max_le_iff] at hA <;>
    simp only [AxOK] at hax <;>
    unfold Good
  case closed => exact ⟨here _ hA.1, trivial⟩
  case axm => exact ⟨here _ hA.1, hax⟩
  case verum => exact ⟨here _ hA.1, trivial⟩
  case and _ _ _ ihp ihq => exact ⟨here _ hA.1, ihp hA.2.1 hax.1, ihq hA.2.2 hax.2⟩
  case or _ _ ih => exact ⟨here _ hA.1, ih hA.2 hax⟩
  case all _ _ ih => exact ⟨here _ hA.1, ih hA.2 hax⟩
  case exs _ t _ ih =>
    refine ⟨here _ hA.1, ?_, ih hA.2.2 hax⟩
    exact le_trans (translateTerm_le t) (le_trans (lvB_mono (cast_le hA.2.1)) hT)
  case wk _ _ ih => exact ⟨here _ hA.1, ih hA.2 hax⟩
  case shift _ ih => exact ⟨here _ hA.1, ih hA.2 hax⟩
  case cut _ _ ihp ihq => exact ⟨here _ hA.1, ihp hA.2.1 hax.1, ihq hA.2.2 hax.2⟩

/-! ## The bounded open compiler -/

theorem cancel_bound_level {x L : V} (hL : 2 ≤ L) (hx : x ≤ lvB L) (hxF : IsUFormula ℒₛₑₜ x) :
    CancelBound (L := ℒₛₑₜ) x (lvB (10 * (L + 1) + 3) + 1) := by
  have hLL : L ≤ 10 * (L + 1) := le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _)
    (by norm_num))
  have hall : ^∀ x ≤ lvB (L + 2) := pair_lvB hL (tag_le_lvB (by norm_num) hL) hx
  have hneg := neg_level L x hx hxF
  have hm2 : (2 : V) ≤ 10 * (L + 1) := le_trans hL hLL
  have hex : ^∃ (neg ℒₛₑₜ x) ≤ lvB (10 * (L + 1) + 2) :=
    pair_lvB hm2 (tag_le_lvB (by norm_num) hm2) hneg
  have lt : ∀ {y m : V}, y ≤ lvB m → m ≤ 10 * (L + 1) + 3 → y < lvB (10 * (L + 1) + 3) + 1 :=
    fun hy hm => lt_of_le_of_lt (lift_lvB hy hm) (lt_add_one _)
  exact
    { hp := lt hx (le_trans hLL le_self_add)
      hall := lt hall (by
        rw [show 10 * (L + 1) + 3 = 10 * (L + 1) + 1 + 2 by ring]
        exact _root_.add_le_add (le_trans hLL le_self_add) le_rfl)
      hsh := lt (shift_level hx) (by
        rw [show 10 * (L + 1) + 3 = 10 * (L + 1) + 2 + 1 by ring]
        exact _root_.add_le_add (le_trans hLL le_self_add) le_rfl)
      hshAll := lt (shift_level hall) (by
        rw [show 10 * (L + 1) + 3 = 10 * (L + 1) + 2 + 1 by ring]
        exact _root_.add_le_add (le_trans (_root_.add_le_add hLL le_rfl) le_rfl) le_rfl)
      hex := lt hex (_root_.add_le_add le_rfl (by norm_num))
      hn := lt hneg le_self_add }

/-- **Bounded open template compilation.** A fixed meta-level template
derivation of `σ`, compiled at placeholders of level `u`, has an internal
proof of the translation with code at most `2^(stg (4·b₀) (stg h e))`, where
`b₀ = bufferBound d` and `h = height d` are meta-level numbers. -/
theorem sized_open_compile (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    {u : V} (hK : ∀ i, (Ks i).val ≤ lvB u) {σ : Sentence (setTemplateLanguage k arities)}
    (d : T₁ ⟹₂ ({(Rewriting.emb σ : Proposition (setTemplateLanguage k arities))} : Finset _))
    {e : V} {A : ℕ} (hA : derMax d ≤ A) (he : 4 ≤ e)
    (hFe : lvB ((A : V) * (u + (bufferBound d + height d : ℕ) + 1)) + 1 ≤ e)
    (hT : lvB (A : V) ≤ Exp.exp e)
    (hcan : lvB (10 * ((A : V) * (u + (bufferBound d + height d : ℕ) + 1) + 1) + 3) + 1 ≤ e)
    (hax : AxOK (fun σ ↦ ∀ b ≤ bufferBound d + height d, DerivableLe U.theory
        (insert (translateFormula (shiftedPredicates Ks b) (Rewriting.emb σ)).val ∅) (Exp.exp e)) d) :
    DerivableLe U.theory (insert (translateFormula Ks (Rewriting.emb σ)).val ∅)
      (Exp.exp (stg (4 * bufferBound d) (stg (height d) e))) := by
  set B := bufferBound d + height d with hB
  have hg := good_open (U := U) Ks hK hT d hA hax
  have h1 := sized_compile (openTranslation Ks) he hFe d (bufferBound d) le_rfl le_rfl hg
  rw [translateSequent_singleton, (openTranslation Ks).closed_buffer _ (by simp)] at h1
  simp only [Bootstrapping.Sequent.val_singleton, singleton_eq_insert] at h1
  refine cancelShiftNLe (T := U.theory) (translateFormula Ks (Rewriting.emb σ))
    (four_le_stg he _) (le_trans hcan (le_stg _ e)) (bufferBound d) (fun j hj => ?_) h1
  have htA0 : tA (Rewriting.emb σ) ≤ A :=
    le_trans (le_seqMax (by simp)) (le_trans (seqMax_le_derMax d) hA)
  have hL2 : (2 : V) ≤ (A : V) * (u + B + 1) := by
    have hA2 : 2 ≤ A := le_trans (two_le_tA (Rewriting.emb σ)) htA0
    have h2' : (2 : V) ≤ (A : V) := by
      have := cast_le (V := V) hA2
      simpa using this
    exact le_trans h2' (le_mul_of_one_le_right (Arithmetic.zero_le _) le_add_self)
  have hx : (shiftN j (translateFormula Ks (Rewriting.emb σ))).val ≤ lvB ((A : V) * (u + B + 1)) := by
    have hcb := (openTranslation Ks).closed_buffer (Rewriting.emb σ) (by simp) j
    change translateFormula (shiftedPredicates Ks j) (Rewriting.emb σ) =
      shiftN j (translateFormula Ks (Rewriting.emb σ)) at hcb
    rw [← hcb]
    refine le_trans (translate_level _ (u + j) _ (shifted_level Ks hK j)) (lvB_mono ?_)
    have htA : (tA (Rewriting.emb σ) : V) ≤ A := cast_le htA0
    have hjB : (j : V) ≤ B := cast_le (by omega)
    exact mul_le_mul htA (_root_.add_le_add (_root_.add_le_add le_rfl hjB) le_rfl)
      (Arithmetic.zero_le _) (Arithmetic.zero_le _)
  exact cancel_bound_level hL2 hx (shiftN j _).isSemiformula.isUFormula

end LeanProofs.ZFCinPA.SizedOpenTemplate
