import GowersSzemeredi.Sections12_13

/-!
# Extracting the row coefficients in Lemma 13.8

Two distinct columns determine both affine row coefficients over a field.
Their Freiman relations therefore determine the corresponding relations for
the coefficient pair. The application to the paper states explicitly that
the selected points belong to the original domain of the separately Freiman
map. `IsStage137Data` alone does not record this containment.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Translating the input preserves equal-length additive relations. -/
theorem FreimanHom.translate_input {G H : Type*} [AddCommMonoid G]
    [AddCommMonoid H] {k : Nat} {A J : Finset G} {f : G → H}
    (hf : FreimanHom k A f) (y : G) (hJ : ∀ h ∈ J, y + h ∈ A) :
    FreimanHom k J (fun h ↦ f (y + h)) := by
  refine ⟨Set.mapsTo_univ _ _, ?_⟩
  intro s t hsJ htJ hs ht hst
  have hsA : ∀ ⦃x⦄, x ∈ s.map (fun h ↦ y + h) → x ∈ (A : Set G) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hx
    exact hJ h (hsJ hh)
  have htA : ∀ ⦃x⦄, x ∈ t.map (fun h ↦ y + h) → x ∈ (A : Set G) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hx
    exact hJ h (htJ hh)
  have heq : (s.map (fun h ↦ y + h)).sum =
      (t.map (fun h ↦ y + h)).sum := by
    calc
      _ = (s.map (fun _ ↦ y)).sum + s.sum := by
        simpa using (Multiset.sum_map_add (m := s) (f := fun _ ↦ y) (g := id))
      _ = (t.map (fun _ ↦ y)).sum + t.sum := by simp [hs, ht, hst]
      _ = _ := by
        simpa using (Multiset.sum_map_add (m := t) (f := fun _ ↦ y) (g := id)).symm
  have h := hf.map_sum_eq_map_sum hsA htA
    (by simpa using hs) (by simpa using ht) heq
  simpa only [Multiset.map_map, Function.comp_def] using h

/-- Two distinct evaluations of affine functions recover all Freiman
relations of their coefficient pairs. No density hypothesis is needed. -/
theorem FreimanHom.coefficients_of_two_evaluations {G K : Type*}
    [AddCommMonoid G] [Field K] {k : Nat} {J : Finset G} {a c : G → K}
    {x₁ x₂ : K} (hx : x₁ ≠ x₂)
    (h₁ : FreimanHom k J (fun h ↦ a h + c h * x₁))
    (h₂ : FreimanHom k J (fun h ↦ a h + c h * x₂)) :
    FreimanHom k J (fun h ↦ (a h, c h)) := by
  have coeff : ∀ (s t : Multiset G),
      (∀ ⦃x⦄, x ∈ s → x ∈ (J : Set G)) →
      (∀ ⦃x⦄, x ∈ t → x ∈ (J : Set G)) →
      s.card = k → t.card = k → s.sum = t.sum →
      (s.map a).sum = (t.map a).sum ∧ (s.map c).sum = (t.map c).sum := by
    intro s t hsJ htJ hs ht hst
    have e₁ := h₁.map_sum_eq_map_sum hsJ htJ hs ht hst
    have e₂ := h₂.map_sum_eq_map_sum hsJ htJ hs ht hst
    simp only [Multiset.sum_map_add, Multiset.sum_map_mul_right] at e₁ e₂
    have hc : (s.map c).sum = (t.map c).sum := by
      apply mul_right_cancel₀ (sub_ne_zero.mpr hx)
      linear_combination e₁ - e₂
    exact ⟨by rw [hc] at e₁; exact add_right_cancel e₁, hc⟩
  have ha : FreimanHom k J a := ⟨Set.mapsTo_univ _ _,
    fun s t hsJ htJ hs ht hst ↦ (coeff s t hsJ htJ hs ht hst).1⟩
  have hc : FreimanHom k J c := ⟨Set.mapsTo_univ _ _,
    fun s t hsJ htJ hs ht hst ↦ (coeff s t hsJ htJ hs ht hst).2⟩
  simpa only [FreimanHom, Set.univ_prod_univ] using ha.prodMk hc

/-- The algebraic step of Lemma 13.8, with primality and original-domain
containment explicit. The selected columns need only meet the chosen rows. -/
theorem lemma138_coefficients_freiman {N : Nat} [Fact N.Prime]
    (S : Section13Context N) {B : Finset (Pair N)} {J : Finset (ZMod N)}
    {a c : ZMod N → ZMod N} {y x₁ x₂ : ZMod N}
    (hBA : B ⊆ S.A) (hx : x₁ ≠ x₂)
    (h₁ : ∀ h ∈ J, (x₁, y + h) ∈ B)
    (h₂ : ∀ h ∈ J, (x₂, y + h) ∈ B)
    (hrow : ∀ h ∈ J, ∀ x, (x, y + h) ∈ B →
      S.phi (x, y + h) = a h + c h * x) :
    FreimanHom 8 J (fun h ↦ (a h, c h)) := by
  have heval : ∀ x, (∀ h ∈ J, (x, y + h) ∈ B) →
      FreimanHom 8 J (fun h ↦ a h + c h * x) := by
    intro x hcol
    have hf := (S.separately_freiman.1 x).translate_input y
      (J := J) (fun h hh ↦ by
        simpa only [verticalSection, Finset.mem_filter, Finset.mem_univ, true_and]
          using hBA (hcol h hh))
    refine ⟨Set.mapsTo_univ _ _, ?_⟩
    intro s t hsJ htJ hs ht hst
    have es : s.map (fun h ↦ S.phi (x, y + h)) =
        s.map (fun h ↦ a h + c h * x) :=
      Multiset.map_congr rfl (fun h hh ↦ hrow h (hsJ hh) x (hcol h (hsJ hh)))
    have et : t.map (fun h ↦ S.phi (x, y + h)) =
        t.map (fun h ↦ a h + c h * x) :=
      Multiset.map_congr rfl (fun h hh ↦ hrow h (htJ hh) x (hcol h (htJ hh)))
    rw [← es, ← et]
    exact hf.map_sum_eq_map_sum hsJ htJ hs ht hst
  exact FreimanHom.coefficients_of_two_evaluations hx (heval x₁ h₁) (heval x₂ h₂)

end LeanProofs.GowersSzemeredi
