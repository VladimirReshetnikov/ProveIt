import OAI.Combinatorics.Progressions.Lattices.NormalizedIntegerDual

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

def integerFormMassBound (n : ℕ) (H D A B : ℝ) : ℝ := A * (2 + H) + ((n : ℝ) * D + 1) * B

theorem scaledFrameForm_mass {α K : Type*} [Fintype α]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ) {H D A B : ℝ}
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (ha : |(a : ℝ)| ≤ A) (hn : ∀ i, realPolynomialMass (map (Int.castRingHom ℝ) (numerator i)) ≤ B)
    (f : Form α K) :
    realPolynomialMass (map (Int.castRingHom ℝ) (scaledFrameForm root difference a numerator f)) ≤
      integerFormMassBound (Fintype.card α) H D A B := by
  have hcross : 0 ≤ (Fintype.card α : ℝ) * D * B := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) hB
  have hax : realPolynomialMass (C (a : ℝ) * X (none : Option K)) ≤ A := by
    exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using ha)
  have hbase (k : K) : realPolynomialMass (X (some k) - C (root k : ℝ) * X (none : Option K)) ≤ 1 + H := by
    have hr : realPolynomialMass (C (root k : ℝ) * X (none : Option K)) ≤ H := by
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using hroot k)
    exact (realPolynomialMass_sub_le _ _).trans (by rw [realPolynomialMass_X]; linarith)
  cases f with
  | coordinate v =>
    cases v with
    | none =>
      simp only [scaledFrameForm, map_mul, map_C, map_X, Int.coe_castRingHom]
      exact hax.trans (by unfold integerFormMassBound; nlinarith)
    | some v =>
      cases v with
      | inl i =>
        exact (hn i).trans (by unfold integerFormMassBound; nlinarith)
      | inr k =>
        have hp : realPolynomialMass (C (a : ℝ) * (X (some k) - C (root k : ℝ) * X none)) ≤ A * (1 + H) :=
          (realPolynomialMass_C_mul_le _ _).trans
            (mul_le_mul ha (hbase k) (realPolynomialMass_nonneg _) hA)
        have hs : realPolynomialMass (∑ i, C (difference i k : ℝ) * map (Int.castRingHom ℝ) (numerator i)) ≤
            (Fintype.card α : ℝ) * (D * B) := by
          apply (realPolynomialMass_sum_le _ _).trans
          calc
            _ ≤ ∑ _i : α, D * B := by
              apply Finset.sum_le_sum
              intro i _
              exact (realPolynomialMass_C_mul_le _ _).trans
                (mul_le_mul (hdiff i k) (hn i) (realPolynomialMass_nonneg _) hD)
            _ = _ := by simp
        simp only [scaledFrameForm, map_sub, map_mul, map_sum, map_C, map_X, Int.coe_castRingHom]
        apply (realPolynomialMass_sub_le _ _).trans
        unfold integerFormMassBound
        nlinarith
  | difference i =>
    simp only [scaledFrameForm, map_sub, map_mul, map_C, map_X, Int.coe_castRingHom]
    apply (realPolynomialMass_sub_le _ _).trans
    have hi := hn i
    unfold integerFormMassBound
    nlinarith

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

theorem exists_affine_vanishing_labels {α K R V : Type*} [Fintype α] [DecidableEq α]
    [CommRing R] [AddCommGroup V] [Module R V]
    (root : K → R) (difference : α → K → R) (q : α → MvPolynomial (Option K) R)
    (hdual : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (Λ : MvPolynomial (Option K) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (fun s => eval (affineSite root difference s) P)) :
    ∃ l : List (Form α K), l.length = h ∧
      (∀ s, eval (affineSite root difference s) (frameProjection root difference q (formProduct l)) = 0) ∧
      Λ (frameProjection root difference q (formProduct l)) ≠ 0 := by
  let E := frameProjection root difference q
  let Λ' := Λ.comp E.toLinearMap
  have hn : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ' P = L (siteEvaluation P) := by
    rintro ⟨L, hL⟩
    apply hnonfactor
    refine ⟨L, ?_⟩
    intro P hP
    have he := hL (frameLift root difference P) (frameLift_homogeneous root difference hP)
    change Λ (frameProjection root difference q (frameLift root difference P)) = _ at he
    rw [frameProjection_lift, frameLift_siteEvaluation root difference q hdual] at he
    exact he
  obtain ⟨l, hl, hz, hΛ⟩ := exists_vanishing_product_of_nonfactor Λ' h hn
  refine ⟨l, hl, ?_, hΛ⟩
  intro s
  exact (frameProjection_eval root difference q hdual s (formProduct l)).trans (hz s)

theorem exists_integer_vanishing_product {α K V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hlinear : ∀ i, (numerator i).IsHomogeneous 1)
    (hdual : ∀ i s, eval (affineSite root difference s) (numerator i) = if i ∈ s then a else 0)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P =
        L (fun s => eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) P)) :
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧ ∃ f : Form α K, P = scaledFrameForm root difference a numerator f) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      Λ (map (Int.castRingHom ℝ) forms.prod) ≠ 0 := by
  let q := normalizedIntegerDual a numerator
  obtain ⟨l, hl, hz, hΛ⟩ := exists_affine_vanishing_labels
    (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) q
    (normalizedIntegerDual_boolean root difference a ha numerator hdual) Λ h hnonfactor
  have hm := scaledFrameProduct_map (Int.castRingHom ℝ) root difference a numerator q
    (normalizedIntegerDual_clear a ha numerator) l
  simp only [Int.coe_castRingHom] at hm
  let forms := l.map (scaledFrameForm root difference a numerator)
  have hzero (s : Finset α) : eval (affineSite root difference s) forms.prod = 0 := by
    have he := affineSite_eval_map (Int.castRingHom ℝ) root difference s forms.prod
    simp only [Int.coe_castRingHom] at he
    have hc : ((eval (affineSite root difference s) forms.prod : ℤ) : ℝ) = 0 := by
      rw [← he]
      change eval _ (map (Int.castRingHom ℝ) ((l.map (scaledFrameForm root difference a numerator)).prod)) = 0
      rw [hm, map_mul, eval_C, hz, mul_zero]
    exact_mod_cast hc
  refine ⟨forms, ?_, ?_, ?_, ?_⟩
  · simpa only [forms, List.length_map] using hl
  · intro P hP
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hP
    exact ⟨scaledFrameForm_homogeneous root difference a numerator hlinear f, f, rfl⟩
  · intro s
    have hp : (forms.map (fun P => eval (affineSite root difference s) P)).prod = 0 := by
      simpa only [map_list_prod] using hzero s
    exact List.mem_map.mp (List.prod_eq_zero_iff.mp hp)
  · change Λ (map (Int.castRingHom ℝ) ((l.map (scaledFrameForm root difference a numerator)).prod)) ≠ 0
    rw [hm, ← smul_eq_C_mul, map_smul]
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    exact smul_ne_zero (pow_ne_zero _ ha') hΛ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

theorem exists_bounded_integer_vanishing_product {α K V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P =
        L (fun s => eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) P)) :
    let A := ((Fintype.card α).factorial : ℝ) * D ^ Fintype.card α
    let B := (Fintype.card α : ℝ) *
      ((((Fintype.card α).factorial : ℝ) * D ^ (Fintype.card α - 1)) * (1 + H))
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) P) ≤ integerFormMassBound (Fintype.card α) H D A B) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      Λ (map (Int.castRingHom ℝ) forms.prod) ≠ 0 := by
  intro A B
  let a := (integerDifferencePivot difference selection).det
  let numerator := integerPivotNumerator root difference selection
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_integer_vanishing_product root difference a hdet numerator
    (integerPivotNumerator_homogeneous root difference selection)
    (integerPivotNumerator_eval root difference selection) Λ h hnonfactor
  refine ⟨forms, hlen, ?_, hz, hΛ⟩
  intro P hP
  obtain ⟨hhom, f, rfl⟩ := hforms P hP
  refine ⟨hhom, scaledFrameForm_mass root difference a numerator hH hD
    (show 0 ≤ A by dsimp [A]; positivity) (show 0 ≤ B by dsimp [B]; positivity) hroot hdiff ?_ ?_ f⟩
  · exact integerDifferencePivot_det_bound difference selection (fun i j => hdiff i (selection j))
  · intro i
    exact integerPivotNumerator_mass root difference selection hD
      (fun j => hroot (selection j)) (fun i j => hdiff i (selection j)) i

end Erdos3.BooleanCubeKernel

end

end OAI
