import OAI.Combinatorics.Progressions.Linear.BooleanCubeCoordinateFrame
import OAI.Combinatorics.Progressions.Linear.RealKernelJetInverse

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

variable {α K R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

omit [DecidableEq α] in
theorem frameProjection_form_homogeneous (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) (hq : ∀ i, (q i).IsHomogeneous 1) (f : Form α K) :
    (frameProjection root difference q (formPolynomial f)).IsHomogeneous 1 := by
  cases f with
  | coordinate v =>
    simpa only [frameProjection, formPolynomial, aeval_X] using
      frameCoordinate_homogeneous root difference q hq v
  | difference i =>
    simpa only [frameProjection, formPolynomial, map_sub, aeval_X, frameCoordinate] using
      (hq i).sub (isHomogeneous_X R none)

theorem frameLift_siteEvaluation (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (P : MvPolynomial (Option K) R) :
    siteEvaluation (frameLift root difference P) = fun s => eval (affineSite root difference s) P := by
  funext s
  change eval (site s) (frameLift root difference P) = _
  rw [← frameProjection_eval root difference q hq, frameProjection_lift]

theorem exists_affine_vanishing_product
    (root : K → R) (difference : α → K → R) (q : α → MvPolynomial (Option K) R)
    (hlinear : ∀ i, (q i).IsHomogeneous 1)
    (hdual : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (Λ : MvPolynomial (Option K) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (fun s => eval (affineSite root difference s) P)) :
    ∃ forms : List (MvPolynomial (Option K) R), forms.length = h ∧
      (∀ Q ∈ forms, Q.IsHomogeneous 1 ∧ ∃ f : Form α K,
        Q = frameProjection root difference q (formPolynomial f)) ∧
      (∀ s : Finset α, eval (affineSite root difference s) forms.prod = 0) ∧ Λ forms.prod ≠ 0 := by
  let E := frameProjection root difference q
  let Λ' := Λ.comp E.toLinearMap
  have hnonfactor' : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ' P = L (siteEvaluation P) := by
    rintro ⟨L, hL⟩
    apply hnonfactor
    refine ⟨L, ?_⟩
    intro P hP
    have he := hL (frameLift root difference P) (frameLift_homogeneous root difference hP)
    change Λ (frameProjection root difference q (frameLift root difference P)) = _ at he
    rw [frameProjection_lift, frameLift_siteEvaluation root difference q hdual] at he
    exact he
  obtain ⟨l, hl, hz, hΛ⟩ := exists_vanishing_product_of_nonfactor Λ' h hnonfactor'
  have hprod : (l.map (fun f => E (formPolynomial f))).prod = E (formProduct l) := by
    simp only [formProduct, map_list_prod, List.map_map, Function.comp_def]
  refine ⟨l.map (fun f => E (formPolynomial f)), ?_, ?_, ?_, ?_⟩
  · simpa only [List.length_map] using hl
  · intro Q hQ
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hQ
    exact ⟨frameProjection_form_homogeneous root difference q hlinear f, f, rfl⟩
  · intro s
    rw [hprod]
    exact (frameProjection_eval root difference q hdual s (formProduct l)).trans (hz s)
  · rw [hprod]
    exact hΛ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators

noncomputable def homogeneousDual {I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (selection : I → K) (n : I → R) : MvPolynomial (Option K) R :=
  ∑ j, C (n j) * (X (some (selection j)) - C (root (selection j)) * X none)

theorem homogeneousDual_homogeneous {I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (selection : I → K) (n : I → R) :
    (homogeneousDual root selection n).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ (fun j _ =>
    ((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root (selection j)))).C_mul (n j))

theorem homogeneousDual_eval {α I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (difference : α → K → R) (selection : I → K) (n : I → R)
    (s : Finset α) :
    eval (affineSite root difference s) (homogeneousDual root selection n) =
      ∑ i ∈ s, ∑ j, n j * difference i (selection j) := by
  simp only [homogeneousDual, map_sum, map_mul, map_sub, eval_C, eval_X,
    affineSite, mul_one, add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_comm

theorem homogeneousDual_boolean {α I K R : Type*} [DecidableEq α] [Fintype I] [CommRing R]
    (root : K → R) (difference : α → K → R) (selection : I → K) (n : α → I → R)
    (hdual : ∀ i r, (∑ j, n i j * difference r (selection j)) = if i = r then 1 else 0)
    (i : α) (s : Finset α) :
    eval (affineSite root difference s) (homogeneousDual root selection (n i)) =
      if i ∈ s then 1 else 0 := by
  rw [homogeneousDual_eval]
  simp only [hdual, Finset.sum_ite_eq]

noncomputable def pivotDual {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K) (i : α) :
    MvPolynomial (Option K) ℝ :=
  homogeneousDual root selection (fun j => (realDifferencePivot difference selection)⁻¹ j i)

theorem pivotDual_boolean {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (hd : (realDifferencePivot difference selection).det ≠ 0) (i : α) (s : Finset α) :
    eval (affineSite root difference s) (pivotDual root difference selection i) = if i ∈ s then 1 else 0 :=
  homogeneousDual_boolean root difference selection _
    (realDifferencePivot_inverse_dual difference selection hd) i s

theorem pivotDual_homogeneous {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K) (i : α) :
    (pivotDual root difference selection i).IsHomogeneous 1 :=
  homogeneousDual_homogeneous root selection _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

theorem homogeneousDual_mass {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) {H N : ℝ}
    (hN : 0 ≤ N) (hroot : ∀ j, |root (selection j)| ≤ H) (hn : ∀ j, |n j| ≤ N) :
    realPolynomialMass (homogeneousDual root selection n) ≤ (Fintype.card I : ℝ) * (N * (1 + H)) := by
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : I, N * (1 + H) := by
      apply Finset.sum_le_sum
      intro j _
      have hr : realPolynomialMass (C (root (selection j)) * X (none : Option K)) ≤ H := by
        exact (realPolynomialMass_C_mul_le (root (selection j)) (X (none : Option K))).trans
            (by simpa only [realPolynomialMass_X, mul_one] using hroot j)
      have hs : realPolynomialMass (X (some (selection j)) - C (root (selection j)) * X none) ≤ 1 + H := by
        exact (realPolynomialMass_sub_le _ _).trans (by rw [realPolynomialMass_X]; linarith)
      exact (realPolynomialMass_C_mul_le _ _).trans
        (mul_le_mul (hn j) hs (realPolynomialMass_nonneg _) hN)
    _ = _ := by simp

def formMassBound (q : ℕ) (H D Q : ℝ) : ℝ := 2 + H + ((q : ℝ) * D + 1) * Q

theorem frameCoordinate_mass {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ) (q : α → MvPolynomial (Option K) ℝ)
    {H D Q : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hroot : ∀ k, |root k| ≤ H) (hdiff : ∀ i k, |difference i k| ≤ D)
    (hq : ∀ i, realPolynomialMass (q i) ≤ Q) (v : Variable α K) :
    realPolynomialMass (frameCoordinate root difference q v) ≤ formMassBound (Fintype.card α) H D Q := by
  have hnonneg : 0 ≤ (Fintype.card α : ℝ) * D * Q := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) hQ
  cases v with
  | none =>
    simp only [frameCoordinate, realPolynomialMass_X, formMassBound]
    nlinarith
  | some v =>
    cases v with
    | inl i =>
      apply (hq i).trans
      unfold formMassBound
      nlinarith
    | inr k =>
      have hr : realPolynomialMass (C (root k) * X (none : Option K)) ≤ H := by
        exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using hroot k)
      have hs : realPolynomialMass (∑ i, C (difference i k) * q i) ≤ (Fintype.card α : ℝ) * (D * Q) := by
        apply (realPolynomialMass_sum_le _ _).trans
        calc
          _ ≤ ∑ _i : α, D * Q := by
            apply Finset.sum_le_sum
            intro i _
            exact (realPolynomialMass_C_mul_le _ _).trans
              (mul_le_mul (hdiff i k) (hq i) (realPolynomialMass_nonneg _) hD)
          _ = _ := by simp
      have ht := realPolynomialMass_sub_le
        (X (some k) - C (root k) * X none) (∑ i, C (difference i k) * q i)
      have hu := realPolynomialMass_sub_le (X (some k)) (C (root k) * X none)
      rw [realPolynomialMass_X] at hu
      change realPolynomialMass (X (some k) - C (root k) * X none - ∑ i, C (difference i k) * q i) ≤ _
      unfold formMassBound
      nlinarith

theorem frameProjection_form_mass {α K : Type*} [Fintype α]
    (root : K → ℝ) (difference : α → K → ℝ) (q : α → MvPolynomial (Option K) ℝ)
    {H D Q : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hroot : ∀ k, |root k| ≤ H) (hdiff : ∀ i k, |difference i k| ≤ D)
    (hq : ∀ i, realPolynomialMass (q i) ≤ Q) (f : Form α K) :
    realPolynomialMass (frameProjection root difference q (formPolynomial f)) ≤
      formMassBound (Fintype.card α) H D Q := by
  cases f with
  | coordinate v =>
    simpa only [frameProjection, formPolynomial, aeval_X] using
      frameCoordinate_mass root difference q hH hD hQ hroot hdiff hq v
  | difference i =>
    simp only [frameProjection, formPolynomial, map_sub, aeval_X, frameCoordinate]
    have hs := realPolynomialMass_sub_le (q i) (X (none : Option K))
    rw [realPolynomialMass_X] at hs
    have hnonneg : 0 ≤ (Fintype.card α : ℝ) * D * Q := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) hQ
    have hi := hq i
    unfold formMassBound
    nlinarith

theorem pivotDual_mass {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    {H D κ : ℝ} (hD : 0 ≤ D) (hκ : 0 < κ)
    (hroot : ∀ j, |root (selection j)| ≤ H) (hdiff : ∀ i j, |difference i (selection j)| ≤ D)
    (hdet : κ ≤ |(realDifferencePivot difference selection).det|) (i : α) :
    realPolynomialMass (pivotDual root difference selection i) ≤
      (Fintype.card α : ℝ) *
        ((((Fintype.card α).factorial : ℝ) * D ^ (Fintype.card α - 1) / κ) * (1 + H)) := by
  apply homogeneousDual_mass root selection _ (by positivity) hroot
  intro j
  exact matrix_inverse_entry_abs_le (realDifferencePivot difference selection) hdiff hκ hdet j i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

noncomputable def scaledFrameForm {α K R : Type*} [Fintype α] [CommRing R]
    (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) : Form α K → MvPolynomial (Option K) R
  | .coordinate none => C a * X none
  | .coordinate (some (.inl i)) => numerator i
  | .coordinate (some (.inr k)) =>
      C a * (X (some k) - C (root k) * X none) - ∑ i, C (difference i k) * numerator i
  | .difference i => numerator i - C a * X none

theorem scaledFrameForm_homogeneous {α K R : Type*} [Fintype α] [CommRing R]
    (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R)
    (hn : ∀ i, (numerator i).IsHomogeneous 1) (f : Form α K) :
    (scaledFrameForm root difference a numerator f).IsHomogeneous 1 := by
  cases f with
  | coordinate v =>
    cases v with
    | none => exact (isHomogeneous_X R _).C_mul a
    | some v =>
      cases v with
      | inl i => exact hn i
      | inr k =>
        apply (((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root k))).C_mul a).sub
        exact IsHomogeneous.sum _ _ _ (fun i _ => (hn i).C_mul (difference i k))
  | difference i => exact (hn i).sub ((isHomogeneous_X R _).C_mul a)

theorem scaledFrameForm_map {α K R S : Type*} [Fintype α] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) (q : α → MvPolynomial (Option K) S)
    (hn : ∀ i, map ρ (numerator i) = C (ρ a) * q i) (f : Form α K) :
    map ρ (scaledFrameForm root difference a numerator f) =
      C (ρ a) * frameProjection (fun k => ρ (root k)) (fun i k => ρ (difference i k)) q (formPolynomial f) := by
  cases f with
  | coordinate v =>
    cases v with
    | none => simp [scaledFrameForm, frameProjection, formPolynomial, frameCoordinate]
    | some v =>
      cases v with
      | inl i => simpa only [scaledFrameForm, frameProjection, formPolynomial, aeval_X, frameCoordinate] using hn i
      | inr k =>
        have hs : (∑ i, C (ρ (difference i k)) * (C (ρ a) * q i)) =
            C (ρ a) * ∑ i, C (ρ (difference i k)) * q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        simp only [scaledFrameForm, map_sub, map_mul, map_sum, map_C, map_X, hn,
          frameProjection, formPolynomial, aeval_X, frameCoordinate]
        rw [hs]
        ring
  | difference i =>
    simp only [scaledFrameForm, map_sub, map_mul, map_C, map_X, hn,
      frameProjection, formPolynomial, aeval_X, frameCoordinate]
    ring

theorem affineSite_map {α K R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (s : Finset α) :
    affineSite (fun k => ρ (root k)) (fun i k => ρ (difference i k)) s = ρ ∘ affineSite root difference s := by
  funext v
  cases v <;> simp [affineSite]

theorem affineSite_eval_map {α K R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (s : Finset α)
    (P : MvPolynomial (Option K) R) :
    eval (affineSite (fun k => ρ (root k)) (fun i k => ρ (difference i k)) s) (map ρ P) =
      ρ (eval (affineSite root difference s) P) := by
  rw [affineSite_map]
  exact (map_eval ρ _ P).symm

theorem scaledFrameProduct_map {α K R S : Type*} [Fintype α] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) (q : α → MvPolynomial (Option K) S)
    (hn : ∀ i, map ρ (numerator i) = C (ρ a) * q i) (l : List (Form α K)) :
    map ρ ((l.map (scaledFrameForm root difference a numerator)).prod) =
      C ((ρ a) ^ l.length) *
        frameProjection (fun k => ρ (root k)) (fun i k => ρ (difference i k)) q (formProduct l) := by
  induction l with
  | nil => simp [formProduct_nil]
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, scaledFrameForm_map ρ root difference a numerator q hn,
      ih, List.length_cons, pow_succ, map_mul, formProduct_cons]
    ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α K V : Type*} [Fintype α] [DecidableEq α]
  [AddCommGroup V] [Module ℝ V]

theorem exists_bounded_vanishing_product
    (root : K → ℝ) (difference : α → K → ℝ) (q : α → MvPolynomial (Option K) ℝ)
    (hlinear : ∀ i, (q i).IsHomogeneous 1)
    (hdual : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    {H D Q : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hQ : 0 ≤ Q)
    (hroot : ∀ k, |root k| ≤ H) (hdiff : ∀ i k, |difference i k| ≤ D)
    (hq : ∀ i, realPolynomialMass (q i) ≤ Q)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (fun s => eval (affineSite root difference s) P)) :
    ∃ forms : List (MvPolynomial (Option K) ℝ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧ realPolynomialMass P ≤ formMassBound (Fintype.card α) H D Q) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧ Λ forms.prod ≠ 0 := by
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ :=
    exists_affine_vanishing_product root difference q hlinear hdual Λ h hnonfactor
  refine ⟨forms, hlen, ?_, ?_, hΛ⟩
  · intro P hP
    obtain ⟨hhom, f, rfl⟩ := hforms P hP
    exact ⟨hhom, frameProjection_form_mass root difference q hH hD hQ hroot hdiff hq f⟩
  · intro s
    have hp : (forms.map (fun P => eval (affineSite root difference s) P)).prod = 0 := by
      simpa only [map_list_prod] using hz s
    exact List.mem_map.mp (List.prod_eq_zero_iff.mp hp)

theorem exists_pivot_vanishing_product
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    {H D κ : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D) (hκ : 0 < κ)
    (hroot : ∀ k, |root k| ≤ H) (hdiff : ∀ i k, |difference i k| ≤ D)
    (hdet : κ ≤ |(realDifferencePivot difference selection).det|)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (fun s => eval (affineSite root difference s) P)) :
    let Q := (Fintype.card α : ℝ) *
      ((((Fintype.card α).factorial : ℝ) * D ^ (Fintype.card α - 1) / κ) * (1 + H))
    ∃ forms : List (MvPolynomial (Option K) ℝ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧ realPolynomialMass P ≤ formMassBound (Fintype.card α) H D Q) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧ Λ forms.prod ≠ 0 := by
  intro Q
  have hd : (realDifferencePivot difference selection).det ≠ 0 := by
    intro he
    rw [he, abs_zero] at hdet
    linarith
  apply exists_bounded_vanishing_product root difference (pivotDual root difference selection)
    (pivotDual_homogeneous root difference selection) (pivotDual_boolean root difference selection hd)
    hH hD (show 0 ≤ Q by dsimp [Q]; positivity) hroot hdiff _ Λ h hnonfactor
  intro i
  exact pivotDual_mass root difference selection hD hκ
    (fun j => hroot (selection j)) (fun i j => hdiff i (selection j)) hdet i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators

def integerDifferencePivot {α K : Type*} (difference : α → K → ℤ) (selection : α → K) :
    Matrix α α ℤ := fun i j => difference i (selection j)

theorem integerDifferencePivot_adjugate_dual {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) (i s : α) :
    (∑ j, (integerDifferencePivot difference selection).adjugate j i * difference s (selection j)) =
      if i = s then (integerDifferencePivot difference selection).det else 0 := by
  have he := congrFun (congrFun (Matrix.mul_adjugate (integerDifferencePivot difference selection)) s) i
  simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, integerDifferencePivot, mul_comm, eq_comm] using he

noncomputable def integerPivotNumerator {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) :
    MvPolynomial (Option K) ℤ :=
  homogeneousDual root selection (fun j => (integerDifferencePivot difference selection).adjugate j i)

theorem integerPivotNumerator_homogeneous {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) :
    (integerPivotNumerator root difference selection i).IsHomogeneous 1 :=
  homogeneousDual_homogeneous root selection _

theorem integerPivotNumerator_eval {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) (s : Finset α) :
    eval (affineSite root difference s) (integerPivotNumerator root difference selection i) =
      if i ∈ s then (integerDifferencePivot difference selection).det else 0 := by
  rw [integerPivotNumerator, homogeneousDual_eval]
  simp only [integerDifferencePivot_adjugate_dual, Finset.sum_ite_eq]

theorem integerDifferencePivot_det_cast {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) :
    ((integerDifferencePivot difference selection).det : ℝ) =
      (realDifferencePivot (fun i k => (difference i k : ℝ)) selection).det :=
  (Int.castRingHom ℝ).map_det _

theorem integerDifferencePivot_adjugate_cast {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) (i j : α) :
    ((integerDifferencePivot difference selection).adjugate i j : ℝ) =
      (realDifferencePivot (fun i k => (difference i k : ℝ)) selection).adjugate i j := by
  exact congrFun (congrFun ((Int.castRingHom ℝ).map_adjugate (integerDifferencePivot difference selection)) i) j

theorem integerDifferencePivot_det_bound {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) {D : ℝ}
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) :
    |((integerDifferencePivot difference selection).det : ℝ)| ≤
      (Fintype.card α).factorial * D ^ Fintype.card α := by
  rw [integerDifferencePivot_det_cast]
  exact matrix_det_abs_le_uniform_bound _ hdiff

theorem integerDifferencePivot_adjugate_bound {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) {D : ℝ}
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) (i j : α) :
    |((integerDifferencePivot difference selection).adjugate i j : ℝ)| ≤
      (Fintype.card α).factorial * D ^ (Fintype.card α - 1) := by
  rw [integerDifferencePivot_adjugate_cast]
  exact matrix_adjugate_entry_abs_le _ hdiff i j

theorem homogeneousDual_map {I K R S : Type*} [Fintype I] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (selection : I → K) (n : I → R) :
    map ρ (homogeneousDual root selection n) =
      homogeneousDual (fun k => ρ (root k)) selection (fun i => ρ (n i)) := by
  simp only [homogeneousDual, map_sum, map_mul, map_sub, map_C, map_X]

theorem integerPivotNumerator_mass {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) {H D : ℝ} (hD : 0 ≤ D)
    (hroot : ∀ j, |(root (selection j) : ℝ)| ≤ H)
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) (i : α) :
    realPolynomialMass (map (Int.castRingHom ℝ) (integerPivotNumerator root difference selection i)) ≤
      (Fintype.card α : ℝ) *
        (((Fintype.card α).factorial * D ^ (Fintype.card α - 1)) * (1 + H)) := by
  rw [integerPivotNumerator, homogeneousDual_map]
  apply homogeneousDual_mass _ selection _ (by positivity) hroot
  intro j
  exact integerDifferencePivot_adjugate_bound difference selection hdiff j i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

noncomputable def normalizedIntegerDual {α K : Type*} (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ) (i : α) : MvPolynomial (Option K) ℝ :=
  (a : ℝ)⁻¹ • map (Int.castRingHom ℝ) (numerator i)

theorem normalizedIntegerDual_clear {α K : Type*} (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ) (i : α) :
    map (Int.castRingHom ℝ) (numerator i) = C (a : ℝ) * normalizedIntegerDual a numerator i := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← smul_eq_C_mul, normalizedIntegerDual, smul_smul, mul_inv_cancel₀ ha', one_smul]

theorem normalizedIntegerDual_homogeneous {α K : Type*} (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hn : ∀ i, (numerator i).IsHomogeneous 1) (i : α) :
    (normalizedIntegerDual a numerator i).IsHomogeneous 1 := by
  simpa only [normalizedIntegerDual, smul_eq_C_mul] using
    ((hn i).map (Int.castRingHom ℝ)).C_mul (a : ℝ)⁻¹

theorem normalizedIntegerDual_boolean {α K : Type*} [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hn : ∀ i s, eval (affineSite root difference s) (numerator i) = if i ∈ s then a else 0)
    (i : α) (s : Finset α) :
    eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s)
      (normalizedIntegerDual a numerator i) = if i ∈ s then 1 else 0 := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have he := affineSite_eval_map (Int.castRingHom ℝ) root difference s (numerator i)
  simp only [Int.coe_castRingHom] at he
  rw [normalizedIntegerDual, smul_eval, he, hn]
  by_cases hi : i ∈ s <;> simp [hi, ha']

end Erdos3.BooleanCubeKernel

end

end OAI
