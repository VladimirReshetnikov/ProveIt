import GowersSzemeredi.Proofs16AnchoredCover
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Bertrand

/-! # Short columns and directly sampled points

If the column set is short, the existing corrected sample budget permits
sampling all columns. A directly sampled point needs only its slice
candidate, extended constantly in the last variable.

`Section16SampledOrAnchoredOn.multilinear_cover` is in
`Proofs16ShortColumnsSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finite_sample_surjective {α : Type*} [Fintype α] [Nonempty α]
    (r : Nat) (hr : Fintype.card α ≤ r) :
    ∃ sample : Fin r → α, Function.Surjective sample := by
  let e := Fintype.equivFin α
  let sample : Fin r → α := fun i =>
    if hi : i.val < Fintype.card α then e.symm ⟨i.val, hi⟩ else Classical.choice inferInstance
  refine ⟨sample, ?_⟩
  intro x
  refine ⟨⟨(e x).val, lt_of_lt_of_le (e x).isLt hr⟩, ?_⟩
  simp [sample, (e x).isLt]

/-- A surviving point is either on a sampled column or in an anchored
subset. The anchored subset and all its anchors remain in F. -/
def Section16SampledOrAnchoredOn {N k r : Nat}
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))) : Prop :=
  ∃ K : Finset (Point N (k + 1)), K ⊆ F ∧ Section16AnchoredOn D phi sample K ∧
    ∀ h x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
      appendCoordinate h x ∈ K ∨ ∃ i, x = sample i

/-- Every nonempty column set admits recovery with the corrected budget.
Long columns use distinct-anchor sampling; short columns are sampled in
their entirety. -/
theorem section16_product_recovered_good_set {N k q r : Nat} [Fact N.Prime]
    (A : Finset (Point N k)) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h ∈ A, ∀ t, LinearOn Finset.univ (ell h t))
    (hcover : ∀ h ∈ A, ∀ x ∈ J, appendCoordinate h x ∈ D →
      ∃ t, phi (appendCoordinate h x) = ell h t x)
    (τ : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ) :
    ∃ (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))),
      (∀ i, sample i ∈ J) ∧ F ⊆ lastProductSet A J ∧
      (1 - 2 * τ) * ((lastProductSet A J).card : ℝ) ≤ F.card ∧
      Section16SampledOrAnchoredOn D phi sample F := by
  by_cases hlong : 2 * (q : ℝ) ≤ τ * J.card
  · obtain ⟨sample, F, hs, hF, hm, ha⟩ :=
      section16_product_anchored_good_set A J D phi ell hell hcover τ hq hτ hlong hr
    exact ⟨sample, F, hs, hF, hm, F, Finset.Subset.rfl, ha, fun _ _ _ hx => Or.inl hx⟩
  · letI : Nonempty J := hJ.to_subtype
    have hnr : J.card ≤ r := by
      by_contra hnr
      have hnr' : (r : ℝ) ≤ J.card := by exact_mod_cast (not_le.mp hnr).le
      linarith [mul_le_mul_of_nonneg_right hnr' hτ.le, not_le.mp hlong, Nat.cast_nonneg (α := ℝ) q]
    obtain ⟨sample, hsurj⟩ := finite_sample_surjective (α := J) r (by simpa using hnr)
    exact ⟨fun i => (sample i).val, lastProductSet A J, fun i => (sample i).property,
      Finset.Subset.rfl, mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith), ∅,
      Finset.empty_subset _, fun _ _ _ hx => absurd hx (Finset.notMem_empty _),
      fun h x _ hx => Or.inr <| (hsurj ⟨x, ((mem_lastProductSet_append A J h x).mp hx).2⟩).imp
        fun i hi => (congrArg Subtype.val hi).symm⟩

theorem section16_box_recovered_good_set {N k q r : Nat} [Fact N.Prime]
    (S : Box N (k + 1)) (T : Box N k) (J : ModAP N)
    (hprod : IsLastCoordinateBoxProduct S T J) (hJ : J.carrier.Nonempty)
    (D : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (ell : Point N k → Fin q → ZMod N → ZMod N)
    (hell : ∀ h ∈ T.carrier, ∀ t, LinearOn Finset.univ (ell h t))
    (hcover : ∀ h ∈ T.carrier, ∀ x ∈ J.carrier, appendCoordinate h x ∈ D →
      ∃ t, phi (appendCoordinate h x) = ell h t x)
    (τ : ℝ) (hq : 0 < q) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * τ) :
    ∃ (sample : Fin r → ZMod N) (F : Finset (Point N (k + 1))),
      (∀ i, sample i ∈ J.carrier) ∧ F ⊆ S.carrier ∧
      (1 - 2 * τ) * (S.carrier.card : ℝ) ≤ F.card ∧
      Section16SampledOrAnchoredOn D phi sample F := by
  have hc : S.carrier = lastProductSet T.carrier J.carrier := hprod.1
  obtain ⟨sample, F, hs, hF, hm, ha⟩ := section16_product_recovered_good_set
    T.carrier J.carrier hJ D phi ell hell hcover τ hq hτ hτ1 hr
  exact ⟨sample, F, hs, hc ▸ hF, hc ▸ hm, ha⟩

end LeanProofs.GowersSzemeredi
