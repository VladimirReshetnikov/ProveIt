import OAI.Combinatorics.Progressions.Dynamics.PeelingReplacementPotential
import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement

namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

noncomputable def replacementIntegralSum (A Q : Finset G) (shape : Finset G → Finset G)
    (a g : G → ℝ) : (G → ℝ) → List (Finset G) → ℝ
  | _, [] => 0
  | f, D :: ds => (D.card : ℝ) / A.card * replacementIntegral D Q (shape D) a f g +
      replacementIntegralSum A Q shape a g (Peeling.remainder D f) ds

variable [Fintype G]

theorem chain_replacement_integral_error
    {A : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' : G → ℝ} {ds : List (Finset G)} (h : Peeling.Chain A Admissible K kappa f f' ds)
    (Q : Finset G) (shape : Finset G → Finset G) (a g : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta) (ha : ∀ x, |a x| ≤ M)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, x ∉ A → f x = 0) →
    |bilinearIntegral A Q a f g -
      (bilinearIntegral A Q a f' g + replacementIntegralSum A Q shape a g f ds)| ≤
        (M * eta) * Peeling.coefficientCost A ds := by
  induction h with
  | nil f => intro _ _; simp [replacementIntegralSum, Peeling.coefficientCost]
  | @step f f' ds D _ hD _ _ ih =>
    intro hf hsupport
    have hrem : ∀ x, 0 ≤ Peeling.remainder D f x ∧ Peeling.remainder D f x ≤ 1 := by
      intro x
      exact ⟨Peeling.remainder_nonneg D f (fun y => (hf y).1) x,
        (Peeling.remainder_le D f (fun y => (hf y).1) x).trans (hf x).2⟩
    have htail := ih hrem (Peeling.remainder_supported A D f hsupport)
    obtain ⟨hDn, hCn, hTV⟩ := hshape D hD
    have hstep := abs_slice_sub_replacement_le A Q D (shape D) hDn hCn a f g
      hM heta ha hf hg hsupport hTV
    rw [bilinearIntegral_peeling A Q D a f g]
    simp only [replacementIntegralSum, Peeling.coefficientCost, List.map_cons,
      List.sum_cons] at htail ⊢
    calc
      _ = |(bilinearIntegral A Q a (Peeling.remainder D f) g -
          (bilinearIntegral A Q a f' g +
            replacementIntegralSum A Q shape a g (Peeling.remainder D f) ds)) +
          (bilinearIntegral A Q a (Peeling.slice D f) g -
            (D.card : ℝ) / A.card * replacementIntegral D Q (shape D) a f g)| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add htail hstep
      _ = _ := by ring

theorem pair_replacement_integral_error
    {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (shape : Finset G → Finset G) (a : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass B (y - t) - realUniformMass B y|) ≤ eta) :
    |bilinearIntegral B B a f g -
      (bilinearIntegral B B a f' g' + replacementIntegralSum B B shape a g f cs +
        replacementIntegralSum B B shape a f' g ds)| ≤
      (M * eta) * (Peeling.coefficientCost B cs + Peeling.coefficientCost B ds) := by
  have hf' : ∀ x, 0 ≤ f' x ∧ f' x ≤ 1 := by
    intro x
    have h := hF.bounds (fun y => (hf y).1) x
    exact ⟨h.1, h.2.trans (hf x).2⟩
  have hfirst := chain_replacement_integral_error hF B shape a g hM heta ha hg hshape hf hfsupport
  have hsecond := chain_replacement_integral_error hG B shape a f' hM heta ha hf' hshape hg hgsupport
  rw [bilinearIntegral_swap B B a g f', bilinearIntegral_swap B B a g' f'] at hsecond
  calc
    _ = |(bilinearIntegral B B a f g -
        (bilinearIntegral B B a f' g + replacementIntegralSum B B shape a g f cs)) +
        (bilinearIntegral B B a f' g -
          (bilinearIntegral B B a f' g' + replacementIntegralSum B B shape a f' g ds))| := by
      congr 1
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hfirst hsecond
    _ = _ := by ring

theorem pair_replacement_integral_error_le_mass
    {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (shape : Finset G → Finset G) (a : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass B (y - t) - realUniformMass B y|) ≤ eta) :
    |bilinearIntegral B B a f g -
      (bilinearIntegral B B a f' g' + replacementIntegralSum B B shape a g f cs +
        replacementIntegralSum B B shape a f' g ds)| ≤
      (M * eta) * (((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa)) :=
  (pair_replacement_integral_error hF hG shape a hM heta ha hf hg hfsupport hgsupport hshape).trans
    (Peeling.weighted_pair_error_le hF hG hK hkappa (mul_nonneg hM heta)
      (fun x => (hf x).1) (fun x => (hg x).1) hfsupport hgsupport)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem replacementIntegral_le_of_cellBilinearBound
    (D Q C : Finset G) (a f g : G → ℝ) (origin : G) {T : ℝ}
    (hD : ∃ x, D = C.image (fun r => x + r)) (hbound : CellBilinearBound C a T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    replacementIntegral D Q C (fun r => a (origin + r)) f g ≤ T * replacementPotential D Q C f g := by
  obtain ⟨x, rfl⟩ := hD
  rw [replacementIntegral_eq_cells]
  unfold replacementPotential
  rw [expect_translated_cell]
  calc
    _ ≤ 𝔼 y ∈ Q, T * (cellAverage C f x * cellAverage C g y) ^ (1 / 4 : ℝ) := by
      apply Finset.expect_le_expect
      intro y _
      exact translated_integral_le_of_cellBilinearBound C a f g origin x y hbound hf hg
    _ = _ := (Finset.mul_expect _ _ T).symm

theorem replacementIntegralSum_le_of_cellBilinearBound
    (A Q : Finset G) (shape : Finset G → Finset G) (a g : G → ℝ) (origin : G)
    (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) {T : ℝ} (ds : List (Finset G))
    (hshape : ∀ D ∈ ds, (∃ x, D = (shape D).image (fun r => x + r)) ∧
      CellBilinearBound (shape D) a T)
    (f : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) :
    replacementIntegralSum A Q shape (fun r => a (origin + r)) g f ds ≤
      T * replacementPotentialSum A Q shape g f ds := by
  induction ds generalizing f with
  | nil => simp [replacementIntegralSum, replacementPotentialSum]
  | cons D ds ih =>
    have hrem : ∀ r, 0 ≤ Peeling.remainder D f r ∧ Peeling.remainder D f r ≤ 1 := by
      intro r
      exact ⟨Peeling.remainder_nonneg D f (fun t => (hf t).1) r,
        (Peeling.remainder_le D f (fun t => (hf t).1) r).trans (hf r).2⟩
    have hhead := replacementIntegral_le_of_cellBilinearBound D Q (shape D) a f g origin
      (hshape D List.mem_cons_self).1 (hshape D List.mem_cons_self).2 hf hg
    have htail := ih (fun C hC => hshape C (List.mem_cons_of_mem D hC)) (Peeling.remainder D f) hrem
    simp only [replacementIntegralSum, replacementPotentialSum]
    calc
      _ ≤ (D.card : ℝ) / A.card * (T * replacementPotential D Q (shape D) f g) +
          T * replacementPotentialSum A Q shape g (Peeling.remainder D f) ds :=
        add_le_add (mul_le_mul_of_nonneg_left hhead (by positivity)) htail
      _ = _ := by ring

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem peeling_parent_bound_of_remainder
    {B : Finset G} (hB : B.Nonempty) {Admissible : Finset G → Prop}
    {K kappa T rho error M eta : ℝ} {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hT : 0 ≤ T) (hrho : 1 / 2 ≤ rho) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (shape : Finset G → Finset G) (a : G → ℝ) (origin : G)
    (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      (∃ x, D = (shape D).image (fun r => x + r)) ∧ CellBilinearBound (shape D) a T ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass B (y - t) - realUniformMass B y|) ≤ eta)
    (hremainder : bilinearIntegral B B (fun r => a (origin + r)) f' g' ≤
      T * rho * ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) + error) :
    bilinearIntegral B B (fun r => a (origin + r)) f g ≤
      T * rho * ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) + error +
        (M * eta) * (((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa)) := by
  have hf' : ∀ x, 0 ≤ f' x ∧ f' x ≤ 1 := by
    intro x
    have h := hF.bounds (fun y => (hf y).1) x
    exact ⟨h.1, h.2.trans (hf x).2⟩
  have hfirst := replacementIntegralSum_le_of_cellBilinearBound B B shape a g origin hg cs
    (fun D hD => ⟨(hshape D (hF.admissible_mem D hD)).2.2.1,
      (hshape D (hF.admissible_mem D hD)).2.2.2.1⟩) f hf
  have hsecond := replacementIntegralSum_le_of_cellBilinearBound B B shape a f' origin hf' ds
    (fun D hD => ⟨(hshape D (hG.admissible_mem D hD)).2.2.1,
      (hshape D (hG.admissible_mem D hD)).2.2.2.1⟩) g hg
  have hbudget := pair_replacement_contraction hB hF hG hK hkappa hKfactor hrho shape
    (fun D hD => (hshape D hD).2.1) (fun x => (hf x).1) (fun x => (hg x).1)
    hfsupport hgsupport
  have hbudgetT := mul_le_mul_of_nonneg_left hbudget hT
  have herr := pair_replacement_integral_error_le_mass hF hG hK hkappa shape
    (fun r => a (origin + r)) hM heta (fun r => ha (origin + r)) hf hg hfsupport hgsupport
    (fun D hD => ⟨(hshape D hD).1, (hshape D hD).2.1, (hshape D hD).2.2.2.2⟩)
  have herrUpper := (abs_le.mp herr).2
  nlinarith only [hfirst, hsecond, hbudgetT, hremainder, herrUpper]

end Erdos3.CellRefinement

end

end OAI
