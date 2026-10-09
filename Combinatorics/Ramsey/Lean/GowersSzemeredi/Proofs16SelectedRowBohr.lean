import GowersSzemeredi.Proofs16QuarterRowAlphabets
import GowersSzemeredi.Proofs16Corollary20AllTriples

/-! Selection turns the common row-difference spectrum into at most four
selected frequencies per piece. The exceptional triples are those already
counted by Corollary 20. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def selectedRowFrequencies {N m : Nat} (L : Fin m → ZMod N → ZMod N) (x : ZMod N) : Finset (ZMod N) :=
  Finset.univ.image fun i => L i x

def selectedTripleFrequencies {N m : Nat} (L : Fin m → ZMod N → ZMod N)
    (y z w : ZMod N) : Finset (ZMod N) :=
  selectedRowFrequencies L (y + z) ∪ selectedRowFrequencies L z ∪
    selectedRowFrequencies L (y + w) ∪ selectedRowFrequencies L w

theorem selectedTripleFrequencies_card_le {N m : Nat}
    (L : Fin m → ZMod N → ZMod N) (y z w : ZMod N) :
    (selectedTripleFrequencies L y z w).card ≤ 4 * m := by
  have hb (x : ZMod N) : (selectedRowFrequencies L x).card ≤ m := by
    exact (Finset.card_image_le).trans (by simp)
  unfold selectedTripleFrequencies
  have h1 := Finset.card_union_le (selectedRowFrequencies L (y + z)) (selectedRowFrequencies L z)
  have h2 := Finset.card_union_le (selectedRowFrequencies L (y + z) ∪ selectedRowFrequencies L z)
    (selectedRowFrequencies L (y + w))
  have h3 := Finset.card_union_le
    (selectedRowFrequencies L (y + z) ∪ selectedRowFrequencies L z ∪ selectedRowFrequencies L (y + w))
    (selectedRowFrequencies L w)
  have := hb (y + z); have := hb z; have := hb (y + w); have := hb w
  omega

/-- Absence of a bad witness covers every common difference. -/
theorem commonDifference_inCovSum {N m : Nat} [NeZero N]
    (U : ZMod N → Finset (ZMod N)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (y z w : ZMod N)
    (hgood : ¬ ∃ v, BadWitness U E L (y, z, w) v) {r : ZMod N}
    (hr : r ∈ frequencyDifference (U (y + z)) (U z) ∩ frequencyDifference (U (y + w)) (U w)) :
    InCovSum U E L y z w r := by
  obtain ⟨hr1, hr2⟩ := Finset.mem_inter.mp hr
  obtain ⟨⟨a, b⟩, hab, habr⟩ := Finset.mem_image.mp hr1
  obtain ⟨⟨c, d⟩, hcd, hcdr⟩ := Finset.mem_image.mp hr2
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
  by_contra hnot
  apply hgood
  refine ⟨![a, b, c, d], ?_⟩
  change a ∈ U (y + z) ∧ b ∈ U z ∧ c ∈ U (y + w) ∧ d ∈ U w ∧
    a - b = c - d ∧ ¬ InCovSum U E L y z w (a - b)
  exact ⟨ha, hb, hc, hd, habr.trans hcdr.symm, by simpa only [habr] using hnot⟩

/-- Four selected row spectra at radius 1/16 control the common-difference
spectrum at radius 1/4 whenever the triple has no bad witness. -/
theorem bohr_selectedTriple_subset_common {N m : Nat} [NeZero N]
    (U : ZMod N → Finset (ZMod N)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (y z w : ZMod N)
    (hgood : ¬ ∃ v, BadWitness U E L (y, z, w) v) :
    bohr (selectedTripleFrequencies L y z w) (1 / 16) ⊆
      bohr (frequencyDifference (U (y + z)) (U z) ∩
        frequencyDifference (U (y + w)) (U w)) (1 / 4) := by
  intro x hx
  have hval (t : ZMod N) (ht : selectedRowFrequencies L t ⊆ selectedTripleFrequencies L y z w)
      (a : ZMod N) (ha : a ∈ covSet U E L t) : (centeredAbs (a * x) : Real) ≤ (1 / 16) * N := by
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp [centeredAbs]
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hx).2 _ (ht (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hrow (t : ZMod N) (ht : t = y + z ∨ t = z ∨ t = y + w ∨ t = w) :
      selectedRowFrequencies L t ⊆ selectedTripleFrequencies L y z w := by
    intro a ha
    rcases ht with rfl | rfl | rfl | rfl <;>
      simp only [selectedTripleFrequencies, Finset.mem_union] <;> tauto
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := commonDifference_inCovSum U E L y z w hgood hr
  have ha' := hval (y + z) (hrow _ (Or.inl rfl)) a ha
  have hb' := hval z (hrow _ (Or.inr (Or.inl rfl))) b hb
  have hc' := hval (y + w) (hrow _ (Or.inr (Or.inr (Or.inl rfl)))) c hc
  have hd' := hval w (hrow _ (Or.inr (Or.inr (Or.inr rfl)))) d hd
  have hsub (u v : ZMod N) : (centeredAbs ((u - v) * x) : Real) ≤
      (centeredAbs (u * x) : Real) + centeredAbs (v * x) := by
    have h := centeredAbs_add_le (u * x) (-(v * x))
    rw [centeredAbs_neg] at h
    rw [sub_mul, sub_eq_add_neg]
    exact_mod_cast h
  have hsum : (centeredAbs (((a - b) + (c - d)) * x) : Real) ≤
      (centeredAbs ((a - b) * x) : Real) + centeredAbs ((c - d) * x) := by
    rw [add_mul]
    exact_mod_cast centeredAbs_add_le ((a - b) * x) ((c - d) * x)
  linarith [hsub a b, hsub c d]

end LeanProofs.GowersSzemeredi
