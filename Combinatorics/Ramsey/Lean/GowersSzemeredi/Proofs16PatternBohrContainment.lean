import GowersSzemeredi.Proofs16GoodRowTriples

/-! Fixed small index patterns control the common-difference Bohr set.
This is the geometric step after index-pattern averaging. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def patternFrequencies {N m : Nat} (L : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (y z w : ZMod N) : Finset (ZMod N) :=
  (J 0).image (fun i => L i (y + z)) ∪ (J 1).image (fun i => L i z) ∪
    (J 2).image (fun i => L i (y + w)) ∪ (J 3).image (fun i => L i w)

theorem patternFrequencies_card_le {N m ell : Nat}
    (L : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    (hJ : ∀ i, (J i).card ≤ ell) (y z w : ZMod N) :
    (patternFrequencies L J y z w).card ≤ 4 * ell := by
  let A := (J 0).image (fun i => L i (y + z))
  let B := (J 1).image (fun i => L i z)
  let C := (J 2).image (fun i => L i (y + w))
  let D := (J 3).image (fun i => L i w)
  have hA : A.card ≤ ell := Finset.card_image_le.trans (hJ 0)
  have hB : B.card ≤ ell := Finset.card_image_le.trans (hJ 1)
  have hC : C.card ≤ ell := Finset.card_image_le.trans (hJ 2)
  have hD : D.card ≤ ell := Finset.card_image_le.trans (hJ 3)
  have h1 := Finset.card_union_le A B
  have h2 := Finset.card_union_le (A ∪ B) C
  have h3 := Finset.card_union_le (A ∪ B ∪ C) D
  change (A ∪ B ∪ C ∪ D).card ≤ 4 * ell
  omega

/-- Four covered-row Bohr conditions control every common difference
when the triple has no bad witness. -/
theorem bohr_common_of_covered_rows {N m : Nat} [NeZero N]
    (U : ZMod N → Finset (ZMod N)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (y z w x : ZMod N)
    (hgood : ¬ ∃ v, BadWitness U E L (y, z, w) v)
    (h1 : x ∈ bohr (covSet U E L (y + z)) (1 / 16))
    (h2 : x ∈ bohr (covSet U E L z) (1 / 16))
    (h3 : x ∈ bohr (covSet U E L (y + w)) (1 / 16))
    (h4 : x ∈ bohr (covSet U E L w) (1 / 16)) :
    x ∈ bohr (frequencyDifference (U (y + z)) (U z) ∩
      frequencyDifference (U (y + w)) (U w)) (1 / 4) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := commonDifference_inCovSum U E L y z w hgood hr
  have ha' := (Finset.mem_filter.mp h1).2 a ha
  have hb' := (Finset.mem_filter.mp h2).2 b hb
  have hc' := (Finset.mem_filter.mp h3).2 c hc
  have hd' := (Finset.mem_filter.mp h4).2 d hd
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


/-- Small index patterns can replace the covered values in the Bohr
condition, keeping the same four-row configuration. -/
theorem pattern_bohr_subset_common {N m : Nat} [NeZero N]
    (U : ZMod N → Finset (ZMod N)) (E : Fin m → Finset (ZMod N))
    (L : Fin m → ZMod N → ZMod N) (I : ZMod N → Finset (Fin m))
    (J : Fin 4 → Finset (Fin m)) {rho : Real}
    (hI : ∀ t, bohr ((I t).image (fun i => L i t)) rho ⊆ bohr (covSet U E L t) (1 / 16))
    (y z w : ZMod N) (h1 : I (y + z) = J 0) (h2 : I z = J 1)
    (h3 : I (y + w) = J 2) (h4 : I w = J 3)
    (hgood : ¬ ∃ v, BadWitness U E L (y, z, w) v) :
    bohr (patternFrequencies L J y z w) rho ⊆
      bohr (frequencyDifference (U (y + z)) (U z) ∩
        frequencyDifference (U (y + w)) (U w)) (1 / 4) := by
  intro x hx
  apply bohr_common_of_covered_rows U E L y z w x hgood
  all_goals apply hI
  all_goals refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
  all_goals apply (Finset.mem_filter.mp hx).2
  all_goals simp only [patternFrequencies, Finset.mem_union]
  · rw [h1] at hq
    exact Or.inl (Or.inl (Or.inl hq))
  · rw [h2] at hq
    exact Or.inl (Or.inl (Or.inr hq))
  · rw [h3] at hq
    exact Or.inl (Or.inr hq)
  · rw [h4] at hq
    exact Or.inr hq

end LeanProofs.GowersSzemeredi
