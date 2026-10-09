import GowersSzemeredi.Proofs16SelectedCommonBohr
import GowersSzemeredi.Proofs16PatternBohrContainment

/-! Recenter both varying rows of a fixed pattern simultaneously. Constant
frequencies are separated from normalized locally additive frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def varyingPatternFrequencies {N m : Nat} (psi : Fin m → ZMod N → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (t : ZMod N) : Finset (ZMod N) :=
  (J 0 ∪ J 2).image fun i => psi i t

theorem varyingPatternFrequencies_card_le {N m ell : Nat}
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    (hJ : ∀ i, (J i).card ≤ ell) (t : ZMod N) :
    (varyingPatternFrequencies psi J t).card ≤ 2 * ell := by
  have h := Finset.card_union_le (J 0) (J 2)
  have h0 := hJ 0
  have h2 := hJ 2
  exact Finset.card_image_le.trans (by omega)

/-- A half-radius condition on the constants and on the variable parts
implies the original Bohr condition. -/
theorem pattern_bohr_of_recentered {N m : Nat} [NeZero N]
    (L psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m))
    (a y z w d : ZMod N) {eta : Real} (heta : 0 ≤ eta)
    (h0 : ∀ i ∈ J 0, L i (y + z) = L i (a + z) + psi i (y - a))
    (h2 : ∀ i ∈ J 2, L i (y + w) = L i (a + w) + psi i (y - a))
    (hc : d ∈ bohr (patternFrequencies L J a z w) (eta / 2))
    (hv : d ∈ bohr (varyingPatternFrequencies psi J (y - a)) (eta / 2)) :
    d ∈ bohr (patternFrequencies L J y z w) eta := by
  have hconst := (Finset.mem_filter.mp hc).2
  have hvar := (Finset.mem_filter.mp hv).2
  have hadd (u v : ZMod N)
      (hu : (centeredAbs (u * d) : Real) ≤ eta / 2 * N)
      (hv' : (centeredAbs (v * d) : Real) ≤ eta / 2 * N) :
      (centeredAbs ((u + v) * d) : Real) ≤ eta * N := by
    have h : (centeredAbs ((u + v) * d) : Real) ≤ centeredAbs (u * d) + centeredAbs (v * d) := by
      rw [add_mul]
      exact_mod_cast centeredAbs_add_le (u * d) (v * d)
    linarith
  have hhalf : eta / 2 * (N : Real) ≤ eta * N := by
    have hN : (0 : Real) ≤ N := Nat.cast_nonneg N
    nlinarith
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  simp only [patternFrequencies, Finset.mem_union, Finset.mem_image] at hr
  rcases hr with ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · rw [h0 i hi]
    exact hadd _ _ (hconst _ (by
      simp only [patternFrequencies, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inl ⟨i, hi, rfl⟩))))
      (hvar _ (Finset.mem_image.mpr ⟨i, Finset.mem_union_left _ hi, rfl⟩))
  · exact (hconst _ (by
      simp only [patternFrequencies, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩)))).trans hhalf
  · rw [h2 i hi]
    exact hadd _ _ (hconst _ (by
      simp only [patternFrequencies, Finset.mem_union, Finset.mem_image]
      exact Or.inl (Or.inr ⟨i, hi, rfl⟩)))
      (hvar _ (Finset.mem_image.mpr ⟨i, Finset.mem_union_right _ hi, rfl⟩))
  · exact (hconst _ (by
      simp only [patternFrequencies, Finset.mem_union, Finset.mem_image]
      exact Or.inr ⟨i, hi, rfl⟩)).trans hhalf

/-- Fixed patterns on a dense row set give a dense set of centered
parameters inside one common neighborhood. The geometric conclusion
splits into at most 4ell constant and 2ell varying frequencies. -/
theorem fixed_patterns_recentered {N m ell : Nat} [NeZero N]
    (A : Finset (ZMod N × ZMod N)) (V : Finset (ZMod N))
    (E : Fin m → Finset (ZMod N)) (L : Fin m → ZMod N → ZMod N)
    (S : Fin m → Finset (ZMod N)) (J : Fin 4 → Finset (Fin m)) (z w : ZMod N)
    {nu rho R eta : Real} (hnu : 0 < nu) (hV : nu * N ≤ V.card)
    (hrho : 0 ≤ rho) (hR : 0 ≤ R) (heta : 0 ≤ eta)
    (hJ : ∀ i, (J i).card ≤ ell)
    (hS : ∀ i, ((S i).card : Real) ≤ R)
    (hB : ∀ i, IsBHomomorphism (E i) (bohr (S i) rho) (L i))
    (hdom : ∀ y ∈ V, (∀ i ∈ J 0, y + z ∈ E i) ∧ (∀ i ∈ J 2, y + w ∈ E i))
    (hgeom : ∀ y ∈ V, ∀ d ∈ bohr (patternFrequencies L J y z w) eta, (d, y) ∈ A) :
    ∃ (T F W : Finset (ZMod N)) (a : ZMod N) (psi : Fin m → ZMod N → ZMod N),
      (T.card : Real) ≤ (2 * ell : Nat) * R ∧ F.card ≤ 4 * ell ∧
      (0 : ZMod N) ∈ W ∧ W ⊆ bohr T rho ∧
      nu * (bohr T (rho / 2)).card ≤ (W.card : Real) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ t, (varyingPatternFrequencies psi J t).card ≤ 2 * ell) ∧
      ∀ t ∈ W, a + t ∈ V ∧ ∀ d ∈ bohr F (eta / 2),
        d ∈ bohr (varyingPatternFrequencies psi J t) (eta / 2) → (d, a + t) ∈ A := by
  have hVpos : V.Nonempty := by
    apply Finset.card_pos.mp
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    exact_mod_cast (mul_pos hnu hN).trans_le hV
  obtain ⟨v, hv⟩ := hVpos
  have hE : ∀ i ∈ J 0 ∪ J 2, (E i).Nonempty := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact ⟨v + z, (hdom v hv).1 i hi⟩
    · exact ⟨v + w, (hdom v hv).2 i hi⟩
  obtain ⟨T, a, C, psi, hT, ha, hCV, hC, hdiff, hpsi⟩ :=
    selected_common_bohr_cluster (J 0 ∪ J 2) E L S V hrho hnu hV hE
      (fun i _ => hS i) (fun i _ => hB i)
  let W := C.image fun y => y - a
  have hWcard : W.card = C.card :=
    Finset.card_image_of_injective _ (fun x y h => by linear_combination h)
  have hJcard : (J 0 ∪ J 2).card ≤ 2 * ell := by
    have := Finset.card_union_le (J 0) (J 2)
    have := hJ 0
    have := hJ 2
    omega
  refine ⟨T, patternFrequencies L J a z w, W, a, psi,
    hT.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hJcard) hR),
    patternFrequencies_card_le L J hJ a z w,
    Finset.mem_image.mpr ⟨a, ha, sub_self a⟩, ?_, ?_, ?_,
    varyingPatternFrequencies_card_le psi J hJ, ?_⟩
  · intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    exact hdiff y hy a ha
  · simpa only [hWcard] using hC
  · intro i hi
    exact ⟨(hpsi i hi).1, (hpsi i hi).2.1, (hpsi i hi).2.2.1⟩
  · intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    have hay : a + (y - a) = y := by ring
    rw [hay]
    refine ⟨hCV hy, fun d hc hd => hgeom y (hCV hy) d ?_⟩
    apply pattern_bohr_of_recentered L psi J a y z w d heta _ _ hc hd
    · intro i hi
      have hg := (hpsi i (Finset.mem_union_left _ hi)).2.2.2 (y + z)
        ((hdom y (hCV hy)).1 i hi) (a + z) ((hdom a (hCV ha)).1 i hi)
        (by simpa only [add_sub_add_right_eq_sub] using hdiff y hy a ha)
      rw [add_sub_add_right_eq_sub] at hg
      linear_combination hg
    · intro i hi
      have hg := (hpsi i (Finset.mem_union_right _ hi)).2.2.2 (y + w)
        ((hdom y (hCV hy)).2 i hi) (a + w) ((hdom a (hCV ha)).2 i hi)
        (by simpa only [add_sub_add_right_eq_sub] using hdiff y hy a ha)
      rw [add_sub_add_right_eq_sub] at hg
      linear_combination hg

end LeanProofs.GowersSzemeredi
