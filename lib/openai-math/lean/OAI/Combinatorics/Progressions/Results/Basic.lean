import Mathlib
import OAI.Combinatorics.Progressions.Model

namespace OAI

section

namespace Erdos3

theorem HasAP.mono {A B : Set ℕ} {k : ℕ} (h : HasAP A k) (hAB : A ⊆ B) :
    HasAP B k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ hAB (h i hi)⟩

theorem HasAP.of_le {A : Set ℕ} {k l : ℕ} (h : HasAP A k) (hlk : l ≤ k) :
    HasAP A l := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ h i (hi.trans_le hlk)⟩

theorem APFree.mono {A B : Set ℕ} {k : ℕ} (h : APFree B k) (hAB : A ⊆ B) :
    APFree A k := fun hA ↦ h (hA.mono hAB)

theorem APFree.of_le {A : Set ℕ} {k l : ℕ} (h : APFree A k) (hkl : k ≤ l) :
    APFree A l := fun hA ↦ h (hA.of_le hkl)

theorem HasAP.affine_image {A : Set ℕ} {k : ℕ} (h : HasAP A k)
    (u v : ℕ) (hv : 0 < v) : HasAP ((fun n ↦ u + v * n) '' A) k := by
  obtain ⟨a, d, hd, h⟩ := h
  refine ⟨u + v * a, v * d, Nat.mul_pos hv hd, fun i hi ↦ ?_⟩
  exact ⟨a + i * d, h i hi, by ring⟩

theorem APFree.affine_preimage {A : Set ℕ} {k : ℕ} (h : APFree A k)
    (u v : ℕ) (hv : 0 < v) : APFree ((fun n ↦ u + v * n) ⁻¹' A) k := by
  intro hpre
  exact h ((hpre.affine_image u v hv).mono (Set.image_preimage_subset _ _))

theorem card_le_extremalNumber {k N : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc 1 N) (hS : APFree (S : Set ℕ) k) :
    S.card ≤ extremalNumber k N := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSN, hS⟩)

theorem extremalNumber_le (k N : ℕ) : extremalNumber k N ≤ N := by
  classical
  apply Finset.sup_le
  intro S hS
  have hSN := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact (Finset.card_le_card hSN).trans (by simp)

theorem exists_extremalSet {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ APFree (S : Set ℕ) k ∧
      S.card = extremalNumber k N := by
  classical
  let candidates := ((Finset.Icc 1 N).powerset).filter
    (fun S : Finset ℕ ↦ APFree (S : Set ℕ) k)
  have hempty : APFree (∅ : Set ℕ) k := by
    rintro ⟨a, d, hd, h⟩
    exact h 0 hk
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
      Finset.coe_empty, true_and]
    exact hempty
  obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup candidates hne Finset.card
  obtain ⟨hSN, hfree⟩ := Finset.mem_filter.mp hS
  exact ⟨S, Finset.mem_powerset.mp hSN, hfree, hmax.symm⟩

theorem extremalNumber_mono {k M N : ℕ} (hMN : M ≤ N) :
    extremalNumber k M ≤ extremalNumber k N := by
  classical
  apply Finset.sup_le
  intro S hS
  obtain ⟨hSM, hfree⟩ := Finset.mem_filter.mp hS
  apply card_le_extremalNumber _ hfree
  exact (Finset.mem_powerset.mp hSM).trans (Finset.Icc_subset_Icc_right hMN)

theorem hasAP_of_extremalNumber_lt_card {k N : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc 1 N) (hS : extremalNumber k N < S.card) :
    HasAP (S : Set ℕ) k := by
  by_contra h
  exact (not_lt_of_ge (card_le_extremalNumber hSN h)) hS

theorem monochromatic_hasAP_of_extremalNumber {k N r : ℕ}
    (hbound : r * extremalNumber k N < N) (color : ℕ → Fin r) :
    ∃ c : Fin r, HasAP {n : ℕ | n ∈ Finset.Icc 1 N ∧ color n = c} k := by
  classical
  have hcard : (Finset.univ : Finset (Fin r)).card * extremalNumber k N <
      (Finset.Icc 1 N).card := by simpa using hbound
  obtain ⟨c, _, hc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (f := color) (fun n (_hn : n ∈ Finset.Icc 1 N) ↦ Finset.mem_univ (color n)) hcard
  refine ⟨c, ?_⟩
  have h := hasAP_of_extremalNumber_lt_card (Finset.filter_subset _ _) hc
  simpa only [Finset.coe_filter, Finset.mem_coe] using h

theorem card_le_extremalNumber_of_interval {k N t : ℕ} {S : Finset ℕ}
    (hSN : S ⊆ Finset.Icc (t + 1) (t + N)) (hS : APFree (S : Set ℕ) k) :
    S.card ≤ extremalNumber k N := by
  classical
  let T := S.image (fun n ↦ n - t)
  have hT : T ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxN := Finset.mem_Icc.mp (hSN hx)
    apply Finset.mem_Icc.mpr
    omega
  have hfree : APFree (T : Set ℕ) k := by
    apply (hS.affine_preimage t 1 (by omega)).mono
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxN := Finset.mem_Icc.mp (hSN hx)
    have heq : t + 1 * (x - t) = x := by omega
    simpa only [Set.mem_preimage, heq, Finset.mem_coe] using hx
  have hcard : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hxN := Finset.mem_Icc.mp (hSN hx)
    have hyN := Finset.mem_Icc.mp (hSN hy)
    change x - t = y - t at hxy
    omega
  rw [← hcard]
  exact card_le_extremalNumber hT hfree

end Erdos3

end

end OAI
