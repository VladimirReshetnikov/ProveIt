import GowersSzemeredi.Proofs16PairEnergyCS
import GowersSzemeredi.Proofs16LineFreimanUnconditional
import GowersSzemeredi.Proofs07BohrHom

/-! Columns of a Freiman bihomomorphism carry Freiman-linear maps on Bohr
sets: the column step of Milićević's Proposition 5.1 (arXiv:2601.01682,
Step 1 of the proof of Theorem 1.4), in prime `ℤ/N` with polynomial bounds.

Milićević passes from a Freiman bihomomorphism `φ : A → H` to Freiman-linear
maps `φ_x : B_x → H` on Bohr sets `B_x`, one for each dense column `x`. He
uses the quasi-polynomial structure theorem for Freiman homomorphisms
(his Theorem 2.26). In `ℤ/N` the corpus's polynomial tools from Gowers's
paper suffice.

* `pairKey_fst_injOn`: for a Freiman 2-homomorphism `f` on `A`, the key
  `(a − c, f a − f c)` of a pair is determined by `a − c`. So at most `N`
  keys occur among the pairs of `A`.
* `phiAdditiveCount_ge_of_freimanHom2`: `|A|⁴ ≤ N·#{respected additive
  quadruples}`, by Cauchy–Schwarz over the key fibres.
* `column_freiman_bohr`: if `|A| = αN`, there are `B ⊆ A` with
  `|B| ≥ 2⁻¹⁸⁸²α⁴⁶⁵⁶N` on which `f` is a Freiman 8-homomorphism
  (Corollary 7.6), a spectrum `K` with `|K| ≤ 16β⁻²` (`β = |B|/N`), and a
  Freiman-linear `ψ` on `B(K; 1/(8π))` with `f x − f y = ψ(x − y)`
  whenever `x, y ∈ B` and `x − y ∈ B(K; 1/(8π))` (Lemma 7.8, constant
  radius).

Applied to the column `y ↦ φ(x, y)` of a Freiman bihomomorphism on a
column of density `α`, this gives Proposition 5.1 (i) and (ii) with
polynomial losses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- For a Freiman 2-homomorphism, the key of a pair is determined by its
difference. -/
theorem pairKey_fst_injOn {N : Nat} [NeZero N] {A : Finset (ZMod N)} {f : ZMod N → ZMod N}
    (hf : FreimanHom 2 A f) :
    Set.InjOn Prod.fst (((A ×ˢ A).image (pairKey f) : Finset (ZMod N × ZMod N)) :
      Set (ZMod N × ZMod N)) := by
  rw [FreimanHom, isAddFreimanHom_two] at hf
  obtain ⟨_, hquad⟩ := hf
  intro κ hκ κ' hκ' heq
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hκ hκ'
  obtain ⟨⟨a, c⟩, ⟨ha, hc⟩, rfl⟩ := hκ
  obtain ⟨⟨a', c'⟩, ⟨ha', hc'⟩, rfl⟩ := hκ'
  simp only [pairKey] at heq ⊢
  have hadd : a + c' = a' + c := by linear_combination heq
  have hfadd := hquad a ha c' hc' a' ha' c hc hadd
  ext
  · exact heq
  · show f a - f c = f a' - f c'
    linear_combination hfadd

/-- **Respected quadruples of a Freiman 2-homomorphism.** -/
theorem phiAdditiveCount_ge_of_freimanHom2 {N : Nat} [NeZero N] (A : Finset (ZMod N))
    (f : ZMod N → ZMod N) (hf : FreimanHom 2 A f) :
    (A.card : Real) ^ 4 ≤ N * phiAdditiveCount A f := by
  rw [← pairEnergy_self_eq_phiAdditiveCount, pairEnergy_eq_sum]
  set S := A ×ˢ A
  set D := S.image (pairKey f)
  -- the fibres partition `S`
  have hpart : ∑ κ ∈ D, ((keyFibre S f κ).card : Real) = (A.card : Real) ^ 2 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := pairKey f) (s := S) (t := D)
      (fun p hp => Finset.mem_image_of_mem _ hp)
    have hS : S.card = A.card ^ 2 := by rw [Finset.card_product, sq]
    rw [hS] at h
    unfold keyFibre
    exact_mod_cast h.symm
  have hD : (D.card : Real) ≤ N := by
    have h := Finset.card_le_card_of_injOn Prod.fst (fun κ _ => Finset.mem_univ κ.1)
      (pairKey_fst_injOn hf)
    rw [Finset.card_univ, ZMod.card] at h
    exact_mod_cast h
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D (fun κ => ((keyFibre S f κ).card : Real))
    (fun _ => (1 : Real))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at hcs
  rw [hpart] at hcs
  -- the sum over `D` is at most the sum over all keys
  have hsub : ∑ κ ∈ D, ((keyFibre S f κ).card : Real) ^ 2 ≤
      (Nat.cast (∑ κ, (keyFibre S f κ).card * (keyFibre S f κ).card) : Real) := by
    push_cast
    calc _ ≤ ∑ κ, ((keyFibre S f κ).card : Real) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => sq_nonneg _)
      _ = _ := Finset.sum_congr rfl fun κ _ => sq _
  have hsum0 : 0 ≤ ∑ κ ∈ D, ((keyFibre S f κ).card : Real) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (A.card : Real) ^ 4 = ((A.card : Real) ^ 2) ^ 2 := by ring
    _ ≤ (∑ κ ∈ D, ((keyFibre S f κ).card : Real) ^ 2) * D.card := hcs
    _ ≤ (∑ κ ∈ D, ((keyFibre S f κ).card : Real) ^ 2) * N :=
        mul_le_mul_of_nonneg_left hD hsum0
    _ ≤ (Nat.cast (∑ κ, (keyFibre S f κ).card * (keyFibre S f κ).card) : Real) * N :=
        mul_le_mul_of_nonneg_right hsub (Nat.cast_nonneg N)
    _ = _ := by push_cast; ring

/-- **A Freiman-linear column map on a Bohr set** (Milićević, Proposition
5.1 (i)–(ii), column step, polynomial bounds in `ℤ/N`). -/
theorem column_freiman_bohr {N : Nat} [NeZero N] [Fact N.Prime] (A : Finset (ZMod N))
    (f : ZMod N → ZMod N) (hf : FreimanHom 2 A f) {α : Real} (hα : 0 < α)
    (hcard : (A.card : Real) = α * N) :
    ∃ B ⊆ A, (2 : Real) ^ (-(1882 : Real)) * (α ^ 4) ^ 1164 * N ≤ B.card ∧
      FreimanHom 8 B f ∧
      ((section7Spectrum B (B.card / N)).card : Real) ≤
        16 * ((B.card : Real) / N) ^ (-(2 : Real)) ∧
      ∃ ψ : ZMod N → ZMod N,
        FreimanHom 2 (bohr (section7Spectrum B (B.card / N)) (1 / (8 * Real.pi))) ψ ∧
        ∀ x ∈ B, ∀ y ∈ B, x - y ∈ bohr (section7Spectrum B (B.card / N)) (1 / (8 * Real.pi)) →
          f x - f y = ψ (x - y) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  -- the energy input of Corollary 7.6
  have hcount := phiAdditiveCount_ge_of_freimanHom2 A f hf
  have henergy : α ^ 4 * (N : Real) ^ 3 ≤
      weightedSimultaneousAdditiveEnergy A (fun _ => 1) (fun _ : Fin 1 => f) := by
    rw [energy_eq_phiAdditiveCount]
    rw [hcard] at hcount
    have : α ^ 4 * (N : Real) ^ 3 * N ≤ (phiAdditiveCount A f : Real) * N := by
      nlinarith
    exact le_of_mul_le_mul_right this hNR
  obtain ⟨B, hBA, hBcard, hB8⟩ := lineFreimanExtraction_eight N A f (α ^ 4) (by positivity)
    henergy
  have hBpos : (0 : Real) < B.card := by
    have : (0 : Real) < (2 : Real) ^ (-(1882 : Real)) * (α ^ 4) ^ 1164 * N := by positivity
    linarith
  have hβ : (0 : Real) < (B.card : Real) / N := div_pos hBpos hNR
  have hβcard : (B.card : Real) = (B.card / N) * N := (div_mul_cancel₀ _ hNR.ne').symm
  obtain ⟨hK, ψ, hψ, hagree⟩ := lemma_7_8_constant_radius N B f (B.card / N) hβ hβcard hB8
  exact ⟨B, hBA, hBcard, hB8, hK, ψ, hψ, hagree⟩

end LeanProofs.GowersSzemeredi
