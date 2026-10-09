import GowersSzemeredi.Proofs16JointVarietyRefinement

/-! Two-stage common partitions for translated Freiman varieties.

The linear stage controls the union of all horizontal and vertical
frequency sets. A single masked mixed-phase refinement on each cell
then handles all translated varieties at once.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Number of distinct horizontal and vertical linear frequencies. -/
def jointVarietyLinearRank {N n : Nat} (Gamma Psi : Fin n → Finset (ZMod N)) : Nat :=
  (Finset.univ.biUnion Gamma).card + (Finset.univ.biUnion Psi).card

/-- A common partition good for every translated member of the family,
with polynomial phase-count thresholds in both stages. -/
theorem joint_variety_partition_of_scales {N n r : Nat} [NeZero N] [Fact N.Prime]
    (Gamma Psi : Fin n → Finset (ZMod N)) (L : Fin n → Fin r → ZMod N → ZMod N)
    (rho : Fin n → Real) (a b : Fin n → ZMod N) (hrho : ∀ i, 0 < rho i)
    (hL : ∀ i k, IsFreimanLinearOn (bohr (Psi i) (rho i)) (L i k))
    {K : Real} {p : Nat} (hMD : MultilinearDiameterPartition K p)
    (P : Box N 2) (hP : P.IsProper)
    (H1 H2 : Nat) (hH2 : 0 < H2)
    (hK2 : K * ((n * r : Nat) + (1 : Real)) ≤ H2)
    (hscale2 : ∀ i, 8 ≤ rho i * H2)
    (hK1 : K * ((jointVarietyLinearRank Gamma Psi : Real) + 1) ≤ H1)
    (hscale1 : ∀ i, 16 ≤ rho i * H1)
    (h21 : H2 ^ (p * (n * r + 1)^8) ≤ H1) (hH21 : H2 ≤ H1)
    (hwide : H1 ^ (p * (jointVarietyLinearRank Gamma Psi + 1)^8) ≤ P.width) :
    ∃ m : Nat, ∃ R : Fin m → Box N 2,
      IsBoxPartition R P ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, (H2 : Real) ≤ (R j).width) ∧
      ∀ j i, CellGood
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (a i) (b i)) (R j) := by
  classical
  let G := Finset.univ.biUnion Gamma
  let S := Finset.univ.biUnion Psi
  have hH1 : 0 < H1 := hH2.trans_le hH21
  obtain ⟨m, Q, hpart, hprop, hw, hdiam⟩ :=
    hMD N (G.card + S.card) P hP (linearForms G S)
      (fun i => linearForms_multilinearOn G S _ i) H1 hH1 hK1 hwide
  have hsmall : ∀ i, (2^2 : Real) / H1 * N ≤ rho i / 4 * N := by
    intro i
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
    rw [div_le_iff₀ (by exact_mod_cast hH1 : (0 : Real) < H1)]
    nlinarith [hscale1 i]
  have hcell : ∀ j, ∃ m' : Nat, ∃ R : Fin m' → Box N 2,
      IsBoxPartition R (Q j) ∧ (∀ j, (R j).IsProper) ∧
      (∀ j, (H2 : Real) ≤ (R j).width) ∧
      ∀ j i, CellGood
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i / 2)) (a i) (b i))
        (shiftPairs (bilinearBohrVariety (Gamma i) (Psi i) (L i) (rho i)) (a i) (b i)) (R j) := by
    intro j
    have hwidej : H2 ^ (p * (n * r + 1)^8) ≤ (Q j).width := by
      have h : ((H2 ^ (p * (n * r + 1)^8) : Nat) : Real) ≤ H1 := by exact_mod_cast h21
      exact_mod_cast h.trans (hw j)
    apply joint_variety_cell_refine Gamma Psi L rho a b hrho hL hMD (Q j) (hprop j)
      ?_ ?_ H2 hH2 hK2 hscale2 hwidej
    · intro i gamma hg x hx y hy
      have hgG : gamma ∈ G := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hg⟩
      have h := image_diam_sub_le (hdiam (Fin.castAdd S.card (G.equivFin ⟨gamma, hgG⟩)) j) hx hy
      rw [linearForms_left S hgG, linearForms_left S hgG] at h
      exact h.trans (hsmall i)
    · intro i psi hp x hx y hy
      have hpS : psi ∈ S := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp⟩
      have h := image_diam_sub_le (hdiam (Fin.natAdd G.card (S.equivFin ⟨psi, hpS⟩)) j) hx hy
      rw [linearForms_right G hpS, linearForms_right G hpS] at h
      exact h.trans (hsmall i)
  choose m' R hRpart hRprop hRw hRgood using hcell
  exact ⟨∑ j, m' j, boxFlatten m' R, boxFlatten_partition P Q m' R hpart hRpart,
    fun j => hRprop _ _, fun j => hRw _ _, fun j i => hRgood _ _ i⟩

end LeanProofs.GowersSzemeredi
