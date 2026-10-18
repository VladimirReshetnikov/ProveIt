import GowersSzemeredi.Proofs16UniformCoverTwoSplit

/-! Declarations of `Proofs16UniformCoverTwoSplit` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **The dimension-two count, in two bases**: `≤ ν^11·W^(2^41)`. -/
theorem uniTwoFejerCount_le_split {V : Real} (hV : 1 ≤ V) {gamma theta rho : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    uniTwoFejerCount theta gamma (n * polyTwoFejerPieces gamma theta) rho ≤
      ((n : Real) + 1) ^ 11 * splitW V theta gamma rho ^ ((2 : Nat) ^ 41) := by
  obtain ⟨hW2, -, hrW, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hqf, -⟩ := two_split_basics hV hg hg1 ht ht1 hr hr1 n
  have hν : (1 : Real) ≤ (n : Real) + 1 := by have := Nat.cast_nonneg (α := Real) n; linarith
  have h := famTwoCount_le_two_bases hν hW2 hr hrW hM hqf
  unfold uniTwoFejerCount
  exact h.trans (tb_mono hν (by linarith only [hW2]) (by norm_num) (by norm_num))

/-- **Dimension two is a split class at `a₂ = 32`, `D₂ = 2^48`.** -/
theorem splitUniformClass_two_small {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) :
    Nonempty (SplitUniformClass 2 V 32 ((2 : Nat) ^ 48)) := by
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (polyTwoFejerPieces gamma theta) → PolyPieceTwoFejer N theta gamma,
        Gamma ⊆ polyPieceTwoFejerGraphs P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => PolyPieceTwoData.empty _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    have hthr : polyTwoFejerThreshold theta gamma ≤ N := by
      refine (polyTwoFejerThreshold_le_power hg hg1 ht ht1).trans (le_trans ?_ hN)
      refine (pow_le_pow_left₀ (by linarith only [hu2])
        (le_mul_of_one_le_left (by linarith only [hu2]) hV) _).trans ?_
      exact pow_le_pow_right₀ hVu (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    obtain ⟨J, hJ, P, hP⟩ := section16_poly_piece_decomposition_two_fejer ht ht1 hg hg1 hthr Gamma
      hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have hcov := section16_uniform_cover_two_fejer (familyWidthPrefactor_pos hK1)
      (familyWidthDivisor_pos hp1) hlemma6 ht ht1 hg hg1 Gamma (fun _ => Finset.univ) P
      (fun i => by rw [restrictRelation_univ]; exact hP i)
    have hsub : Finset.univ.biUnion Gamma ⊆
        Finset.univ.biUnion fun i => restrictRelation (Gamma i) Finset.univ := by
      simp only [restrictRelation_univ]; exact le_rfl
    have hν : (1 : Real) ≤ (n : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) n; linarith only [this]
    refine (hcov.subset hsub).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      exact (uniTwoFejerCount_le_split hV hg hg1 ht ht1 hr hr1 n).trans
        (tb_mono hν (by linarith only [hW2]) (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have : (0 : Real) < splitW V theta gamma rho := by linarith only [hW2]
      positivity
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have h := (uniTwoFejerExp_inv_le_split hV (by omega : 0 < K1) hp1 hKV hpV hg hg1 ht ht1 hr hr1
        n).trans (tb_mono hν (by linarith only [hW2]) (by norm_num : 29 ≤ 32)
          (Nat.pow_le_pow_right (by norm_num) (by norm_num) : (2 : Nat) ^ 46 ≤ (2 : Nat) ^ 48))
      have h0 := uniTwoFejerExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
        (familyWidthDivisor_pos (k := 1) hp1)
        (theta := theta) (gamma := gamma) (n * polyTwoFejerPieces gamma theta) hr
      have := inv_anti₀ (inv_pos.mpr h0) h
      rwa [inv_inv] at this

end

end LeanProofs.GowersSzemeredi
