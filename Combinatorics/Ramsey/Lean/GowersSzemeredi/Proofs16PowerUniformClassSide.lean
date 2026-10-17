import GowersSzemeredi.Proofs16PowerUniformClass
import GowersSzemeredi.Proofs16PrintedControls
import GowersSzemeredi.Proofs16UniformCoverTwoBounds
import GowersSzemeredi.Proofs18LengthSixCountsSide

/-! Declarations of `Proofs16PowerUniformClass` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false
set_option exponentiation.threshold 1024

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **Theorem 16.2 in dimension `k` from a uniform class.** -/
theorem PowerUniformClass.theorem162At {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hk : 0 < k) (hV : 1 ≤ V)
    (hVb : 2 * V ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat} (hDC : dC ≤ D)
    (hDE : dE ≤ D) (hDT : dT + k + 1 ≤ D) (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 8))) :
    Theorem162At k := by
  have hbase : ∀ gamma theta rho : Real,
      uniformBase V 1 theta gamma rho = 2 * V * (2 / (gamma * theta * rho)) := by
    intro gamma theta rho; unfold uniformBase; push_cast; ring
  refine theorem162At_of_polyCover (C.polyCoverAt hk hV hDC hDE hDT) (W0 := 2 * V)
    (by linarith) hVb hD ?_ ?_
  · intro gamma theta rho _ _ _ _ _ _
    rw [hbase]
  · intro gamma theta rho _ _ _ _ _ _
    rw [hbase]

/-- **Theorem 16.2 in dimension `k` from a uniform class of tower-bounded degree.** -/
theorem PowerUniformClass.theorem162At_tower {k : Nat} {V : Real} {dC dE dT : Nat}
    (C : PowerUniformClass k V dC dE dT) (hk : 0 < k) (hV : 1 ≤ V)
    (hVb : 2 * V ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)) - 1)) {D : Nat} (hDC : dC ≤ D)
    (hDE : dE ≤ D) (hDT : dT + k + 1 ≤ D) (hD : D ≤ (2 : Nat) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6)))) :
    Theorem162At k := by
  have hbase : ∀ gamma theta rho : Real,
      uniformBase V 1 theta gamma rho = 2 * V * (2 / (gamma * theta * rho)) := by
    intro gamma theta rho; unfold uniformBase; push_cast; ring
  refine theorem162At_of_polyCover_tower (C.polyCoverAt hk hV hDC hDE hDT) (W0 := 2 * V)
    (by linarith) hVb hD ?_ ?_
  · intro gamma theta rho _ _ _ _ _ _
    rw [hbase]
  · intro gamma theta rho _ _ _ _ _ _
    rw [hbase]

/-- A family of `n` relations, each in `polyTwoPieces γ θ` pieces, has at most
`w^(2^84)` pieces. -/
theorem nPieces_le_base {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) {n : Nat} {w : Real} (hvw : 2 / (gamma * theta) ≤ w)
    (hnw : (n : Real) + 1 ≤ w) (hw2 : 2 ≤ w) :
    ((n * polyTwoPieces gamma theta : Nat) : Real) ≤ w ^ ((2 : Nat) ^ 84) := by
  have hm := polyTwoPieces_le_power hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hw1 : 1 ≤ w := by linarith only [hw2]
  have hmw : (polyTwoPieces gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 70) :=
    hm.trans (pow_le_pow_left₀ (by linarith only [hu2]) hvw _)
  have hn : (n : Real) ≤ w := by linarith only [hnw]
  calc ((n * polyTwoPieces gamma theta : Nat) : Real)
      = (n : Real) * (polyTwoPieces gamma theta : Real) := by push_cast; ring
    _ ≤ w * w ^ ((2 : Nat) ^ 70) :=
        mul_le_mul hn hmw (Nat.cast_nonneg _) (by linarith only [hw2])
    _ = w ^ ((2 : Nat) ^ 70 + 1) := by rw [pow_succ]; ring
    _ ≤ w ^ ((2 : Nat) ^ 84) := pow_le_pow_right₀ hw1 (by norm_num)

/-- **Dimension two is a uniform class**, at degrees `(2^89, 2^130, 2^45)`. -/
theorem powerUniformClass_two {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) :
    Nonempty (PowerUniformClass 2 V ((2 : Nat) ^ 89) ((2 : Nat) ^ 130) ((2 : Nat) ^ 45)) := by
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (polyTwoPieces gamma theta) → PolyPieceTwo N theta gamma,
        Gamma ⊆ polyPieceTwoGraphs P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => PolyPieceTwoData.empty _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    have hthr : polyTwoThreshold theta gamma ≤ N := by
      refine (polyTwoThreshold_le_power hg hg1 ht ht1).trans (le_trans ?_ hN)
      obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
      exact pow_le_pow_left₀ (by linarith only [hu2])
        (le_mul_of_one_le_left (by linarith only [hu2]) hV) _
    obtain ⟨J, hJ, P, hP⟩ := section16_poly_piece_decomposition_two ht ht1 hg hg1 hthr Gamma
      hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have hcov := section16_uniform_cover_two (familyWidthPrefactor_pos hK1)
      (familyWidthDivisor_pos hp1) hlemma6 ht ht1 hg hg1 Gamma (fun _ => Finset.univ) P
      (fun i => by rw [restrictRelation_univ]; exact hP i)
    have hsub : Finset.univ.biUnion Gamma ⊆
        Finset.univ.biUnion fun i => restrictRelation (Gamma i) Finset.univ := by
      simp only [restrictRelation_univ]; exact le_rfl
    refine (hcov.subset hsub).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hvw, hrw, hnw, _, hw2⟩ := uniformBase_facts hV n hg hg1 ht ht1 hr hr1
      refine uniTwoCount_le_power hg hg1 ht ht1 hr hr1 hvw hrw ?_
      exact (nPieces_le_base hg hg1 ht ht1 hvw hnw hw2)
    · intro rho hr hr1
      have := (uniformBase_facts hV n hg hg1 ht ht1 hr hr1).2.2.2.2
      positivity
    · intro rho hr hr1
      obtain ⟨hvw, hrw, hnw, hVw, hw2⟩ := uniformBase_facts hV n hg hg1 ht ht1 hr hr1
      have hV1w : V ≤ uniformBase V n theta gamma rho := by
        obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
        nlinarith
      have hw1 : 1 ≤ uniformBase V n theta gamma rho := by linarith only [hw2]
      have hV3 : V ≤ uniformBase V n theta gamma rho ^ 3 :=
        hV1w.trans (le_self_pow₀ hw1 (by norm_num))
      have h := uniTwoExp_inv_le_power (by omega : 0 < K1) hp1 hg hg1 ht ht1 hr hr1 hvw hrw
        (nPieces_le_base hg hg1 ht ht1 hvw hnw hw2) (hKV.trans hV3) (hpV.trans hV3)
      have h0 := uniTwoExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
        (familyWidthDivisor_pos (k := 1) hp1)
        (theta := theta) (gamma := gamma) (n * polyTwoPieces gamma theta) hr
      have := inv_anti₀ (inv_pos.mpr h0) h
      rwa [inv_inv] at this

end

end LeanProofs.GowersSzemeredi
