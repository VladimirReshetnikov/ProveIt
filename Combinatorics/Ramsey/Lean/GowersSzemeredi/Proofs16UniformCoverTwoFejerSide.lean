import GowersSzemeredi.Proofs16UniformCoverTwoFejer
import GowersSzemeredi.Proofs16ClassStepDegreesSide
import GowersSzemeredi.Proofs16SplitUniformClassSide

/-! Declarations of `Proofs16UniformCoverTwoFejer` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false
set_option exponentiation.threshold 1024

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem nPieces_le_base_fejer {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) {n : Nat} {w : Real} (hvw : 2 / (gamma * theta) ≤ w)
    (hnw : (n : Real) + 1 ≤ w) (hw2 : 2 ≤ w) :
    ((n * polyTwoFejerPieces gamma theta : Nat) : Real) ≤ w ^ ((2 : Nat) ^ 38) := by
  have hm := polyTwoFejerPieces_le_power hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hw1 : 1 ≤ w := by linarith only [hw2]
  have hmw : (polyTwoFejerPieces gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 24) :=
    hm.trans (pow_le_pow_left₀ (by linarith only [hu2]) hvw _)
  have hn : (n : Real) ≤ w := by linarith only [hnw]
  calc ((n * polyTwoFejerPieces gamma theta : Nat) : Real)
      = (n : Real) * (polyTwoFejerPieces gamma theta : Real) := by push_cast; ring
    _ ≤ w * w ^ ((2 : Nat) ^ 24) :=
        mul_le_mul hn hmw (Nat.cast_nonneg _) (by linarith only [hw2])
    _ = w ^ ((2 : Nat) ^ 24 + 1) := by rw [pow_succ]; ring
    _ ≤ w ^ ((2 : Nat) ^ 38) := pow_le_pow_right₀ hw1 (by norm_num)

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem uniTwoFejerCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 38)) :
    uniTwoFejerCount theta gamma M rho ≤ w ^ ((2 : Nat) ^ 43) := by
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := polyPieceFaceCountW_fejer_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  clear_value v
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  -- both counts below `w^(2^38)`
  have hq' : (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤ w ^ ((2 : Nat) ^ 38) :=
    hq.trans (pow_le_pow_left₀ hv0 hvw _)
  unfold uniTwoFejerCount
  exact le_pow_mono hw2 (by norm_num) (famTwoCount_le_power hw2 hr hrw hM hq')

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem uniTwoFejerExp_inv_le_power {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 38))
    (hK : (K1 : Real) ≤ w ^ 3)
    (hp : (p1 : Real) ≤ w ^ 3) :
    (uniTwoFejerExp (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) theta gamma M rho)⁻¹ ≤
      w ^ ((2 : Nat) ^ 46) := by
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hζ0, hζ1, hζi⟩ := tightZeta_fejer_one_bounds hg hg1 ht ht1
  have hqs := polyPieceSpecCountW_fejer_le_power hg hg1 ht ht1
  have hqf := polyPieceFaceCountW_fejer_le_power hg hg1 ht ht1
  unfold uniTwoFejerExp
  dsimp only
  set ζ := tightZeta (fejerThetaOne theta gamma 1 / 4)
  set m := M with hmM
  set qs := polyPieceSpecCountW (fejerThetaOne theta gamma 1)
  set qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma
  set v := 2 / (gamma * theta) with hv
  clear_value v ζ m qs qf
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hw1 : 1 ≤ w := le_trans (by norm_num) hw2
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  have hm' : (m : Real) ≤ w ^ ((2 : Nat) ^ 38) := hM
  have hqs' : (qs : Real) ≤ w ^ ((2 : Nat) ^ 38) := hqs.trans (pow_le_pow_left₀ hv0 hvw _)
  have hqf' : (qf : Real) ≤ w ^ ((2 : Nat) ^ 38) := hqf.trans (pow_le_pow_left₀ hv0 hvw _)
  have hζw : ζ⁻¹ ≤ Real.exp (w ^ ((2 : Nat) ^ 40)) :=
    hζi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hv0 hvw _))
  have h := famTwoWidth_inv_le_power hK1 hp1 hw2 hr hr1 hrw hm' hqs' hqf' hK hp hζ0 hζ1 hζw
  exact h.trans (pow_le_pow_right₀ hw1 (by norm_num))

/-- **Dimension two is a uniform class**, at degrees `(2^89, 2^130, 2^45)`. -/
theorem powerUniformClass_two_fejer {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) :
    Nonempty (PowerUniformClass 2 V ((2 : Nat) ^ 43) ((2 : Nat) ^ 46) ((2 : Nat) ^ 15)) := by
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
    have hthr : polyTwoFejerThreshold theta gamma ≤ N := by
      refine (polyTwoFejerThreshold_le_power hg hg1 ht ht1).trans (le_trans ?_ hN)
      obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
      exact pow_le_pow_left₀ (by linarith only [hu2])
        (le_mul_of_one_le_left (by linarith only [hu2]) hV) _
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
    refine (hcov.subset hsub).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hvw, hrw, hnw, _, hw2⟩ := uniformBase_facts hV n hg hg1 ht ht1 hr hr1
      refine uniTwoFejerCount_le_power hg hg1 ht ht1 hr hr1 hvw hrw ?_
      exact (nPieces_le_base_fejer hg hg1 ht ht1 hvw hnw hw2)
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
      have h := uniTwoFejerExp_inv_le_power (by omega : 0 < K1) hp1 hg hg1 ht ht1 hr hr1 hvw hrw
        (nPieces_le_base_fejer hg hg1 ht ht1 hvw hnw hw2) (hKV.trans hV3) (hpV.trans hV3)
      have h0 := uniTwoFejerExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
        (familyWidthDivisor_pos (k := 1) hp1)
        (theta := theta) (gamma := gamma) (n * polyTwoFejerPieces gamma theta) hr
      have := inv_anti₀ (inv_pos.mpr h0) h
      rwa [inv_inv] at this

/-- **The dimension-two split class under the Fejér θ₁**, at any
`d ≥ 2^46`. -/
theorem splitUniformClass_two_fejer {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) {d : Nat}
    (hd : (2 : Nat) ^ 46 ≤ d) :
    Nonempty (SplitUniformClass 2 V d d) := by
  obtain ⟨C⟩ := powerUniformClass_two_fejer hK1 hp1 hlemma6 hV hKV hpV
  have h43 : (2 : Nat) ^ 43 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  have h15 : (2 : Nat) ^ 15 ≤ d := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hd
  exact ⟨(C.weaken hV le_rfl h43 hd h15).toSplit⟩

end

end LeanProofs.GowersSzemeredi
