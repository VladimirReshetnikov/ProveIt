import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedBooleanSite
import OAI.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem slicedSourceErrorBudget {ι : Type*} [Fintype ι]
    (O m : ℕ) {Pcap Op E F C a δ : ℝ}
    (hPcap : 0 ≤ Pcap) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C) (hCF : C ≤ Real.exp F)
    (ha : a⁻¹ ≤ Real.exp Pcap) (hδ : δ⁻¹ ≤ Real.exp Pcap) :
    let Qcap := VectorPolynomial.slicedJointDensityLogBudget O m Pcap
    let G := (Fintype.card ι : ℝ) * max Op 0
    let εgrid := Real.exp (-(Qcap + (E + F) + 1))
    let εlong := Real.exp (-(G + (E + F) + 1))
    let P := max Pcap (G + (E + F) + 2)
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Qcap + (E + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp P ∧
      0 ≤ P ∧ a⁻¹ ≤ Real.exp P ∧ δ⁻¹ ≤ Real.exp P ∧ 4 ≤ Real.exp P ∧
      C * (Real.exp Qcap * εgrid + εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  intro Qcap G εgrid εlong P
  have hQ : 0 ≤ Qcap := VectorPolynomial.slicedJointDensityLogBudget_nonneg O m hPcap
  have hG : 0 ≤ G := mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, herr⟩ :=
    slicedSourceAccuracy_bounds hQ hG (add_nonneg hE hF)
  have hPcapP : Pcap ≤ P := le_max_left _ _
  have hP2 : 2 ≤ P := (by linarith only [hG, hE, hF] : 2 ≤ G + (E + F) + 2).trans (le_max_right _ _)
  have hPlong : G + (E + F) + 1 ≤ P :=
    (by linarith : G + (E + F) + 1 ≤ G + (E + F) + 2).trans (le_max_right _ _)
  have hprod : (∏ _i : ι, Real.exp Op) ≤ Real.exp G := by
    simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  refine ⟨hg0, hg1, hgi, hl0, hl1, hli.trans_le (Real.exp_le_exp.mpr hPlong),
    hPcap.trans hPcapP, ha.trans (Real.exp_le_exp.mpr hPcapP),
    hδ.trans (Real.exp_le_exp.mpr hPcapP), hfour.trans (Real.exp_le_exp.mpr hP2), ?_⟩
  calc
    _ ≤ C * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_left (herr _ hprod) hC0
    _ ≤ Real.exp F * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_right hCF (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

theorem slicedSourceErrorBudget_of_card_le {ι : Type*} [Fintype ι]
    (O m : ℕ) {D Pcap Op E F C a δ : ℝ}
    (hD : 0 ≤ D) (hcard : (Fintype.card ι : ℝ) ≤ D)
    (hPcap : 0 ≤ Pcap) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C) (hCF : C ≤ Real.exp F)
    (ha : a⁻¹ ≤ Real.exp Pcap) (hδ : δ⁻¹ ≤ Real.exp Pcap) :
    let Qcap := VectorPolynomial.slicedJointDensityLogBudget O m Pcap
    let G := D * max Op 0
    let εgrid := Real.exp (-(Qcap + (E + F) + 1))
    let εlong := Real.exp (-(G + (E + F) + 1))
    let P := max Pcap (G + (E + F) + 2)
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Qcap + (E + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp P ∧
      0 ≤ P ∧ a⁻¹ ≤ Real.exp P ∧ δ⁻¹ ≤ Real.exp P ∧ 4 ≤ Real.exp P ∧
      C * (Real.exp Qcap * εgrid + εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  intro Qcap G εgrid εlong P
  have hQ : 0 ≤ Qcap := VectorPolynomial.slicedJointDensityLogBudget_nonneg O m hPcap
  have hG : 0 ≤ G := mul_nonneg hD (le_max_right _ _)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, herr⟩ :=
    slicedSourceAccuracy_bounds hQ hG (add_nonneg hE hF)
  have hPcapP : Pcap ≤ P := le_max_left _ _
  have hP2 : 2 ≤ P := (by linarith only [hG, hE, hF] : 2 ≤ G + (E + F) + 2).trans (le_max_right _ _)
  have hPlong : G + (E + F) + 1 ≤ P :=
    (by linarith : G + (E + F) + 1 ≤ G + (E + F) + 2).trans (le_max_right _ _)
  have hprod : (∏ _i : ι, Real.exp Op) ≤ Real.exp G := by
    simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcard (le_max_right _ _))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  refine ⟨hg0, hg1, hgi, hl0, hl1, hli.trans_le (Real.exp_le_exp.mpr hPlong),
    hPcap.trans hPcapP, ha.trans (Real.exp_le_exp.mpr hPcapP),
    hδ.trans (Real.exp_le_exp.mpr hPcapP), hfour.trans (Real.exp_le_exp.mpr hP2), ?_⟩
  calc
    _ ≤ C * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_left (herr _ hprod) hC0
    _ ≤ Real.exp F * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_right hCF (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
