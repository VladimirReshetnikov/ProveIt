import DiophantineConsistency.SplitGeometry59
import DiophantineConsistency.SplitWordBounds
import Mathlib.Tactic.Linarith

/-!
# Literal report59 split116 kernels

Generated from SHA-pinned split_kernels.json by generate_split_kernels59.py.
All four native ports remain parameters. These are the actual89 polynomial
coefficient recipes, with degree ceilings and a sharp generic box bound.
-/
namespace DiophantineConsistency.SplitKernelData59

open Polynomial
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def sparseKernel (e : Fin n → ℕ) (a : Fin n → R) : R[X] :=
  ∑ i, monomial (e i) (a i)

theorem coeff_sparseKernel (e : Fin n → ℕ) (he : Function.Injective e)
    (a : Fin n → R) (i : Fin n) : (sparseKernel e a).coeff (e i) = a i := by
  classical
  simp only [sparseKernel, finsetSum_coeff, coeff_monomial, he.eq_iff]
  simp

theorem sparseKernel_degree (e : Fin n → ℕ) (a : Fin n → R) {d : ℕ}
    (hd : ∀ i, e i ≤ d) : (sparseKernel e a).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp only [sparseKernel, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro i _
  have hne : e i ≠ j := by have hi := hd i; omega
  exact if_neg hne

theorem sparseKernel_height (e : Fin n → ℕ) (he : Function.Injective e)
    (a : Fin n → ℤ) {H : ℤ} (hH : 0 ≤ H) (ha : ∀ i, |a i| ≤ H) (j : ℕ) :
    |(sparseKernel e a).coeff j| ≤ H := by
  classical
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [coeff_sparseKernel e he]
    exact ha i
  · have hz : (sparseKernel e a).coeff j = 0 := by
      simp only [sparseKernel, finsetSum_coeff, coeff_monomial]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun hi => hj ⟨i,hi⟩)
    simpa only [hz,abs_zero] using hH

def positions0 : Fin 7 → ℕ := ![28,
    85,
    286,
    384,
    906,
    1083,
    1719]

def coefficients0 (ports : Fin 4 → R) : Fin 7 → R := ![(-2),
    (-2),
    (-2),
    ((2) * ports 1),
    (-2),
    (-2),
    (-6)]

theorem positions0_injective : Function.Injective positions0 := by decide +kernel

theorem positions0_le : ∀ i, positions0 i ≤ 1719 := by decide +kernel

noncomputable def D0 (ports : Fin 4 → R) : R[X] := sparseKernel positions0 (coefficients0 ports)

theorem degree_D0 (ports : Fin 4 → R) : (D0 ports).natDegree ≤ 1719 :=
  sparseKernel_degree _ _ positions0_le

def positions1 : Fin 39 → ℕ := ![1,
    26,
    27,
    293,
    323,
    377,
    383,
    502,
    540,
    543,
    547,
    551,
    608,
    619,
    639,
    810,
    814,
    826,
    957,
    1115,
    1122,
    1175,
    1333,
    1354,
    1356,
    1444,
    1470,
    1566,
    1582,
    1603,
    1631,
    1659,
    1788,
    1873,
    1879,
    1997,
    2011,
    2020,
    2027]

def coefficients1 (ports : Fin 4 → R) : Fin 39 → R := ![(-2),
    (2),
    ((-2) * ports 0),
    (2),
    ((-2) * ports 1),
    (-2 + (-2) * ports 1),
    ((2) * ports 0 + (2) * ports 0 * ports 1),
    (-2),
    (2),
    (-6),
    (2),
    (2),
    (-2),
    (2),
    (2),
    (2),
    (2),
    (2),
    (2),
    (2),
    (-2),
    (2),
    (2),
    (2),
    (2),
    (2),
    ((-4) * ports 0),
    (2),
    (-2),
    (-8),
    (2),
    (2),
    (-2),
    (-2),
    ((-2) * ports 3 + (-2) * ports 2 + (2) * ports 0),
    (2),
    (-2),
    (2),
    (-2)]

theorem positions1_injective : Function.Injective positions1 := by decide +kernel

theorem positions1_le : ∀ i, positions1 i ≤ 2027 := by decide +kernel

noncomputable def D1 (ports : Fin 4 → R) : R[X] := sparseKernel positions1 (coefficients1 ports)

theorem degree_D1 (ports : Fin 4 → R) : (D1 ports).natDegree ≤ 2027 :=
  sparseKernel_degree _ _ positions1_le

def positions2 : Fin 43 → ℕ := ![0,
    27,
    39,
    66,
    80,
    96,
    260,
    289,
    343,
    347,
    365,
    378,
    427,
    607,
    648,
    712,
    751,
    782,
    908,
    968,
    977,
    998,
    1218,
    1232,
    1386,
    1466,
    1469,
    1473,
    1482,
    1487,
    1489,
    1700,
    1725,
    1792,
    1846,
    1871,
    1872,
    1877,
    1878,
    1886,
    1902,
    1922,
    1929]

def coefficients2 (ports : Fin 4 → R) : Fin 43 → R := ![((-(ports 0))),
    (2),
    (-1),
    (-2),
    (1),
    (1),
    (2),
    (-1),
    (-1),
    ((-(ports 0))),
    (-1),
    (-2),
    (-4),
    ((-(ports 0))),
    (-1),
    (-1),
    (-1),
    (2),
    (-2),
    (-1),
    (2),
    (-2),
    (-1),
    (-1),
    (-1),
    (-1),
    ((-2) * ports 0 ^ 2),
    (1),
    (-1),
    (-2),
    (1),
    (-2),
    (1),
    (-1),
    (-1),
    (1),
    ((-(ports 0))),
    ((-(ports 0))),
    ((-2) * ports 0 * ports 3 + (2) * ports 0 ^ 2),
    (-1),
    (1),
    (-1),
    (1)]

theorem positions2_injective : Function.Injective positions2 := by decide +kernel

theorem positions2_le : ∀ i, positions2 i ≤ 1929 := by decide +kernel

noncomputable def D2 (ports : Fin 4 → R) : R[X] := sparseKernel positions2 (coefficients2 ports)

theorem degree_D2 (ports : Fin 4 → R) : (D2 ports).natDegree ≤ 1929 :=
  sparseKernel_degree _ _ positions2_le

theorem leading_D2 (ports : Fin 4 → R) : (D2 ports).coeff 1929 = 1 := by
  change (sparseKernel positions2 (coefficients2 ports)).coeff (positions2 42) = 1
  rw [coeff_sparseKernel _ positions2_injective]
  rfl

theorem kernelBounds_of_records (ports : Fin 4 → ℤ) (H : ℤ) (hH : 0 ≤ H)
    (h0 : ∀ i, |coefficients0 ports i| ≤ H)
    (h1 : ∀ i, |coefficients1 ports i| ≤ H)
    (h2 : ∀ i, |coefficients2 ports i| ≤ H) :
    SplitWordBounds.KernelBounds (D0 ports) (D1 ports) (D2 ports) H :=
  ⟨degree_D0 ports,degree_D1 ports,degree_D2 ports,
    sparseKernel_height _ positions0_injective _ hH h0,
    sparseKernel_height _ positions1_injective _ hH h1,
    sparseKernel_height _ positions2_injective _ hH h2,leading_D2 ports⟩

private theorem box_facts (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ports 0 ^ 2 ≤ B ^ 2 ∧ ports 3 * ports 0 ≤ 2*B^2 ∧
      ports 0 * (ports 1+1) < B*K ∧ 16*B^2 ≤ B*K := by
  have hsq : ports 0 ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hb.1 (by omega)).mpr hb.2.le
  have hp : ports 3 * ports 0 ≤ 2*B^2 := by
    calc
      _ ≤ (2*B)*B := mul_le_mul hf.2.le hb.2.le hb.1 (by omega)
      _ = _ := by ring
  have hl : ports 0 * (ports 1+1) < B*K := by
    calc
      _ ≤ ports 0*K := mul_le_mul_of_nonneg_left (by omega) hb.1
      _ < B*K := mul_lt_mul_of_pos_right hb.2 (by omega)
  refine ⟨hsq,hp,hl,?_⟩
  nlinarith [mul_nonneg (by omega : 0 ≤ B) (sub_nonneg.mpr hK)]

/-- Arithmetic facts shared by the two kernel coefficient bounds. -/
theorem port_box_facts (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ports 0 ^ 2 ≤ B ^ 2 ∧ ports 3 * ports 0 ≤ 2*B^2 ∧
      ports 0 * (ports 1+1) < B*K ∧ 16*B^2 ≤ B*K :=
  box_facts ports B K hB hK hb hk hm hf

theorem records0_lt (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ∀ i, |coefficients0 ports i| < 2*B*K := by
  obtain ⟨hsq,hp,hl,hBK⟩ := box_facts ports B K hB hK hb hk hm hf
  have hb0 := hb.1
  have hb1 := hb.2
  have hk0 := hk.1
  have hk1 := hk.2
  have hm0 := hm.1
  have hm1 := hm.2
  have hf0 := hf.1
  have hf1 := hf.2
  intro i
  fin_cases i <;> dsimp [coefficients0] <;> rw [abs_lt] <;> constructor <;>
    nlinarith only [hB,hK,hb0,hb1,hk0,hk1,hm0,hm1,hf0,hf1,hsq,hp,hl,hBK,sq_nonneg B]

theorem records1_lt (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ∀ i, |coefficients1 ports i| < 2*B*K := by
  obtain ⟨hsq,hp,hl,hBK⟩ := box_facts ports B K hB hK hb hk hm hf
  have hb0 := hb.1
  have hb1 := hb.2
  have hk0 := hk.1
  have hk1 := hk.2
  have hm0 := hm.1
  have hm1 := hm.2
  have hf0 := hf.1
  have hf1 := hf.2
  intro i
  fin_cases i <;> dsimp [coefficients1] <;> rw [abs_lt] <;> constructor <;>
    nlinarith only [hB,hK,hb0,hb1,hk0,hk1,hm0,hm1,hf0,hf1,hsq,hp,hl,hBK,sq_nonneg B]

theorem records2_lt (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    ∀ i, |coefficients2 ports i| < 2*B*K := by
  obtain ⟨hsq,hp,hl,hBK⟩ := box_facts ports B K hB hK hb hk hm hf
  have hb0 := hb.1
  have hb1 := hb.2
  have hk0 := hk.1
  have hk1 := hk.2
  have hm0 := hm.1
  have hm1 := hm.2
  have hf0 := hf.1
  have hf1 := hf.2
  intro i
  fin_cases i <;> dsimp [coefficients2] <;> rw [abs_lt] <;> constructor <;>
    nlinarith only [hB,hK,hb0,hb1,hk0,hk1,hm0,hm1,hf0,hf1,hsq,hp,hl,hBK,sq_nonneg B]

theorem kernelBounds_box (ports : Fin 4 → ℤ) (B K : ℤ)
    (hB : 2 ≤ B) (hK : 16*B ≤ K)
    (hb : 0 ≤ ports 0 ∧ ports 0 < B)
    (hk : 0 ≤ ports 1 ∧ ports 1 < K)
    (hm : 0 ≤ ports 2 ∧ ports 2 < B)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*B) :
    SplitWordBounds.KernelBounds (D0 ports) (D1 ports) (D2 ports) (2*B*K) := by
  apply kernelBounds_of_records ports (2*B*K) (by have hBK := hK; nlinarith)
  · exact fun i => (records0_lt ports B K hB hK hb hk hm hf i).le
  · exact fun i => (records1_lt ports B K hB hK hb hk hm hf i).le
  · exact fun i => (records2_lt ports B K hB hK hb hk hm hf i).le

end DiophantineConsistency.SplitKernelData59
