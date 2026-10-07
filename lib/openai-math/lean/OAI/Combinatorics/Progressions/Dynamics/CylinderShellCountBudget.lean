import OAI.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
import OAI.Combinatorics.Progressions.Estimates.WeightedListError
import OAI.Combinatorics.Progressions.Probability.DensityNormalizationScales

namespace OAI

section

namespace Erdos3

theorem uniform_section_norm_product_le_exp {τ L T : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (L + 2 * T + 4) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hM : 3 * τ⁻¹ ≤ Real.exp (T + 2) := by
    rw [Real.exp_add]
    exact (mul_le_mul h3 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hN : 3 * Real.exp (L + T) ≤ Real.exp (L + T + 2) := by
    rw [Real.exp_add (L + T) 2]
    exact (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  calc
    _ ≤ Real.exp (T + 2) * Real.exp (L + T + 2) := mul_le_mul hM hN (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem retained_shell_prefactor_le_exp {m level v τ ε L T : ℝ} {i j : ℕ}
    (_hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hl0 : 0 ≤ level) (hl2 : level ≤ 2)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) (hij : i ≤ j) :
    m * level * (v + τ) * (6 + 2 * ε) * (2 : ℝ) ^ i *
      (3 * τ⁻¹) * (3 * Real.exp (L + T)) ≤ Real.exp (ε + L + 2 * T + j + 10) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) htwo 4
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  have hbase : m * level * (v + τ) * (6 + 2 * ε) ≤ 16 * (3 + ε) := by
    calc
      _ ≤ 2 * 2 * (1 + 1) * (6 + 2 * ε) := by gcongr
      _ = _ := by ring
  have hconstant : m * level * (v + τ) * (6 + 2 * ε) ≤ Real.exp (ε + 6) := by
    apply hbase.trans
    calc
      _ ≤ Real.exp 4 * Real.exp (ε + 2) :=
        mul_le_mul h16 (by linarith [Real.add_one_le_exp (ε + 2)]) (by linarith) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : (2 : ℝ) ^ i ≤ Real.exp j := by
    calc
      _ ≤ (Real.exp 1) ^ i := pow_le_pow_left₀ (by norm_num) htwo i
      _ = Real.exp i := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr (by exact_mod_cast hij)
  have hn := uniform_section_norm_product_le_exp (L := L) hτ hτinv
  calc
    _ = (m * level * (v + τ) * (6 + 2 * ε)) * (2 : ℝ) ^ i *
        ((3 * τ⁻¹) * (3 * Real.exp (L + T))) := by ring
    _ ≤ Real.exp (ε + 6) * Real.exp j * Real.exp (L + 2 * T + 4) :=
      mul_le_mul (mul_le_mul hconstant hp (by positivity) (Real.exp_pos _).le) hn
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem list_map_sum_le_exp {α : Type*} (xs : List α) (f : α → ℝ) {U V : ℝ}
    (hlen : (xs.length : ℝ) ≤ Real.exp U) (hf : ∀ x ∈ xs, f x ≤ Real.exp V) :
    (xs.map f).sum ≤ Real.exp (U + V) := by
  have hs := list_weighted_error_sum xs f (fun _ => 1) (fun _ => 0) (Real.exp V)
    (fun x hx => by simpa using hf x hx)
  have hs' : (xs.map f).sum ≤ (xs.length : ℝ) * Real.exp V := by
    simpa [mul_comm] using hs
  exact (hs'.trans (mul_le_mul_of_nonneg_right hlen (Real.exp_pos _).le)).trans_eq (Real.exp_add U V).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.shell_prefactor_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ η P S V level v ε L T : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hη : η ≤ 1)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η j)
    (hP : 0 ≤ P) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp S)
    (hY : ∀ i, (Fintype.card (Y i) : ℝ) ≤ Real.exp V)
    (hl0 : 0 ≤ level) (hl2 : level ≤ 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hε : 0 ≤ ε)
    (hτinv : τ⁻¹ ≤ Real.exp T) :
    ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤
      Real.exp ((j : ℝ) * (P + S + V + 2) + ε + L + 2 * T + 10) := by
  have hlen := hchain.length_le_exp hτ.le (fun z => (hw z).1) hP hS hcount hX
  have hlen' : ((cs.zip (removedCylinderWeights F w cs)).length : ℝ) ≤
      Real.exp ((j : ℝ) * (P + S + 1)) := by
    simpa only [List.length_zip, removedCylinderWeights_length, min_self] using hlen
  have hmass := hchain.removed_mass_le_two hμ hw hη hclose
  have hs := list_map_sum_le_exp (cs.zip (removedCylinderWeights F w cs))
    (fun cf => (Fintype.card (∀ i : cf.1.1, Y i.val) : ℝ) *
      (cf.1.mass μ base (observedProductDensity μ p F cf.2) * level * (v + τ) * (6 + 2 * ε) *
        (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))
    (V := (j : ℝ) * V + (ε + L + 2 * T + j + 10)) hlen' (by
      intro cf hcf
      obtain ⟨hsize, hpositive⟩ := hchain.removed_size_mass cf hcf
      have hm0 := (hτ.trans hpositive).le
      have hc := partial_assignment_card_le_exp hV hY cf.1.1 hsize
      have hp := retained_shell_prefactor_le_exp (L := L) hm0 (hmass cf hcf) hl0 hl2 hv0 hv1 hτ hτ1 hε hτinv hsize
      exact (mul_le_mul hc hp (by positivity) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm)
  exact hs.trans_eq (by congr 1; ring)

end Erdos3

end

end OAI
