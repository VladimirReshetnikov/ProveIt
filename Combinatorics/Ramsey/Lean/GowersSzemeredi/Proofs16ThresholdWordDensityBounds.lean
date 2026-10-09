import GowersSzemeredi.Proofs16ThresholdWordDensity

/-! The cubic density schedule decreases with word length when the input
densities lie in the unit interval. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

theorem thresholdColumnWordDensity_step_le {lambda eta x : Real}
    (hl : 0 ≤ lambda) (hl1 : lambda ≤ 1) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : eta^2*lambda^3*x^3/128 ≤ x := by
  have he2 : eta^2 ≤ 1 := pow_le_one₀ he he1
  have hl3 : lambda^3 ≤ 1 := pow_le_one₀ hl hl1
  have hx3 : x^3 ≤ x := by simpa only [pow_one] using pow_le_pow_of_le_one hx hx1 (by norm_num : 1 ≤ 3)
  have hc : eta^2*lambda^3 ≤ 1 := (mul_le_mul he2 hl3 (by positivity) (by norm_num)).trans_eq (by ring)
  have hm := mul_le_mul hc hx3 (by positivity : 0 ≤ x^3) (by norm_num : (0 : Real) ≤ 1)
  nlinarith

theorem thresholdColumnWordDensity_le_one {lambda eta : Real}
    (hl : 0 < lambda) (hl1 : lambda ≤ 1) (he : 0 < eta) (he1 : eta ≤ 1) (k : Nat) :
    thresholdColumnWordDensity lambda eta k ≤ 1 := by
  induction k with
  | zero => exact hl1
  | succ k ih =>
    exact (thresholdColumnWordDensity_step_le hl.le hl1 he.le he1
      (thresholdColumnWordDensity_pos hl he k).le ih).trans ih

theorem thresholdColumnWordDensity_antitone {lambda eta : Real}
    (hl : 0 < lambda) (hl1 : lambda ≤ 1) (he : 0 < eta) (he1 : eta ≤ 1) :
    Antitone (thresholdColumnWordDensity lambda eta) := by
  apply antitone_nat_of_succ_le
  intro k
  exact thresholdColumnWordDensity_step_le hl.le hl1 he.le he1
    (thresholdColumnWordDensity_pos hl he k).le (thresholdColumnWordDensity_le_one hl hl1 he he1 k)

theorem thresholdColumnWordDensity_formula (lambda eta : Real) (k : Nat) :
    thresholdColumnWordDensity lambda eta k =
      (eta^2*lambda^3/128)^(∑ i ∈ Finset.range k, 3^i)*lambda^(3^k) := by
  induction k with
  | zero => simp [thresholdColumnWordDensity]
  | succ k ih =>
    have hg : (∑ i ∈ Finset.range k, (3 : Nat)^i)*2+1 = 3^k := by
      simpa using geom_sum_mul_add (2 : Nat) k
    have hs : (∑ i ∈ Finset.range k, (3 : Nat)^i)*3+1 =
        (∑ i ∈ Finset.range k, (3 : Nat)^i)+3^k := by omega
    calc thresholdColumnWordDensity lambda eta (k+1)
        = (eta^2*lambda^3/128)*
            ((eta^2*lambda^3/128)^(∑ i ∈ Finset.range k, 3^i)*lambda^(3^k))^3 := by
              rw [thresholdColumnWordDensity,ih]; ring
      _ = (eta^2*lambda^3/128)^((∑ i ∈ Finset.range k, 3^i)*3+1)*lambda^(3^k*3) := by
        simp only [pow_succ,mul_pow,pow_mul]; ring
      _ = _ := by rw [Finset.sum_range_succ,hs,pow_succ (3 : Nat) k]

end LeanProofs.GowersSzemeredi
