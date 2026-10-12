import GowersSzemeredi.Proofs16IntegerSourceBudget

/-! The numerical obstruction to an unrestricted loss parameter in Lemma 16.6.
For sufficiently large positive loss the allowed graph count is below one,
while the required width exceeds the input width, already at input width two. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The numbered graph and width budgets cannot hold uniformly over every
positive loss. This statement concerns the numerical requirements themselves. -/
theorem section16Lemma6_uncapped_loss_width_obstruction (k : Nat)
    {delta theta1 zeta : Real} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (ht : 0 < theta1) (ht1 : theta1 ≤ 1) (hz : 0 < zeta) :
    ∃ sigma : Real, 0 < sigma ∧ ∀ q : Nat,
      (q : Real) ≤ section16Lemma6QBound sigma delta theta1 k →
      2 < section16Lemma6Width 2 q k sigma delta theta1 zeta := by
  let t := section16T delta theta1 k
  have ht16 : 16 ≤ t := section16T_sixteen_le k hd hd1 ht ht1
  have ht0 : 0 < t := by linarith
  let n : Nat := ⌈4 / zeta⌉₊ + 1
  have hn : (1 : Real) ≤ n := by
    exact_mod_cast (show 1 ≤ n by dsimp [n]; omega)
  have hnlarge : 4 / zeta < (n : Real) := by
    have h := Nat.le_ceil (4 / zeta)
    dsimp [n]
    push_cast
    linarith
  let sigma := t / delta * (2 * (n : Real))
  have hs : 0 < sigma := by dsimp [sigma]; positivity
  have hbase : delta * (sigma / t) = 2 * (n : Real) := by
    dsimp [sigma]
    field_simp [hd.ne', ht0.ne']
  let c := multipleC (sigma / t) delta k
  have hc : 2 * (n : Real) ≤ c := by
    dsimp [c, multipleC]
    rw [hbase]
    exact le_self_pow₀ (by linarith) (by positivity)
  have hc1 : 1 ≤ c := by linarith
  let a : Real := c ^ t
  have ha : 2 * (n : Real) ≤ a :=
    hc.trans (Real.self_le_rpow_of_one_le hc1 (by linarith))
  have ha0 : 0 < a := by linarith
  have hbudget : section16Lemma6QBound sigma delta theta1 k = a⁻¹ := by
    change c⁻¹ ^ t = (c ^ t)⁻¹
    exact Real.inv_rpow (by linarith) t
  have hbudget1 : section16Lemma6QBound sigma delta theta1 k < 1 := by
    rw [hbudget]
    exact (inv_lt_one₀ ha0).mpr (by linarith)
  refine ⟨sigma, hs, ?_⟩
  intro q hq
  have hq0 : q = 0 := by
    have hq1 : (q : Real) < 1 := hq.trans_lt hbudget1
    have : q < 1 := by exact_mod_cast hq1
    omega
  subst q
  have hnPow : (n : Real) < (2 : Real) ^ n := by
    exact_mod_cast (show n < 2 ^ n from Nat.lt_two_pow_self)
  have hpow : (2 : Real) ^ n ≤ (2 : Real) ^ (a / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlarge : 4 / zeta < (2 : Real) ^ (a / 2) :=
    hnlarge.trans (hnPow.trans_le hpow)
  have hproduct : 4 < (2 : Real) ^ (a / 2) * zeta := (div_lt_iff₀ hz).mp hlarge
  change 2 < zeta / 2 * (2 : Real) ^ (a / (2 * (section16K k : Real) ^ (2 ^ (k + 1) * 0)))
  simp only [Nat.mul_zero, pow_zero, mul_one]
  nlinarith

/-- The obstruction persists at arbitrary moduli: a nonempty input box with
an axis of size at most two cannot have all its nonempty subboxes wider than two. -/
theorem section16Lemma6_uncapped_loss_small_box_false {N : Nat} [NeZero N] (k : Nat)
    {delta theta1 zeta : Real} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (ht : 0 < theta1) (ht1 : theta1 ≤ 1) (hz : 0 < zeta)
    (P : Box N (k + 1)) (hP : P.carrier.Nonempty)
    (haxis : (P.axis 0).carrier.card ≤ 2) :
    ¬ (∀ sigma : Real, 0 < sigma → ∃ q : Nat,
      (q : Real) ≤ section16Lemma6QBound sigma delta theta1 k ∧
      ∃ M : Nat, ∃ S : Fin M → Box N (k + 1),
        IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
        ∀ u, section16Lemma6Width 2 q k sigma delta theta1 zeta ≤ (S u).width) := by
  intro h
  obtain ⟨sigma, hs, hlarge⟩ := section16Lemma6_uncapped_loss_width_obstruction k hd hd1 ht ht1 hz
  obtain ⟨q, hq, M, S, hpart, hproper, hwidth⟩ := h sigma hs
  obtain ⟨x, hx⟩ := hP
  obtain ⟨u, hxu⟩ := (hpart.1 x).mp hx
  have hsub := (S u).axis_carrier_subset_of_carrier_subset P ⟨x, hxu⟩
    (IsPartition.cell_subset hpart u) 0
  have hcap : ((S u).width : Real) ≤ 2 := by
    exact_mod_cast ((S u).width_le_axis_card (hproper u) 0).trans
      ((Finset.card_mono hsub).trans haxis)
  exact (not_lt_of_ge ((hwidth u).trans hcap)) (hlarge q hq)

/-- Already over the two-element cyclic group, no partition of a nonempty
box can satisfy both numbered budgets for every positive loss. -/
theorem section16Lemma6_uncapped_loss_partition_false (k : Nat)
    {delta theta1 zeta : Real} (hd : 0 < delta) (hd1 : delta ≤ 1)
    (ht : 0 < theta1) (ht1 : theta1 ≤ 1) (hz : 0 < zeta)
    (P : Box 2 (k + 1)) (hP : P.carrier.Nonempty) :
    ¬ (∀ sigma : Real, 0 < sigma → ∃ q : Nat,
      (q : Real) ≤ section16Lemma6QBound sigma delta theta1 k ∧
      ∃ M : Nat, ∃ S : Fin M → Box 2 (k + 1),
        IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
        ∀ u, section16Lemma6Width 2 q k sigma delta theta1 zeta ≤ (S u).width) := by
  intro h
  obtain ⟨sigma, hs, hlarge⟩ := section16Lemma6_uncapped_loss_width_obstruction k hd hd1 ht ht1 hz
  obtain ⟨q, hq, M, S, hpart, hproper, hwidth⟩ := h sigma hs
  obtain ⟨x, hx⟩ := hP
  obtain ⟨u, _⟩ := (hpart.1 x).mp hx
  have hcap : ((S u).width : Real) ≤ 2 := by
    exact_mod_cast (S u).width_le_modulus (hproper u)
  exact (not_lt_of_ge ((hwidth u).trans hcap)) (hlarge q hq)

end LeanProofs.GowersSzemeredi
