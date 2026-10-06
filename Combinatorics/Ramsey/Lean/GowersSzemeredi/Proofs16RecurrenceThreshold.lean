import GowersSzemeredi.Proofs16ShortScale
import GowersSzemeredi.Proofs16Lemma1
import GowersSzemeredi.Proofs16ShortProduct

/-! # Recovering the multilinear threshold from the non-singleton width -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The Section 16 iteration exponent dominates the polynomial threshold's
inner exponent in the next dimension. -/
theorem section16_iteration_dominates_polynomial (k : Nat) :
    40 * (k + 1) ^ 3 ≤ (2 : Nat) ^ ((2 : Nat) ^ (k + 6)) := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hpow : (k + 1) ^ 3 ≤ (2 ^ k) ^ 3 := Nat.pow_le_pow_left hk 3
  have hexp : 3 * k + 6 ≤ (2 : Nat) ^ (k + 6) := by
    rw [pow_add]
    norm_num
    omega
  calc
    40 * (k + 1) ^ 3 ≤ 40 * (2 ^ k) ^ 3 := Nat.mul_le_mul_left 40 hpow
    _ ≤ 64 * (2 ^ k) ^ 3 := Nat.mul_le_mul_right _ (by norm_num)
    _ = (2 : Nat) ^ (3 * k + 6) := by rw [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hexp

/-- The reciprocal radius is sufficiently large to cover the base of the
rounding-safe simultaneous multilinear threshold. -/
theorem section16_polynomial_threshold_le_radius {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    (2 * polynomialPartitionThreshold (k + 1) : Nat) ≤
      (2 / section16Zeta theta gamma k) ^ (2 : Nat) := by
  let W : Nat := 2 ^ (40 * (k + 1) ^ 3)
  let S := multipleS theta gamma k
  have hp : 0 < theta * gamma := mul_pos ht hg
  have hb : (2 : Real) ≤ 2 / (theta * gamma) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hS : (W : Real) ≤ S := by
    dsimp only [W]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ (2 : Real) ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 6))) :=
        pow_le_pow_right₀ (by norm_num) (section16_iteration_dominates_polynomial k)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hb _
  have hleft : ((2 * polynomialPartitionThreshold (k + 1) : Nat) : Real) =
      (2 : Real) ^ (1 + 2 * (W : Real)) := by
    unfold polynomialPartitionThreshold weylThreshold
    push_cast
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one,
      mul_comm (2 : Real) (W : Real), Real.rpow_mul (by norm_num : (0 : Real) ≤ 2),
      Real.rpow_natCast, Real.rpow_ofNat]
  have hright : (2 / section16Zeta theta gamma k) ^ (2 : Nat) =
      (2 : Real) ^ (2 + 2 * S) := by
    unfold section16Zeta
    change (2 / (2 : Real) ^ (-S)) ^ (2 : Nat) = _
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), div_inv_eq_mul, mul_pow,
      ← Real.rpow_natCast ((2 : Real) ^ S) 2, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2)]
    rw [Real.rpow_add (by norm_num : (0 : Real) < 2)]
    norm_num [mul_comm]
  rw [hleft, hright]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- The simultaneous threshold is equivalent to its base threshold after
taking the positive recurrence root. -/
theorem section16WidthThreshold_of_root {k q m : Nat} (hk : 1 ≤ k)
    (hm : 0 < m)
    (hroot : (2 * polynomialPartitionThreshold (k + 1) : Nat) ≤
      (m : Real) ^ section16RecurrenceExponent k q) :
    section16WidthThreshold k q ≤ m := by
  let E := section16K k ^ (2 ^ (k + 1) * q)
  have hK : 0 < section16K k := by unfold section16K; positivity
  have hE : (0 : Real) < E := by exact_mod_cast (show 0 < E by dsimp [E]; positivity)
  have hmr : (0 : Real) < m := by exact_mod_cast hm
  have he : section16RecurrenceExponent k q = (E : Real)⁻¹ := by
    simp only [section16RecurrenceExponent, zpow_neg, zpow_natCast, E, Nat.cast_pow]
  have hmEq : ((m : Real) ^ section16RecurrenceExponent k q) ^ E = m := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hmr.le,
      inv_mul_cancel₀ hE.ne', Real.rpow_one]
  have hpow := pow_le_pow_left₀
    (Nat.cast_nonneg (2 * polynomialPartitionThreshold (k + 1)) : (0 : Real) ≤ _) hroot E
  rw [hmEq] at hpow
  change (2 * polynomialPartitionThreshold (k + 1)) ^ E ≤ m
  exact_mod_cast hpow

/-- When the target width exceeds one, its radius factor forces the full
multilinear threshold; the complementary case can use singleton cells. -/
theorem section16_threshold_of_large_width {theta gamma : Real} {k q m : Nat}
    (hk : 1 ≤ k) (hm : 0 < m)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hlarge : 1 < (section16Zeta theta gamma k / 2) *
      Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q)) :
    section16WidthThreshold k q ≤ m := by
  have hz := (section16Zeta_pos_le_half k ht ht1 hg hg1).1
  have hmr : (0 : Real) < m := by exact_mod_cast hm
  have hs : 0 < (m : Real) ^ section16RecurrenceExponent k q := Real.rpow_pos_of_pos hmr _
  have hroot : 2 / section16Zeta theta gamma k ≤
      Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q) := by
    apply (div_le_iff₀ hz).mpr
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / section16Zeta theta gamma k) hroot 2
  rw [Real.sq_sqrt hs.le] at hsq
  exact section16WidthThreshold_of_root hk hm
    ((section16_polynomial_threshold_le_radius k ht ht1 hg hg1).trans hsq)

/-- The non-singleton part of the local Lemma 16.6 construction, with
its threshold and rounded short-cell budgets discharged. -/
theorem section16_local_linearity_above_one {N k q m : Nat} [NeZero N]
    (hk : 1 ≤ k) (hm : 0 < m) (theta gamma : Real)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (P : Box N (k + 1)) (hP : P.IsProper) (hmP : m ≤ P.width)
    (mu : Fin q → Point N k → ZMod N) (hmu : ∀ i, IsMultilinear (mu i))
    (K : Point N k → Finset (ZMod N)) (G : Finset (Point N k))
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
    (hcover : ∀ x ∈ (boxInit P).carrier, x ∈ G → ∀ r ∈ K x, ∃ i, r = mu i x)
    (hlinear : ∀ x ∈ G, ∀ v : Nat, 0 < v → ∀ I : ModAP N, I.length ≤ v →
      I.step ∈ bohr (K x) (section16Zeta theta gamma k / v) →
      LinearOn (I.carrier ∩ A x) (f x))
    (hlarge : 1 < (section16Zeta theta gamma k / 2) *
      Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q)) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (section16Zeta theta gamma k / 2) *
        Real.sqrt ((m : Real) ^ section16RecurrenceExponent k q) ≤ (Q j).width) ∧
      ∀ j x, x ∈ (boxInit (Q j)).carrier → x ∈ G →
        LinearOn (((Q j).axis (Fin.last k)).carrier.filter fun y => y ∈ A x) (f x) := by
  have hmr : (0 : Real) < m := by exact_mod_cast hm
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  obtain ⟨v, hv, hvwidth, hvscale, hvbudget⟩ := section16_short_scale
    ((m : Real) ^ section16RecurrenceExponent k q) (section16Zeta theta gamma k)
    (Real.rpow_pos_of_pos hmr _) hz hzHalf hlarge
  have hthreshold := section16_threshold_of_large_width hk hm ht ht1 hg hg1 hlarge
  have hbudget : 2 * (m : Real) ^ (-section16RecurrenceExponent k q) ≤ section16Zeta theta gamma k / v := by
    simpa only [Real.rpow_neg hmr.le, div_eq_mul_inv] using hvbudget
  obtain ⟨M, Q, hpart, hproper, hwidth, hlin⟩ := proper_short_product_linearity
    hk P hP mu hmu hthreshold hmP hv hvscale K (section16Zeta theta gamma k) G A f
    hcover (fun x hx I hI hd => hlinear x hx v (by omega) I hI hd) hbudget
  refine ⟨M, Q, hpart, hproper, ?_, hlin⟩
  intro j
  exact hvwidth.trans (by exact_mod_cast hwidth j)

end LeanProofs.GowersSzemeredi
