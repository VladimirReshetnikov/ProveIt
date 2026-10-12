import GowersSzemeredi.Proofs13SmallIntegerSquare
import GowersSzemeredi.Proofs13FourierThresholdEnvelope
import GowersSzemeredi.Proofs13FejerPrintedRange
import GowersSzemeredi.Proofs13EndpointGlobalFourier

/-! Remove the eventual-modulus restriction from Theorem 13.12.
Below the explicit extraction threshold, the printed target length is at
most two. Near maximal uniformity, a global bilinear frequency map gives
the square over every prime modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Four times the explicit threshold exponent still lies below the
printed top power, throughout the away-from-one parameter range. -/
theorem section13_printed_top_dominates_threshold {alpha : Real}
    (ha : 0 < alpha) (hau : alpha ≤ 1023 / 1024) :
    4 * (2 / alpha) ^ ((2 : Nat) ^ 54) ≤ (1 / alpha) ^ ((2 : Nat) ^ 70) := by
  let t : Real := 1 / alpha
  have ht : 1 + 1 / 1024 ≤ t := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [hau]
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hb := one_add_mul_sub_le_pow (by linarith only [ht1] : -1 ≤ t) 1024
  have ht1024 : 2 ≤ t ^ (1024 : Nat) := by
    norm_num only [Nat.cast_ofNat] at hb
    nlinarith only [ht, hb]
  have hstep : 2 * t ≤ t ^ (1025 : Nat) := by
    calc
      _ ≤ t ^ (1024 : Nat) * t := mul_le_mul_of_nonneg_right ht1024 ht0
      _ = _ := (pow_succ _ _).symm
  have hfour : (4 : Real) ≤ t ^ (2048 : Nat) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) ht1024 2
    simpa only [← pow_mul, show (1024 : Nat) * 2 = 2048 by omega,
      show (2 : Real) ^ (2 : Nat) = 4 by norm_num] using h
  have hbase : 2 / alpha = 2 * t := by dsimp [t]; ring
  rw [hbase]
  calc
    4 * (2 * t) ^ ((2 : Nat) ^ 54) ≤
        t ^ (2048 : Nat) * (t ^ (1025 : Nat)) ^ ((2 : Nat) ^ 54) :=
      mul_le_mul hfour (pow_le_pow_left₀ (by positivity) hstep _)
        (by positivity) (by positivity)
    _ = t ^ (2048 + 1025 * (2 : Nat) ^ 54) := by rw [← pow_mul, ← pow_add]
    _ ≤ t ^ ((2 : Nat) ^ 70) := pow_le_pow_right₀ ht1 (by norm_num)

/-- A generic comparison avoids expanding the enormous powers in the
printed exponent: below exp(exp(x)), the target side length is at most two
whenever its inverse exponent is at least `2^(4*x)`. -/
theorem rpow_small_below_double_exp {x y n : Real} (hx : 2 ≤ x)
    (hy : 4 * x ≤ y) (hn : 1 ≤ n) (hupper : n ≤ Real.exp (Real.exp x)) :
    n ^ ((1 / 2 : Real) ^ y) ≤ 2 := by
  have hn0 : 0 < n := by linarith only [hn]
  have hy0 : 0 ≤ y := by linarith only [hx, hy]
  have hlog2 : (1 / 2 : Real) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num only [invOf_eq_inv] at h
    norm_num at h ⊢
    exact h
  have hlogn : Real.log n ≤ Real.exp x := by
    have h := Real.log_le_log hn0 hupper
    simpa only [Real.log_exp] using h
  have he0 : 0 ≤ (1 / 2 : Real) ^ y := Real.rpow_nonneg (by norm_num) _
  have heq : (1 / 2 : Real) ^ y * Real.exp x = Real.exp (x - Real.log 2 * y) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 1 / 2)]
    have hhalf : Real.log (1 / 2 : Real) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [hhalf, ← Real.exp_add]
    congr 1
    ring
  have hexp : x - Real.log 2 * y ≤ -x := by
    have hmul := mul_le_mul_of_nonneg_right hlog2 hy0
    nlinarith only [hy, hmul]
  have hsmall : Real.exp (-x) ≤ (1 / 2 : Real) := by
    have h2 : (2 : Real) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp (2 : Real)
      linarith only [h]
    have hanti := inv_anti₀ (by norm_num : (0 : Real) < 2) h2
    rw [Real.exp_neg]
    exact (inv_anti₀ (Real.exp_pos _) (Real.exp_le_exp.mpr hx)).trans
      (by simpa only [inv_eq_one_div] using hanti)
  have hproduct : Real.log n * (1 / 2 : Real) ^ y ≤ Real.log 2 := by
    calc
      _ = (1 / 2 : Real) ^ y * Real.log n := mul_comm _ _
      _ ≤ (1 / 2 : Real) ^ y * Real.exp x := mul_le_mul_of_nonneg_left hlogn he0
      _ = Real.exp (x - Real.log 2 * y) := heq
      _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr hexp
      _ ≤ 1 / 2 := hsmall
      _ ≤ Real.log 2 := hlog2
  rw [Real.rpow_def_of_pos hn0]
  exact (Real.exp_le_exp.mpr hproduct).trans_eq (Real.exp_log (by norm_num))

theorem section13_printed_width_small_below_threshold {alpha : Real}
    (ha : 0 < alpha) (hau : alpha ≤ 1023 / 1024) {N : Nat} [NeZero N]
    (hN : (N : Real) ≤ Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54)))) :
    (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ 2 := by
  have hbase : 2 ≤ 2 / alpha := (le_div_iff₀ ha).mpr (by linarith only [hau])
  have hx : 2 ≤ (2 / alpha) ^ ((2 : Nat) ^ 54) := by
    calc
      2 = (2 : Real) ^ (1 : Nat) := by norm_num
      _ ≤ (2 / alpha) ^ (1 : Nat) := pow_le_pow_left₀ (by norm_num) hbase _
      _ ≤ _ := pow_le_pow_right₀ (by linarith only [hbase]) (by norm_num)
  exact rpow_small_below_double_exp hx (section13_printed_top_dominates_threshold ha hau)
    (by exact_mod_cast NeZero.pos N) hN

/-- A wider near-one range already has a genuine global integer square,
with no modulus threshold. -/
theorem theorem_13_12_integer_near_one {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (hnear : 333 / 334 < alpha) (ha1 : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step ≠ 0 ∧ P.step = Q.step ∧ P.HasIntegerRepresentatives ∧
      Q.HasIntegerRepresentatives ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  classical
  have ha : 0 < alpha := by linarith only [hnear]
  have hmean : 1 - (1 - alpha) ≤ endpointCubeMean f 4 := by
    have hgt := lt_of_not_ge ((uniformOfDegree_iff_endpointCubeMean (d := 3) f alpha).not.mp hnot)
    linarith only [hgt]
  obtain ⟨c, B, hmass, hfourier⟩ := endpoint_global_fourier f hf (1 - alpha) hmean
  let P : ModAP N := modInterval N 0 N
  have hPuniv : P.carrier = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    exact Finset.mem_image.mpr ⟨⟨y.val, ZMod.val_lt y⟩, Finset.mem_univ _, by
      simp [P, modInterval]⟩
  have hPgeo : P.HasIntegerRepresentatives := by
    let Q : NatAP := ⟨0, 1, N⟩
    have h := Q.toModAP_hasIntegerRepresentatives_of_bound (by simp [Q]) (by
      intro i hi; simpa only [Q, zero_add, mul_one] using hi)
    simpa only [Q, P, NatAP.toModAP, modInterval, Nat.cast_zero, Nat.cast_one] using h
  let phi : Pair N → ZMod N := fun z => c * z.1 * z.2
  refine ⟨P, P, B, phi, by simp [P, modInterval], rfl, hPgeo, hPgeo, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have he : (1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70)) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos N) he).trans_eq
      (by rw [Real.rpow_one]; rfl)
  · rw [hPuniv]
    intro z _
    simp [Finset.product]
  · have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (1 / 256 : Real) := by
      have hE : 8 ≤ (2 : Nat) ^ 76 := by have h := Nat.lt_two_pow_self (n := 76); omega
      calc
        _ ≤ (alpha / 2) ^ (8 : Nat) :=
          pow_le_pow_of_le_one (by positivity) (by linarith only [ha1]) hE
        _ ≤ (1 / 2 : Real) ^ (8 : Nat) :=
          pow_le_pow_left₀ (by positivity) (by linarith only [ha1]) _
        _ = 1 / 256 := by norm_num
    have hcoefficient : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ 1 - 332 * (1 - alpha) :=
      (show ∀ a b : Real, 333 / 334 < a → b ≤ 1 / 256 → b ≤ 1 - 332 * (1 - a) from by
        intro a b h1 h2; linarith only [h1, h2]) _ _ hnear hcoef
    change (alpha / 2) ^ ((2 : Nat) ^ 76) * (N : Real) * N ≤ B.card
    calc
      _ = (alpha / 2) ^ ((2 : Nat) ^ 76) * (N : Real) ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ (1 - 332 * (1 - alpha)) * (N : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
      _ ≤ _ := hmass
  · exact ⟨phi, ⟨0, 0, 0, c, by intro z; simp [phi]⟩, fun _ _ => rfl⟩
  · intro z hz
    have hcoefficient : alpha / 2 ≤ 3 / 4 - 4 * (1 - alpha) := by linarith only [hnear, ha1]
    have hscaled := mul_le_mul_of_nonneg_right hcoefficient (Nat.cast_nonneg N : (0 : Real) ≤ N)
    have hgood := hfourier z hz
    change alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (c * z.1 * z.2)‖
    nlinarith only [hscaled, hgood]

/-- The printed modulus range of Theorem 13.12 is valid over every prime.
This removes the extra eventual threshold in the catalogue. The large-width
branch's genuine integer geometry remains a separate obligation. -/
theorem theorem_13_12_all_prime {N : Nat} [NeZero N] [Fact N.Prime]
    (alpha : Real) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (f : ZMod N → Complex) (hf : DiscValued f) (hnot : ¬ UniformOfDegree f alpha 3) :
    ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
      P.step ≠ 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
      (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
      B ⊆ P.carrier.product Q.carrier ∧
      (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
      BilinearOn (P.carrier.product Q.carrier) phi ∧
      ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  by_cases hnear : 333 / 334 < alpha
  · obtain ⟨P, Q, B, phi, h1, h2, hP, hQ, h3, h4, h5, h6, h7, h8⟩ :=
      theorem_13_12_integer_near_one alpha hnear ha1 f hf hnot
    exact ⟨P, Q, B, phi, h1, h2, hP.isProper, hQ.isProper, h3, h4, h5, h6, h7, h8⟩
  have hau : alpha ≤ 1023 / 1024 := by linarith only [hnear]
  by_cases hsmall : (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ 2
  · obtain ⟨P, Q, B, phi, h1, h2, hP, hQ, h3, h4, h5, h6, h7, h8⟩ :=
      theorem_13_12_integer_small alpha ha ha1 hsmall f hf hnot
    exact ⟨P, Q, B, phi, h1, h2, hP.isProper, hQ.isProper, h3, h4, h5, h6, h7, h8⟩
  have hN : Real.exp (Real.exp ((2 / alpha) ^ ((2 : Nat) ^ 54))) ≤ N := by
    by_contra h
    exact hsmall (section13_printed_width_small_below_threshold ha hau (le_of_not_ge h))
  obtain ⟨P, Q, B, phi, h1, h2, hP, hQ, h3, h4, h5, h6, h7, h8⟩ :=
    theorem_13_12_fejer_double_exponential alpha ha ha1 N hN f hf hnot
  refine ⟨P, Q, B, phi, bne_iff_ne.mp h1, h2, hP, hQ, h3, ?_, h5, ?_, h7, h8⟩
  · exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos N)
      (section13_fejer_printed_exponent_comparison ha hau)).trans h4
  · have hcoef : (alpha / 2) ^ ((2 : Nat) ^ 76) ≤ (alpha / 2) ^ ((2 : Nat) ^ 42) :=
      pow_le_pow_of_le_one (by positivity) (by linarith only [ha1]) (by norm_num)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef
      (Nat.cast_nonneg P.length)) (Nat.cast_nonneg Q.length)).trans h6

/-- Theorem 13.12 without the catalogue's additional eventual-modulus
restriction. Genuine integer geometry in the large-width branch is not
silently included in this predicate. -/
def theorem_13_12_without_modulus_threshold : Prop :=
  ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step ≠ 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((1 / alpha) ^ ((2 : Nat) ^ 70))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖

theorem theorem_13_12_without_modulus_threshold_holds : theorem_13_12_without_modulus_threshold := by
  intro alpha ha ha1 N _ _ f hf hnot
  exact theorem_13_12_all_prime alpha ha ha1 f hf hnot

end LeanProofs.GowersSzemeredi
