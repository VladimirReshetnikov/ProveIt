import ExponentialIdentities.TwoBaseIntegerExponent.AlgebraicTowerTransition
import ExponentialIdentities.TwoBaseIntegerExponent.KernelDichotomy
import ExponentialIdentities.TwoBaseIntegerExponent.Localization

/-!
# Cross-base algebraic transitions in the two power towers

This module shows that a hypothetical Alaoglu--Erdos counterexample cannot have an
algebraic adjacent pair anywhere in both the base-two and base-three towers.  It then
extends the obstruction to every rational `2,3`-unit base direction in the
multiplicatively-dependent output branch.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-- The base-three analogue of `TwoRpowAlgebraicTransition`. -/
def ThreeRpowAlgebraicTransition (x y : ℝ) : Prop :=
  IsAlgebraic ℚ ((3 : ℝ) ^ y) ∧ IsAlgebraic ℚ ((3 : ℝ) ^ (y * x))

private theorem three_rpow_eq_two_rpow_logRatio_mul (y : ℝ) :
    (3 : ℝ) ^ y = (2 : ℝ) ^ (logThreeDivLogTwo * y) := by
  rw [← two_rpow_logThreeDivLogTwo,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- A base-three transition is a base-two transition after scaling the exponent
by `log 3 / log 2`. -/
theorem threeRpowAlgebraicTransition_iff_twoRpowAlgebraicTransition_scaled
    {x y : ℝ} :
    ThreeRpowAlgebraicTransition x y ↔
      TwoRpowAlgebraicTransition x (logThreeDivLogTwo * y) := by
  rw [ThreeRpowAlgebraicTransition, TwoRpowAlgebraicTransition,
    three_rpow_eq_two_rpow_logRatio_mul,
    three_rpow_eq_two_rpow_logRatio_mul]
  ring_nf

/-- Exact base-three transition locus, in a denominator-free form: `y` starts
an algebraic adjacent base-three pair exactly when `(log 3 / log 2) * y`
belongs to the affine plane `ℚ + ℚ * (log 3 / log 2)`. -/
theorem TwoBaseNonintegerSolution.threeRpowAlgebraicTransition_iff_scaled_affine_logRatio
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {y : ℝ} :
    ThreeRpowAlgebraicTransition x y ↔
      ∃ q r : ℚ,
        logThreeDivLogTwo * y =
          (q : ℝ) + (r : ℝ) * logThreeDivLogTwo := by
  rw [threeRpowAlgebraicTransition_iff_twoRpowAlgebraicTransition_scaled,
    hx.twoRpowAlgebraicTransition_iff_affine_logRatio]

/-- A hypothetical counterexample cannot have an algebraic adjacent pair at
any positive depth in both the base-two and base-three towers.  The depths need
not be equal or consecutive. -/
theorem TwoBaseNonintegerSolution.not_baseTwo_and_baseThree_tower_transitions
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) :
    ¬ (TwoRpowAlgebraicTransition x (x ^ n) ∧
        ThreeRpowAlgebraicTransition x (x ^ m)) := by
  rintro ⟨hTwo, hThree⟩
  obtain ⟨a, b, hN⟩ :=
    (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp hTwo
  obtain ⟨c, d, hM⟩ :=
    (hx.threeRpowAlgebraicTransition_iff_scaled_affine_logRatio).mp hThree
  have hxTrans : Transcendental ℚ x :=
    transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2
  have hb : b ≠ 0 := by
    intro hb0
    subst b
    apply hxTrans
    apply IsAlgebraic.of_pow hn
    rw [hN]
    simp only [Rat.cast_zero, zero_mul, add_zero]
    exact isAlgebraic_rat ℚ a
  let L : Polynomial ℚ :=
    Polynomial.C b * Polynomial.X + Polynomial.C a
  let R : Polynomial ℚ :=
    Polynomial.C d * Polynomial.X + Polynomial.C c
  let P : Polynomial ℚ :=
    Polynomial.X ^ n * L ^ m - R ^ n
  have hLne : L ≠ 0 := by
    intro hzero
    have hdeg := congrArg Polynomial.natDegree hzero
    rw [show L.natDegree = 1 by
      exact Polynomial.natDegree_linear hb,
      Polynomial.natDegree_zero] at hdeg
    omega
  have hleftDegree : (Polynomial.X ^ n * L ^ m).natDegree = n + m := by
    rw [Polynomial.natDegree_mul
      (pow_ne_zero n Polynomial.X_ne_zero) (pow_ne_zero m hLne),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow,
      show L.natDegree = 1 by exact Polynomial.natDegree_linear hb]
    omega
  have hRdegree : R.natDegree ≤ 1 := by
    have hmul := Polynomial.natDegree_mul_le
      (p := Polynomial.C d) (q := Polynomial.X)
    simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] at hmul
    dsimp only [R]
    calc
      (Polynomial.C d * Polynomial.X + Polynomial.C c).natDegree ≤
          max (Polynomial.C d * Polynomial.X).natDegree
            (Polynomial.C c).natDegree :=
        Polynomial.natDegree_add_le _ _
      _ ≤ 1 := max_le hmul (by simp)
  have hrightDegree : (R ^ n).natDegree ≤ n := by
    rw [Polynomial.natDegree_pow]
    nlinarith
  have hdegreeLt : (R ^ n).natDegree <
      (Polynomial.X ^ n * L ^ m).natDegree := by
    rw [hleftDegree]
    omega
  have hPdegree : P.natDegree = n + m := by
    dsimp only [P]
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdegreeLt,
      hleftDegree]
  have hPne : P ≠ 0 := by
    intro hzero
    have hdeg := congrArg Polynomial.natDegree hzero
    rw [hPdegree, Polynomial.natDegree_zero] at hdeg
    omega
  have hN' :
      (b : ℝ) * logThreeDivLogTwo + (a : ℝ) = x ^ n := by
    rw [hN]
    ring
  have hM' :
      (d : ℝ) * logThreeDivLogTwo + (c : ℝ) =
        logThreeDivLogTwo * x ^ m := by
    rw [hM]
    ring
  have hpower :
      logThreeDivLogTwo ^ n * (x ^ n) ^ m =
        (logThreeDivLogTwo * x ^ m) ^ n := by
    rw [mul_pow]
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n m]
  have hPzero : Polynomial.aeval logThreeDivLogTwo P = 0 := by
    simp only [P, L, R, map_sub, map_add, map_mul, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast]
    rw [hN', hM']
    exact sub_eq_zero.mpr hpower
  exact transcendental_logThreeDivLogTwo ⟨P, hPne, hPzero⟩

/-- A hypothetical counterexample has at most one positive algebraic transition
depth in its base-three tower. -/
theorem TwoBaseNonintegerSolution.not_two_distinct_baseThree_tower_transitions
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) :
    ¬ (ThreeRpowAlgebraicTransition x (x ^ n) ∧
        ThreeRpowAlgebraicTransition x (x ^ m)) := by
  rintro ⟨hNtrans, hMtrans⟩
  obtain ⟨a, b, hN⟩ :=
    (hx.threeRpowAlgebraicTransition_iff_scaled_affine_logRatio).mp hNtrans
  obtain ⟨c, d, hM⟩ :=
    (hx.threeRpowAlgebraicTransition_iff_scaled_affine_logRatio).mp hMtrans
  have hxTrans : Transcendental ℚ x :=
    transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2
  have htheta : logThreeDivLogTwo ≠ 0 := by
    intro hzero
    have hpow := two_rpow_logThreeDivLogTwo
    rw [hzero, Real.rpow_zero] at hpow
    norm_num at hpow
  have ha : a ≠ 0 := by
    intro ha0
    subst a
    have hxpow : x ^ n = (b : ℝ) := by
      apply mul_left_cancel₀ htheta
      simpa only [Rat.cast_zero, zero_add, mul_comm] using hN
    apply hxTrans
    apply IsAlgebraic.of_pow hn
    rw [hxpow]
    exact isAlgebraic_rat ℚ b
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    have hxpow : x ^ m = (d : ℝ) := by
      apply mul_left_cancel₀ htheta
      simpa only [Rat.cast_zero, zero_add, mul_comm] using hM
    apply hxTrans
    apply IsAlgebraic.of_pow hm
    rw [hxpow]
    exact isAlgebraic_rat ℚ d
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · let L : Polynomial ℚ :=
      Polynomial.C b * Polynomial.X + Polynomial.C a
    let R : Polynomial ℚ :=
      Polynomial.C d * Polynomial.X + Polynomial.C c
    let P : Polynomial ℚ :=
      L ^ m - Polynomial.X ^ (m - n) * R ^ n
    have hsub : 0 < m - n := Nat.sub_pos_of_lt hlt
    have hPne : P ≠ 0 := by
      intro hzero
      have heval := congrArg (Polynomial.eval (0 : ℚ)) hzero
      have heval' : a ^ m = 0 := by
        simpa [P, L, R, hsub.ne'] using heval
      exact (pow_ne_zero m ha) heval'
    have hN' :
        (b : ℝ) * logThreeDivLogTwo + (a : ℝ) =
          logThreeDivLogTwo * x ^ n := by
      rw [hN]
      ring
    have hM' :
        (d : ℝ) * logThreeDivLogTwo + (c : ℝ) =
          logThreeDivLogTwo * x ^ m := by
      rw [hM]
      ring
    have hpowtheta :
        logThreeDivLogTwo ^ (m - n) * logThreeDivLogTwo ^ n =
          logThreeDivLogTwo ^ m := by
      rw [← pow_add]
      congr
      omega
    have hpower :
        (logThreeDivLogTwo * x ^ n) ^ m =
          logThreeDivLogTwo ^ (m - n) *
            (logThreeDivLogTwo * x ^ m) ^ n := by
      rw [mul_pow, mul_pow]
      have hxpower : (x ^ n) ^ m = (x ^ m) ^ n := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm n m]
      calc
        logThreeDivLogTwo ^ m * (x ^ n) ^ m =
            logThreeDivLogTwo ^ m * (x ^ m) ^ n := by rw [hxpower]
        _ = (logThreeDivLogTwo ^ (m - n) * logThreeDivLogTwo ^ n) *
            (x ^ m) ^ n := by rw [hpowtheta]
        _ = logThreeDivLogTwo ^ (m - n) *
            (logThreeDivLogTwo ^ n * (x ^ m) ^ n) := by ring
    have hPzero : Polynomial.aeval logThreeDivLogTwo P = 0 := by
      simp only [P, L, R, map_sub, map_add, map_mul, map_pow,
        Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast]
      rw [hN', hM']
      exact sub_eq_zero.mpr hpower
    exact transcendental_logThreeDivLogTwo ⟨P, hPne, hPzero⟩
  · exact hx.not_two_distinct_baseThree_tower_transitions hm hn hnm.symm
      ⟨hMtrans, hNtrans⟩

/-- A positive depth starts an algebraic adjacent pair in at least one of the
two principal (`2` or `3`) power towers. -/
def TwoOrThreeRpowAlgebraicTowerTransition (x : ℝ) (n : ℕ) : Prop :=
  TwoRpowAlgebraicTransition x (x ^ n) ∨
    ThreeRpowAlgebraicTransition x (x ^ n)

/-- Across both principal towers together, a hypothetical counterexample has
at most one positive depth that starts an algebraic adjacent pair.  The
cross-base theorem above also says that both bases cannot occur at that one
depth. -/
theorem TwoBaseNonintegerSolution.eq_of_twoOrThree_tower_transitions
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (hN : TwoOrThreeRpowAlgebraicTowerTransition x n)
    (hM : TwoOrThreeRpowAlgebraicTowerTransition x m) :
    n = m := by
  rcases hN with hTwoN | hThreeN
  · rcases hM with hTwoM | hThreeM
    · by_contra hnm
      exact hx.not_two_distinct_algebraic_tower_transitions
        hn hm hnm ⟨hTwoN, hTwoM⟩
    · exact (hx.not_baseTwo_and_baseThree_tower_transitions
        hn hm ⟨hTwoN, hThreeM⟩).elim
  · rcases hM with hTwoM | hThreeM
    · exact (hx.not_baseTwo_and_baseThree_tower_transitions
        hm hn ⟨hTwoM, hThreeN⟩).elim
    · by_contra hnm
      exact hx.not_two_distinct_baseThree_tower_transitions
        hn hm hnm ⟨hThreeN, hThreeM⟩

/-! ## All rational `2,3`-unit base directions -/

/-- The transition in the algebraic base direction `2^u * 3^v`, transported
to base two.  Its exponent is `(u + v * log_2 3) * x^n`. -/
def UnitDirectionTowerTransition (x : ℝ) (u v : ℚ) (n : ℕ) : Prop :=
  TwoRpowAlgebraicTransition x
    (((u : ℝ) + (v : ℝ) * logThreeDivLogTwo) * x ^ n)

private theorem ratAffine_logRatio_ne_zero {u v : ℚ}
    (huv : ¬ (u = 0 ∧ v = 0)) :
    (u : ℝ) + (v : ℝ) * logThreeDivLogTwo ≠ 0 := by
  intro hzero
  by_cases hv : v = 0
  · subst v
    simp only [Rat.cast_zero, zero_mul, add_zero] at hzero
    exact huv ⟨Rat.cast_eq_zero.mp hzero, rfl⟩
  · apply transcendental_logThreeDivLogTwo
    have hvR : (v : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hv
    have htheta : logThreeDivLogTwo = ((-u / v : ℚ) : ℝ) := by
      push_cast
      rw [eq_div_iff hvR]
      linear_combination hzero
    rw [htheta]
    exact isAlgebraic_rat ℚ (-u / v)

private theorem rational_of_ratAffine_mul_eq_ratAffine_of_proportional
    {x : ℝ} {u v a b : ℚ}
    (hden : (u : ℝ) + (v : ℝ) * logThreeDivLogTwo ≠ 0)
    (hrel : ((u : ℝ) + (v : ℝ) * logThreeDivLogTwo) * x =
      (a : ℝ) + (b : ℝ) * logThreeDivLogTwo)
    (hv : v ≠ 0) (hprop : v * a = b * u) :
    x = ((b / v : ℚ) : ℝ) := by
  apply mul_left_cancel₀ hden
  rw [hrel]
  have hvR : (v : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hv
  have hpropR : (v : ℝ) * (a : ℝ) = (b : ℝ) * (u : ℝ) := by
    exact_mod_cast hprop
  push_cast
  field_simp
  linear_combination hpropR

/-- Once one nonzero rational `2,3`-unit direction has an algebraic transition
at depth one, no nonzero rational `2,3`-unit direction can have a transition at
any depth `n ≥ 2`.  Thus the multiplicatively-dependent output branch has no
higher smooth-base transition hidden beyond the two principal towers. -/
theorem TwoBaseNonintegerSolution.not_higher_unitDirectionTowerTransition_of_depth_one
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    {u v s t : ℚ} (huv : ¬ (u = 0 ∧ v = 0))
    (hst : ¬ (s = 0 ∧ t = 0))
    (hdepthOne : UnitDirectionTowerTransition x u v 1)
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ UnitDirectionTowerTransition x s t n := by
  intro hdepthN
  obtain ⟨a, b, hOne⟩ :=
    (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp hdepthOne
  obtain ⟨c, d, hN⟩ :=
    (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mp hdepthN
  simp only [pow_one] at hOne
  have hxTrans : Transcendental ℚ x :=
    transcendental_of_not_integer_of_two_rpow_integer hx.1.1 hx.2
  have hDval : (u : ℝ) + (v : ℝ) * logThreeDivLogTwo ≠ 0 :=
    ratAffine_logRatio_ne_zero huv
  have hEval : (s : ℝ) + (t : ℝ) * logThreeDivLogTwo ≠ 0 :=
    ratAffine_logRatio_ne_zero hst
  let D : Polynomial ℚ :=
    Polynomial.C v * Polynomial.X + Polynomial.C u
  let N : Polynomial ℚ :=
    Polynomial.C b * Polynomial.X + Polynomial.C a
  let E : Polynomial ℚ :=
    Polynomial.C t * Polynomial.X + Polynomial.C s
  let G : Polynomial ℚ :=
    Polynomial.C d * Polynomial.X + Polynomial.C c
  have hDeval : Polynomial.aeval logThreeDivLogTwo D =
      (u : ℝ) + (v : ℝ) * logThreeDivLogTwo := by
    simp only [D, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    ring
  have hNeval : Polynomial.aeval logThreeDivLogTwo N =
      (a : ℝ) + (b : ℝ) * logThreeDivLogTwo := by
    simp only [N, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    ring
  have hEeval : Polynomial.aeval logThreeDivLogTwo E =
      (s : ℝ) + (t : ℝ) * logThreeDivLogTwo := by
    simp only [E, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    ring
  have hGeval : Polynomial.aeval logThreeDivLogTwo G =
      (c : ℝ) + (d : ℝ) * logThreeDivLogTwo := by
    simp only [G, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
    ring
  have hpolyEval :
      Polynomial.aeval logThreeDivLogTwo (E * N ^ n) =
        Polynomial.aeval logThreeDivLogTwo (G * D ^ n) := by
    simp only [map_mul, map_pow, hDeval, hNeval, hEeval, hGeval]
    rw [← hOne, ← hN]
    rw [mul_pow]
    ring
  have hpoly : E * N ^ n = G * D ^ n :=
    eq_of_aeval_eq_of_transcendental transcendental_logThreeDivLogTwo hpolyEval
  have hEne : E ≠ 0 := by
    intro hzero
    have heval := congrArg (Polynomial.aeval logThreeDivLogTwo) hzero
    rw [hEeval, map_zero] at heval
    exact hEval heval
  by_cases hv : v = 0
  · subst v
    have hu : u ≠ 0 := by tauto
    have hb : b ≠ 0 := by
      intro hb0
      subst b
      apply hxTrans
      have hxrat : x = ((a / u : ℚ) : ℝ) := by
        have huR : (u : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hu
        push_cast
        rw [eq_div_iff huR]
        simpa [mul_comm] using hOne
      rw [hxrat]
      exact isAlgebraic_rat ℚ (a / u)
    have hNne : N ≠ 0 := by
      intro hzero
      have hdeg := congrArg Polynomial.natDegree hzero
      rw [show N.natDegree = 1 by exact Polynomial.natDegree_linear hb,
        Polynomial.natDegree_zero] at hdeg
      omega
    have hleftDegree : (E * N ^ n).natDegree = E.natDegree + n := by
      rw [Polynomial.natDegree_mul hEne (pow_ne_zero n hNne),
        Polynomial.natDegree_pow,
        show N.natDegree = 1 by exact Polynomial.natDegree_linear hb]
      omega
    have hDdegree : D.natDegree = 0 := by simp [D]
    have hGdegree : G.natDegree ≤ 1 := by
      have hmul := Polynomial.natDegree_mul_le
        (p := Polynomial.C d) (q := Polynomial.X)
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add] at hmul
      dsimp only [G]
      calc
        (Polynomial.C d * Polynomial.X + Polynomial.C c).natDegree ≤
            max (Polynomial.C d * Polynomial.X).natDegree
              (Polynomial.C c).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 1 := max_le hmul (by simp)
    have hrightDegree : (G * D ^ n).natDegree ≤ 1 := by
      calc
        (G * D ^ n).natDegree ≤ G.natDegree + (D ^ n).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1 := by rw [Polynomial.natDegree_pow, hDdegree]; omega
    have hdegrees := congrArg Polynomial.natDegree hpoly
    rw [hleftDegree] at hdegrees
    omega
  · have hDne : D ≠ 0 := by
      intro hzero
      have hdeg := congrArg Polynomial.natDegree hzero
      rw [show D.natDegree = 1 by exact Polynomial.natDegree_linear hv,
        Polynomial.natDegree_zero] at hdeg
      omega
    let z : ℚ := -u / v
    have hDz : Polynomial.eval z D = 0 := by
      simp [z, D]
      field_simp
      ring
    have hNz : Polynomial.eval z N ≠ 0 := by
      intro hNz0
      have hprop : v * a = b * u := by
        simp [z, N] at hNz0
        field_simp at hNz0
        linarith
      have hxrat := rational_of_ratAffine_mul_eq_ratAffine_of_proportional
        hDval (by simpa only [pow_one] using hOne) hv hprop
      apply hxTrans
      rw [hxrat]
      exact isAlgebraic_rat ℚ (b / v)
    have hEz : Polynomial.eval z E = 0 := by
      have heq := congrArg (Polynomial.eval z) hpoly
      rw [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_mul, Polynomial.eval_pow] at heq
      rw [hDz, zero_pow (by omega : n ≠ 0), mul_zero] at heq
      have heq' : Polynomial.eval z E * (Polynomial.eval z N) ^ n = 0 := heq
      exact (mul_eq_zero.mp heq').resolve_right (pow_ne_zero n hNz)
    have ht : t ≠ 0 := by
      intro ht0
      subst t
      have hs : s = 0 := by simpa [E] using hEz
      exact hst ⟨hs, rfl⟩
    let k : ℚ := t / v
    have hEeq : E = Polynomial.C k * D := by
      have hprop : v * s = t * u := by
        have hz := hEz
        simp [z, E] at hz
        field_simp at hz
        linarith
      have hkv : k * v = t := by
        dsimp only [k]
        field_simp
      have hku : k * u = s := by
        dsimp only [k]
        field_simp
        linarith
      dsimp only [E, D]
      rw [← hkv, ← hku]
      simp only [map_mul]
      ring
    have hk : k ≠ 0 := div_ne_zero ht hv
    have hnsub : 0 < n - 1 := by omega
    have hpowD : D ^ n = D * D ^ (n - 1) := by
      calc
        D ^ n = D ^ ((n - 1) + 1) := by
          congr 1
          omega
        _ = D ^ (n - 1) * D := pow_succ D (n - 1)
        _ = D * D ^ (n - 1) := mul_comm _ _
    have hcancel : Polynomial.C k * N ^ n = G * D ^ (n - 1) := by
      apply mul_left_cancel₀ hDne
      calc
        D * (Polynomial.C k * N ^ n) = E * N ^ n := by rw [hEeq]; ring
        _ = G * D ^ n := hpoly
        _ = D * (G * D ^ (n - 1)) := by
          rw [hpowD]
          ring
    have heval := congrArg (Polynomial.eval z) hcancel
    have heval' : k * (Polynomial.eval z N) ^ n = 0 := by
      simpa [hDz, hnsub.ne'] using heval
    exact (mul_ne_zero hk (pow_ne_zero n hNz)) heval'

/-- Kernel-relation form of the preceding exclusion.  In the nontrivial
second-iterate-kernel branch, every rational `2,3`-unit base direction has no
algebraic transition at any depth at least two. -/
theorem TwoBaseNonintegerSolution.not_higher_unitDirectionTowerTransition_of_kernelRelation
    {x : ℝ} (hx : TwoBaseNonintegerSolution x)
    (hkernel : SecondIterateKernelRelation x)
    {s t : ℚ} (hst : ¬ (s = 0 ∧ t = 0))
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ UnitDirectionTowerTransition x s t n := by
  obtain ⟨a, b, c, d, hab, hrel⟩ := hkernel
  have habQ : ¬ (((a : ℚ) = 0) ∧ ((b : ℚ) = 0)) := by
    rintro ⟨ha, hb⟩
    apply hab
    exact ⟨Int.cast_eq_zero.mp ha, Int.cast_eq_zero.mp hb⟩
  have hdepthOne : UnitDirectionTowerTransition x (a : ℚ) (b : ℚ) 1 := by
    apply (hx.twoRpowAlgebraicTransition_iff_affine_logRatio).mpr
    refine ⟨(-c : ℚ), (-d : ℚ), ?_⟩
    simp only [pow_one]
    push_cast
    linear_combination hrel
  exact hx.not_higher_unitDirectionTowerTransition_of_depth_one
    habQ hst hdepthOne hn

/-- Multiplicative-output form: if the four integers `M`, `A`, `2`, `3` are
multiplicatively dependent, then no nonzero rational `2,3`-unit direction has
a higher (`n ≥ 2`) algebraic tower transition. -/
theorem TwoBaseNonintegerSolution.not_higher_unitDirectionTowerTransition_of_dependentOutputs
    {x : ℝ} (hx : TwoBaseNonintegerSolution x) {M A : ℕ}
    (hM : (M : ℝ) = (2 : ℝ) ^ x) (hA : (A : ℝ) = (3 : ℝ) ^ x)
    (hdep : MultiplicativelyDependentOutputs M A)
    {s t : ℚ} (hst : ¬ (s = 0 ∧ t = 0))
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ UnitDirectionTowerTransition x s t n :=
  hx.not_higher_unitDirectionTowerTransition_of_kernelRelation
    (secondIterateKernelRelation_of_multiplicativelyDependentOutputs hM hA hdep)
    hst hn

end

end LeanProofs.TwoBaseIntegerExponent
