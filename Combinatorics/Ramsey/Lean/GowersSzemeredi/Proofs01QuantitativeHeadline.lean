import GowersSzemeredi.Proofs18Consequences

/-!
# The quantitative headline consequence

This module isolates the real-power calculation which turns Gowers's
five-level threshold in Theorem 18.2 into the log--log density formulation
stated as Theorem 1.3. The final entry point supplies Theorem 18.2 to
this implication, preserving the paper's exact density exponent.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

private def headlineOuterExponent (k : Nat) : Real :=
  (2 : Real) ^ ((2 : Real) ^ (k + 9 : Nat))

private def headlineLogFloor (k : Nat) : Real :=
  (2 : Real) ^ headlineOuterExponent k

private lemma headlineConstant_mul_outer (k : Nat) :
    theorem_1_3_constant k * headlineOuterExponent k = 1 := by
  rw [theorem_1_3_constant, headlineOuterExponent,
    Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) _).ne'

/-- Above a concrete (enormous) log--log floor, the density appearing in
Theorem 1.3 lies in `(0,1/2]` and satisfies Theorem 18.2's tower threshold. -/
private lemma headline_density_threshold (k N : Nat)
    (hfloor : Real.exp (Real.exp (headlineLogFloor k)) <= (N : Real)) :
    let L := Real.log (Real.log N)
    let delta := L ^ (-theorem_1_3_constant k)
    0 < delta /\ delta <= 1 / 2 /\ szemerediThreshold delta k <= N := by
  let L : Real := Real.log (Real.log N)
  let c : Real := theorem_1_3_constant k
  let E : Real := headlineOuterExponent k
  have hNpos : (0 : Real) < N := (Real.exp_pos _).trans_le hfloor
  have hlogNLower : Real.exp (headlineLogFloor k) <= Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) hfloor
    simpa only [Real.log_exp] using h
  have hlogNpos : 0 < Real.log N :=
    (Real.exp_pos (headlineLogFloor k)).trans_le hlogNLower
  have hLlower : headlineLogFloor k <= L := by
    have h := Real.log_le_log (Real.exp_pos _) hlogNLower
    simpa only [Real.log_exp, L] using h
  have hLpos : 0 < L :=
    (show 0 < headlineLogFloor k by unfold headlineLogFloor; positivity).trans_le hLlower
  have hcpos : 0 < c := by dsimp [c, theorem_1_3_constant]; positivity
  have hcE : c * E = 1 := by
    simpa only [c, E] using headlineConstant_mul_outer k
  have hEc : E * c = 1 := by simpa only [mul_comm] using hcE
  let delta : Real := L ^ (-c)
  have hdeltaPos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have htwoPow : ((2 : Real) ^ E) ^ c = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 2), hEc, Real.rpow_one]
  have hpowLower : (2 : Real) <= L ^ c := by
    rw [← htwoPow]
    exact Real.rpow_le_rpow (by positivity) hLlower hcpos.le
  have hdeltaForm : delta = (L ^ c)⁻¹ := by
    change L ^ (-c) = (L ^ c)⁻¹
    rw [Real.rpow_neg hLpos.le]
  have hdeltaHalf : delta <= 1 / 2 := by
    rw [hdeltaForm, one_div]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hLpos c)
      (by norm_num : (0 : Real) < 2)).2 hpowLower
  have hdeltaInv : delta⁻¹ = L ^ c := by
    rw [hdeltaForm, inv_inv]
  have hpowerCollapse : delta⁻¹ ^ E = L := by
    rw [hdeltaInv, ← Real.rpow_mul hLpos.le, hcE, Real.rpow_one]
  have htwoExpLeExp (x : Real) (hx : 0 <= x) : (2 : Real) ^ x <= Real.exp x := by
    calc (2 : Real) ^ x <= (Real.exp 1) ^ x :=
          Real.rpow_le_rpow (by norm_num) (by linarith only [Real.add_one_le_exp (1 : Real)]) hx
      _ = Real.exp x := Real.exp_one_rpow x
  have hinner : (2 : Real) ^ L <= Real.log N := by
    calc
      (2 : Real) ^ L <= Real.exp L := htwoExpLeExp L hLpos.le
      _ = Real.log N := by
        change Real.exp (Real.log (Real.log N)) = Real.log N
        rw [Real.exp_log hlogNpos]
  have hthreshold : szemerediThreshold delta k <= N := by
    change (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ E)) <= N
    rw [hpowerCollapse]
    calc
      (2 : Real) ^ ((2 : Real) ^ L) <= Real.exp ((2 : Real) ^ L) :=
        htwoExpLeExp _ (Real.rpow_nonneg (by norm_num) _)
      _ <= Real.exp (Real.log N) := Real.exp_le_exp.mpr hinner
      _ = (N : Real) := Real.exp_log hNpos
  exact ⟨hdeltaPos, hdeltaHalf, hthreshold⟩

/-- **Gowers, Theorem 1.3, conditional on Theorem 18.2.**  This closes the
headline log--log/tower conversion with the paper's exact displayed constant
`2^(-2^(k+9))`. -/
theorem theorem_1_3_holds_of_theorem_18_2
    (h18 : theorem_18_2) : theorem_1_3 := by
  intro k hk
  refine ⟨⌈Real.exp (Real.exp (headlineLogFloor k))⌉₊, ?_⟩
  intro N hN A hAsub hAcard
  have hfloor : Real.exp (Real.exp (headlineLogFloor k)) <= (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  let L : Real := Real.log (Real.log N)
  let delta : Real := L ^ (-theorem_1_3_constant k)
  obtain ⟨hdelta, hdeltaHalf, hthreshold⟩ :=
    headline_density_threshold k N hfloor
  have hcard : delta * N <= A.card := by
    simpa only [delta, L, mul_comm] using hAcard
  exact h18 delta k N hdelta hdeltaHalf hk hthreshold A hAsub hcard

end LeanProofs.GowersSzemeredi
