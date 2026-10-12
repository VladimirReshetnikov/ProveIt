import GowersSzemeredi.Proofs18CoverSharperShortLengths
import GowersSzemeredi.Proofs01QuantitativeHeadline

/-! **Theorem 1.3 with a sharper constant** (Notes L.15h).

Theorem 1.3 states that a subset of `[1, N]` of density at least
`(log log N)^(-2^(-2^(k+9)))` contains a `k`-term progression for large `N`.
The corpus derives it from Theorem 18.2 (`theorem_1_3_holds_of_theorem_18_2`)
by a real-power calculation in which the constant enters only through
`2^(k+9)`. Here the calculation is repeated with `k + c`:
* `theorem_1_3_constantAt c k = 2^(-2^(k+c))` and `Theorem13At c`, which is
  the catalogue's `theorem_1_3` at `c = 9` (`theorem13At_nine_iff`);
* `theorem13At_of_sharp`: Theorem 18.2 with `k + c` in every length gives
  Theorem 1.3 with constant `2^(-2^(k+c))`.
With Theorem 18.2 at `L + 5` this gives the exponent `2^(-2^(k+5))`
(`theorem_1_3_L5`, in `Proofs18CoverSharperAllDegrees`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The constant of Theorem 1.3 with `k + c` in place of the printed `k + 9`. -/
def theorem_1_3_constantAt (c k : Nat) : Real :=
  (2 : Real) ^ (-((2 : Real) ^ (k + c : Nat)))

/-- Theorem 1.3 with the constant `theorem_1_3_constantAt c`. -/
def Theorem13At (c : Nat) : Prop :=
  forall k : Nat, 0 < k -> exists N0 : Nat, forall N : Nat, N0 <= N ->
    forall A : Finset Nat, A ⊆ Finset.Icc 1 N ->
      (N : Real) * (Real.log (Real.log N)) ^ (-theorem_1_3_constantAt c k) <= A.card ->
      HasNatAP A k

/-- At `c = 9` it is the catalogue's Theorem 1.3. -/
theorem theorem13At_nine_iff : Theorem13At 9 ↔ theorem_1_3 := Iff.rfl

/-- **The log--log density reaches the threshold with `k + c` on top.** -/
theorem headline_density_thresholdAt (c k N : Nat)
    (hfloor : Real.exp (Real.exp ((2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))
      <= (N : Real)) :
    let L := Real.log (Real.log N)
    let delta := L ^ (-theorem_1_3_constantAt c k)
    0 < delta /\ delta <= 1 / 2 /\ szemerediThresholdAt c delta k <= N := by
  let F : Real := (2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))
  let L : Real := Real.log (Real.log N)
  let cc : Real := theorem_1_3_constantAt c k
  let E : Real := (2 : Real) ^ ((2 : Real) ^ (k + c : Nat))
  have hFpos : 0 < F := Real.rpow_pos_of_pos (by norm_num) _
  have hNpos : (0 : Real) < N := (Real.exp_pos _).trans_le hfloor
  have hlogNLower : Real.exp F <= Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) hfloor
    simpa only [Real.log_exp] using h
  have hlogNpos : 0 < Real.log N := (Real.exp_pos F).trans_le hlogNLower
  have hLlower : F <= L := by
    have h := Real.log_le_log (Real.exp_pos _) hlogNLower
    simpa only [Real.log_exp, L] using h
  have hLpos : 0 < L := hFpos.trans_le hLlower
  have hcpos : 0 < cc := Real.rpow_pos_of_pos (by norm_num) _
  have hcE : cc * E = 1 := by
    change (2 : Real) ^ (-((2 : Real) ^ (k + c : Nat))) * (2 : Real) ^ ((2 : Real) ^ (k + c : Nat)) = 1
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) _).ne'
  have hEc : E * cc = 1 := by rw [mul_comm]; exact hcE
  let delta : Real := L ^ (-cc)
  have hdeltaPos : 0 < delta := Real.rpow_pos_of_pos hLpos _
  have htwoPow : ((2 : Real) ^ E) ^ cc = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 2), hEc, Real.rpow_one]
  have hpowLower : (2 : Real) <= L ^ cc := by
    rw [← htwoPow]
    exact Real.rpow_le_rpow (by positivity) hLlower hcpos.le
  have hdeltaForm : delta = (L ^ cc)⁻¹ := by
    change L ^ (-cc) = (L ^ cc)⁻¹
    rw [Real.rpow_neg hLpos.le]
  have hdeltaHalf : delta <= 1 / 2 := by
    rw [hdeltaForm, one_div]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos hLpos cc) (by norm_num : (0 : Real) < 2)).2 hpowLower
  have hdeltaInv : delta⁻¹ = L ^ cc := by rw [hdeltaForm, inv_inv]
  have hpowerCollapse : delta⁻¹ ^ E = L := by
    rw [hdeltaInv, ← Real.rpow_mul hLpos.le, hcE, Real.rpow_one]
  have htwoExpLeExp (x : Real) (hx : 0 <= x) : (2 : Real) ^ x <= Real.exp x := by
    have htwoExp : (2 : Real) <= Real.exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    calc (2 : Real) ^ x <= (Real.exp 1) ^ x := Real.rpow_le_rpow (by norm_num) htwoExp hx
      _ = Real.exp x := Real.exp_one_rpow x
  have hinner : (2 : Real) ^ L <= Real.log N := by
    calc (2 : Real) ^ L <= Real.exp L := htwoExpLeExp L hLpos.le
      _ = Real.log N := by
        change Real.exp (Real.log (Real.log N)) = Real.log N
        rw [Real.exp_log hlogNpos]
  have hthreshold : szemerediThresholdAt c delta k <= N := by
    change (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ E)) <= N
    rw [hpowerCollapse]
    calc (2 : Real) ^ ((2 : Real) ^ L) <= Real.exp ((2 : Real) ^ L) :=
          htwoExpLeExp _ (Real.rpow_nonneg (by norm_num) _)
      _ <= Real.exp (Real.log N) := Real.exp_le_exp.mpr hinner
      _ = (N : Real) := Real.exp_log hNpos
  exact ⟨hdeltaPos, hdeltaHalf, hthreshold⟩

/-- **Theorem 18.2 with `k + c` gives Theorem 1.3 with constant `2^(-2^(k+c))`.** -/
theorem theorem13At_of_sharp {c : Nat} (h : ∀ k, Theorem182AtSharp c k) : Theorem13At c := by
  intro k _hk
  let X : Real := Real.exp (Real.exp ((2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))
  refine ⟨Nat.ceil X, fun N hN A hAsub hAcard => ?_⟩
  have hfloor : X <= (N : Real) := (Nat.le_ceil X).trans (by exact_mod_cast hN)
  obtain ⟨hdelta, hdeltaHalf, hthreshold⟩ := headline_density_thresholdAt c k N hfloor
  have hcard : (Real.log (Real.log N)) ^ (-theorem_1_3_constantAt c k) * N <= A.card := by
    simpa only [mul_comm] using hAcard
  exact h k _ N hdelta hdeltaHalf hthreshold A hAsub hcard

end LeanProofs.GowersSzemeredi
