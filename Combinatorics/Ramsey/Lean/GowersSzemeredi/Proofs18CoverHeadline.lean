import GowersSzemeredi.Proofs18SharpInterfaces
import GowersSzemeredi.Proofs01QuantitativeHeadline

/-! **Theorem 1.3 with a sharper constant** (Notes L.15h).

Theorem 1.3 states that a subset of `[1, N]` of density at least
`(log log N)^(-2^(-2^(k+9)))` contains a `k`-term progression for large `N`.
The corpus derives it from Theorem 18.2 (`theorem_1_3_holds_of_theorem_18_2`)
by the shared real-power calculation in `headline_density_threshold_of_exponent`.
Here the same calculation is specialized with `k + c`:
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
  simpa only [theorem_1_3_constantAt, szemerediThresholdAt,
    Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)] using
    headline_density_threshold_of_exponent
      ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat))) (by positivity) N hfloor

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
