import GowersSzemeredi.Proofs18CoverHeadline

/-! **Theorem 1.3 from a given length on** (Notes L.16i).

`theorem13At_of_sharp` derives Theorem 1.3 with constant `2^(-2^(k+c))`
from Theorem 18.2 with `k + c` in *every* length. The derivation uses one
length at a time, so a bound that holds from some length `k₀` on gives
Theorem 1.3 from `k₀` on:
* `Theorem13AtFrom c k₀`: Theorem 1.3 with constant `2^(-2^(k+c))` for every
  `k ≥ k₀`; at `k₀ = 1` it is `Theorem13At c` (`theorem13AtFrom_one_iff`);
* `theorem13AtFrom_of_sharp`.
With Theorem 18.2 at `L + 3` for `L ≥ 14` this gives Theorem 1.3 with
constant `2^(-2^(k+3))` for every `k ≥ 14` (`theorem_1_3_L3_fourteen_le`, in
`Proofs18CoverFejerAllDegrees`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Theorem 1.3 with the constant `theorem_1_3_constantAt c` for every `k ≥ k0`. -/
def Theorem13AtFrom (c k0 : Nat) : Prop :=
  forall k : Nat, k0 <= k -> exists N0 : Nat, forall N : Nat, N0 <= N ->
    forall A : Finset Nat, A ⊆ Finset.Icc 1 N ->
      (N : Real) * (Real.log (Real.log N)) ^ (-theorem_1_3_constantAt c k) <= A.card ->
      HasNatAP A k

/-- From `k₀ = 1` on it is `Theorem13At c`. -/
theorem theorem13AtFrom_one_iff (c : Nat) : Theorem13AtFrom c 1 ↔ Theorem13At c :=
  ⟨fun h k hk => h k hk, fun h k hk => h k hk⟩

/-- **Theorem 18.2 with `k + c` from `k₀` on gives Theorem 1.3 from `k₀` on.** -/
theorem theorem13AtFrom_of_sharp {c k0 : Nat} (h : ∀ k, k0 ≤ k → Theorem182AtSharp c k) :
    Theorem13AtFrom c k0 := by
  intro k hk
  let X : Real := Real.exp (Real.exp ((2 : Real) ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))
  refine ⟨Nat.ceil X, fun N hN A hAsub hAcard => ?_⟩
  have hfloor : X <= (N : Real) := (Nat.le_ceil X).trans (by exact_mod_cast hN)
  obtain ⟨hdelta, hdeltaHalf, hthreshold⟩ := headline_density_thresholdAt c k N hfloor
  have hcard : (Real.log (Real.log N)) ^ (-theorem_1_3_constantAt c k) * N <= A.card := by
    simpa only [mul_comm] using hAcard
  exact h k hk _ N hdelta hdeltaHalf hthreshold A hAsub hcard

end LeanProofs.GowersSzemeredi
