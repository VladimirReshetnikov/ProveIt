import GowersSzemeredi.Proofs16CoherentSparseDomain

/-! Exact rank and density states for coherent regularity. Error and cutoff
may depend on both coordinates, with no monotonicity assumption. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentAdaptiveState (epsilon : Nat × Real → Real) (cutoff : Nat × Real → Nat)
    (cells ell : Nat) (rho : Real) (a : Nat × Real) : Nat × Real :=
  let d := coherentRelationBudget (epsilon a) (cutoff a) cells ell a.1
  (d, a.2*coherentIterationLoss d rho)

theorem coherentAdaptiveState_pos (epsilon : Nat × Real → Real) (cutoff : Nat × Real → Nat)
    (cells ell : Nat) {rho : Real} (hr : 0 < rho) {a : Nat × Real} (ha : 0 < a.2) :
    ∀ s, 0 < ((coherentAdaptiveState epsilon cutoff cells ell rho)^[s] a).2 := by
  intro s
  induction s with
  | zero => exact ha
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    exact mul_pos ih (coherentIterationLoss_pos _ hr)

/-- Finite, explicit collision budget along every possible stopping state. -/
def coherentAdaptiveModulusBound (epsilon : Nat × Real → Real) (cutoff : Nat × Real → Nat)
    (cells ell : Nat) (rho : Real) (a : Nat × Real) : Nat :=
  (Finset.range (ell+1)).sup fun s =>
    ⌈8/((coherentAdaptiveState epsilon cutoff cells ell rho)^[s] a).2⌉₊

theorem coherentAdaptiveModulusBound_mass (epsilon : Nat × Real → Real)
    (cutoff : Nat × Real → Nat) (cells ell : Nat) {rho : Real} (hr : 0 < rho)
    {a : Nat × Real} (ha : 0 < a.2) {N s : Nat} (hs : s ≤ ell)
    (hN : coherentAdaptiveModulusBound epsilon cutoff cells ell rho a ≤ N) :
    8 ≤ ((coherentAdaptiveState epsilon cutoff cells ell rho)^[s] a).2*(N : Real) := by
  have h : 8/((coherentAdaptiveState epsilon cutoff cells ell rho)^[s] a).2 ≤ (N : Real) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (Finset.le_sup (f := fun j =>
      ⌈8/((coherentAdaptiveState epsilon cutoff cells ell rho)^[j] a).2⌉₊)
      (Finset.mem_range.mpr (by omega : s < ell+1))).trans hN
  simpa only [mul_comm] using
    (div_le_iff₀ (coherentAdaptiveState_pos epsilon cutoff cells ell hr ha s)).mp h

end LeanProofs.GowersSzemeredi
