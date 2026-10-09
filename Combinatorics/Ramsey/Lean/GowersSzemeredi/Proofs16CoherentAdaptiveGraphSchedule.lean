import GowersSzemeredi.Proofs16CoherentAdaptiveIteration
import GowersSzemeredi.Proofs16CoherentQuasirandomDomain

/-! An accuracy schedule evaluated at the exact retained quadruple density.
Both regularity and Fourier thresholds range over finitely many states. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coherentAdaptiveGraphState (e : Nat × Real → Real) (H m cells ell : Nat)
    (rho : Real) : Nat × Real → Nat × Real :=
  coherentAdaptiveState (fun a => (e a)^4/6)
    (fun a => relationProfileCutoff ((e a)^4) H m) cells ell rho

def coherentAdaptiveGraphModulusBound (e : Nat × Real → Real) (H m cells ell : Nat)
    (rho : Real) (a : Nat × Real) : Nat :=
  max (coherentAdaptiveModulusBound (fun a => (e a)^4/6)
    (fun a => relationProfileCutoff ((e a)^4) H m) cells ell rho a)
    ((Finset.range (ell+1)).sup fun s =>
      ⌈1/relationProfileSmoothing ((e ((coherentAdaptiveGraphState e H m cells ell rho)^[s] a))^4) H m⌉₊)

theorem coherentAdaptiveGraphModulusBound_mass (e : Nat × Real → Real)
    (H m cells ell : Nat) {rho : Real} (hr : 0 < rho)
    {a : Nat × Real} (ha : 0 < a.2) {N s : Nat} (hs : s ≤ ell)
    (hN : coherentAdaptiveGraphModulusBound e H m cells ell rho a ≤ N) :
    8 ≤ ((coherentAdaptiveGraphState e H m cells ell rho)^[s] a).2*(N : Real) :=
  coherentAdaptiveModulusBound_mass _ _ cells ell hr ha hs ((le_max_left _ _).trans hN)

theorem coherentAdaptiveGraphModulusBound_analytic (e : Nat × Real → Real)
    (H m cells ell : Nat) (rho : Real) (a : Nat × Real) {N s : Nat} (hs : s ≤ ell)
    (hN : coherentAdaptiveGraphModulusBound e H m cells ell rho a ≤ N) :
    1/relationProfileSmoothing ((e ((coherentAdaptiveGraphState e H m cells ell rho)^[s] a))^4) H m ≤ N := by
  apply (Nat.le_ceil _).trans
  exact_mod_cast (Finset.le_sup (f := fun j =>
    ⌈1/relationProfileSmoothing ((e ((coherentAdaptiveGraphState e H m cells ell rho)^[j] a))^4) H m⌉₊)
    (Finset.mem_range.mpr (by omega : s < ell+1))).trans ((le_max_right _ _).trans hN)

/-- A concrete schedule can request any prescribed power of the current
coherent density, while retaining the positive graph-density guarantee. -/
def coherentDensityAccuracy (H m power : Nat) (scale : Real) (a : Nat × Real) : Real :=
  min ((1/((4*H : Nat) : Real)^m)/2) (a.2^power/scale)

theorem coherentDensityAccuracy_pos (H m power : Nat) [NeZero H]
    {scale : Real} (hc : 0 < scale) {a : Nat × Real} (ha : 0 < a.2) :
    0 < coherentDensityAccuracy H m power scale a := by
  have hH : (0 : Real) < H := by exact_mod_cast NeZero.pos H
  unfold coherentDensityAccuracy
  exact lt_min (by push_cast; positivity) (by positivity)

theorem coherentDensityAccuracy_le_half (H m power : Nat) (scale : Real) (a : Nat × Real) :
    coherentDensityAccuracy H m power scale a ≤ (1/((4*H : Nat) : Real)^m)/2 := min_le_left _ _

theorem coherentDensityAccuracy_fourth_le (H m power : Nat) [NeZero H]
    {scale : Real} (hc : 0 < scale) {a : Nat × Real} (ha : 0 < a.2) :
    (coherentDensityAccuracy H m power scale a)^4 ≤ (a.2^power/scale)^4 :=
  pow_le_pow_left₀ (coherentDensityAccuracy_pos H m power hc ha).le (min_le_right _ _) _

end LeanProofs.GowersSzemeredi
