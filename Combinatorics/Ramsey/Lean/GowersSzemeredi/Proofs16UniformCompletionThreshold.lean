import GowersSzemeredi.Proofs16AdaptiveSevenOperator

/-! Uniform finite modulus thresholds over bounded initial geometry.
Taking finite maxima avoids assuming monotonicity of the adaptive schedule. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def uniformCompletionModulusBound (alpha : Real) (Q H M K D : Nat) : Nat :=
  (Finset.range (M + 1)).sup fun m =>
    (Finset.range (K + 1)).sup fun k =>
      (Finset.range (D + 1)).sup fun d =>
        adaptiveGraphModulusBound (adaptiveFillingError alpha Q H m) H m Q k d

/-- One threshold covers all bounded tuple sizes and initial states. -/
theorem uniformCompletionModulusBound_spec (alpha : Real) (Q H M K D m k d : Nat)
    (hm : m ≤ M) (hk : k ≤ K) (hd : d ≤ D) :
    adaptiveGraphModulusBound (adaptiveFillingError alpha Q H m) H m Q k d ≤
      uniformCompletionModulusBound alpha Q H M K D := by
  apply le_trans (Finset.le_sup (f := fun j =>
    adaptiveGraphModulusBound (adaptiveFillingError alpha Q H m) H m Q k j)
    (Finset.mem_range.mpr (by omega : d < D + 1)))
  apply le_trans (Finset.le_sup (f := fun j =>
    (Finset.range (D + 1)).sup fun d =>
      adaptiveGraphModulusBound (adaptiveFillingError alpha Q H m) H m Q j d)
    (Finset.mem_range.mpr (by omega : k < K + 1)))
  exact Finset.le_sup (f := fun j => (Finset.range (K + 1)).sup fun k =>
    (Finset.range (D + 1)).sup fun d =>
      adaptiveGraphModulusBound (adaptiveFillingError alpha Q H j) H j Q k d)
    (Finset.mem_range.mpr (by omega : m < M + 1))

/-- Cardinality caps on the initial frequency data discharge the adaptive
threshold used by seven-operator completion. -/
theorem uniformCompletionModulusBound_geometry {N : Nat}
    {κ : Type*} [Fintype κ] (F Gamma : Finset (ZMod N))
    (alpha : Real) (Q H f g k : Nat) (hF : F.card ≤ f) (hG : Gamma.card ≤ g)
    (hk : Fintype.card κ ≤ k)
    (hN : uniformCompletionModulusBound alpha Q H (f + k * k + 2 * k) k (max g f) ≤ N) :
    adaptiveGraphModulusBound
      (adaptiveFillingError alpha Q H (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)) H
      (F.card + Fintype.card κ * Fintype.card κ + 2 * Fintype.card κ)
      Q (Fintype.card κ) (max Gamma.card F.card) ≤ N := by
  apply (uniformCompletionModulusBound_spec alpha Q H _ _ _ _ _ _ _ hk
    (max_le_max hG hF)).trans hN
  have hsq := Nat.mul_le_mul hk hk
  omega

end LeanProofs.GowersSzemeredi
