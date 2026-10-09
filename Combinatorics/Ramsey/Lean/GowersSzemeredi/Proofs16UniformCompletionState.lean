import GowersSzemeredi.Proofs16UniformCompletionThreshold

/-! Uniform bounds for the exact adaptive state, independent of any
monotonicity of the accuracy schedule. These bounds control the rank
and size of the extracted target progression. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def uniformCompletionStateBound (alpha : Real) (Q H M K D : Nat) : Nat :=
  (Finset.range (M + 1)).sup fun m =>
    (Finset.range (K + 1)).sup fun k =>
      (Finset.range (D + 1)).sup fun d =>
        (Finset.range (K + 1)).sup fun s =>
          (adaptiveGraphState (adaptiveFillingError alpha Q H m) H m Q k)^[s] d

theorem uniformCompletionStateBound_spec (alpha : Real) (Q H M K D m k d s : Nat)
    (hm : m ≤ M) (hk : k ≤ K) (hd : d ≤ D) (hs : s ≤ K) :
    (adaptiveGraphState (adaptiveFillingError alpha Q H m) H m Q k)^[s] d ≤
      uniformCompletionStateBound alpha Q H M K D := by
  apply le_trans (Finset.le_sup (f := fun j =>
    (adaptiveGraphState (adaptiveFillingError alpha Q H m) H m Q k)^[j] d)
    (Finset.mem_range.mpr (by omega : s < K + 1)))
  apply le_trans (Finset.le_sup (f := fun j => (Finset.range (K + 1)).sup fun s =>
    (adaptiveGraphState (adaptiveFillingError alpha Q H m) H m Q k)^[s] j)
    (Finset.mem_range.mpr (by omega : d < D + 1)))
  apply le_trans (Finset.le_sup (f := fun j => (Finset.range (D + 1)).sup fun d =>
    (Finset.range (K + 1)).sup fun s =>
      (adaptiveGraphState (adaptiveFillingError alpha Q H m) H m Q j)^[s] d)
    (Finset.mem_range.mpr (by omega : k < K + 1)))
  exact Finset.le_sup (f := fun j => (Finset.range (K + 1)).sup fun k =>
    (Finset.range (D + 1)).sup fun d => (Finset.range (K + 1)).sup fun s =>
      (adaptiveGraphState (adaptiveFillingError alpha Q H j) H j Q k)^[s] d)
    (Finset.mem_range.mpr (by omega : m < M + 1))

/-- A uniform state cap gives a uniform spectrum-rank cap. -/
theorem completion_spectrum_card_uniform {N Q : Nat} [NeZero Q]
    (U : Finset (ZMod N)) {alpha : Real} (ha : 0 < alpha) (D d : Nat) (hd : d ≤ D)
    (hU : (U.card : Real) ≤ 16 / (alpha / (Q : Real)^d)^2) :
    U.card ≤ ⌈16 / (alpha / (Q : Real)^D)^2⌉₊ := by
  have hQ : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hp : (Q : Real)^d ≤ (Q : Real)^D := by exact_mod_cast Nat.pow_le_pow_right (NeZero.pos Q) hd
  have hden : alpha / (Q : Real)^D ≤ alpha / (Q : Real)^d :=
    div_le_div_of_nonneg_left ha.le (by positivity) hp
  have hbound : (U.card : Real) ≤ 16 / (alpha / (Q : Real)^D)^2 :=
    hU.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_left₀ (by positivity) hden 2))
  exact Nat.cast_le.mp (hbound.trans (Nat.le_ceil _))

end LeanProofs.GowersSzemeredi
