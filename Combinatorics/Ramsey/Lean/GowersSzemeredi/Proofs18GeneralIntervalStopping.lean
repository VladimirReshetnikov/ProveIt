import GowersSzemeredi.Proofs18GeneralProgressionExistence
import GowersSzemeredi.Proofs18IntervalUniformStopping

/-! Relative-uniform stopping on integer intervals at every progression
length. The explicit constants specialize to the existing four-term bound. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Starts and nonnegative steps below L/k produce k-term progressions
entirely inside the interval. Both parameters are recovered from the pair. -/
theorem finiteInterval_progressionCount_floor {N L k : Nat} [NeZero N] (hL : L ≤ N) (_hk : 0 < k) :
    (L / k) ^ 2 ≤ progressionCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) k := by
  classical
  let m := L / k
  let F : Fin m × Fin m → ZMod N × ZMod N := fun p => (-(p.2 : Nat), (p.1 : Nat))
  have hmL : m ≤ L := Nat.div_le_self _ _
  have hcast := finiteInterval_cast_injective (hmL.trans hL)
  have hF : Function.Injective F := by
    intro p q hpq
    apply Prod.ext
    · exact hcast (congrArg Prod.snd hpq)
    · exact hcast (neg_inj.mp (congrArg Prod.fst hpq))
  have hsub : Finset.univ.image F ⊆
      Finset.univ.filter (fun p : ZMod N × ZMod N =>
        ∀ i : Fin k, p.2 - (i : Nat) * p.1 ∈
          finiteIntervalImage N (Finset.univ : Finset (Fin L))) := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    have hzL : (q.1 : Nat) + (i : Nat) * (q.2 : Nat) < L := by
      calc
        _ < m + (i : Nat) * m := Nat.add_lt_add_of_lt_of_le q.1.isLt
          (Nat.mul_le_mul_left _ q.2.isLt.le)
        _ = ((i : Nat) + 1) * m := by ring
        _ ≤ k * m := Nat.mul_le_mul_right m i.isLt
        _ ≤ L := Nat.mul_div_le L k
    apply Finset.mem_image.mpr
    refine ⟨⟨(q.1 : Nat) + (i : Nat) * (q.2 : Nat), hzL⟩, Finset.mem_univ _, ?_⟩
    dsimp [F]
    push_cast
    ring
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hF] at hcard
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← pow_two] at hcard
  convert hcard using 1
  unfold progressionCount countWhere
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem finiteInterval_progressionCount_lower {N L k : Nat} [NeZero N]
    (hL : L ≤ N) (hk : 0 < k) (hkL : k ≤ L) :
    (L : Real) ^ 2 / (4 * (k : Real) ^ 2) ≤
      (progressionCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) k : Real) := by
  have hf : L ≤ (2 * k) * (L / k) := by
    have hdiv : 0 < L / k := Nat.div_pos hkL hk
    have hmul : k ≤ k * (L / k) := Nat.le_mul_of_pos_right k hdiv
    have hrem := Nat.mod_lt L hk
    have hdecomp := Nat.mod_add_div L k
    rw [Nat.mul_assoc]
    omega
  have hfr : (L : Real) ≤ (2 * k) * (L / k : Nat) := by exact_mod_cast hf
  have hs : ((L : Real) / (2 * k)) ^ 2 ≤ ((L / k : Nat) : Real) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by apply (div_le_iff₀ (by positivity : (0 : Real) < 2 * k)).mpr; nlinarith)
  have hc : (((L / k) ^ 2 : Nat) : Real) ≤
      (progressionCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) k : Real) := by
    exact_mod_cast finiteInterval_progressionCount_floor hL hk
  push_cast at hc
  have heq : ((L : Real) / (2 * k)) ^ 2 = (L : Real) ^ 2 / (4 * (k : Real) ^ 2) := by
    rw [div_pow]
    ring
  rw [heq] at hs
  exact hs.trans hc

/-- At arbitrary length k, sufficiently small relative-uniformity error
forces an ordinary progression in the original interval. -/
theorem interval_relative_uniform_hasNatAP {N L k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hL : 2 * L < N) (hkL : k ≤ L) (hNL : N ≤ 8 * L)
    (B : Finset (Fin L)) (delta alpha : Real)
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hsmall : k * alpha ^ (1 / (2 : Real) ^ (k - 1)) ≤ delta ^ k / (512 * (k : Real) ^ 2))
    (hlarge : 512 * (k : Real) ^ 2 < delta ^ k * N)
    (hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha (k - 2)) :
    HasNatAP (B.image Fin.val) k := by
  have hLN : L ≤ N := by omega
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  have hcount : (N : Real) ^ 2 / (256 * (k : Real) ^ 2) ≤ (progressionCount S k : Real) := by
    have hnlr : (N : Real) ≤ 8 * L := by exact_mod_cast hNL
    have hs := (sq_le_sq₀ (by positivity : (0 : Real) ≤ N) (by positivity : (0 : Real) ≤ 8 * L)).mpr hnlr
    have hc := finiteInterval_progressionCount_lower hLN (by omega : 0 < k) hkL
    have hc' := (div_le_iff₀ (by positivity : (0 : Real) < 4 * (k : Real) ^ 2)).mp hc
    apply (div_le_iff₀ (by positivity : (0 : Real) < 256 * (k : Real) ^ 2)).mpr
    change (N : Real) ^ 2 ≤ (progressionCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) k : Real) * _
    nlinarith
  apply finiteIntervalImage_hasNatAP B hL
  apply relative_uniform_hasModAP hk (by omega) (finiteIntervalImage N B) S delta alpha
    (finiteIntervalImage_subset B) hδ hδone hα
    (by simpa only [S, relativeBalanced_finiteIntervalImage hLN] using hu)
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hden : (0 : Real) < 512 * (k : Real) ^ 2 := by positivity
  have he := mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mp hsmall) (sq_nonneg (N : Real))
  have hl := mul_lt_mul_of_pos_right hlarge hNpos
  have hc := mul_le_mul_of_nonneg_left
    ((div_le_iff₀ (by positivity : (0 : Real) < 256 * (k : Real) ^ 2)).mp hcount)
    (pow_nonneg hδ k)
  apply (mul_lt_mul_iff_left₀ hden).mp
  nlinarith

/-- An explicit uniformity parameter meeting the general interval count
budget. At k=4 this is the existing quadratic stopping parameter. -/
def intervalUniformityParameter (delta : Real) (k : Nat) : Real :=
  (delta ^ k / (512 * (k : Real) ^ 3)) ^ ((2 : Nat) ^ (k - 1))

theorem intervalUniformityParameter_pos {delta : Real} {k : Nat}
    (hδ : 0 < delta) (hk : 0 < k) : 0 < intervalUniformityParameter delta k := by
  unfold intervalUniformityParameter
  positivity

theorem intervalUniformityParameter_le_one {delta : Real} {k : Nat}
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hk : 0 < k) :
    intervalUniformityParameter delta k ≤ 1 := by
  have hkR : (1 : Real) ≤ k := by exact_mod_cast hk
  have hp : delta ^ k ≤ 1 := pow_le_one₀ hδ hδone
  have hden : (1 : Real) ≤ 512 * (k : Real) ^ 3 := by
    have hh : (1 : Real) ≤ (k : Real) ^ 3 := one_le_pow₀ hkR
    linarith
  apply pow_le_one₀ (by positivity)
  exact (div_le_one (by positivity : (0 : Real) < 512 * (k : Real) ^ 3)).mpr (hp.trans hden)

theorem intervalUniformityParameter_count_error {delta : Real} {k : Nat}
    (hδ : 0 ≤ delta) (hk : 0 < k) :
    k * intervalUniformityParameter delta k ^ (1 / (2 : Real) ^ (k - 1)) =
      delta ^ k / (512 * (k : Real) ^ 2) := by
  have hkR : (0 : Real) < k := by exact_mod_cast hk
  have hroot : intervalUniformityParameter delta k ^ (1 / (2 : Real) ^ (k - 1)) =
      delta ^ k / (512 * (k : Real) ^ 3) := by
    simpa only [intervalUniformityParameter, one_div, Nat.cast_pow, Nat.cast_ofNat] using
      (Real.pow_rpow_inv_natCast (show 0 ≤ delta ^ k / (512 * (k : Real) ^ 3) by positivity)
        (by positivity : (2 : Nat) ^ (k - 1) ≠ 0))
  rw [hroot]
  field_simp

/-- A single explicit parameter suffices for the stopping branch at any
progression length. No higher-degree inverse theorem is assumed here. -/
theorem interval_uniform_stopping {N L k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hL : 2 * L < N) (hkL : k ≤ L) (hNL : N ≤ 8 * L)
    (B : Finset (Fin L)) (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (hlarge : 512 * (k : Real) ^ 2 < delta ^ k * N)
    (hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta))
      (intervalUniformityParameter delta k) (k - 2)) : HasNatAP (B.image Fin.val) k := by
  exact interval_relative_uniform_hasNatAP hk hL hkL hNL B delta
    (intervalUniformityParameter delta k) hδ.le hδone
    (intervalUniformityParameter_pos hδ (by omega)).le
    (intervalUniformityParameter_count_error hδ.le (by omega)).le hlarge hu

end LeanProofs.GowersSzemeredi
