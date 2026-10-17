import GowersSzemeredi.Proofs18RelativeIntervalModel
import GowersSzemeredi.Proofs18IntervalTransfer
import GowersSzemeredi.Proofs18RelativeProgressionCount

/-! An explicit relative-uniform stopping condition on an integer interval.
The support itself supplies quadratically many four-term progressions.

`finiteInterval_fourTermCount_floor`, `finiteInterval_fourTermCount_lower` and
`interval_relative_uniform_hasNatAP_four` are in
`Proofs18IntervalUniformStoppingSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Starts and nonnegative steps below L/k produce k-term progressions
entirely inside the interval. Both parameters are recovered from the pair. -/
theorem finiteInterval_progressionCount_floor {N L k : Nat} [NeZero N] (hL : L ≤ N) (_hk : 0 < k) :
    (L / k) ^ 2 ≤ progressionCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) k := by
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

/-- No-wrap transfer for the zero-based interval convention used by Fin L. -/
theorem finiteIntervalImage_hasNatAP {N L k : Nat} [NeZero N]
    (B : Finset (Fin L)) (hL : 2 * L < N)
    (hAP : HasModAP (finiteIntervalImage N B) k) : HasNatAP (B.image Fin.val) k := by
  obtain ⟨a, d, hd, hAP⟩ := hAP
  apply hasNatAP_of_short_modular_sequence (B.image Fin.val)
    (fun i => (a + (i : ZMod N) * d).val) a d (bne_iff_ne.mp hd) hL
  intro i hi
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (hAP i hi)
  have hxN : (x : Nat) < N := by omega
  have hval : (a + (i : ZMod N) * d).val = (x : Nat) := by
    rw [← hxeq, ZMod.val_natCast_of_lt hxN]
  rw [hval]
  exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, x.isLt.le, hxeq⟩

end LeanProofs.GowersSzemeredi
