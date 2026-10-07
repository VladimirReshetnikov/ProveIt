import GowersSzemeredi.Proofs18RelativeProgressionExistence
import GowersSzemeredi.Proofs18RelativeIntervalModel
import GowersSzemeredi.Proofs18IntervalTransfer

/-! An explicit relative-uniform stopping condition on an integer interval.
The support itself supplies quadratically many four-term progressions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Starts and nonnegative steps below L/4 produce four-term progressions
entirely inside the interval. Both parameters are recovered from the pair. -/
theorem finiteInterval_fourTermCount_floor {N L : Nat} [NeZero N] (hL : L ≤ N) :
    (L / 4) ^ 2 ≤ fourTermCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) := by
  classical
  let m := L / 4
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
        ∀ i : Fin 4, p.2 - (i : Nat) * p.1 ∈
          finiteIntervalImage N (Finset.univ : Finset (Fin L))) := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    have hi : (i : Nat) ≤ 3 := by omega
    have hmul := Nat.mul_le_mul_right (q.2 : Nat) hi
    have hm4 : m * 4 ≤ L := Nat.div_mul_le_self _ _
    have hzL : (q.1 : Nat) + (i : Nat) * (q.2 : Nat) < L := by omega
    apply Finset.mem_image.mpr
    refine ⟨⟨(q.1 : Nat) + (i : Nat) * (q.2 : Nat), hzL⟩, Finset.mem_univ _, ?_⟩
    dsimp [F]
    push_cast
    ring
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hF] at hcard
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← pow_two] at hcard
  convert hcard using 1
  unfold fourTermCount countWhere
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem finiteInterval_fourTermCount_lower {N L : Nat} [NeZero N]
    (hL : L ≤ N) (hLfour : 4 ≤ L) :
    (L : Real) ^ 2 / 64 ≤
      (fourTermCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) : Real) := by
  have hf : L ≤ 8 * (L / 4) := by omega
  have hfr : (L : Real) ≤ 8 * (L / 4 : Nat) := by exact_mod_cast hf
  have hs : ((L : Real) / 8) ^ 2 ≤ ((L / 4 : Nat) : Real) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
  have hc : (((L / 4) ^ 2 : Nat) : Real) ≤
      (fourTermCount (finiteIntervalImage N (Finset.univ : Finset (Fin L))) : Real) := by
    exact_mod_cast finiteInterval_fourTermCount_floor hL
  push_cast at hc
  nlinarith

/-- No-wrap transfer for the zero-based interval convention used by Fin L. -/
theorem finiteIntervalImage_hasNatAP {N L k : Nat} [NeZero N]
    (B : Finset (Fin L)) (hL : 2 * L < N)
    (hAP : HasModAP (finiteIntervalImage N B) k) : HasNatAP (B.image Fin.val) k := by
  classical
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

/-- Explicit relative-uniform stopping: when the modulus is at most eight
times the interval length, a small enough uniformity error guarantees a
nonconstant ordinary four-term progression. -/
theorem interval_relative_uniform_hasNatAP_four {N L : Nat} [NeZero N] [Fact N.Prime]
    (hL : 2 * L < N) (hLfour : 4 ≤ L) (hNL : N ≤ 8 * L)
    (B : Finset (Fin L)) (delta alpha : Real)
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hsmall : 4 * alpha ^ (1 / 8 : Real) ≤ delta ^ 4 / 8192)
    (hlarge : 8192 < delta ^ 4 * N)
    (hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B delta)) alpha 2) :
    HasNatAP (B.image Fin.val) 4 := by
  have hLN : L ≤ N := by omega
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  have hcount : (N : Real) ^ 2 / 4096 ≤ (fourTermCount S : Real) := by
    have hnlr : (N : Real) ≤ 8 * L := by exact_mod_cast hNL
    have hs : (N : Real) ^ 2 ≤ (8 * (L : Real)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hnlr
    have hc := finiteInterval_fourTermCount_lower hLN hLfour
    dsimp [S]
    nlinarith
  apply finiteIntervalImage_hasNatAP B hL
  apply relative_uniform_hasModAP_four (by omega) (finiteIntervalImage N B) S delta alpha
    (finiteIntervalImage_subset B) hδ hδone hα
    (by simpa only [S, relativeBalanced_finiteIntervalImage hLN] using hu)
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have he := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (N : Real))
  have hl := mul_lt_mul_of_pos_right hlarge hNpos
  have hc := mul_le_mul_of_nonneg_left hcount (pow_nonneg hδ 4)
  nlinarith

end LeanProofs.GowersSzemeredi
