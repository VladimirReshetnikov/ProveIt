import GowersSzemeredi.Proofs18DensityIterationGrowth
import GowersSzemeredi.Proofs18QuadraticIteration

/-! Closed length bounds for the four-term interval and cyclic theorems. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def quadraticIntervalClosedThreshold (delta : Real) : Real :=
  densityIterationClosedThreshold (intervalQuadraticStepThreshold delta)
    (intervalQuadraticLengthFactor delta) (intervalQuadraticLengthExponent delta)
    ⌈(intervalQuadraticGain delta)⁻¹⌉₊

theorem quadraticIntervalIterationThreshold_le_closed {delta : Real} (hδ : 0 < delta) :
    quadraticIntervalIterationThreshold delta ≤ quadraticIntervalClosedThreshold delta := by
  obtain ⟨_, hρ, hc⟩ := intervalQuadratic_constants_pos hδ
  exact densityIterationThreshold_le_closed hc hρ _

theorem quadratic_interval_szemeredi_closed
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (L : Nat) (hL : quadraticIntervalClosedThreshold delta ≤ L)
    (B : Finset (Fin L)) (hcard : delta * L ≤ B.card) : HasNatAP (B.image Fin.val) 4 :=
  quadratic_interval_szemeredi_recursive delta hδ hδone L
    ((quadraticIntervalIterationThreshold_le_closed hδ).trans hL) B hcard

/-- A progression in the natural index set casts back to a nonconstant
modular progression. The second point ensures its positive step is < N. -/
theorem finiteInterval_hasModAP_of_hasNatAP {N k : Nat} [NeZero N]
    (B : Finset (Fin N)) (hk : 2 ≤ k) (hAP : HasNatAP (B.image Fin.val) k) :
    HasModAP (finiteIntervalImage N B) k := by
  classical
  obtain ⟨a, d, hd, hAP⟩ := hAP
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hAP 1 (by omega))
  have hdN : d < N := by have := j.isLt; omega
  have hd0 : (d : ZMod N) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt hd hdN ((ZMod.natCast_eq_zero_iff d N).mp h)
  refine ⟨(a : ZMod N), (d : ZMod N), bne_iff_ne.mpr hd0, ?_⟩
  intro i hi
  obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp (hAP i hi)
  apply Finset.mem_image.mpr
  refine ⟨j, hj, ?_⟩
  rw [hji]
  push_cast
  rfl

/-- The closed interval bound implies the cyclic four-term conclusion for
every nonzero modulus. The final modulus itself need not be prime. -/
theorem quadratic_cyclic_szemeredi_closed
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (N : Nat) [NeZero N] (hN : quadraticIntervalClosedThreshold delta ≤ N)
    (A : Finset (ZMod N)) (hcard : delta * N ≤ A.card) : HasModAP A 4 := by
  classical
  let B : Finset (Fin N) := Finset.univ.filter fun i => ((i : Nat) : ZMod N) ∈ A
  have himage : finiteIntervalImage N B = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨⟨x.val, ZMod.val_lt x⟩, ?_, ZMod.natCast_zmod_val x⟩
      simpa [B] using hx
  have hBcard : B.card = A.card := by
    rw [← himage, finiteIntervalImage_card (le_refl N)]
  have hAP := quadratic_interval_szemeredi_closed delta hδ hδone N hN B
    (by simpa only [hBcard] using hcard)
  rw [← himage]
  exact finiteInterval_hasModAP_of_hasNatAP B (by norm_num) hAP

end LeanProofs.GowersSzemeredi
