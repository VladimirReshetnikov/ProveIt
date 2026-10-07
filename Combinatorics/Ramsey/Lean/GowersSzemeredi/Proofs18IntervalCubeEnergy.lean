import GowersSzemeredi.Proofs18IntervalCubeGeometry
import GowersSzemeredi.Proofs17PhaseRemoval

/-! Exact weighted cube energy under a change of ambient modulus. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

noncomputable instance intervalCube_fintype (L d : Nat) : Fintype (IntervalCube L d) := by
  classical
  exact Fintype.ofFinite _

/-- Embed a function on [0,L) into a cyclic group, extending it by zero. -/
def intervalExtension {L : Nat} (N : Nat) (g : Fin L → Complex) : ZMod N → Complex :=
  fun x => if hx : x.val < L then g ⟨x.val, hx⟩ else 0

theorem intervalExtension_natCast {N L : Nat} [NeZero N] (hL : L ≤ N)
    (g : Fin L → Complex) (i : Fin L) : intervalExtension N g (i : Nat) = g i := by
  simp only [intervalExtension, ZMod.val_natCast_of_lt (i.isLt.trans_le hL), dif_pos i.isLt]

/-- The weighted sum of integer cube patterns, with the usual parity signs. -/
def intervalCubeForm {L : Nat} (d : Nat) (g : Fin L → Complex) : Complex :=
  ∑ v : IntervalCube L d, ∏ e : Fin d → Bool, parityConj e (g (v.1 e))

/-- No-wrap identifies the full modular cube form with a sum depending only
on the interval function. All cubes leaving the interval have zero weight. -/
theorem cubeForm_intervalExtension {N L d : Nat} [NeZero N]
    (hsize : (d + 1) * L ≤ N) (g : Fin L → Complex) :
    cubeForm (fun _ : Fin d → Bool => intervalExtension N g) = intervalCubeForm d g := by
  classical
  have hL : L ≤ N := (Nat.le_mul_of_pos_left L (by omega)).trans hsize
  let F : Point N d × ZMod N → Complex := fun p =>
    ∏ e : Fin d → Bool, parityConj e (intervalExtension N g (cubeArgument p.2 p.1 e))
  have hzero (p : Point N d × ZMod N)
      (hp : ¬ ∀ e, (cubeArgument p.2 p.1 e).val < L) : F p = 0 := by
    obtain ⟨e, he⟩ := not_forall.mp hp
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [parityConj, intervalExtension, he]
  have hrestrict : (∑ p : Point N d × ZMod N, F p) =
      ∑ p : SupportedIntervalCube N L d, F p.1 := by
    exact Finset.sum_congr_set {p : Point N d × ZMod N | ∀ e, (cubeArgument p.2 p.1 e).val < L}
      F (fun p => F p.1) (fun _ _ => rfl) hzero
  calc
    _ = ∑ p : Point N d × ZMod N, F p := by rw [Fintype.sum_prod_type]; rfl
    _ = ∑ p : SupportedIntervalCube N L d, F p.1 := hrestrict
    _ = ∑ v : IntervalCube L d, F ((intervalCubeEquiv hsize).symm v).1 :=
      ((intervalCubeEquiv hsize).symm.sum_comp (fun p => F p.1)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.prod_congr rfl
      intro e _
      change parityConj e (intervalExtension N g
        (cubeArgument (v.toSupported hL).1.2 (v.toSupported hL).1.1 e)) = _
      rw [IntervalCube.toSupported_vertex, intervalExtension_natCast hL]

/-- Exact preservation of unnormalized uniformity energy when an interval
function is placed in either of two sufficiently large moduli. -/
theorem intervalExtension_uniformEnergy_eq {N M L k : Nat} [NeZero N] [NeZero M]
    (hN : (k + 2) * L ≤ N) (hM : (k + 2) * L ≤ M) (g : Fin L → Complex) :
    (∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference (intervalExtension N g) a s‖ ^ 2) =
      ∑ a : Point M k, ‖∑ s : ZMod M, cubeDifference (intervalExtension M g) a s‖ ^ 2 := by
  have hcomplex : cubeForm (fun _ : Fin (k + 1) → Bool => intervalExtension N g) =
      cubeForm (fun _ : Fin (k + 1) → Bool => intervalExtension M g) :=
    (cubeForm_intervalExtension hN g).trans (cubeForm_intervalExtension hM g).symm
  rw [constant_cubeForm_eq_sum_cubeDifference, constant_cubeForm_eq_sum_cubeDifference,
    sum_cube_succ_eq_sum_norm_sq, sum_cube_succ_eq_sum_norm_sq] at hcomplex
  exact Complex.ofReal_injective hcomplex

/-- Changing modulus changes normalized uniformity by the exact factor
(N/M)^(k+2), even though the unnormalized energy is unchanged. -/
theorem intervalExtension_uniform_iff {N M L k : Nat} [NeZero N] [NeZero M]
    (hN : (k + 2) * L ≤ N) (hM : (k + 2) * L ≤ M)
    (g : Fin L → Complex) (alpha : Real) :
    UniformOfDegree (intervalExtension N g) alpha k ↔
      UniformOfDegree (intervalExtension M g) (alpha * ((N : Real) / M) ^ (k + 2)) k := by
  have hMne : (M : Real) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hscale : (alpha * ((N : Real) / M) ^ (k + 2)) * (M : Real) ^ (k + 2) =
      alpha * (N : Real) ^ (k + 2) := by rw [div_pow]; field_simp
  unfold UniformOfDegree
  rw [intervalExtension_uniformEnergy_eq hN hM g, hscale]

end LeanProofs.GowersSzemeredi
