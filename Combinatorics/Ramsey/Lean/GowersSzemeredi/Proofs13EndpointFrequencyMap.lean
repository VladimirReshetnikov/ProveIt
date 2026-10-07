import GowersSzemeredi.Proofs13EndpointDominantFourier
import GowersSzemeredi.Proofs13EndpointFiniteError

/-! A coherent symmetric frequency map for second derivatives, with exact
zero rows and averaged concentration defect controlled by the fourth cube
mean. No additive-correction assumption is used in this construction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpointCubeMean_difference_average {N d : Nat} [NeZero N] (g : ZMod N → Complex) :
    (𝔼 r : ZMod N, endpointCubeMean (difference g r) d) = endpointCubeMean g (d + 1) := by
  unfold endpointCubeMean
  simp_rw [cubeDifference_difference]
  calc
    _ = 𝔼 p : ZMod N × Point N d, 𝔼 x : ZMod N, (cubeDifference g (Fin.cons p.1 p.2) x).re := by
      rw [endpoint_expect_prod]
      simp only [cubeDifference_cons]
    _ = _ := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (d + 1) => ZMod N)) _ _ (fun _ => rfl)

theorem endpointCubeMean_secondDifference_average {N : Nat} [NeZero N] (g : ZMod N → Complex) :
    (𝔼 p : Pair N, endpointCubeMean (secondDifference g p.1 p.2) 2) = endpointCubeMean g 4 := by
  rw [endpoint_expect_prod]
  change (𝔼 k : ZMod N, 𝔼 l : ZMod N, endpointCubeMean (difference (difference g k) l) 2) = _
  simp_rw [endpointCubeMean_difference_average]

theorem endpointCubeMean_nonneg {N d : Nat} [NeZero N] (g : ZMod N → Complex) :
    0 ≤ endpointCubeMean g (d + 1) := by rw [endpointCubeMean_succ]; positivity

theorem endpointCubeMean_le_one {N d : Nat} [NeZero N] (g : ZMod N → Complex) (hg : DiscValued g) :
    endpointCubeMean g d ≤ 1 := by
  apply (endpointCubeMean_le_mean_norm g hg).trans
  exact Finset.expect_le Finset.univ_nonempty (fun x _ => hg x)

def endpointFrequencyMap {N : Nat} [NeZero N] (g : ZMod N → Complex) (p : Pair N) : ZMod N :=
  endpointDominantFrequency (secondDifference g p.1 p.2)

def endpointFrequencyDefect {N : Nat} [NeZero N] (g : ZMod N → Complex) (p : Pair N) : Real :=
  1 - endpointCubeMean (secondDifference g p.1 p.2) 2

theorem endpointFrequencyMap_symmetric {N : Nat} [NeZero N] (g : ZMod N → Complex) (k l : ZMod N) :
    endpointFrequencyMap g (k, l) = endpointFrequencyMap g (l, k) := by
  unfold endpointFrequencyMap secondDifference
  rw [difference_comm]

theorem difference_zero_of_unit {N : Nat} (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) :
    difference g 0 = fun _ => 1 := by
  funext x
  simp only [difference, sub_zero, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, hg]
  norm_num

theorem endpointFrequencyMap_zero_right {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) (k : ZMod N) :
    endpointFrequencyMap g (k, 0) = 0 := by
  have hunit : ∀ x, ‖difference g k x‖ = 1 := by
    intro x
    exact iteratedDifference_unit_norm g hg [k] x
  unfold endpointFrequencyMap secondDifference
  rw [difference_zero_of_unit _ hunit]
  exact endpointDominantFrequency_one

theorem endpointFrequencyDefect_bounds {N : Nat} [NeZero N] (g : ZMod N → Complex)
    (hg : DiscValued g) (p : Pair N) : 0 ≤ endpointFrequencyDefect g p ∧ endpointFrequencyDefect g p ≤ 1 := by
  have hdisc : DiscValued (secondDifference g p.1 p.2) := difference_discValued (difference_discValued hg _) _
  have hl := endpointCubeMean_le_one (d := 2) _ hdisc
  have hn := endpointCubeMean_nonneg (d := 1) (secondDifference g p.1 p.2)
  dsimp [endpointFrequencyDefect]
  constructor <;> linarith only [hl, hn]

theorem endpointFrequencyDefect_mean {N : Nat} [NeZero N] (g : ZMod N → Complex) :
    (𝔼 p : Pair N, endpointFrequencyDefect g p) = 1 - endpointCubeMean g 4 := by
  unfold endpointFrequencyDefect
  rw [Finset.expect_sub_distrib, Fintype.expect_const, endpointCubeMean_secondDifference_average]

theorem endpointFrequencyMap_concentration {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : ∀ x, ‖g x‖ = 1) (p : Pair N) :
    1 - endpointFrequencyDefect g p ≤
      ‖endpointFourierCoefficient (secondDifference g p.1 p.2) (endpointFrequencyMap g p)‖ ^ 2 := by
  have hunit : ∀ x, ‖secondDifference g p.1 p.2 x‖ = 1 :=
    fun x => iteratedDifference_unit_norm g hg [p.2, p.1] x
  simpa only [endpointFrequencyDefect, sub_sub_cancel, endpointFrequencyMap] using
    endpointDominantFrequency_concentration (secondDifference g p.1 p.2) hunit

end LeanProofs.GowersSzemeredi
