import GowersSzemeredi.Proofs17PrimeRange

/-! A quadratic phase refutes the printed degree-k conclusion of
Proposition 17.2 even in its corrected characteristic range. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private lemma phase_add (x y : ZMod 3) :
    exponential (x + y) = exponential x * exponential y :=
  AddChar.map_add_eq_mul (ZMod.stdAddChar (N := 3)) x y

private lemma phase_star (x : ZMod 3) :
    star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := 3)) x).symm

private lemma phase_norm (x : ZMod 3) : ‖exponential x‖ = 1 :=
  AddChar.norm_apply (ZMod.stdAddChar (N := 3)) x

private lemma phase_sum (x : ZMod 3) :
    (∑ s : ZMod 3, exponential (x * s)) = if x = 0 then (3 : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar 3)

private def quadraticPhase (b c : ZMod 3) (s : ZMod 3) : Complex :=
  exponential (s ^ 2 + b * s + c)

private lemma quadratic_difference (b c h s : ZMod 3) :
    difference (quadraticPhase b c) h s =
      exponential (2 * h * s + (b * h - h ^ 2)) := by
  simp only [difference, quadraticPhase, phase_star, ← phase_add]
  congr 1
  ring

private lemma one_difference (f : ZMod 3 → Complex) (x : Point 3 1) :
    cubeDifference f x = difference f (x 0) := by
  funext s
  simp only [cubeDifference, List.ofFn_succ, List.ofFn_zero, iteratedDifference]

private lemma quadratic_fourier (b c h : ZMod 3) :
    fourier (difference (quadraticPhase b c) h) (2 * h) =
      (3 : Complex) * exponential (b * h - h ^ 2) := by
  change (∑ s : ZMod 3, exponential (-(s * (2 * h))) *
    difference (quadraticPhase b c) h s) = _
  simp_rw [quadratic_difference, ← phase_add]
  have heq (s : ZMod 3) : -(s * (2 * h)) + (2 * h * s + (b * h - h ^ 2)) =
      b * h - h ^ 2 := by ring
  simp_rw [heq]
  simp [ZMod.card]

private lemma quadratic_fourier_norm (b c h : ZMod 3) :
    ‖fourier (difference (quadraticPhase b c) h) (2 * h)‖ = 3 := by
  rw [quadratic_fourier, norm_mul, phase_norm]
  norm_num

private lemma quadratic_sum_norm_sq (b c h : ZMod 3) :
    ‖∑ s : ZMod 3, difference (quadraticPhase b c) h s‖ ^ 2 =
      if h = 0 then (9 : Real) else 0 := by
  classical
  simp_rw [quadratic_difference, phase_add]
  rw [← Finset.sum_mul, phase_sum]
  have htwo : (2 : ZMod 3) ≠ 0 := by decide
  have heq : (2 : ZMod 3) * h = 0 ↔ h = 0 := by
    simp [mul_eq_zero, htwo]
  simp only [heq]
  by_cases hh : h = 0 <;> norm_num [hh, norm_mul, phase_norm]

private lemma sum_one_points (F : ZMod 3 → Real) :
    (∑ x : Point 3 1, F (x 0)) = ∑ h : ZMod 3, F h := by
  simpa using (Equiv.funUnique (Fin 1) (ZMod 3)).sum_comp F

private lemma quadratic_energy (b c : ZMod 3) :
    (∑ x : Point 3 1, ‖∑ s : ZMod 3, cubeDifference (quadraticPhase b c) x s‖ ^ 2) = 9 := by
  classical
  simp_rw [one_difference, quadratic_sum_norm_sq]
  rw [sum_one_points (fun h => if h = 0 then (9 : Real) else 0)]
  simp

private lemma quadratic_twist_energy (phi : ZMod 3 → ZMod 3)
    (hp : PolynomialOn 1 Finset.univ phi) :
    (∑ x : Point 3 1,
      ‖∑ s : ZMod 3, cubeDifference (phaseTwist (quadraticPhase 0 0) phi) x s‖ ^ 2) = 9 := by
  obtain ⟨c, hc⟩ := hp
  have hphi (s : ZMod 3) : phi s = c 0 + c 1 * s := by
    simpa [Fin.sum_univ_two] using hc s (Finset.mem_univ s)
  have heq : phaseTwist (quadraticPhase 0 0) phi = quadraticPhase (-c 1) (-c 0) := by
    funext s
    simp only [phaseTwist, quadraticPhase, ← phase_add, hphi]
    congr 1
    ring
  rw [heq]
  exact quadratic_energy _ _

/-- The degree-k conclusion, even after imposing positive dimension,
0<alpha<=1/2 and the corrected prime characteristic range. -/
def proposition_17_2_degree_k_in_prime_range : Prop :=
  ∀ (N k : Nat) [NeZero N] [Fact N.Prime]
      (f : ZMod N → Complex) (sigma : Point N k → ZMod N) (alpha : Real),
    0 < k → k + 1 < N → 0 < alpha → alpha ≤ 1 / 2 →
    DiscValued f → IsMultilinear sigma →
    alpha * (N : Real) ^ (k + 2) ≤
      ∑ x : Point N k, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 →
    ∃ phi : ZMod N → ZMod N,
      PolynomialOn k Finset.univ phi ∧
      alpha * (N : Real) ^ (k + 2) ≤
        ∑ x : Point N k, ‖∑ s : ZMod N, cubeDifference (phaseTwist f phi) x s‖ ^ 2

/-- At N=3,k=1, a quadratic phase has full Fourier energy27, but every
linear phase twist leaves energy9, below the required27/2. -/
theorem proposition_17_2_printed_degree_counterexample :
    ¬ proposition_17_2_degree_k_in_prime_range := by
  classical
  intro claim
  have hf : DiscValued (quadraticPhase 0 0) := by
    intro s
    exact (phase_norm _).le
  have hsigma : IsMultilinear (fun x : Point 3 1 => 2 * x 0) := by
    refine ⟨fun e => if e = (fun _ => true) then 2 else 0, ?_⟩
    intro x
    rw [Finset.sum_eq_single (fun _ : Fin 1 => true)]
    · simp
    · intro e _ he
      simp only [if_neg he, zero_mul]
    · simp
  have henergy : (1 / 2 : Real) * (3 : Real) ^ (1 + 2 : Nat) ≤
      ∑ x : Point 3 1, ‖fourier (cubeDifference (quadraticPhase 0 0) x) (2 * x 0)‖ ^ 2 := by
    simp_rw [one_difference, quadratic_fourier_norm]
    norm_num [Point, ZMod.card]
  obtain ⟨phi, hp, hbad⟩ := claim 3 1 (quadraticPhase 0 0) (fun x => 2 * x 0) (1 / 2)
    (by omega) (by omega) (by norm_num) (by norm_num) hf hsigma henergy
  rw [quadratic_twist_energy phi hp] at hbad
  norm_num at hbad

end LeanProofs.GowersSzemeredi
