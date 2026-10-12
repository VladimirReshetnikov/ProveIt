import GowersSzemeredi.Sections17_18

/-! Certify the strict positivity requirement in Proposition 17.7. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def proposition_17_7_nonnegative_parameter : Prop :=
  ∀ (N k m : Nat) [NeZero N] [Fact N.Prime] (f : ZMod N → Complex)
      (P : Box N k) (sigma : Point N k → ZMod N) (alpha : Real),
    0 ≤ alpha → 0 < k → Odd m → P.width = m →
    (∀ i, (P.axis i).length = m) → P.commonDiff != 0 →
    (m : Real) ≤ Real.sqrt N → DiscValued f → IsMultilinear sigma →
    alpha * (N : Real) ^ 2 * (m : Real) ^ k ≤
      ∑ x ∈ P.carrier, ‖fourier (cubeDifference f x) (sigma x)‖ ^ 2 →
    ∃ phi : ZMod N → ZMod N, ∃ M l : Nat,
      ∃ Q : Fin M → ModAP N,
        PolynomialOn (k + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper ∧ ((Q i).length = l ∨ (Q i).length = l + 1)) ∧
        (m : Real) / (3 * k) ≤ l ∧
        ¬ UniformOnPartition (phaseTwist f phi) k
          ((2 : Real) ^ (-(2 * (k + 1) ^ 3 : Int)) * alpha) Q (l + 1)

/-- Zero remains zero-uniform after every phase twist and every partition. -/
theorem zero_phase_twist_uniform_on_partition (phi : ZMod 3 → ZMod 3)
    (M m : Nat) (Q : Fin M → ModAP 3) :
    UniformOnPartition (phaseTwist (fun _ => 0) phi) 1 0 Q m := by
  simp [UniformOnPartition, phaseTwist, restrictToCell, cubeDifference,
    List.ofFn_succ, List.ofFn_zero, iteratedDifference, difference]

/-- The zero function refutes the alpha=0 endpoint, even for a positive
one-dimensional box with odd side length and prime modulus. -/
theorem proposition_17_7_zero_parameter_counterexample :
    ¬ proposition_17_7_nonnegative_parameter := by
  classical
  intro claim
  let P : Box 3 1 := {
    axis := fun _ => modInterval 3 0 1
    commonDiff := 1
    axis_step := fun _ => rfl }
  have hwidth : P.width = 1 := by simp [P, Box.width, modInterval]
  have hdisc : DiscValued (fun _ : ZMod 3 => (0 : Complex)) := by
    intro s
    norm_num
  have hmulti : IsMultilinear (fun _ : Point 3 1 => (0 : ZMod 3)) := by
    refine ⟨fun _ => 0, ?_⟩
    intro x
    simp
  obtain ⟨phi, M, l, Q, _, _, _, _, hnot⟩ :=
    claim 3 1 1 (fun _ => 0) P (fun _ => 0) 0 (by norm_num)
      (by omega) (by decide) hwidth (by intro i; rfl) (by norm_num [P])
      (by norm_num) hdisc hmulti (by simp only [zero_mul]; positivity)
  simp only [mul_zero] at hnot
  exact hnot (zero_phase_twist_uniform_on_partition phi M (l + 1) Q)

end LeanProofs.GowersSzemeredi
