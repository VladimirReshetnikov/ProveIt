import GowersSzemeredi.Sections14_15

/-! Separate source-scope refutations for the weighted sign and signed-Walsh
claims. Both examples use the prime modulus two. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def proposition_14_1_without_sign_hypothesis : Prop :=
  ∀ (N p : Nat) [NeZero N] (lambda : ZMod N → Real)
      (f : Fin p → Pair N → Complex) (sigma : Fin p → ZMod N → ZMod N)
      (alpha : Real),
    (∀ h, 0 ≤ lambda h) → (∀ i, DiscValued (f i)) →
    alpha * (N : Real) ^ (4 * p + 1) ≤
      ∑ h : ZMod N, lambda h *
        ∏ i : Fin p,
          ‖fourier (firstCoordinateCorrelation (f i) h) (sigma i h)‖ ^ 2 →
    alpha ^ 4 * (N : Real) ^ 3 ≤
      weightedSimultaneousAdditiveEnergy Finset.univ lambda sigma

/-- Zero weights refute the unrestricted alpha reading even at a prime modulus. -/
theorem proposition_14_1_negative_alpha_counterexample :
    ¬ proposition_14_1_without_sign_hypothesis := by
  intro h
  have hbad := h 2 1 (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (-1)
    (by intro i; norm_num) (by intro i; simp [DiscValued]) (by simp)
  norm_num [weightedSimultaneousAdditiveEnergy] at hbad

def lemma_15_1_without_odd_hypothesis : Prop :=
  ∀ (N k : Nat) [NeZero N], Nat.Prime N →
    ∀ (h : Point N k) (eta : (Fin k → Bool) → Int),
      (∀ i, h i ≠ 0) → IsTernaryCoefficient eta →
      (∀ A : Finset (Fin k), ∀ y z : Point N k,
        signedWalshMoment eta h y A = signedWalshMoment eta h z A) →
      IsModularMultiple eta (fun e => ∏ i, walshSign (N := N) (e i))

/-- The signed patterns collapse after reduction modulo two, so invariant
moments need not determine the coefficient function. -/
theorem lemma_15_1_even_prime_counterexample :
    ¬ lemma_15_1_without_odd_hypothesis := by
  intro claim
  let h : Point 2 2 := fun _ => 1
  let eta : (Fin 2 → Bool) → Int := fun e => if e 0 then 0 else 1
  have hnonzero : ∀ i, h i ≠ 0 := by intro i; norm_num [h]
  have hternary : IsTernaryCoefficient eta := by
    intro e
    simp only [eta]
    split_ifs <;> norm_num
  have hsign (b : Bool) : walshSign (N := 2) b = 1 := by
    cases b <;> decide
  have hsum : (∑ e : Fin 2 → Bool, (eta e : ZMod 2)) = 0 := by decide
  have hmoment (A : Finset (Fin 2)) (y : Point 2 2) :
      signedWalshMoment eta h y A = 0 := by
    unfold signedWalshMoment
    calc
      _ = ∑ e : Fin 2 → Bool, (eta e : ZMod 2) * ∏ i ∈ A, (y i + 1) := by
        apply Finset.sum_congr rfl
        intro e _
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        simp [hsign, h]
      _ = (∑ e : Fin 2 → Bool, (eta e : ZMod 2)) * ∏ i ∈ A, (y i + 1) :=
        by rw [Finset.sum_mul]
      _ = 0 := by rw [hsum, zero_mul]
  have hinvariant : ∀ A : Finset (Fin 2), ∀ y z : Point 2 2,
      signedWalshMoment eta h y A = signedWalshMoment eta h z A := by
    intro A y z
    rw [hmoment, hmoment]
  obtain ⟨c, hc⟩ := claim 2 2 (by decide) h eta hnonzero hternary hinvariant
  have h0 := hc (fun _ => false)
  have h1 := hc (fun _ => true)
  norm_num [eta, walshSign] at h0 h1
  have hbad : (1 : ZMod 2) = 0 := h0.trans h1.symm
  norm_num at hbad

/-- The sum of slices cannot be moved inside a quadratic correlation.
For the constant-one function at N=3 and k=2, the source's proposed summed
slice is constant three, so its correlation is 27 while the cube correlation is 9. -/
theorem summed_slice_correlation_counterexample :
    let g : Pair 3 → Complex := fun _ => ∑ _u : ZMod 3, (1 : Complex)
    firstCoordinateCorrelation g 0 0 ≠
      higherCubeCorrelation (fun _ : Point 3 3 => (1 : Complex))
        (0 : Point 3 2) 0 := by
  norm_num [firstCoordinateCorrelation, higherCubeCorrelation, Point, ZMod.card]

end LeanProofs.GowersSzemeredi
