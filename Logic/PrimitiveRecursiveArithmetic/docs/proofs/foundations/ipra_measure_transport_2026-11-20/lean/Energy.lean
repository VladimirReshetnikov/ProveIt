import Truncation

/-! Rational energy calculations and bounded energy-window selection.
Ordinary Lean results; the object-iPRA translation remains a separate task. -/
namespace IPRAIntegration

/-- Average of two child values. -/
def mean2 (a b : Rat) : Rat := (a + b) / 2

/-- Squared detail at one binary refinement. -/
def detail2 (a b : Rat) : Rat := ((a - b) / 2) * ((a - b) / 2)

theorem dyadic_energy_identity (a b : Rat) :
    (a * a + b * b) / 2 = mean2 a b * mean2 a b + detail2 a b := by
  unfold mean2 detail2
  grind

theorem dyadic_residual_identity (a b : Rat) :
    ((a - mean2 a b) * (a - mean2 a b) +
      (b - mean2 a b) * (b - mean2 a b)) / 2 = detail2 a b := by
  unfold mean2 detail2
  grind

theorem dyadic_energy_monotone (a b : Rat) :
    mean2 a b * mean2 a b ≤ (a * a + b * b) / 2 := by
  have h := square_nonneg ((a - b) / 2)
  have he := dyadic_energy_identity a b
  unfold detail2 at he
  grind

/-- The exact finite sum of one-step energy increments. -/
theorem energy_telescope (E : Nat → Rat) (n : Nat) :
    E n = E 0 + sumN (fun j => E (j + 1) - E j) n := by
  induction n with
  | zero => simp only [sumN]; grind
  | succ n ih => simp only [sumN]; grind

/-- Exhaustive bounded search for an energy increment at most δ.
Returns the latest such increment, or none if every tested increment is large. -/
def smallWindow (E : Nat → Rat) (δ : Rat) : Nat → Option Nat
  | 0 => none
  | n + 1 => if E (n + 1) ≤ E n + δ then some n else smallWindow E δ n

theorem smallWindow_sound (E : Nat → Rat) (δ : Rat) (n j : Nat)
    (h : smallWindow E δ n = some j) :
    j < n ∧ E (j + 1) ≤ E j + δ := by
  induction n with
  | zero => simp [smallWindow] at h
  | succ n ih =>
      simp only [smallWindow] at h
      split at h
      · rename_i hj
        have he : n = j := Option.some.inj h
        subst j
        exact ⟨by omega, hj⟩
      · have hh := ih h
        exact ⟨by omega, hh.2⟩

/-- No witness implies growth by δ at each tested step. -/
theorem smallWindow_none_growth (E : Nat → Rat) (δ : Rat) (n : Nat)
    (h : smallWindow E δ n = none) :
    E 0 + (n : Rat) * δ ≤ E n := by
  induction n with
  | zero => grind
  | succ n ih =>
      simp only [smallWindow] at h
      split at h
      · contradiction
      · rename_i hn
        have hh := ih h
        have cast : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
          rw [Rat.natCast_add]
          rfl
        rw [cast]
        grind

/-- A bounded energy budget gives a finite small-increment witness.
For metastability apply E to iterated endpoints N(j+1)=N(j)+g(N(j)),
and put δ=ε². The output is an actual bounded-search result. -/
theorem energy_window (E : Nat → Rat) (δ B : Rat) (n : Nat)
    (hzero : 0 ≤ E 0) (hbound : E n ≤ B) (hbudget : B < (n : Rat) * δ) :
    ∃ j, smallWindow E δ n = some j ∧ j < n ∧ E (j + 1) ≤ E j + δ := by
  cases hh : smallWindow E δ n with
  | none =>
      have hg := smallWindow_none_growth E δ n hh
      have hf : False := by grind
      exact False.elim hf
  | some j =>
      exact ⟨j, rfl, smallWindow_sound E δ n j hh⟩

/-- Energy-tail-to-L2 comparison in cleared arithmetic. -/
theorem energy_tail {squareDistance energyGap ε : Rat}
    (hidentity : squareDistance = energyGap)
    (hgap : energyGap ≤ ε * ε) : squareDistance ≤ ε * ε := by
  rw [hidentity]
  exact hgap

/-- Simultaneously averages every pair of sibling cells. -/
theorem dyadic_energy_finite (a b : Nat → Rat) (n : Nat) :
    sumN (fun i => (a i * a i + b i * b i) / 2) n =
      sumN (fun i => mean2 (a i) (b i) * mean2 (a i) (b i)) n +
      sumN (fun i => detail2 (a i) (b i)) n := by
  simp only [dyadic_energy_identity, sumN_add]

/-- The arbitrary finite weighted square expansion. -/
theorem weighted_square_expansion (w f g : Nat → Rat) (n : Nat) :
    sumN (fun i => w i * ((f i - g i) * (f i - g i))) n =
      sumN (fun i => w i * (f i * f i)) n +
      sumN (fun i => w i * (g i * g i)) n -
      2 * sumN (fun i => w i * (f i * g i)) n := by
  induction n with
  | zero => simp only [sumN]; grind
  | succ n ih => simp only [sumN, ih]; grind

/-- The conditional-expectation energy identity after the finite cell-average
calculation supplies orthogonality. No limit or existence assertion is hidden
in this algebraic theorem. -/
theorem finite_orthogonal_energy (w f g : Nat → Rat) (n : Nat)
    (hcross : sumN (fun i => w i * (f i * g i)) n =
      sumN (fun i => w i * (g i * g i)) n) :
    sumN (fun i => w i * ((f i - g i) * (f i - g i))) n =
      sumN (fun i => w i * (f i * f i)) n -
      sumN (fun i => w i * (g i * g i)) n := by
  have h := weighted_square_expansion w f g n
  rw [hcross] at h
  grind

end IPRAIntegration
