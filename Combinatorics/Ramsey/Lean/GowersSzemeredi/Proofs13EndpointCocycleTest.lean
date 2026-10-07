import GowersSzemeredi.Proofs13EndpointCharacterOrthogonality

/-! A derivative cocycle forces dominant frequencies to add, except on
triples charged to their squared character approximation errors. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem endpoint_difference_cocycle {N : Nat} (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) (h h' x : ZMod N) :
    difference g (h + h') x = difference g h (x - h') * difference g h' x := by
  have hu : star (g (x - h')) * g (x - h') = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hg]
    norm_num
  simp only [difference]
  rw [show x - h' - h = x - (h + h') by abel]
  calc
    _ = (g x * star (g (x - (h + h')))) * (star (g (x - h')) * g (x - h')) := by rw [hu, mul_one]
    _ = _ := by ring

theorem endpoint_secondDifference_cocycle {N : Nat} (g : ZMod N → Complex)
    (hg : ∀ x, ‖g x‖ = 1) (h h' k x : ZMod N) :
    secondDifference g (h + h') k x =
      secondDifference g h k (x - h') * secondDifference g h' k x := by
  have hu : ∀ x, ‖difference g k x‖ = 1 := fun x => iteratedDifference_unit_norm g hg [k] x
  simpa only [secondDifference, difference_comm g _ k] using
    endpoint_difference_cocycle (difference g k) hu h h' x

theorem endpoint_character_cocycle_test {N : Nat} [NeZero N]
    (F₀ F₁ F₂ : ZMod N → Complex) (hF₂ : ∀ x, ‖F₂ x‖ = 1)
    (z₀ z₁ z₂ : Complex) (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (r₀ r₁ r₂ h : ZMod N) (hcocycle : ∀ x, F₀ x = F₁ (x - h) * F₂ x) :
    (if r₀ = r₁ + r₂ then (0 : Real) else 1) ≤ 3 / 2 *
      (endpointL2Error F₀ (endpointCharacter z₀ r₀) +
       endpointL2Error F₁ (endpointCharacter z₁ r₁) +
       endpointL2Error F₂ (endpointCharacter z₂ r₂)) := by
  by_cases hr : r₀ = r₁ + r₂
  · rw [if_pos hr]
    positivity [endpointL2Error_nonneg F₀ (endpointCharacter z₀ r₀),
      endpointL2Error_nonneg F₁ (endpointCharacter z₁ r₁),
      endpointL2Error_nonneg F₂ (endpointCharacter z₂ r₂)]
  · rw [if_neg hr]
    have hz : ‖z₁ * z₂ * exponential (-(r₁ * h))‖ = 1 := by
      rw [norm_mul, norm_mul, hz₁, hz₂, endpoint_exponential_norm]; norm_num
    have hp (x : ZMod N) := endpoint_unit_product_error (F₁ (x - h)) (F₂ x)
      (endpointCharacter z₁ r₁ (x - h)) (endpointCharacter z₂ r₂ x)
      (endpointCharacter z₀ r₀ x) (hF₂ x) (endpointCharacter_norm z₁ hz₁ r₁ (x - h))
    simp_rw [← hcocycle, endpointCharacter_shift_product,
      norm_sub_rev (endpointCharacter z₀ r₀ _) (F₀ _)] at hp
    have havg := Finset.expect_le_expect (fun x (_ : x ∈ (Finset.univ : Finset (ZMod N))) => hp x)
    rw [← Finset.mul_expect, Finset.expect_add_distrib, Finset.expect_add_distrib] at havg
    have hshift : (𝔼 x : ZMod N, ‖F₁ (x - h) - endpointCharacter z₁ r₁ (x - h)‖ ^ 2) =
        endpointL2Error F₁ (endpointCharacter z₁ r₁) :=
      Fintype.expect_equiv (Equiv.subRight h) _ _ (fun _ => rfl)
    rw [hshift] at havg
    change endpointL2Error (endpointCharacter z₀ r₀)
      (endpointCharacter (z₁ * z₂ * exponential (-(r₁ * h))) (r₁ + r₂)) ≤ _ at havg
    rw [endpointCharacter_orthogonality _ _ hz₀ hz _ _ hr] at havg
    change 2 ≤ 3 * (endpointL2Error F₀ (endpointCharacter z₀ r₀) +
      endpointL2Error F₁ (endpointCharacter z₁ r₁) + endpointL2Error F₂ (endpointCharacter z₂ r₂)) at havg
    linarith only [havg]

end LeanProofs.GowersSzemeredi
