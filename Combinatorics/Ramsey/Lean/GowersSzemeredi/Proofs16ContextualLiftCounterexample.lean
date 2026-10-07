import GowersSzemeredi.Proofs16NonUnitIntervalSlabs
import GowersSzemeredi.Proofs16SlabStructuredPair
import GowersSzemeredi.Proofs16ContextualInduction
import GowersSzemeredi.Proofs16FullGoodDomain
import GowersSzemeredi.Proofs16SelectionReserve
import Mathlib.Data.Nat.Prime.Infinite

/-! The universal common-base lifting contract is false in every positive
dimension, even with the actual product property and structured-pair fields.
The counterexample retains all fields of a complete common-base witness.
It does not refute an existential selection or the structural theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Genuine upstream inputs with a common-base witness whose entire good
domain has no unit cover, at every sufficiently large prime modulus. The
same witness admits a further unit domain of the required source mass. -/
theorem section16_genuine_contextual_obstructions {k : Nat} (hk : 1 ≤ k) :
    ∃ theta : Real, 0 < theta ∧ theta ≤ 1 ∧ ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∃ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
          HasProductProperty B phi 1 ∧ Section16StructuredPair theta 1 B phi ∧
          ∃ D : Section16CommonBaseData theta 1 B phi,
            ¬ MultiplyLinearFunction 1 1
              (section16GoodDomain B (D.H ∩ D.J) D.Y D.x0) (section16PhiOne phi D.x0) ∧
            Section16SelectedUnitDomain D := by
  classical
  obtain ⟨R, N₀, hR, hwords⟩ := exists_nonunit_interval_slabs k
  let theta : Real := 1 / (8 * R)
  have hRpos : (0 : Real) < R := by exact_mod_cast hR
  have hRone : (1 : Real) ≤ R := by exact_mod_cast hR
  have ht : 0 < theta := by dsimp [theta]; positivity
  have ht1 : theta ≤ 1 := by
    dsimp [theta]
    exact (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨theta, ht, ht1, N₀, ?_⟩
  intro N _ _ hN
  obtain ⟨L, f, hRN, hL, hLN, hsize, hmass, hf, hnot⟩ := hwords N hN
  let A := (modInterval N 0 L).carrier
  let S := (modInterval N 0 R).carrier
  let B := lastProductSet (Finset.univ : Finset (Point N k)) A
  let phi : Point N (k + 1) → ZMod N := fun z => f (section16Last z)
  have hA : theta * N ≤ (A.card : Real) := by
    have hc : A.card = L := modInterval_zero_isProper hLN
    rw [hc]
    exact hmass
  have hS : (S.card : Real) ≤ theta⁻¹ := by
    have hc : S.card = R := modInterval_zero_isProper hRN
    rw [hc]
    dsimp [theta]
    simp only [one_div, inv_inv]
    linarith only [hRpos]
  have hcommon : section16ThetaOne theta 1 k / 4 * (N : Real) ≤ A.card := by
    have hth : section16ThetaOne theta 1 k ≤ theta :=
      (section16ThetaOne_le_density_sixteen k ht ht1 (by norm_num) (by norm_num)).trans
        (pow_le_of_le_one ht.le ht1 (by norm_num : (16 : Nat) ≠ 0))
    apply le_trans (mul_le_mul_of_nonneg_right (show section16ThetaOne theta 1 k / 4 ≤ theta by linarith) (Nat.cast_nonneg N)) hA
  let D := section16SlabCommonBaseData hk A f (0 : Point N k) ht ht1
    (by norm_num : (0 : Real) < 1) (by norm_num : (1 : Real) ≤ 1) hcommon
  refine ⟨B, phi, section16_interval_slab_unit_product f (fun x _ => hf x) hsize,
    section16_slab_structured_pair hk A S f (fun x _ => hf x) ht ht1
      (by norm_num) (by norm_num) hA hS, D, ?_, ?_⟩
  · intro hcover
    have hdom := section16SlabCommonBaseData_good_domain hk A f (0 : Point N k) ht ht1
      (by norm_num : (0 : Real) < 1) (by norm_num : (1 : Real) ≤ 1) hcommon
    change MultiplyLinearFunction 1 1
      (section16GoodDomain (lastProductSet Finset.univ A) (D.H ∩ D.J) D.Y D.x0)
      (section16PhiOne (fun z => f (section16Last z)) (0 : Point N k)) at hcover
    rw [hdom, section16PhiOne_last_function] at hcover
    exact hnot hcover
  · apply D.selected_unit_domain_of_value_budget ht ht1 (by norm_num) (by norm_num)
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (show B.image phi ⊆ S from ?_))) hS
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf _

/-- Literal negation of the previously unasserted universal lifting
predicate. The quantifier over every common-base witness is essential. -/
theorem section16_contextual_lift_counterexample {k : Nat} (hk : 1 ≤ k) :
    ¬ Section16ContextualLiftAt k := by
  intro hlift
  obtain ⟨theta, ht, ht1, Nword, hword⟩ := section16_genuine_contextual_obstructions hk
  obtain ⟨Nlift, hNlift⟩ := hlift theta 1 ht ht1 (by norm_num) (by norm_num)
  obtain ⟨N, hN, hprime⟩ := Nat.exists_infinite_primes (max Nword Nlift)
  letI : Fact N.Prime := ⟨hprime⟩
  letI : NeZero N := ⟨hprime.ne_zero⟩
  obtain ⟨B, phi, hprod, hstruct, D, hnot, _hselected⟩ := hword N ((le_max_left _ _).trans hN)
  exact hnot (hNlift N ((le_max_right _ _).trans hN) B phi hprod hstruct D)

end LeanProofs.GowersSzemeredi
