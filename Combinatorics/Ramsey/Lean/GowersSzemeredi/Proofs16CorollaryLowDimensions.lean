import GowersSzemeredi.Proofs16CorollaryFromInduction
import GowersSzemeredi.Proofs16DimensionTwo
import GowersSzemeredi.Proofs16BaseCaseEndpoint

/-! Corollary 16.11 dimension by dimension.

`corollary_16_11` quantifies over every dimension `k ≥ 1`. In a fixed
dimension it follows from Theorem 16.2 in that dimension alone
(`corollary_16_11_of_dimension_induction`). So the dimensions where Theorem
16.2 is proved give the corollary with its exact catalogue exponent
`section16CorollaryExponent alpha k`:

* `k = 1`, from Lemma 16.3;
* `k = 2`, from `theorem_16_2_at_two`.

The catalogue entry stays open, because higher dimensions need the
higher-dimensional structural induction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Corollary 16.11 in a single dimension `k`. -/
def Corollary1611At (k : Nat) : Prop :=
  ∀ (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N → Odd N →
      ∀ f : ZMod N → Complex, DiscValued f →
        ¬ UniformOfDegree f alpha (k + 1) →
        ∃ P : Box N k, ∃ mu : Point N k → ZMod N,
          IsMultilinear mu ∧
          (N : Real) ^ section16CorollaryExponent alpha k ≤ P.width ∧
          section16CorollaryExponent alpha k * P.carrier.card ≤
            section16LargeMultilinearFrequencyCount f P mu alpha

/-- The catalogue entry is exactly Corollary 16.11 in every positive dimension. -/
theorem corollary_16_11_iff_forall_dimension :
    corollary_16_11 ↔ ∀ k, 1 ≤ k → Corollary1611At k := by
  constructor
  · intro h k hk alpha ha haHalf
    exact h k alpha hk ha haHalf
  · intro h k alpha hk ha haHalf
    exact h k hk alpha ha haHalf

/-- Theorem 16.2 in dimension `k` gives Corollary 16.11 in dimension `k`. -/
theorem Theorem162At.corollary_16_11 {k : Nat} (hk : 1 ≤ k) (hth : Theorem162At k) :
    Corollary1611At k := by
  intro alpha ha haHalf
  obtain ⟨N0, hN0⟩ := corollary_16_11_of_dimension_induction hk hth alpha ha haHalf
  refine ⟨N0, fun N _ _ hN _hOdd f hf hnot ↦ ?_⟩
  obtain ⟨P, mu, _, hmu, hwidth, hmass⟩ := hN0 N hN f hf hnot
  refine ⟨P, mu, hmu, ?_, hmass⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hNreal
    (section16_corollary_common_exponent_lt_width ha haHalf k).le).trans hwidth

/-- **Corollary 16.11 in dimension one.** -/
theorem corollary_16_11_at_one : Corollary1611At 1 :=
  Theorem162At.corollary_16_11 le_rfl (show Theorem162At 1 from lemma_16_3_holds)

/-- **Corollary 16.11 in dimension two.** -/
theorem corollary_16_11_at_two : Corollary1611At 2 :=
  Theorem162At.corollary_16_11 (by norm_num) theorem_16_2_at_two

end LeanProofs.GowersSzemeredi
