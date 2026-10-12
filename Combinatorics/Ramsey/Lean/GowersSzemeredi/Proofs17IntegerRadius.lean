import GowersSzemeredi.Proofs17FinitePatterns

/-! The integer-radius scope of Corollaries 17.5 and 17.6.
Negative radii give empty coefficient domains in positive dimension.
The affine result needs that dimension condition when the radius is negative. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Corollary 17.5 for every integer radius, with the literal integer exponent. -/
theorem corollary_17_5_integer_radius (k : Nat) (r : Int) :
    ∃ F : Finset ((Fin k → Bool) → Int),
      (F.card : Real) ≤ (2 : Real) ^ (2 * r * (k : Int) ^ 3) ∧
      ∀ alpha : Fin k → Real,
        (∀ i, -(r : Real) < alpha i ∧ alpha i < r) → floorDotPattern alpha ∈ F := by
  classical
  by_cases hr : 0 ≤ r
  · lift r to Nat using hr
    obtain ⟨F, hcard, hmem⟩ := corollary_17_5_holds k r
    refine ⟨F, ?_, ?_⟩
    · have hcast : (F.card : Real) ≤ (2 : Real) ^ (2 * r * k ^ 3 : Nat) := by
        exact_mod_cast hcard
      simpa only [← Nat.cast_ofNat (R := Int), ← Nat.cast_mul, ← Nat.cast_pow,
        zpow_natCast] using hcast
    · simpa only [Int.cast_natCast] using hmem
  by_cases hk : k = 0
  · subst k
    refine ⟨{fun _ => 0}, by simp, ?_⟩
    intro alpha _
    simp only [Finset.mem_singleton]
    funext e
    simp [floorDotPattern]
  refine ⟨∅, ?_, ?_⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · intro alpha ha
    have hi := ha ⟨0, Nat.pos_of_ne_zero hk⟩
    have hrR : (r : Real) < 0 := by exact_mod_cast lt_of_not_ge hr
    exfalso
    linarith [hi.1, hi.2]

/-- Corollary 17.6 for integer radii. In dimension zero the radius must be
nonnegative, because the unrestricted affine offset still produces patterns. -/
theorem corollary_17_6_integer_radius (k M : Nat) (r : Int) (hM : 0 < M)
    (hrk : 0 ≤ r ∨ 1 ≤ k) :
    ∃ F : Finset ((Fin k → Bool) → ZMod M),
      (F.card : Real) ≤ M * (2 : Real) ^ (2 * r * ((k : Int) + 1) ^ 3) ∧
      ∀ (alpha0 : Real) (alpha : Fin k → Real),
        (∀ i, -(r : Real) < alpha i ∧ alpha i < r) →
        floorAffinePattern alpha0 alpha ∈ F := by
  classical
  by_cases hr : 0 ≤ r
  · lift r to Nat using hr
    obtain ⟨F, hcard, hmem⟩ := corollary_17_6_holds k M r hM
    refine ⟨F, ?_, ?_⟩
    · have hcast : (F.card : Real) ≤ M * (2 : Real) ^ (2 * r * (k + 1) ^ 3 : Nat) := by
        exact_mod_cast hcard
      have he : ((2 * r * (k + 1) ^ 3 : Nat) : Int) =
          2 * (r : Int) * ((k : Int) + 1) ^ 3 := by simp
      rw [← he, zpow_natCast]
      exact hcast
    · simpa only [Int.cast_natCast] using hmem
  have hk : 1 ≤ k := hrk.resolve_left hr
  refine ⟨∅, ?_, ?_⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · intro alpha0 alpha ha
    have hi := ha ⟨0, hk⟩
    have hrR : (r : Real) < 0 := by exact_mod_cast lt_of_not_ge hr
    exfalso
    linarith [hi.1, hi.2]

/-- The negative-radius, zero-dimensional affine reading is false already
at modulus one and radius minus one: one pattern cannot fit a budget of 1/4. -/
theorem corollary_17_6_negative_radius_zero_dimension_false :
    ¬ ∃ F : Finset ((Fin 0 → Bool) → ZMod 1),
      (F.card : Real) ≤ (1 : Real) * (2 : Real) ^ (2 * (-1 : Int) * (0 + 1) ^ 3) ∧
      ∀ (alpha0 : Real) (alpha : Fin 0 → Real),
        (∀ i, -((-1 : Int) : Real) < alpha i ∧ alpha i < ((-1 : Int) : Real)) →
        floorAffinePattern alpha0 alpha ∈ F := by
  rintro ⟨F, hcard, hmem⟩
  have hnonempty : F.Nonempty :=
    ⟨floorAffinePattern 0 (fun i => Fin.elim0 i), hmem 0 _ (fun i => Fin.elim0 i)⟩
  have hcard1 : (1 : Real) ≤ F.card := by
    exact_mod_cast Finset.one_le_card.mpr hnonempty
  norm_num at hcard
  linarith

end LeanProofs.GowersSzemeredi
