import GowersSzemeredi.Proofs16RelationWeightDensity

/-! Replace the complex relation weight by an approximate density in [0,1],
retaining the smaller base-set size in the additional error term. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A complex factorization estimate yields a real density estimate.
The perturbation error is proportional to the base size Y, not M. -/
theorem real_factor_error_of_complex {X Y M epsilon zeta delta : Real} {w : Complex}
    (hY : 0 ≤ Y) (hM : 0 ≤ M) (heps : 0 ≤ epsilon) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hw : ‖w - (delta : Complex)‖ ≤ zeta)
    (hfactor : ‖(X : Complex) - w * (Y : Complex)‖ ≤
      2 * epsilon * M + ‖w‖ * (2 * epsilon * M)) :
    |X - delta * Y| ≤ (4 + 2 * zeta) * epsilon * M + zeta * Y := by
  have hw1 : ‖w‖ ≤ 1 + zeta := by
    have h := norm_sub_norm_le w (delta : Complex)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd0] at h
    linarith
  have htri : ‖((X - delta * Y : Real) : Complex)‖ ≤
      ‖(X : Complex) - w * (Y : Complex)‖ + ‖(w - (delta : Complex)) * (Y : Complex)‖ := by
    convert norm_add_le ((X : Complex) - w * (Y : Complex))
      ((w - (delta : Complex)) * (Y : Complex)) using 1
    congr 1
    push_cast
    ring
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hY] at htri
  have hpert := mul_le_mul_of_nonneg_right hw hY
  have hmain := mul_le_mul_of_nonneg_right hw1 (show 0 ≤ 2 * epsilon * M by positivity)
  nlinarith only [htri, hfactor, hpert, hmain]

/-- The mixed-radius factorization with a real density and a fully explicit
error coefficient, instead of an unbounded complex factor. -/
theorem bohr_card_factor_of_split_density {N : Nat} [NeZero N] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (gamma : ι → ZMod N) (ell : κ → ZMod N)
    (a : ι → Nat) (b : κ → Nat) {c R : Nat}
    (hca : ∀ i, c ≤ a i) (hcb : ∀ j, c ≤ b j) (ha : ∀ i, 2 * a i < N)
    (hb : ∀ j, 2 * b j < N) (hc : 2 * c < N) (Lambda : Set (κ → centeredBall N R))
    (hsplit : ∀ (nu : ι → centeredBall N R) (mu : κ → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * ell j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ mu ∈ Lambda))
    {epsilon zeta delta : Real} (heps : 0 ≤ epsilon) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hweight : ‖latticeWeightMixed b c R Lambda - (delta : Complex)‖ ≤ zeta)
    (hband : ((mixedBohr gamma (fun i => a i + c)).card : Real) ≤
      (mixedBohr gamma (fun i => a i - c)).card + epsilon * N)
    (hband' : ((mixedBohr (Sum.elim gamma ell) (fun q => Sum.elim a b q + c)).card : Real) ≤
      (mixedBohr (Sum.elim gamma ell) (fun q => Sum.elim a b q - c)).card + epsilon * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ epsilon)
    (htrunc' : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ κ) - 1 ≤ epsilon) :
    |(mixedBohr (Sum.elim gamma ell) (fun q => Sum.elim a b q - c)).card -
      delta * ((mixedBohr gamma (fun i => a i - c)).card : Real)| ≤
      (4 + 2 * zeta) * epsilon * N + zeta * (mixedBohr gamma (fun i => a i - c)).card := by
  exact real_factor_error_of_complex (by positivity) (by positivity) heps hd0 hd1 hweight
    (bohr_card_factor_of_split_mixed gamma ell a b hca hcb ha hb hc Lambda hsplit
      hband hband' htrunc htrunc')

end LeanProofs.GowersSzemeredi
