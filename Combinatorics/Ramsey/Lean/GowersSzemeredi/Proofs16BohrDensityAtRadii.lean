import GowersSzemeredi.Proofs16PairedRelationDensity

/-! A factorization interface at the actual inner radii. Smoothing expands
these radii by 2c, so no subtraction of natural radii remains in the result. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_card_factor_at_radii {N : Nat} [NeZero N] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (gamma : ι → ZMod N) (ell : κ → ZMod N)
    (a : ι → Nat) (b : κ → Nat) {c R : Nat}
    (ha : ∀ i, 2 * (a i + c) < N) (hb : ∀ j, 2 * (b j + c) < N) (hc : 2 * c < N)
    (Lambda : Set (κ → centeredBall N R))
    (hsplit : ∀ (nu : ι → centeredBall N R) (mu : κ → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * ell j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧ mu ∈ Lambda))
    {epsilon zeta delta : Real} (heps : 0 ≤ epsilon) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hweight : ‖latticeWeightMixed (fun j => b j + c) c R Lambda - (delta : Complex)‖ ≤ zeta)
    (hband : ((mixedBohr gamma (fun i => a i + 2 * c)).card : Real) ≤
      (mixedBohr gamma a).card + epsilon * N)
    (hband' : ((mixedBohr (Sum.elim gamma ell) (fun q => Sum.elim a b q + 2 * c)).card : Real) ≤
      (mixedBohr (Sum.elim gamma ell) (Sum.elim a b)).card + epsilon * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ epsilon)
    (htrunc' : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ κ) - 1 ≤ epsilon) :
    |(mixedBohr (Sum.elim gamma ell) (Sum.elim a b)).card -
      delta * ((mixedBohr gamma a).card : Real)| ≤
      (4 + 2 * zeta) * epsilon * N + zeta * (mixedBohr gamma a).card := by
  have hab : Sum.elim (fun i => a i + c) (fun j => b j + c) = fun q => Sum.elim a b q + c := by
    funext q
    cases q <;> rfl
  have hadd (n : Nat) : n + c + c = n + 2 * c := by omega
  have h := bohr_card_factor_of_split_density gamma ell (fun i => a i + c) (fun j => b j + c)
    (fun i => by omega) (fun j => by omega) ha hb hc Lambda hsplit heps hd0 hd1 hweight
    (by simpa only [Nat.add_sub_cancel, hadd] using hband)
    (by simpa only [hab, Nat.add_sub_cancel, hadd] using hband') htrunc htrunc'
  simpa only [hab, Nat.add_sub_cancel] using h

/-- The paired block has density delta², with the same single-block weight
controlling its error. The relation class is explicitly the product class. -/
theorem bohr_pair_card_factor_at_radii {N : Nat} [NeZero N] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (gamma : ι → ZMod N) (ell ell' : κ → ZMod N)
    (a : ι → Nat) (b : κ → Nat) {c R : Nat}
    (ha : ∀ i, 2 * (a i + c) < N) (hb : ∀ j, 2 * (b j + c) < N) (hc : 2 * c < N)
    (Lambda : Set (κ → centeredBall N R))
    (hsplit : ∀ (nu : ι → centeredBall N R) (mu : (κ ⊕ κ) → centeredBall N R),
      (∑ i, (nu i : ZMod N) * gamma i) + (∑ j, (mu j : ZMod N) * Sum.elim ell ell' j) = 0 ↔
        (∑ i, (nu i : ZMod N) * gamma i = 0 ∧
          (fun j => mu (Sum.inl j)) ∈ Lambda ∧ (fun j => mu (Sum.inr j)) ∈ Lambda))
    {epsilon zeta delta : Real} (heps : 0 ≤ epsilon) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hweight : ‖latticeWeightMixed (fun j => b j + c) c R Lambda - (delta : Complex)‖ ≤ zeta)
    (hband : ((mixedBohr gamma (fun i => a i + 2 * c)).card : Real) ≤
      (mixedBohr gamma a).card + epsilon * N)
    (hband' : ((mixedBohr (Sum.elim gamma (Sum.elim ell ell'))
      (fun q => Sum.elim a (Sum.elim b b) q + 2 * c)).card : Real) ≤
      (mixedBohr (Sum.elim gamma (Sum.elim ell ell')) (Sum.elim a (Sum.elim b b))).card + epsilon * N)
    (htrunc : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^ Fintype.card ι - 1 ≤ epsilon)
    (htrunc' : (1 + N / ((centeredBall N c).card * (R + 1 : Real))) ^
      Fintype.card (ι ⊕ (κ ⊕ κ)) - 1 ≤ epsilon) :
    |(mixedBohr (Sum.elim gamma (Sum.elim ell ell')) (Sum.elim a (Sum.elim b b))).card -
      delta^2 * ((mixedBohr gamma a).card : Real)| ≤
      (4 + 2 * (zeta * (2 + zeta))) * epsilon * N +
        (zeta * (2 + zeta)) * (mixedBohr gamma a).card := by
  have hb' : ∀ q : κ ⊕ κ, 2 * (Sum.elim b b q + c) < N := by
    intro q
    cases q with
    | inl j => exact hb j
    | inr j => exact hb j
  have hweight' := paired_latticeWeightMixed_near_density (fun j => b j + c) c R Lambda hd0 hd1 hweight
  have hab : Sum.elim (fun j => b j + c) (fun j => b j + c) = fun q => Sum.elim b b q + c := by
    funext q
    cases q <;> rfl
  rw [hab] at hweight'
  exact bohr_card_factor_at_radii gamma (Sum.elim ell ell') a (Sum.elim b b) ha hb' hc
    {mu | (fun j => mu (Sum.inl j)) ∈ Lambda ∧ (fun j => mu (Sum.inr j)) ∈ Lambda}
    hsplit heps (sq_nonneg _) (pow_le_one₀ hd0 hd1) hweight' hband hband' htrunc htrunc'

end LeanProofs.GowersSzemeredi
