import IPRADerivations.DiophantineNumberTheory.TwoSquaresObstruction

/-!
# Quadratic reciprocity by residue classes modulo 4

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, §"The rectangle and
the reciprocity sign": "Finally, `h` is odd exactly when `p ≡ 3 (mod 4)`, and likewise for `k`. This proves the
residue-class formulation": for distinct odd primes `p`, `q`,

* if `p ≡ 1 (mod 4)` or `q ≡ 1 (mod 4)`, then `(p/q) = (q/p)`;
* if `p ≡ q ≡ 3 (mod 4)`, then `(p/q) = −(q/p)`.

With the sign bits (`0` for a square, `1` for a nonsquare):

* `qr_open`: the law `par (signBit p q + signBit q p) = par (⌊p/2⌋ ⌊q/2⌋)` in an arbitrary context;
* `sign_cases`: a sign bit is `0` or `1`;
* `bits_even`, `bits_odd`: for two bits, an even sum means that they are equal, an odd sum that it is `1`;
* **`qr_equal_left`**, **`qr_equal_right`**: `signBit p q = signBit q p` when `⌊p/2⌋` (resp. `⌊q/2⌋`) is even;
* **`qr_opposite`**: `signBit p q + signBit q p = 1` when `⌊p/2⌋` and `⌊q/2⌋` are odd;
* **`reciprocity_one_left`**, **`reciprocity_one_right`**, **`reciprocity_three`**: the same with the hypotheses
  `p ≡ 1 (mod 4)`, `q ≡ 1 (mod 4)`, `p ≡ q ≡ 3 (mod 4)`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.ReciprocityClasses

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedSyntax (bit bit_cases program_correct)
open LeanProofs.IPRA.Foundations.BoundedReflection (one_ne_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (signBit nonsquare assumptions conclusion
  assemble)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocity (premises)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares (mod4_parities)
open LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresObstruction (parities_three)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The law in an arbitrary context -/

/-- Quadratic reciprocity in an arbitrary context. -/
theorem qr_open {p q : PTm n} (h : Γ ⊢[PRAAx] assumptions p q) :
    Γ ⊢[PRAAx] par (signBit p q + signBit q p) ≐ par (half p * half q) := by
  obtain ⟨h1, h2, h3⟩ := premises h
  have c : Γ ⊢[PRAAx] conclusion p q := assemble p q h1 h2 h3
  exact c

/-- A sign bit is `0` or `1`. -/
theorem sign_cases (p a : PTm n) : Γ ⊢[PRAAx] (signBit p a ≐ zero) ⋎ (signBit p a ≐ one) := by
  have pc : Γ ⊢[PRAAx] signBit p a ≐ bit nonsquare ![p, a] := program_correct nonsquare ![p, a]
  exact .orE (bit_cases (Γ := Γ) nonsquare ![p, a]) (.orI₁ (pc.wk.eqTrans Prf.hyp0))
    (.orI₂ (pc.wk.eqTrans Prf.hyp0))

/-! ## Two bits and the parity of their sum -/

theorem p00 : Γ ⊢[PRAAx] par ((zero : PTm n) + zero) ≐ zero :=
  (congrAp1 parF (by ipra_ring)).eqTrans (par_double zero)

theorem p01 : Γ ⊢[PRAAx] par ((zero : PTm n) + one) ≐ one :=
  (congrAp1 parF (by ipra_ring)).eqTrans (par_double_succ zero)

theorem p10 : Γ ⊢[PRAAx] par ((one : PTm n) + zero) ≐ one :=
  (congrAp1 parF (by ipra_ring)).eqTrans (par_double_succ zero)

theorem p11 : Γ ⊢[PRAAx] par ((one : PTm n) + one) ≐ zero :=
  (congrAp1 parF (by ipra_ring)).eqTrans (par_double one)

theorem sum_alg {x y a b c : PTm n} (ex : Γ ⊢[PRAAx] x ≐ a) (ey : Γ ⊢[PRAAx] y ≐ b)
    (e : Γ ⊢[PRAAx] a + b ≐ c) : Γ ⊢[PRAAx] x + y ≐ c := (congrAdd ex ey).eqTrans e

/-- Two bits with an even sum are equal. -/
theorem bits_even {x y : PTm n} (hx : Γ ⊢[PRAAx] (x ≐ zero) ⋎ (x ≐ one))
    (hy : Γ ⊢[PRAAx] (y ≐ zero) ⋎ (y ≐ one)) (h : Γ ⊢[PRAAx] par (x + y) ≐ zero) : Γ ⊢[PRAAx] x ≐ y := by
  refine .orE hx ?_ ?_
  · refine .orE hy.wk ?_ ?_
    · exact Prf.hyp1.eqTrans Prf.hyp0.eqSymm
    · have ex : ((y ≐ one) :: (x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp1
      have ey : ((y ≐ one) :: (x ≐ zero) :: Γ) ⊢[PRAAx] y ≐ one := Prf.hyp0
      exact one_ne_zero _ (p01.eqSymm.eqTrans ((congrAp1 parF (congrAdd ex ey)).eqSymm.eqTrans h.wk.wk))
  · refine .orE hy.wk ?_ ?_
    · have ex : ((y ≐ zero) :: (x ≐ one) :: Γ) ⊢[PRAAx] x ≐ one := Prf.hyp1
      have ey : ((y ≐ zero) :: (x ≐ one) :: Γ) ⊢[PRAAx] y ≐ zero := Prf.hyp0
      exact one_ne_zero _ (p10.eqSymm.eqTrans ((congrAp1 parF (congrAdd ex ey)).eqSymm.eqTrans h.wk.wk))
    · exact Prf.hyp1.eqTrans Prf.hyp0.eqSymm

/-- Two bits with an odd sum have sum `1`. -/
theorem bits_odd {x y : PTm n} (hx : Γ ⊢[PRAAx] (x ≐ zero) ⋎ (x ≐ one))
    (hy : Γ ⊢[PRAAx] (y ≐ zero) ⋎ (y ≐ one)) (h : Γ ⊢[PRAAx] par (x + y) ≐ one) :
    Γ ⊢[PRAAx] x + y ≐ one := by
  refine .orE hx ?_ ?_
  · refine .orE hy.wk ?_ ?_
    · have ex : ((y ≐ zero) :: (x ≐ zero) :: Γ) ⊢[PRAAx] x ≐ zero := Prf.hyp1
      have ey : ((y ≐ zero) :: (x ≐ zero) :: Γ) ⊢[PRAAx] y ≐ zero := Prf.hyp0
      exact one_ne_zero _ (h.wk.wk.eqSymm.eqTrans ((congrAp1 parF (congrAdd ex ey)).eqTrans p00))
    · exact sum_alg Prf.hyp1 Prf.hyp0 (zero_add one)
  · refine .orE hy.wk ?_ ?_
    · exact sum_alg Prf.hyp1 Prf.hyp0 (add_zero one)
    · have ex : ((y ≐ one) :: (x ≐ one) :: Γ) ⊢[PRAAx] x ≐ one := Prf.hyp1
      have ey : ((y ≐ one) :: (x ≐ one) :: Γ) ⊢[PRAAx] y ≐ one := Prf.hyp0
      exact one_ne_zero _ (h.wk.wk.eqSymm.eqTrans ((congrAp1 parF (congrAdd ex ey)).eqTrans p11))

/-! ## The parity of `⌊p/2⌋ ⌊q/2⌋` -/

theorem ev_alg {h k : PTm n} (e : Γ ⊢[PRAAx] h ≐ two * half h) :
    Γ ⊢[PRAAx] h * k ≐ two * (half h * k) := by
  ipra_lc 𝔞 k * natEq e

theorem ev_alg' {h k : PTm n} (e : Γ ⊢[PRAAx] k ≐ two * half k) :
    Γ ⊢[PRAAx] h * k ≐ two * (h * half k) := by
  ipra_lc 𝔞 h * natEq e

theorem od_alg {h k : PTm n} (e1 : Γ ⊢[PRAAx] h ≐ two * half h + one)
    (e2 : Γ ⊢[PRAAx] k ≐ two * half k + one) :
    Γ ⊢[PRAAx] h * k ≐ two * (two * (half h * half k) + half h + half k) + one := by
  ipra_lc 𝔞 k * natEq e1 + (2 * 𝔞 (half h) + 1) * natEq e2

/-! ## The residue-class form -/

/-- `(p/q) = (q/p)` when `⌊p/2⌋` is even. -/
theorem qr_equal_left {p q : PTm n} (h : Γ ⊢[PRAAx] assumptions p q)
    (hp : Γ ⊢[PRAAx] par (half p) ≐ zero) : Γ ⊢[PRAAx] signBit p q ≐ signBit q p :=
  bits_even (sign_cases p q) (sign_cases q p)
    ((qr_open h).eqTrans ((congrAp1 parF (ev_alg (even_of hp))).eqTrans (par_double _)))

/-- `(p/q) = (q/p)` when `⌊q/2⌋` is even. -/
theorem qr_equal_right {p q : PTm n} (h : Γ ⊢[PRAAx] assumptions p q)
    (hq : Γ ⊢[PRAAx] par (half q) ≐ zero) : Γ ⊢[PRAAx] signBit p q ≐ signBit q p :=
  bits_even (sign_cases p q) (sign_cases q p)
    ((qr_open h).eqTrans ((congrAp1 parF (ev_alg' (even_of hq))).eqTrans (par_double _)))

/-- `(p/q) = −(q/p)` when `⌊p/2⌋` and `⌊q/2⌋` are odd. -/
theorem qr_opposite {p q : PTm n} (h : Γ ⊢[PRAAx] assumptions p q)
    (hp : Γ ⊢[PRAAx] par (half p) ≐ one) (hq : Γ ⊢[PRAAx] par (half q) ≐ one) :
    Γ ⊢[PRAAx] signBit p q + signBit q p ≐ one :=
  bits_odd (sign_cases p q) (sign_cases q p)
    ((qr_open h).eqTrans ((congrAp1 parF (od_alg (odd_of hp) (odd_of hq))).eqTrans (par_double_succ _)))

/-- **`p ≡ 1 (mod 4)`**: `(p/q) = (q/p)` for an odd prime `q ≠ p`. -/
theorem reciprocity_one_left {p q : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q)
    (oq : Γ ⊢[PRAAx] par q ≐ one) (hne : Γ ⊢[PRAAx] neg (p ≐ q))
    (h1 : Γ ⊢[PRAAx] rem p (two * two) ≐ one) : Γ ⊢[PRAAx] signBit p q ≐ signBit q p := by
  have m := mod4_parities h1
  have A : Γ ⊢[PRAAx] assumptions p q := .andI hp (.andI hq (.andI (Prf.andE₁ m) (.andI oq hne)))
  exact qr_equal_left A (Prf.andE₂ m)

/-- **`q ≡ 1 (mod 4)`**: `(p/q) = (q/p)` for an odd prime `p ≠ q`. -/
theorem reciprocity_one_right {p q : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q)
    (op : Γ ⊢[PRAAx] par p ≐ one) (hne : Γ ⊢[PRAAx] neg (p ≐ q))
    (h1 : Γ ⊢[PRAAx] rem q (two * two) ≐ one) : Γ ⊢[PRAAx] signBit p q ≐ signBit q p := by
  have m := mod4_parities h1
  have A : Γ ⊢[PRAAx] assumptions p q := .andI hp (.andI hq (.andI op (.andI (Prf.andE₁ m) hne)))
  exact qr_equal_right A (Prf.andE₂ m)

/-- **`p ≡ q ≡ 3 (mod 4)`**: `(p/q) = −(q/p)` for distinct primes. -/
theorem reciprocity_three {p q : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q)
    (hne : Γ ⊢[PRAAx] neg (p ≐ q)) (h3p : Γ ⊢[PRAAx] rem p (two * two) ≐ succ two)
    (h3q : Γ ⊢[PRAAx] rem q (two * two) ≐ succ two) : Γ ⊢[PRAAx] signBit p q + signBit q p ≐ one := by
  have mp := parities_three h3p
  have mq := parities_three h3q
  have A : Γ ⊢[PRAAx] assumptions p q :=
    .andI hp (.andI hq (.andI (Prf.andE₁ mp) (.andI (Prf.andE₁ mq) hne)))
  exact qr_opposite A (Prf.andE₂ mp) (Prf.andE₂ mq)

end LeanProofs.IPRA.DiophantineNumberTheory.ReciprocityClasses
