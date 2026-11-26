import IPRADerivations.DiophantineNumberTheory.TwoSquaresByDescent
import IPRADerivations.AnalyticNumberTheory.PrimeGaps
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.Header

/-!
# Fermat's two-square theorem: sorted bounds and the biconditional

Packet: `diophantine-number-theory/fermat_two_squares_ipra_2026-11-22`, `fermat_two_squares_ipra.tex`:

* §"Positive direction for primes": "A prime is not a square. […] Its output is bounded by `h = ⌊√p⌋`. Neither
  output can be zero, since that would again make `p` a square. Sorting gives `1 ≤ A(p) ≤ B(p) ≤ h`."
* Theorem `thm:main`, as one formula with a bounded existential: for a prime `p`, `p = 2` or `p ≡ 1 (mod 4)` if
  and only if `∃ a, b ≤ p. a² + b² = p`.

Here:

* **`prime_not_square`**: no `h` has `h² = p` for a prime `p`;
* `pos_parts`, `le_isqrt`: in `a² + b² = p` with `p` prime, `1 ≤ a`, `1 ≤ b`, and `a ≤ ⌊√p⌋` (the latter for
  any `p`);
* `mn`, `mx`, `sorted`: the minimum and the maximum of two numbers, and the two cases;
* **`sorted_bounds`**: for `a² + b² = p` with `p` prime, `min² + max² = p` and
  `1 ≤ min ≤ max ≤ ⌊√p⌋`;
* **`fermat_sorted`**: the sorted witnesses `As(p) = min(A(p), B(p))`, `Bs(p) = max(A(p), B(p))` of
  `FermatTwoSquares.fermat_witness`;
* **`fermat_iff`**: the closed sentence
  `∀ p. prime p → ((T(p) = 1 → p = 2 ∨ p ≡ 1 (mod 4)) ∧ (p = 2 ∨ p ≡ 1 (mod 4) → T(p) = 1))`, where `T(p)` is the
  bit of the bounded search `∃ c < (p + 1)². (c mod (p + 1))² + ⌊c/(p + 1)⌋² = p`
  (`TwoSquaresByDescent.T`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresBounds

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeGaps (prime_no_divisor)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq')
open LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares (Aw Bw fermat_witness fermat_converse_open)
open LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresByDescent (T rep_intro rep_elim)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## A prime is not a square -/

/-- **A prime is not a square**. -/
theorem prime_not_square {p h : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] h * h ≐ p) :
    Γ ⊢[PRAAx] Fm.bot := by
  have hp2 := prime_two hp
  refine .orE (lt_or_le h two) ?_ ?_
  · -- `h ≤ 1`: `h² ≤ 1 < 2 ≤ p`
    have hl : (lt h two :: Γ) ⊢[PRAAx] lt h two := Prf.hyp0
    have hp2' := hp2.wk (ψ := lt h two)
    have en := natEq (e.wk (ψ := lt h two))
    have bad : (lt h two :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le sl hp2' + sl hl * (𝔞 h + 1) with en
    exact lt_zero_absurd _ bad
  · -- `h ≥ 2`: `h` is a proper divisor
    have h2 : (le two h :: Γ) ⊢[PRAAx] le two h := Prf.hyp0
    have en := natEq (e.wk (ψ := le two h))
    have hlt : (le two h :: Γ) ⊢[PRAAx] lt h p := by
      ipra_le sl h2 * 𝔞 h + sl h2 + 1 with -en
    exact .impE (prime_no_divisor hp.wk h2 hlt) (dvd_of_eq' (p_pos h2) e.wk.eqSymm)

theorem zero_part {a b p : PTm n} (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) (ha : Γ ⊢[PRAAx] a ≐ zero) :
    Γ ⊢[PRAAx] b * b ≐ p := by
  ipra_lc natEq e - 𝔞 a * natEq ha

theorem sq_swap {a b p : PTm n} (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) : Γ ⊢[PRAAx] b * b + a * a ≐ p := by
  ipra_lc natEq e

/-- In `a² + b² = p` with `p` prime, `a ≥ 1`. -/
theorem pos_part {a b p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) :
    Γ ⊢[PRAAx] le one a := by
  refine .orE (zero_or_succ a) ?_ (one_le_pos Prf.hyp0)
  exact .botE _ (prime_not_square hp.wk (zero_part e.wk Prf.hyp0))

/-- `a² + R = p` gives `a ≤ ⌊√p⌋`. -/
theorem le_isqrt {a R p : PTm n} (e : Γ ⊢[PRAAx] a * a + R ≐ p) : Γ ⊢[PRAAx] le a (isqrt p) := by
  refine .orE (lt_or_le (isqrt p) a) ?_ Prf.hyp0
  have hs : (lt (isqrt p) a :: Γ) ⊢[PRAAx] lt (isqrt p) a := Prf.hyp0
  have hlt := lt_isqrt_succ_sq (Γ := lt (isqrt p) a :: Γ) p
  have en := natEq (e.wk (ψ := lt (isqrt p) a))
  have bad : (lt (isqrt p) a :: Γ) ⊢[PRAAx] le one zero := by
    ipra_le sl hlt + sl hs * (𝔞 a + 𝔞 (isqrt p) + 1) + 𝔞 R with -en
  exact lt_zero_absurd _ bad

/-! ## Sorting -/

/-- `min(a, b)`. -/
abbrev mn (a b : PTm n) : PTm n := monus a (monus a b)

/-- `max(a, b)`. -/
abbrev mx (a b : PTm n) : PTm n := a + monus b a

/-- The two cases of sorting a pair. -/
theorem sorted (a b : PTm n) :
    Γ ⊢[PRAAx] ((mn a b ≐ a) ⋏ ((mx a b ≐ b) ⋏ le a b)) ⋎ ((mn a b ≐ b) ⋏ ((mx a b ≐ a) ⋏ le b a)) := by
  refine .orE (lt_or_le b a) (.orI₂ ?_) (.orI₁ ?_)
  · have hl : (lt b a :: Γ) ⊢[PRAAx] le b a := le_of_lt Prf.hyp0
    exact .andI (monus_of_eq ((eq_add_of_le hl).eqTrans (add_comm _ _)))
      (.andI ((congrAdd (.eqRefl a) hl).eqTrans (add_zero a)) hl)
  · have hl : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    exact .andI ((congrMonus (.eqRefl a) hl).eqTrans (monus_zero a)) (.andI (eq_add_of_le hl).eqSymm hl)

/-- **Sorted bounds**: for `a² + b² = p` with `p` prime, the sorted pair `(m, M)` satisfies `m² + M² = p` and
`1 ≤ m ≤ M ≤ ⌊√p⌋`. -/
theorem sorted_bounds {a b p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (e : Γ ⊢[PRAAx] a * a + b * b ≐ p) :
    Γ ⊢[PRAAx] (mn a b * mn a b + mx a b * mx a b ≐ p) ⋏
      (le one (mn a b) ⋏ (le (mn a b) (mx a b) ⋏ le (mx a b) (isqrt p))) := by
  have pa := pos_part hp e
  have pb := pos_part hp (sq_swap e)
  have la := le_isqrt e
  have lb := le_isqrt (sq_swap e)
  refine .orE (sorted a b) ?_ ?_
  · let C : List (Fm PTm n) := ((mn a b ≐ a) ⋏ ((mx a b ≐ b) ⋏ le a b)) :: Γ
    have h0 : C ⊢[PRAAx] (mn a b ≐ a) ⋏ ((mx a b ≐ b) ⋏ le a b) := Prf.hyp0
    have e1 := Prf.andE₁ h0; have e2 := Prf.andE₁ (Prf.andE₂ h0); have hl := Prf.andE₂ (Prf.andE₂ h0)
    exact .andI ((congrAdd (congrMul e1 e1) (congrMul e2 e2)).eqTrans e.wk)
      (.andI (le_congr (.eqRefl _) e1.eqSymm pa.wk)
        (.andI (le_congr e1.eqSymm e2.eqSymm hl) (le_congr e2.eqSymm (.eqRefl _) lb.wk)))
  · let C : List (Fm PTm n) := ((mn a b ≐ b) ⋏ ((mx a b ≐ a) ⋏ le b a)) :: Γ
    have h0 : C ⊢[PRAAx] (mn a b ≐ b) ⋏ ((mx a b ≐ a) ⋏ le b a) := Prf.hyp0
    have e1 := Prf.andE₁ h0; have e2 := Prf.andE₁ (Prf.andE₂ h0); have hl := Prf.andE₂ (Prf.andE₂ h0)
    exact .andI ((congrAdd (congrMul e1 e1) (congrMul e2 e2)).eqTrans (sq_swap e).wk)
      (.andI (le_congr (.eqRefl _) e1.eqSymm pb.wk)
        (.andI (le_congr e1.eqSymm e2.eqSymm hl) (le_congr e2.eqSymm (.eqRefl _) la.wk)))

/-! ## The sorted witnesses of Fermat's theorem -/

/-- `As(p) = min(A(p), B(p))`. -/
abbrev As (p : PTm n) : PTm n := mn (Aw p) (Bw p)

/-- `Bs(p) = max(A(p), B(p))`. -/
abbrev Bs (p : PTm n) : PTm n := mx (Aw p) (Bw p)

/-- **`thm:main` with sorted witnesses**: for a prime `p` with `p = 2` or `p ≡ 1 (mod 4)`,
`As(p)² + Bs(p)² = p` and `1 ≤ As(p) ≤ Bs(p) ≤ ⌊√p⌋`. -/
theorem fermat_sorted {p : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (h : Γ ⊢[PRAAx] (p ≐ two) ⋎ (rem p (two * two) ≐ one)) :
    Γ ⊢[PRAAx] (As p * As p + Bs p * Bs p ≐ p) ⋏
      (le one (As p) ⋏ (le (As p) (Bs p) ⋏ le (Bs p) (isqrt p))) :=
  sorted_bounds hp (fermat_witness hp h)

/-! ## The biconditional -/

/-- For a prime `p`: the bounded search succeeds exactly when `p = 2` or `p ≡ 1 (mod 4)`. -/
theorem fermat_iff_open {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] ((T p ≐ one) ⟶ ((p ≐ two) ⋎ (rem p (two * two) ≐ one))) ⋏
      (((p ≐ two) ⋎ (rem p (two * two) ≐ one)) ⟶ (T p ≐ one)) :=
  .andI (.impI (fermat_converse_open hp.wk (rep_elim Prf.hyp0)))
    (.impI (rep_intro (fermat_witness hp.wk Prf.hyp0)))

/-- `∀ p. prime p → ((T(p) = 1 → p = 2 ∨ p ≡ 1 (mod 4)) ∧ (p = 2 ∨ p ≡ 1 (mod 4) → T(p) = 1))`. -/
abbrev iffSentence : Fm PTm 0 :=
  univ 1 (prime (var 0) ⟶
    (((T (var 0) ≐ one) ⟶ ((var 0 ≐ two) ⋎ (rem (var 0) (two * two) ≐ one))) ⋏
      (((var 0 ≐ two) ⋎ (rem (var 0) (two * two) ≐ one)) ⟶ (T (var 0) ≐ one))))

/-- **Fermat's two-square theorem** as one closed sentence of iPRA with a bounded existential. -/
theorem fermat_iff : ([] : List (Fm PTm 0)) ⊢[PRAAx] iffSentence :=
  closeUniv 1 (.impI (fermat_iff_open Prf.hyp0))

end LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresBounds
