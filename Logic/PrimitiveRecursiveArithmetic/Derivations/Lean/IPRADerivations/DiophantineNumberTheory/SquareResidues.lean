import IPRADerivations.DiophantineNumberTheory.FourSquaresSeed

/-!
# The square residues modulo an odd prime

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, Lemma
`qr:squares-half`: for `p = 2h + 1`, the residues `1², …, h²` are distinct, they are exactly the nonzero square
residues, and each has precisely two square roots modulo `p`.

Distinctness is `FourSquaresSeed.sq_inj`. Here:

* **`sq_roots`**: for a prime `p` and `y ≤ x`, `x² ≡ y² (mod p)` gives `p ∣ x − y` or `p ∣ x + y`: the only roots
  of `X² − y²` are `y` and `−y` (from `x² = y² + (x − y)(x + y)` and Euclid's lemma);
* **`neg_sq`**: `(p − x)² ≡ x² (mod p)` for `x ≤ p`;
* **`half_cases`**: for `p = 2h + 1` and `x < p`, `x ≤ h` or `p − x ≤ h`: with `neg_sq`, every nonzero square
  residue is one of `1², …, h²`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.SquareResidues

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The two roots -/

theorem diff_alg {x y d : PTm k} (e : Γ ⊢[PRAAx] x ≐ y + d) : Γ ⊢[PRAAx] x * x ≐ y * y + d * (x + y) := by
  ipra_lc (𝔞 x + 𝔞 y) * natEq e

/-- **The roots of `X² − y²`**: for a prime `p` and `y ≤ x`, `x² ≡ y² (mod p)` gives `p ∣ x − y` or
`p ∣ x + y`. -/
theorem sq_roots {p x y : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hxy : Γ ⊢[PRAAx] le y x)
    (h : Γ ⊢[PRAAx] rem (x * x) p ≐ rem (y * y) p) :
    Γ ⊢[PRAAx] dvd p (monus x y) ⋎ dvd p (x + y) := by
  have hp1 := p_pos (prime_two hp)
  have e := diff_alg (eq_add_of_le hxy)
  have h1 : Γ ⊢[PRAAx] rem (y * y + monus x y * (x + y)) p ≐ rem (y * y + zero) p :=
    (congrAp2 remF e.eqSymm (.eqRefl _)).eqTrans (h.eqTrans (congrAp2 remF (add_zero _).eqSymm (.eqRefl _)))
  have h2 : Γ ⊢[PRAAx] dvd p (monus x y * (x + y)) := (rem_cancel hp1 h1).eqTrans (rem_zero p)
  exact euclid_lemma_at hp h2

/-! ## Exhaustion -/

theorem neg_alg {p x m : PTm k} (e : Γ ⊢[PRAAx] p ≐ x + m) :
    Γ ⊢[PRAAx] p * (two * x) + m * m ≐ p * p + x * x := by
  ipra_lc -(𝔞 p - 𝔞 x + 𝔞 m) * natEq e

/-- `(p − x)² ≡ x² (mod p)` for `x ≤ p`. -/
theorem neg_sq {p x : PTm k} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hx : Γ ⊢[PRAAx] le x p) :
    Γ ⊢[PRAAx] rem (monus p x * monus p x) p ≐ rem (x * x) p :=
  (rem_add_mul hp1 (two * x) (monus p x * monus p x)).eqSymm.eqTrans
    ((congrAp2 remF (neg_alg (eq_add_of_le hx)) (.eqRefl _)).eqTrans (rem_add_mul hp1 p (x * x)))

theorem upper_alg {p x h m s : PTm k} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (em : Γ ⊢[PRAAx] p ≐ x + m)
    (es : Γ ⊢[PRAAx] x ≐ succ h + s) : Γ ⊢[PRAAx] h ≐ m + s := by
  ipra_lc -natEq ep + natEq em + natEq es

/-- For `p = 2h + 1` and `x ≤ p`: `x ≤ h` or `p − x ≤ h`. -/
theorem half_cases {p x h : PTm k} (ep : Γ ⊢[PRAAx] p ≐ two * h + one) (hx : Γ ⊢[PRAAx] le x p) :
    Γ ⊢[PRAAx] le x h ⋎ le (monus p x) h := by
  refine .orE (lt_or_le h x) ?_ (.orI₁ Prf.hyp0)
  have hlt : (lt h x :: Γ) ⊢[PRAAx] le (succ h) x := Prf.hyp0
  exact .orI₂ (le_of_eq_add (upper_alg ep.wk (eq_add_of_le hx.wk) (eq_add_of_le hlt)))

end LeanProofs.IPRA.DiophantineNumberTheory.SquareResidues
