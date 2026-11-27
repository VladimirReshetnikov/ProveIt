import IPRADerivations.Combinatorics.CatalanNarayana

/-!
# The hockey-stick identity and the stars-and-bars ranks

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15` (`thm:pn-cohomology`: the ranks
`C(n + d, n)` of `H⁰(Pⁿ, O(d))` and `C(−d − 1, n)` of `Hⁿ(Pⁿ, O(d))`, counted by stars and
bars). Coefficients are the guarded `C(m, k)` of `Combinatorics/Vandermonde`.

* `hockey_stick`: `∑_{k ≤ d} C(m + k, k) = C(m + d + 1, d)`, by induction on `d` with Pascal's rule;
* `stars_bars_rec`: the numbers `N(n, d) = C(n + d, d)` satisfy the stars-and-bars recursion
  `N(n + 1, d) = ∑_{k ≤ d} N(n, k)` (fix the last exponent `d − k`), with `N(0, d) = 1`; so they
  count the exponent vectors of `n + 1` nonnegative entries with sum `d`;
* `neg_rank`: for an all-negative vector `eᵢ = −aᵢ − 1` the `aᵢ` have sum `−d − (n + 1)`, and
  `N(n, −d − n − 1) = C(−d − 1, n)` (with `D = −d`).

The enumeration of exponent vectors, the Čech complex and the insertion homotopy are not
formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.HockeyStick

open_ipra
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_pascal)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (gb_symm)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `C(m + k, k)`; variables `0 = k`, `1 = m`. -/
abbrev hB : PTm 2 := gb (var 1 + var 0) (var 0)

theorem inst2_h (k m : PTm n) : inst2 hB k m = gb (m + k) k := by simp [inst2]

theorem hs_base (m : PTm n) : Γ ⊢[PRAAx] ap2 (sumF hB) (succ zero) m ≐ gb (m + zero + one) zero := by
  refine (sum_singleton hB m).eqTrans ?_
  rw [inst2_h]
  exact (gb_zero _).eqTrans (gb_zero _).eqSymm

theorem hs_step {m d : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF hB) (succ d) m ≐ gb (m + d + one) d) :
    Γ ⊢[PRAAx] ap2 (sumF hB) (succ (succ d)) m ≐ gb (m + succ d + one) (succ d) := by
  have s := sum_succ' (Γ := Γ) hB (succ d) m
  rw [inst2_h] at s
  have e₁ : Γ ⊢[PRAAx] m + succ d + one ≐ succ (m + d + one) := by ipra_ring
  have e₂ : Γ ⊢[PRAAx] m + succ d ≐ m + d + one := by ipra_ring
  refine s.eqTrans ((congrAdd ih (congrGb e₂ (.eqRefl _))).eqTrans ?_)
  exact (add_comm _ _).eqTrans ((gb_pascal _ _).eqSymm.eqTrans (congrGb e₁.eqSymm (.eqRefl _)))

/-- Variables: `0 = d` (induction), `1 = m`. -/
private abbrev hsF : Fm PTm 2 := ap2 (sumF hB) (succ (var 0)) (var 1) ≐ gb (var 1 + var 0 + one) (var 0)

private theorem hs₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] hsF := by
  ipra_ind [subst_ap2]
  · exact hs_base _
  · exact hs_step Prf.hyp0

/-- The hockey-stick identity: `∑_{k ≤ d} C(m + k, k) = C(m + d + 1, d)`. -/
theorem hockey_stick (m d : PTm n) : Γ ⊢[PRAAx] ap2 (sumF hB) (succ d) m ≐ gb (m + d + one) d := by
  have h := inst (Γ := Γ) hs₀ (![d, m] : Fin 2 → PTm n)
  simpa using h

/-- The stars-and-bars recursion for `N(n, d) = C(n + d, d)`: `N(n + 1, d) = ∑_{k ≤ d} N(n, k)`. -/
theorem stars_bars_rec (m d : PTm n) :
    Γ ⊢[PRAAx] gb (succ m + d) d ≐ ap2 (sumF hB) (succ d) m := by
  have e : Γ ⊢[PRAAx] succ m + d ≐ m + d + one := by ipra_ring
  exact (congrGb e (.eqRefl _)).eqTrans (hockey_stick m d).eqSymm

/-- `N(0, d) = 1`. -/
theorem stars_bars_zero (d : PTm n) : Γ ⊢[PRAAx] gb (zero + d) d ≐ one :=
  (congrGb (zero_add d) (.eqRefl _)).eqTrans (LeanProofs.IPRA.Combinatorics.Vandermonde.gb_self d)

/-- The rank of `Hⁿ`: with `d = −D` and `D ≥ n + 1`, the vectors `aᵢ ≥ 0` have sum
`s = D − (n + 1)`, and `N(n, s) = C(n + s, s) = C(D − 1, n)`. -/
theorem neg_rank {m D : PTm n} (h : Γ ⊢[PRAAx] le (succ m) D) :
    Γ ⊢[PRAAx] gb (m + monus D (succ m)) (monus D (succ m)) ≐ gb (monus D one) m := by
  have e := natEq (eq_add_of_le h)
  have t : Γ ⊢[PRAAx] m + monus D (succ m) ≐ monus D one := by
    have a : Γ ⊢[PRAAx] D ≐ (m + monus D (succ m)) + one := by apply deriveNat; ipra_simps; linear_combination e
    exact ((add_monus _ _).eqSymm.eqTrans (congrMonus a.eqSymm (.eqRefl _)))
  have s : Γ ⊢[PRAAx] monus (m + monus D (succ m)) m ≐ monus D (succ m) := add_monus' _ _
  refine (congrGb t (.eqRefl _)).eqTrans ?_
  have l : Γ ⊢[PRAAx] le m (monus D one) := le_of_eq_add t.eqSymm
  refine (congrGb (.eqRefl _) ?_).eqTrans (gb_symm l)
  exact (congrMonus t.eqSymm (.eqRefl _)).eqTrans s |>.eqSymm

end LeanProofs.IPRA.Combinatorics.HockeyStick
