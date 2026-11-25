import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.Combinatorics.BellTriangle
import IPRADerivations.Core.CertificateTactics

/-!
# Product form, the form `C(2n, n − 1) / n` and the central binomial bound (`catalan_numbers_ipra_2026-11-16`)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, the corollary "Equivalent closed
forms" ((2.6), (2.7)) and the bound (4.5) of `thm:boundary-tail`. With `cat n = Cat_n` and
`cb n = C(2n, n)` of `Combinatorics/Catalan`, for arbitrary terms:

* `cat_fact_prod` ((2.7)): `(n + 1)! Cat_n = ∏_{j<n} (4j + 2)`, that is
  `∏_{j=1}^{n} (4j − 2)`; by induction from `(n + 2) Cat_{n+1} = 2 (2n + 1) Cat_n`;
* `cat_lower_binom` ((2.6)): `(m + 1) Cat_{m+1} = C(2m + 2, m)`, that is
  `n Cat_n = C(2n, n − 1)` for `n = m + 1 ≥ 1`; from the ratio
  `n C(2n, n) = (n + 1) C(2n, n + 1)` and the symmetry of the binomial coefficient;
* `cb_sq_bound` ((4.5), cleared of the square root: `2 C(2m, m) / 4^m ≤ 2 / √(m + 1)`):
  `(m + 1) C(2m, m)² ≤ 16^m`; by induction, the step being
  `(m + 2)(2m + 1)² + (3m + 2) = 4 (m + 1)³`.

Closed forms: `cat_fact_prod_closed`, `cat_lower_binom_closed`, `cb_sq_bound_closed`.

The modulus form of (4.5), the limit (4.6) and the remaining items of the packet are not
derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanProducts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel catalan_ratio_open)
open LeanProofs.IPRA.Combinatorics.BellTriangle (binom_symm)
open LeanProofs.IPRA.Combinatorics.Catalan
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The product form (2.7) -/

/-- The factor `4j + 2`. -/
abbrev oddB : PTm 2 := two * two * var 0 + two

/-- `∏_{j<N} (4j + 2)`. -/
abbrev oddProd (N : PTm n) : PTm n := ap2 (prodF oddB) N zero

theorem oddProd_zero : Γ ⊢[PRAAx] oddProd (zero : PTm n) ≐ one := prod_zero _ _

theorem oddProd_succ (N : PTm n) :
    Γ ⊢[PRAAx] oddProd (succ N) ≐ oddProd N * (two * two * N + two) := by
  have h := prod_succ (Γ := Γ) oddB N zero
  simp only [PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Matrix.cons_val_zero] at h
  exact h

theorem fact_prod_base : Γ ⊢[PRAAx] fact (succ (zero : PTm n)) * cat zero ≐ oddProd zero := by
  ipra_lc 𝔞 (cat (zero : PTm n)) * natEq (fact_succ (Γ := Γ) zero zero) +
    𝔞 (cat (zero : PTm n)) * natEq (fact_zero (Γ := Γ) zero) + natEq (cat_zero (Γ := Γ)) -
    natEq (oddProd_zero (Γ := Γ))

theorem fact_prod_step {N : PTm n} (ih : Γ ⊢[PRAAx] fact (succ N) * cat N ≐ oddProd N) :
    Γ ⊢[PRAAx] fact (succ (succ N)) * cat (succ N) ≐ oddProd (succ N) := by
  ipra_lc 𝔞 (cat (succ N)) * natEq (fact_succ (Γ := Γ) (succ N) zero) +
    𝔞 (fact (succ N)) * natEq (cat_rec (Γ := Γ) N) + (2 * (2 * 𝔞 N + 1)) * natEq ih - natEq (oddProd_succ (Γ := Γ) N)

/-- Variable: `0 = n`. -/
abbrev factProdFormula : Fm PTm 1 := fact (succ (var 0)) * cat (var 0) ≐ oddProd (var 0)

private theorem fact_prod₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] factProdFormula := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fact_prod_base
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fact_prod_step Prf.hyp0

/-- (2.7): `(n + 1)! Cat_n = ∏_{j<n} (4j + 2)`. -/
theorem cat_fact_prod (N : PTm n) : Γ ⊢[PRAAx] fact (succ N) * cat N ≐ oddProd N := by
  have h := inst (Γ := Γ) fact_prod₀ (![N] : Fin 1 → PTm n)
  simpa using h

theorem cat_fact_prod_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 factProdFormula :=
  closeUniv 1 fact_prod₀

/-! ## The form (2.6) -/

/-- `n C(2n, n) = (n + 1) C(2n, n + 1)` for `n = m + 1`, at an arbitrary term. -/
theorem ratio_at (m : PTm n) :
    Γ ⊢[PRAAx] succ m * binom (two * succ m) (succ m) ≐
      succ (succ m) * binom (two * succ m) (succ (succ m)) := by
  have h := inst (Γ := Γ) catalan_ratio_open (![m] : Fin 1 → PTm n)
  simpa using h

/-- `(m + 1) Cat_{m+1} = C(2m + 2, m + 2)`. -/
theorem cat_upper_binom (m : PTm n) :
    Γ ⊢[PRAAx] succ m * cat (succ m) ≐ binom (two * succ m) (succ (succ m)) := by
  refine mul_cancel (D := succ (succ m)) (succ_pos _) ?_
  ipra_lc (𝔞 m + 1) * natEq (cat_spec (Γ := Γ) (succ m)) + natEq (ratio_at (Γ := Γ) m)

/-- (2.6): `(m + 1) Cat_{m+1} = C(2m + 2, m)`. -/
theorem cat_lower_binom (m : PTm n) :
    Γ ⊢[PRAAx] succ m * cat (succ m) ≐ binom (two * succ m) m := by
  have e : Γ ⊢[PRAAx] two * succ m ≐ succ (succ m) + m := by
    ipra_ring
  have hle : Γ ⊢[PRAAx] le (succ (succ m)) (two * succ m) := le_of_eq_add e
  have hm : Γ ⊢[PRAAx] monus (two * succ m) (succ (succ m)) ≐ m :=
    (congrMonus e (.eqRefl _)).eqTrans (add_monus' m (succ (succ m)))
  have hs : Γ ⊢[PRAAx] binom (two * succ m) m ≐ binom (two * succ m) (succ (succ m)) :=
    (congrAp2 quoF (.eqRefl _) (bden_congr hm.eqSymm)).eqTrans (binom_symm hle)
  exact (cat_upper_binom m).eqTrans hs.eqSymm

/-- Variable: `0 = m`. -/
abbrev lowerBinomFormula : Fm PTm 1 :=
  succ (var 0) * cat (succ (var 0)) ≐ binom (two * succ (var 0)) (var 0)

theorem cat_lower_binom_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 lowerBinomFormula :=
  closeUniv 1 (cat_lower_binom (var 0))

/-! ## The bound (4.5) -/

/-- The base `16`. -/
abbrev sixteen : PTm n := (two * two) * (two * two)

theorem cb_sq_base :
    Γ ⊢[PRAAx] le (succ (zero : PTm n) * (cb zero * cb zero)) (pw sixteen zero) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq (pw_zero (Γ := Γ) (sixteen : PTm n)) - (𝔞 (cb (zero : PTm n)) + 1) * natEq (cb_zero (Γ := Γ))

theorem cb_sq_step {m : PTm n} (ih : Γ ⊢[PRAAx] le (succ m * (cb m * cb m)) (pw sixteen m)) :
    Γ ⊢[PRAAx] le (succ (succ m) * (cb (succ m) * cb (succ m))) (pw sixteen (succ m)) := by
  refine mul_le_cancel (d' := m) (mul_le_cancel (d' := m) ?_)
  refine le_of_eq_add (d := (two * two) * ((succ two * m + two) * (cb m * cb m) +
    (two * two) * (succ m * succ m) * monus (pw sixteen m) (succ m * (cb m * cb m)))) ?_
  ipra_lc (𝔞 m + 1) ^ 2 * natEq (pw_succ (Γ := Γ) (sixteen : PTm n) m) +
    16 * (𝔞 m + 1) ^ 2 * natEq (eq_add_of_le ih) -
    ((𝔞 m + 2) * ((𝔞 m + 1) * 𝔞 (cb (succ m)) + 2 * (2 * 𝔞 m + 1) * 𝔞 (cb m))) * natEq (cb_rec (Γ := Γ) m)

/-- Variable: `0 = m`. -/
abbrev cbSqFormula : Fm PTm 1 :=
  le (succ (var 0) * (cb (var 0) * cb (var 0))) (pw sixteen (var 0))

private theorem cb_sq₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] cbSqFormula := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact cb_sq_base
  · simp only [subst_le, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact cb_sq_step Prf.hyp0

/-- (4.5): `(m + 1) C(2m, m)² ≤ 16^m`. -/
theorem cb_sq_bound (m : PTm n) : Γ ⊢[PRAAx] le (succ m * (cb m * cb m)) (pw sixteen m) := by
  have h := inst (Γ := Γ) cb_sq₀ (![m] : Fin 1 → PTm n)
  simpa using h

theorem cb_sq_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 cbSqFormula :=
  closeUniv 1 cb_sq₀

end LeanProofs.IPRA.Combinatorics.CatalanProducts
