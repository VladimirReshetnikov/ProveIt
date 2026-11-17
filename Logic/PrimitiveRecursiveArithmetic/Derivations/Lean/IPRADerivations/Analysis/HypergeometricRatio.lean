import IPRADerivations.Analysis.Pochhammer

/-!
# Generalized hypergeometric terms: symmetry and the term ratio

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/03_series.tex`:

* `prop:symmetry`: `₂F₁(a, b; c; z) = ₂F₁(b, a; c; z)` and `₂F₁(a, b; c; 0) = 1`, coefficientwise;
* `prop:pfq-ratio`: the successive terms of `ₚF_q` satisfy
  `(n + 1) ∏_{j<q} (n + b_j) T_{n+1} = z ∏_{i<p} (n + a_i) T_n`.

For fixed `p`, `q` the parameters are lists of natural-number terms `a_i`, `b_j`, and the term
`T_n = z^n ∏_i (a_i)_n / (n! ∏_j (b_j)_n)` is the numerator `Num_n = z^n ∏_i (a_i)_n` over the
denominator `Den_n = n! ∏_j (b_j)_n`; the ratio identity is cross-multiplied by `Den_n Den_{n+1}`.

* `prodL`, `pochL`: finite products over a parameter list; `pochL_succ`:
  `∏_i (a_i)_{n+1} = ∏_i (a_i)_n · ∏_i (a_i + n)`;
* `pochL_perm`: the products depend only on the multiset of parameters (any permutation), which is the
  general form of the symmetry `a ↔ b`; `gauss_symm`, `gauss_norm` are the `₂F₁` statements;
* `pfq_ratio`: the cross-multiplied term ratio.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.HypergeometricRatio

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_zero poch_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `∏ l`. -/
def prodL : List (PTm n) → PTm n
  | [] => one
  | t :: l => t * prodL l

/-- `∏_i (a_i)_k`. -/
def pochL (as : List (PTm n)) (k : PTm n) : PTm n := prodL (as.map fun a => poch a k)

/-- `∏_i (a_i + k)`. -/
def shiftL (as : List (PTm n)) (k : PTm n) : PTm n := prodL (as.map fun a => a + k)

theorem pochL_succ (as : List (PTm n)) (k : PTm n) :
    Γ ⊢[PRAAx] pochL as (succ k) ≐ pochL as k * shiftL as k := by
  induction as with
  | nil => simp only [pochL, shiftL, List.map, prodL]; apply deriveNat; ipra_simps; ring
  | cons a l ih =>
    simp only [pochL, shiftL, List.map, prodL] at ih ⊢
    refine (congrMul (poch_succ a k) ih).eqTrans ?_
    apply deriveNat; ipra_simps; ring

theorem pochL_zero (as : List (PTm n)) : Γ ⊢[PRAAx] pochL as zero ≐ one := by
  induction as with
  | nil => simp only [pochL, List.map, prodL]; exact .eqRefl _
  | cons a l ih =>
    simp only [pochL, List.map, prodL] at ih ⊢
    exact (congrMul (poch_zero a) ih).eqTrans (by apply deriveNat; ipra_simps; ring)

/-- Products over a list are invariant under permutation. -/
theorem prodL_perm {l₁ l₂ : List (PTm n)} (h : l₁.Perm l₂) : Γ ⊢[PRAAx] prodL l₁ ≐ prodL l₂ := by
  induction h with
  | nil => exact .eqRefl _
  | cons t _ ih => exact congrMul (.eqRefl t) ih
  | swap s t l => simp only [prodL]; apply deriveNat; ipra_simps; ring
  | trans _ _ ih₁ ih₂ => exact ih₁.eqTrans ih₂

/-- `prop:symmetry` in general form: permuting the parameters does not change the Pochhammer products. -/
theorem pochL_perm {as bs : List (PTm n)} (h : as.Perm bs) (k : PTm n) :
    Γ ⊢[PRAAx] pochL as k ≐ pochL bs k :=
  prodL_perm (h.map _)

/-- The numerator `z^k ∏_i (a_i)_k`. -/
abbrev Num (as : List (PTm n)) (z k : PTm n) : PTm n := pw z k * pochL as k
/-- The denominator `k! ∏_j (b_j)_k`. -/
abbrev Den (bs : List (PTm n)) (k : PTm n) : PTm n := fact k * pochL bs k

/-- `prop:pfq-ratio`: `(k + 1) ∏_j (k + b_j) T_{k+1} = z ∏_i (k + a_i) T_k`, with `T_k = Num_k / Den_k`
cross-multiplied by `Den_k Den_{k+1}`. -/
theorem pfq_ratio (as bs : List (PTm n)) (z k : PTm n) :
    Γ ⊢[PRAAx] (succ k * shiftL bs k) * (Num as z (succ k) * Den bs k) ≐
      (z * shiftL as k) * (Num as z k * Den bs (succ k)) := by
  have nE : Γ ⊢[PRAAx] Num as z (succ k) ≐ (pw z k * z) * (pochL as k * shiftL as k) :=
    congrMul (pw_succ z k) (pochL_succ as k)
  have dE : Γ ⊢[PRAAx] Den bs (succ k) ≐ (fact k * succ k) * (pochL bs k * shiftL bs k) :=
    congrMul (fact_succ k zero) (pochL_succ bs k)
  refine (congrMul (.eqRefl _) (congrMul nE (.eqRefl _))).eqTrans (.eqTrans ?_
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) dE)).eqSymm)
  apply deriveNat; ipra_simps; ring

/-- `₂F₁` symmetry: `(a)_k (b)_k = (b)_k (a)_k`. -/
theorem gauss_symm (a b k : PTm n) : Γ ⊢[PRAAx] pochL [a, b] k ≐ pochL [b, a] k :=
  pochL_perm (List.Perm.swap b a []) k

/-- `₂F₁(a, b; c; 0) = 1`: the constant term has numerator `(a)_0 (b)_0 = 1` and denominator
`(c)_0 0! = 1`. -/
theorem gauss_norm (a b c z : PTm n) :
    Γ ⊢[PRAAx] (Num [a, b] z zero ≐ one) ⋏ (Den [c] zero ≐ one) := by
  refine .andI ((congrMul (pw_zero z) (pochL_zero _)).eqTrans (by apply deriveNat; ipra_simps; ring)) ?_
  exact (congrMul (fact_zero zero) (pochL_zero _)).eqTrans (by apply deriveNat; ipra_simps; ring)

end LeanProofs.IPRA.Analysis.HypergeometricRatio
