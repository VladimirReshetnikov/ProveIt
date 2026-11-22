import IPRADerivations.Core.PolynomialImplications
import Mathlib.Algebra.BigOperators.Fin

/-!
# Quotient rings by ideal-combination witnesses (`ipra_algebraic_geometry_framework`)

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15`, Section "Finitely presented
algebra with proof-relevant equality", `thm:quotient-setoid` ("Exact certified presentation of a
quotient ring"): for `A = ℤ[X]/(g_0, …, g_{r−1})`, a witness that `p` and `q` represent the same
element is a vector `h` with `p − q = ∑_{i<r} h_i g_i` (`eq:ideal-witness`), and

`refl(p) = (0, …, 0)`, `sym(h) = (−h_0, …, −h_{r−1})`, `trans(h, k) = (h_0 + k_0, …)`;
"Addition, negation, and multiplication admit primitive-recursive congruence transformers":
`(p + q) − (p′ + q′) = ∑ (h_i + k_i) g_i`, `pq − p′q′ = ∑ (h_i q + p′ k_i) g_i`.

The number `r` of generators is a parameter of the Lean statements (each instance is one iPRA
derivation). The elements `p, p′, q, q′`, the generators `g_i` and the witness entries `h_i`, `k_i`
are independent variables (`vP`, …, `vG i`, `vH i`, `vK i`), so every statement below is an
identity in the free commutative ring on these symbols: it holds for all polynomials substituted
for them, and in particular coefficientwise.

* `zsum`, `eval_zsum`: the sum `∑_{i<r}` of expressions, evaluated as a `Finset` sum;
* `refl_witness`, `symm_witness`, `trans_witness`: the witnesses of reflexivity, symmetry and
  transitivity;
* `add_witness`, `neg_witness`, `mul_witness`: the congruence transformers of addition, negation
  and multiplication;
* `comm_witness`, `distrib_witness`: two ring laws with the zero witness ("Ring laws are literal
  polynomial identities and therefore have fixed zero … certificates").

Not formalized: polynomial codes as finite lists, the coefficientwise checker as a primitive
recursive function on codes, and presentations over a certified base ring other than `ℤ`.
-/

namespace LeanProofs.IPRA.Geometry.QuotientPresentation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp
open scoped BigOperators

/-! ## Finite sums of expressions -/

/-- `∑_{i<r} f(i)` as an expression. -/
def zsum {k : ℕ} : {r : ℕ} → (Fin r → ZExp k) → ZExp k
  | 0, _ => 0
  | _ + 1, f => f 0 + zsum (fun i => f i.succ)

theorem eval_zsum {k : ℕ} {R : Type} [CommRing R] (ρ : Fin k → R) :
    ∀ {r : ℕ} (f : Fin r → ZExp k), eval ρ (zsum f) = ∑ i, eval ρ (f i)
  | 0, _ => by simp [zsum]
  | r + 1, f => by
    rw [Fin.sum_univ_succ]
    show eval ρ (f 0) + eval ρ (zsum (fun i => f i.succ)) = _
    rw [eval_zsum ρ (fun i => f i.succ)]

/-! ## The symbols -/

section Symbols

variable (r : ℕ)

/-- `p`. -/
def vP : ZExp (4 + 3 * r) := var ⟨0, by omega⟩
/-- `p′` (or the second element of a chain). -/
def vP' : ZExp (4 + 3 * r) := var ⟨1, by omega⟩
/-- `q` (or the third element of a chain). -/
def vQ : ZExp (4 + 3 * r) := var ⟨2, by omega⟩
/-- `q′`. -/
def vQ' : ZExp (4 + 3 * r) := var ⟨3, by omega⟩
/-- The generator `g_i`. -/
def vG (i : Fin r) : ZExp (4 + 3 * r) := var ⟨4 + i.val, by omega⟩
/-- The witness entry `h_i`. -/
def vH (i : Fin r) : ZExp (4 + 3 * r) := var ⟨4 + r + i.val, by omega⟩
/-- The witness entry `k_i`. -/
def vK (i : Fin r) : ZExp (4 + 3 * r) := var ⟨4 + 2 * r + i.val, by omega⟩

/-- `∑_{i<r} w(i) g_i`. -/
def comb (w : Fin r → ZExp (4 + 3 * r)) : ZExp (4 + 3 * r) := zsum (fun i => w i * vG r i)

theorem eval_comb {R : Type} [CommRing R] (ρ : Fin (4 + 3 * r) → R) (w : Fin r → ZExp (4 + 3 * r)) :
    eval ρ (comb r w) = ∑ i, eval ρ (w i) * eval ρ (vG r i) := by
  simp [comb, eval_zsum]

end Symbols

/-- Start the certificate of a witness transformer. -/
local macro "wit_poly" : tactic =>
  `(tactic| simp only [holds_cons, holds_nil, and_true, eval_comb, eval_sub, eval_add,
    eval_mul, eval_neg, eval_zero] at *)

/-! ## Reflexivity, symmetry, transitivity -/

/-- `refl(p) = (0, …, 0)`: `p − p = ∑ 0 · g_i`. -/
theorem refl_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [] (vP r - vP r, comb r (fun _ => 0))) :=
  derive_imp _ _ (by intro R _ ρ h; wit_poly; simp)

/-- `sym(h) = (−h_i)`: from `p − q = ∑ h_i g_i`, `q − p = ∑ (−h_i) g_i`. -/
theorem symm_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [(vP r - vP' r, comb r (vH r))] (vP' r - vP r, comb r (fun i => -vH r i))) :=
  derive_imp _ _ (by
    intro R _ ρ h
    wit_poly
    have e : ∑ i, -eval ρ (vH r i) * eval ρ (vG r i) = -∑ i, eval ρ (vH r i) * eval ρ (vG r i) := by
      rw [← Finset.sum_neg_distrib]; congr 1; funext i; ring
    rw [e]
    linear_combination -h)

/-- `trans(h, k) = (h_i + k_i)`: from `p − p′ = ∑ h_i g_i` and `p′ − q = ∑ k_i g_i`,
`p − q = ∑ (h_i + k_i) g_i`. -/
theorem trans_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [(vP r - vP' r, comb r (vH r)), (vP' r - vQ r, comb r (vK r))]
      (vP r - vQ r, comb r (fun i => vH r i + vK r i))) :=
  derive_imp _ _ (by
    intro R _ ρ h
    wit_poly
    obtain ⟨h₁, h₂⟩ := h
    have e : ∑ i, (eval ρ (vH r i) + eval ρ (vK r i)) * eval ρ (vG r i) =
        ∑ i, eval ρ (vH r i) * eval ρ (vG r i) + ∑ i, eval ρ (vK r i) * eval ρ (vG r i) := by
      rw [← Finset.sum_add_distrib]; congr 1; funext i; ring
    rw [e]
    linear_combination h₁ + h₂)

/-! ## Congruence transformers -/

/-- Addition: `(p + q) − (p′ + q′) = ∑ (h_i + k_i) g_i`. -/
theorem add_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [(vP r - vP' r, comb r (vH r)), (vQ r - vQ' r, comb r (vK r))]
      ((vP r + vQ r) - (vP' r + vQ' r), comb r (fun i => vH r i + vK r i))) :=
  derive_imp _ _ (by
    intro R _ ρ h
    wit_poly
    obtain ⟨h₁, h₂⟩ := h
    have e : ∑ i, (eval ρ (vH r i) + eval ρ (vK r i)) * eval ρ (vG r i) =
        ∑ i, eval ρ (vH r i) * eval ρ (vG r i) + ∑ i, eval ρ (vK r i) * eval ρ (vG r i) := by
      rw [← Finset.sum_add_distrib]; congr 1; funext i; ring
    rw [e]
    linear_combination h₁ + h₂)

/-- Negation: `(−p) − (−p′) = ∑ (−h_i) g_i`. -/
theorem neg_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [(vP r - vP' r, comb r (vH r))] ((-vP r) - (-vP' r), comb r (fun i => -vH r i))) :=
  derive_imp _ _ (by
    intro R _ ρ h
    wit_poly
    have e : ∑ i, -eval ρ (vH r i) * eval ρ (vG r i) = -∑ i, eval ρ (vH r i) * eval ρ (vG r i) := by
      rw [← Finset.sum_neg_distrib]; congr 1; funext i; ring
    rw [e]
    linear_combination -h)

/-- Multiplication: `pq − p′q′ = (p − p′) q + p′ (q − q′) = ∑ (h_i q + p′ k_i) g_i`. -/
theorem mul_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [(vP r - vP' r, comb r (vH r)), (vQ r - vQ' r, comb r (vK r))]
      (vP r * vQ r - vP' r * vQ' r, comb r (fun i => vH r i * vQ r + vP' r * vK r i))) :=
  derive_imp _ _ (by
    intro R _ ρ h
    wit_poly
    obtain ⟨h₁, h₂⟩ := h
    have e : ∑ i, (eval ρ (vH r i) * eval ρ (vQ r) + eval ρ (vP' r) * eval ρ (vK r i)) *
          eval ρ (vG r i) =
        eval ρ (vQ r) * ∑ i, eval ρ (vH r i) * eval ρ (vG r i) +
          eval ρ (vP' r) * ∑ i, eval ρ (vK r i) * eval ρ (vG r i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; funext i; ring
    rw [e]
    linear_combination eval ρ (vQ r) * h₁ + eval ρ (vP' r) * h₂)

/-! ## Ring laws with the zero witness -/

/-- Commutativity of multiplication: `pq − qp = ∑ 0 · g_i`. -/
theorem comm_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [] (vP r * vQ r - vQ r * vP r, comb r (fun _ => 0))) :=
  derive_imp _ _ (by intro R _ ρ h; wit_poly; simp; ring)

/-- Distributivity: `p (q + q′) − (pq + pq′) = ∑ 0 · g_i`. -/
theorem distrib_witness (r : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * (4 + 3 * r))
    (imp [] (vP r * (vQ r + vQ' r) - (vP r * vQ r + vP r * vQ' r), comb r (fun _ => 0))) :=
  derive_imp _ _ (by intro R _ ρ h; wit_poly; simp; ring)

end LeanProofs.IPRA.Geometry.QuotientPresentation
