import FabiusFunction.HessenbergDeterminant
import FabiusFunction.BellPolynomialInversion
import FabiusFunction.ElementarySymmetricBell
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The two Hessenberg determinants for the complete Bell polynomials

This module formalizes the Bell-determinant cluster of the *Combinatorial Coefficient
Calculus* manuscript.

## Manuscript labels

* `thm:bell-determinants` (`eq:bell-determinants`), `B_n(x_1,…,x_n) = det H_n = det K_n`
  for the two upper-Hessenberg matrices

  `(H_n)_{ij} = C(n-i, j-i) x_{j-i+1}` for `j ≥ i`, `-1` for `j = i-1`, `0` below, and
  `(K_n)_{ij} = x_{j-i+1}/(j-i)!` for `j ≥ i`, `-(i-1)` for `j = i-1`, `0` below.

  Formalized as `Fabius.det_bellMatrixH` (over every commutative ring) and
  `Fabius.det_bellMatrixK` / `Fabius.det_bellMatrixK_invFactorial`.

* `cor:det-traces-bell` (`eq:det-traces-bell`), `det A = ((-1)^n/n!) B_n(w_1,…,w_n)` with
  `w_k = -(k-1)! tr(A^k)`.  Formalized as `Fabius.det_eq_bell_complete_traceWeight`, with the
  eigenvalue family supplied as a hypothesis — see the caveat below.

* `thm:cycle-index-bell` (`eq:cycle-index-bell`), `Z(S_n) = (1/n!) B_n(0!a_1,…,(n-1)!a_n)`.
  Only the specialization to equal marks `a_j = a` is proved here, as
  `Fabius.bell_complete_cycleWeightConst`; see the caveat below.

## What the formalization exposed

The manuscript proves `det H_n = B_n` by expanding along the first row, obtaining
`D_n = ∑_j C(n-1,j-1) x_j D_{n-j}`.  That expansion is not the honest formal content, and it is
not the recurrence of a single matrix family either: the entries of `H_n` contain the binomials
`C(n-i, j-i)`, which depend on the **size** `n`, so `H_n` is not the Hessenberg matrix of a
size-independent linear recurrence and the corpus's generic `Fabius.det_hessenbergMatrix` does
not apply to it directly.

Reversing the index order removes the size dependence completely.  Writing `J` for the
order-reversing involution `i ↦ n-1-i` of `Fin n`, an entrywise computation
(`Fabius.submatrix_revPerm_bellMatrixH`) gives that `J H_n J` is the lower-Hessenberg matrix of
the recurrence `α_{m+1} = ∑_{k ≤ m} C(m,k) x_{m+1-k} α_k`, whose coefficients
`β(m,k) = C(m-1,k) x_{m-k}` (`Fabius.bellBeta`) no longer mention `n`: the reversal makes
`n-1-i` cancel the `n-i` inside the binomial, `C(n-1-J r, J c - J r) = C(r, r-c) = C(r,c)`.
That recurrence is the complete Bell recurrence (`Fabius.hessenbergSeq_bellBeta`), so
`det H_n = B_n` follows from `Fabius.det_hessenbergMatrix` with **no determinant expansion at
all** — only `Matrix.det_submatrix_equiv_self`.  The better decomposition really is "recurrence
plus identification", but the recurrence becomes visible only after the reversal.

The second matrix is then pure bookkeeping: `K_n` is the entrywise rescaling
`(K_n)_{rc} = r! · (1/c!) · Q_{rc}` of the reversed transpose `Q = J H_n^T J`
(`Fabius.bellMatrixQ`), and `Matrix.det_mul_row` / `Matrix.det_mul_column` contribute the
reciprocal products `(∏ r!) · (∏ 1/r!) = 1`.  This is exactly the manuscript's
`K_n = D (J H_n^T J) D^{-1}` with `D = diag(0!,1!,…,(n-1)!)`, made division-free by taking the
reciprocal factorials as a hypothesis `d` with `m! · d m = 1` instead of forming `D^{-1}`.

## What is *not* covered

* `det K_n = B_n` is stated over a commutative ring **equipped with reciprocal factorials**
  (`Fabius.det_bellMatrixK`), specialized to commutative `ℚ`-algebras
  (`Fabius.det_bellMatrixK_invFactorial`).  The identity is in fact true over every commutative
  ring once denominators are cleared, by specialization from `ℤ[y]`, but that
  universal-coefficient argument is not formalized.

* `cor:det-traces-bell` is proved from the corpus's `Fabius.esymm_eq_neg_bell_complete` exactly
  as the manuscript proves it — by applying the symmetric-function identity to the eigenvalues —
  but the *existence* of the eigenvalue family is a hypothesis (`hdet`, `htr`).  Mathlib has
  `Matrix.det_eq_prod_roots_charpoly` and `Matrix.trace_eq_sum_roots_charpoly` over an
  algebraically closed field, but it has no `tr(A^k) = ∑ λ_i^k`; that needs triangularization,
  which Mathlib does not have for matrices.  Discharging the hypotheses is therefore left open.
  They hold for triangular matrices and, classically, for every matrix over an algebraically
  closed field.

* `thm:cycle-index-bell` for general marks `a_1,…,a_n` is **not** formalized.  Its content is
  the exponential formula, i.e. the cycle-removal bijection
  `S_[n] ≃ Σ_{S ∋ n} (cyclic orders on S) × S_{[n]∖S}`, for which Mathlib has no API.  What is
  proved is the identity the theorem reduces to when all marks are equal,
  `B_n(0!a, 1!a, …, (n-1)!a) = a(a+1)⋯(a+n-1)` (`Fabius.bell_complete_cycleWeightConst`) — i.e.
  `∑_{σ ∈ S_n} a^{#cycles σ}` is the rising factorial — together with its `a = 1` instance
  `B_n(0!,1!,…,(n-1)!) = n! = |S_n|` (`Fabius.card_perm_eq_bell_complete`), where both sides are
  computed independently and so a genuine instance of the cycle-index identity is verified.

## Numeric status

Every identity here was checked in exact rational arithmetic before formalization:
`det H_n = det K_n = B_n` for `n = 0,…,10`; the entrywise reindexings above for `n = 0,…,10`;
the cycle-index specializations for `n ≤ 20`; the trace corollary for `n ≤ 7`.  The manuscript's
statements are correct as printed.
-/

set_option autoImplicit false

open Finset Matrix

namespace Fabius

/-! ## The reflected form of the complete Bell recurrence -/

section CommSemiring

variable {S : Type*} [CommSemiring S]

/-- The complete Bell recurrence written with the weight carrying the *large* index, i.e.
`B_{n+1} = ∑_{k ≤ n} C(n,k) x_{n+1-k} B_k`.  This is the orientation in which the recurrence is
the first-row expansion of the manuscript's Hessenberg determinant; `Bell.complete_succ`
supplies the mirror-image orientation. -/
theorem bell_complete_succ' (x : ℕ → S) (n : ℕ) :
    Bell.complete x (n + 1) =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : S) * x (n + 1 - k) * Bell.complete x k := by
  rw [Bell.complete_succ, Bell.binomialConv_eq_sum_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Bell.shift_apply, show n + 1 - k = n - k + 1 by omega]
  ring

/-! ## Cycle indices -/

/-- The cycle-index weights `x_r = (r-1)!·a_r` of `thm:cycle-index-bell`, with `x_0 = 0`.  The
theorem asserts `n!·Z(S_n) = B_n(x_1,…,x_n)`, where `a_j` marks the cycles of length `j`. -/
def cycleIndexWeight (a : ℕ → S) (r : ℕ) : S :=
  if r = 0 then 0 else (((r - 1).factorial : ℕ) : S) * a r

/-- The cycle-index weights with all marks equal to `a`: `x_r = (r-1)!·a`, and `x_0 = 0`. -/
def cycleWeightConst (a : S) (r : ℕ) : S :=
  if r = 0 then 0 else (((r - 1).factorial : ℕ) : S) * a

/-- Setting every mark to `a` in the cycle-index weights gives `Fabius.cycleWeightConst`. -/
theorem cycleIndexWeight_const (a : S) : cycleIndexWeight (fun _ => a) = cycleWeightConst a := by
  funext r
  rfl

/-- Evaluation of the constant cycle-index weights at a positive index. -/
theorem cycleWeightConst_succ (a : S) (m : ℕ) :
    cycleWeightConst a (m + 1) = ((m.factorial : ℕ) : S) * a := by
  unfold cycleWeightConst
  rw [if_neg (show m + 1 ≠ 0 by omega), Nat.add_sub_cancel]

/-- The arithmetic core of the uniform cycle index:
`∑_{k ≤ n} C(n,k)·(n-k)!·a·∏_{i<k}(a+i) = ∏_{i<n+1}(a+i)`.  Equivalently
`∑_{k ≤ n} (n!/k!)·a·a^{(k)} = a^{(n+1)}` for the rising factorial `a^{(k)}`; the induction runs
on `C(n+1,k)·(n+1-k)! = (n+1)·C(n,k)·(n-k)!`. -/
theorem sum_range_choose_factorial_mul_prod (a : S) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : S) * ((((n - k).factorial : ℕ) : S) * a) *
        ∏ i ∈ Finset.range k, (a + (i : S)))
      = ∏ i ∈ Finset.range (n + 1), (a + (i : S)) := by
  induction n with
  | zero => simp
  | succ m ih =>
      have key : ∀ k ∈ Finset.range (m + 1),
          (((m + 1).choose k : ℕ) : S) * (((((m + 1) - k).factorial : ℕ) : S) * a) *
              (∏ i ∈ Finset.range k, (a + (i : S)))
            = ((m : S) + 1) * (((m.choose k : ℕ) : S) * ((((m - k).factorial : ℕ) : S) * a) *
                ∏ i ∈ Finset.range k, (a + (i : S))) := by
        intro k hk
        have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hnat : (m + 1).choose k * ((m + 1) - k).factorial
            = (m + 1) * (m.choose k * (m - k).factorial) := by
          refine Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos k) ?_
          calc (m + 1).choose k * ((m + 1) - k).factorial * k.factorial
              = (m + 1).choose k * k.factorial * ((m + 1) - k).factorial := by ring
            _ = (m + 1).factorial :=
                Nat.choose_mul_factorial_mul_factorial (show k ≤ m + 1 by omega)
            _ = (m + 1) * m.factorial := Nat.factorial_succ m
            _ = (m + 1) * (m.choose k * k.factorial * (m - k).factorial) := by
                rw [Nat.choose_mul_factorial_mul_factorial hk']
            _ = (m + 1) * (m.choose k * (m - k).factorial) * k.factorial := by ring
        have hcast : (((m + 1).choose k : ℕ) : S) * (((((m + 1) - k).factorial) : ℕ) : S)
            = ((m : S) + 1) * (((m.choose k : ℕ) : S) * ((((m - k).factorial) : ℕ) : S)) := by
          have hc := congrArg (Nat.cast : ℕ → S) hnat
          push_cast at hc
          exact hc
        calc (((m + 1).choose k : ℕ) : S) * (((((m + 1) - k).factorial : ℕ) : S) * a) *
              (∏ i ∈ Finset.range k, (a + (i : S)))
            = ((((m + 1).choose k : ℕ) : S) * (((((m + 1) - k).factorial) : ℕ) : S)) *
                (a * ∏ i ∈ Finset.range k, (a + (i : S))) := by ring
          _ = (((m : S) + 1) * (((m.choose k : ℕ) : S) * ((((m - k).factorial) : ℕ) : S))) *
                (a * ∏ i ∈ Finset.range k, (a + (i : S))) := by rw [hcast]
          _ = ((m : S) + 1) * (((m.choose k : ℕ) : S) * ((((m - k).factorial : ℕ) : S) * a) *
                ∏ i ∈ Finset.range k, (a + (i : S))) := by ring
      have hsum : (∑ k ∈ Finset.range (m + 1),
            (((m + 1).choose k : ℕ) : S) * (((((m + 1) - k).factorial : ℕ) : S) * a) *
              ∏ i ∈ Finset.range k, (a + (i : S)))
          = ∑ k ∈ Finset.range (m + 1), ((m : S) + 1) *
              (((m.choose k : ℕ) : S) * ((((m - k).factorial : ℕ) : S) * a) *
                ∏ i ∈ Finset.range k, (a + (i : S))) :=
        Finset.sum_congr rfl key
      rw [Finset.prod_range_succ, Finset.sum_range_succ, hsum, ← Finset.mul_sum, ih]
      simp only [Nat.choose_self, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul]
      push_cast
      ring

/-- **The cycle index of `S_n` at equal marks** (`thm:cycle-index-bell` with every `a_j = a`):
`B_n(0!a, 1!a, …, (n-1)!a) = a(a+1)⋯(a+n-1)`.  The right-hand side is the rising factorial,
which is `∑_{σ ∈ S_n} a^{#cycles σ}`, so this is `n!·Z(S_n)` at equal marks. -/
theorem bell_complete_cycleWeightConst (a : S) (n : ℕ) :
    Bell.complete (cycleWeightConst a) n = ∏ i ∈ Finset.range n, (a + (i : S)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ m =>
        have hterm : ∀ k ∈ Finset.range (m + 1),
            ((m.choose k : ℕ) : S) * cycleWeightConst a (m + 1 - k) *
                Bell.complete (cycleWeightConst a) k
              = ((m.choose k : ℕ) : S) * ((((m - k).factorial : ℕ) : S) * a) *
                ∏ i ∈ Finset.range k, (a + (i : S)) := by
          intro k hk
          have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [show m + 1 - k = (m - k) + 1 by omega, cycleWeightConst_succ,
            ih k (Finset.mem_range.mp hk)]
        have hsum : (∑ k ∈ Finset.range (m + 1), ((m.choose k : ℕ) : S) *
              cycleWeightConst a (m + 1 - k) * Bell.complete (cycleWeightConst a) k)
            = ∑ k ∈ Finset.range (m + 1), ((m.choose k : ℕ) : S) *
                ((((m - k).factorial : ℕ) : S) * a) * ∏ i ∈ Finset.range k, (a + (i : S)) :=
          Finset.sum_congr rfl hterm
        rw [bell_complete_succ', hsum]
        exact sum_range_choose_factorial_mul_prod a m

/-- The cycle index at all marks equal to `1`: `B_n(0!, 1!, …, (n-1)!) = n!`. -/
theorem bell_complete_cycleWeightConst_one (n : ℕ) :
    Bell.complete (cycleWeightConst (1 : S)) n = ((n.factorial : ℕ) : S) := by
  rw [bell_complete_cycleWeightConst]
  have hprod : (∏ i ∈ Finset.range n, ((1 : S) + (i : S)))
      = ∏ i ∈ Finset.range n, ((i + 1 : ℕ) : S) :=
    Finset.prod_congr rfl fun i _ => by push_cast; ring
  rw [hprod]
  have hc := congrArg (Nat.cast : ℕ → S) (Finset.prod_range_add_one_eq_factorial n)
  push_cast at hc ⊢
  exact hc

/-- **`thm:cycle-index-bell` at all marks equal to `1`:** `∑_{σ ∈ S_n} 1 = B_n(0!, 1!, …,
(n-1)!)`.  Both sides are computed independently — the left from `Fintype.card_perm`, the right
from the Bell recurrence — so this is a genuine instance of the cycle-index identity. -/
theorem card_perm_eq_bell_complete (n : ℕ) :
    ((Fintype.card (Equiv.Perm (Fin n)) : ℕ) : S)
      = Bell.complete (cycleWeightConst (1 : S)) n := by
  rw [bell_complete_cycleWeightConst_one, Fintype.card_perm, Fintype.card_fin]

end CommSemiring

/-! ## The Bell recurrence as a Hessenberg recurrence -/

section CommRing

variable {R : Type*} [CommRing R]

/-- The Hessenberg coefficients of the complete Bell recurrence: `β(m,k) = C(m-1,k)·x_{m-k}`,
so that `α_m = ∑_{k < m} β(m,k)·α_k` reads `B_m = ∑_{k<m} C(m-1,k)·x_{m-k}·B_k`.  These do not
depend on the size of the matrix, which is what makes `Fabius.det_hessenbergMatrix`
applicable. -/
def bellBeta (x : ℕ → R) (m k : ℕ) : R := (((m - 1).choose k : ℕ) : R) * x (m - k)

/-- The Bell–Hessenberg coefficients at a successor: `β(n+1,k) = C(n,k)·x_{n+1-k}`. -/
theorem bellBeta_succ (x : ℕ → R) (n k : ℕ) :
    bellBeta x (n + 1) k = ((n.choose k : ℕ) : R) * x (n + 1 - k) := by
  unfold bellBeta
  rw [Nat.add_sub_cancel]

/-- The generic Hessenberg recurrence with the Bell coefficients is the complete Bell family. -/
theorem hessenbergSeq_bellBeta (x : ℕ → R) : hessenbergSeq (bellBeta x) = Bell.complete x := by
  refine Bell.eq_complete_of_recurrence x _ (hessenbergSeq_zero _) fun n => ?_
  rw [hessenbergSeq_succ, Bell.binomialConv_eq_sum_range]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [bellBeta_succ, Bell.shift_apply, show n + 1 - k = n - k + 1 by omega]
  ring

/-! ## The two matrices -/

/-- The manuscript's upper-Hessenberg matrix `H_N` of `thm:bell-determinants`, in `0`-based
indices (`r = i-1`, `c = j-1`):

`(H_N)_{rc} = C(N-1-r, c-r)·x_{c-r+1}` for `r ≤ c`, `-1` for `r = c+1`, and `0` otherwise. -/
def bellMatrixH (x : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R := fun r c =>
  if (r : ℕ) ≤ (c : ℕ) then
    ((((N - 1 - (r : ℕ)).choose ((c : ℕ) - (r : ℕ))) : ℕ) : R) * x ((c : ℕ) - (r : ℕ) + 1)
  else if (r : ℕ) = (c : ℕ) + 1 then -1 else 0

/-- The transpose of the corpus's lower-Hessenberg matrix of the Bell recurrence, in `0`-based
indices:  `Q_{rc} = C(c,r)·x_{c-r+1}` for `r ≤ c`, `-1` for `r = c+1`, and `0` otherwise.  This
is the manuscript's `J H_N^T J`, of which `K_N` is a diagonal rescaling. -/
def bellMatrixQ (x : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R := fun r c =>
  if (r : ℕ) ≤ (c : ℕ) then ((((c : ℕ).choose (r : ℕ)) : ℕ) : R) * x ((c : ℕ) - (r : ℕ) + 1)
  else if (r : ℕ) = (c : ℕ) + 1 then -1 else 0

/-- The manuscript's second upper-Hessenberg matrix `K_N` of `thm:bell-determinants`, in
`0`-based indices, with the reciprocal factorials supplied as a sequence `d` (`d m` plays the
role of `1/m!`):

`(K_N)_{rc} = d_{c-r}·x_{c-r+1}` for `r ≤ c`, `-r` for `r = c+1`, and `0` otherwise.

Over a `ℚ`-algebra, take `d = Fabius.invFactorial`. -/
def bellMatrixK (x d : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R := fun r c =>
  if (r : ℕ) ≤ (c : ℕ) then d ((c : ℕ) - (r : ℕ)) * x ((c : ℕ) - (r : ℕ) + 1)
  else if (r : ℕ) = (c : ℕ) + 1 then -((r : ℕ) : R) else 0

/-! ## `det H_N = B_N` -/

/-- **Reversing the index order turns `H_N` into the Bell recurrence matrix.**  This is the
computation that removes the size dependence of the entries of `H_N`: at the reversed indices
the binomial `C(N-1-r, c-r)` becomes `C(r, r-c) = C(r,c)`, which no longer mentions `N`. -/
theorem submatrix_revPerm_bellMatrixH (x : ℕ → R) (n : ℕ) :
    (bellMatrixH x (n + 1)).submatrix Fin.revPerm Fin.revPerm
      = hessenbergMatrix (bellBeta x) n := by
  ext r c
  have hrn : (r : ℕ) ≤ n := Nat.lt_succ_iff.mp r.isLt
  have hcn : (c : ℕ) ≤ n := Nat.lt_succ_iff.mp c.isLt
  have hr : ((Fin.revPerm r : Fin (n + 1)) : ℕ) = n - (r : ℕ) := by
    show ((Fin.rev r : Fin (n + 1)) : ℕ) = n - (r : ℕ)
    rw [Fin.val_rev]
    omega
  have hc : ((Fin.revPerm c : Fin (n + 1)) : ℕ) = n - (c : ℕ) := by
    show ((Fin.rev c : Fin (n + 1)) : ℕ) = n - (c : ℕ)
    rw [Fin.val_rev]
    omega
  rw [Matrix.submatrix_apply]
  unfold bellMatrixH hessenbergMatrix hessenbergEntry
  rw [hr, hc]
  by_cases hle : (c : ℕ) ≤ (r : ℕ)
  · rw [if_pos (show n - (r : ℕ) ≤ n - (c : ℕ) by omega), if_pos hle, bellBeta_succ,
      show n + 1 - 1 - (n - (r : ℕ)) = (r : ℕ) by omega,
      show n - (c : ℕ) - (n - (r : ℕ)) = (r : ℕ) - (c : ℕ) by omega,
      show (r : ℕ) - (c : ℕ) + 1 = (r : ℕ) + 1 - (c : ℕ) by omega,
      Nat.choose_symm hle]
  · rw [if_neg (show ¬ n - (r : ℕ) ≤ n - (c : ℕ) by omega), if_neg hle]
    by_cases h2 : (c : ℕ) = (r : ℕ) + 1
    · rw [if_pos h2, if_pos (show n - (r : ℕ) = n - (c : ℕ) + 1 by omega)]
    · rw [if_neg h2, if_neg (show ¬ n - (r : ℕ) = n - (c : ℕ) + 1 by omega)]

/-- **The first Bell determinant** (`thm:bell-determinants`, `eq:bell-determinants`, first
equality): `det H_N = B_N(x_1,…,x_N)`, over every commutative ring and for every `N`, the empty
determinant `N = 0` included. -/
theorem det_bellMatrixH (x : ℕ → R) (N : ℕ) : (bellMatrixH x N).det = Bell.complete x N := by
  cases N with
  | zero => rw [Matrix.det_isEmpty, Bell.complete_zero]
  | succ n =>
      rw [← Matrix.det_submatrix_equiv_self Fin.revPerm (bellMatrixH x (n + 1)),
        submatrix_revPerm_bellMatrixH, det_hessenbergMatrix, hessenbergSeq_bellBeta]

/-! ## `det K_N = B_N` -/

/-- The corpus's Bell–Hessenberg matrix, transposed, is `Fabius.bellMatrixQ`. -/
theorem transpose_hessenbergMatrix_bellBeta (x : ℕ → R) (n : ℕ) :
    (hessenbergMatrix (bellBeta x) n)ᵀ = bellMatrixQ x (n + 1) := by
  ext r c
  rw [Matrix.transpose_apply]
  unfold hessenbergMatrix hessenbergEntry bellMatrixQ
  by_cases h : (r : ℕ) ≤ (c : ℕ)
  · rw [if_pos h, if_pos h, bellBeta_succ,
      show (c : ℕ) + 1 - (r : ℕ) = (c : ℕ) - (r : ℕ) + 1 by omega]
  · rw [if_neg h, if_neg h]

/-- The transposed Bell–Hessenberg determinant: `det Q_N = B_N`. -/
theorem det_bellMatrixQ (x : ℕ → R) (N : ℕ) : (bellMatrixQ x N).det = Bell.complete x N := by
  cases N with
  | zero => rw [Matrix.det_isEmpty, Bell.complete_zero]
  | succ n =>
      rw [← transpose_hessenbergMatrix_bellBeta, Matrix.det_transpose, det_hessenbergMatrix,
        hessenbergSeq_bellBeta]

/-- **The second Bell determinant** (`thm:bell-determinants`, `eq:bell-determinants`, second
equality): `det K_N = B_N(x_1,…,x_N)`, over any commutative ring carrying reciprocal factorials
`d` (`m!·d m = 1`).

The proof is the manuscript's `K_N = D (J H_N^T J) D^{-1}` with `D = diag(0!,1!,…,(N-1)!)`, made
division-free: `K_N` is the entrywise product `r!·d_c·Q_{rc}`, and the two determinant scaling
lemmas contribute the factor `(∏ r!)·(∏ d_r) = 1`. -/
theorem det_bellMatrixK (x d : ℕ → R) (hd : ∀ m : ℕ, ((m.factorial : ℕ) : R) * d m = 1) (N : ℕ) :
    (bellMatrixK x d N).det = Bell.complete x N := by
  cases N with
  | zero => rw [Matrix.det_isEmpty, Bell.complete_zero]
  | succ n =>
      have key : ∀ p q : ℕ, p ≤ q →
          d (q - p) = ((p.factorial : ℕ) : R) * d q * ((q.choose p : ℕ) : R) := by
        intro p q hpq
        have hfac : ((q.choose p : ℕ) : R) * ((p.factorial : ℕ) : R) *
            (((q - p).factorial : ℕ) : R) = ((q.factorial : ℕ) : R) := by
          have hc := congrArg (Nat.cast : ℕ → R) (Nat.choose_mul_factorial_mul_factorial hpq)
          push_cast at hc
          exact hc
        have h1 : (((q - p).factorial : ℕ) : R) *
            (((p.factorial : ℕ) : R) * d q * ((q.choose p : ℕ) : R)) = 1 := by
          calc (((q - p).factorial : ℕ) : R) *
                (((p.factorial : ℕ) : R) * d q * ((q.choose p : ℕ) : R))
              = (((q.choose p : ℕ) : R) * ((p.factorial : ℕ) : R) *
                  (((q - p).factorial : ℕ) : R)) * d q := by ring
            _ = ((q.factorial : ℕ) : R) * d q := by rw [hfac]
            _ = 1 := hd q
        calc d (q - p)
            = d (q - p) * ((((q - p).factorial : ℕ) : R) *
                (((p.factorial : ℕ) : R) * d q * ((q.choose p : ℕ) : R))) := by
              rw [h1, mul_one]
          _ = ((((q - p).factorial : ℕ) : R) * d (q - p)) *
                (((p.factorial : ℕ) : R) * d q * ((q.choose p : ℕ) : R)) := by ring
          _ = ((p.factorial : ℕ) : R) * d q * ((q.choose p : ℕ) : R) := by
              rw [hd (q - p), one_mul]
      have hK : bellMatrixK x d (n + 1) =
          Matrix.of (fun r c : Fin (n + 1) => (((r : ℕ).factorial : ℕ) : R) *
            (Matrix.of (fun r' c' : Fin (n + 1) =>
              d (c' : ℕ) * bellMatrixQ x (n + 1) r' c')) r c) := by
        ext r c
        simp only [Matrix.of_apply]
        unfold bellMatrixK bellMatrixQ
        by_cases hle : (r : ℕ) ≤ (c : ℕ)
        · rw [if_pos hle, if_pos hle, key (r : ℕ) (c : ℕ) hle]
          ring
        · rw [if_neg hle, if_neg hle]
          by_cases h2 : (r : ℕ) = (c : ℕ) + 1
          · have hfac : (((r : ℕ).factorial : ℕ) : R) * d (c : ℕ) = ((r : ℕ) : R) := by
              rw [h2, Nat.factorial_succ, Nat.cast_mul, mul_assoc, hd (c : ℕ), mul_one]
            rw [if_pos h2, if_pos h2]
            calc -((r : ℕ) : R) = -((((r : ℕ).factorial : ℕ) : R) * d (c : ℕ)) := by rw [hfac]
              _ = (((r : ℕ).factorial : ℕ) : R) * (d (c : ℕ) * -1) := by ring
          · rw [if_neg h2, if_neg h2]
            ring
      have hprod : (∏ r : Fin (n + 1), (((r : ℕ).factorial : ℕ) : R)) *
          (∏ c : Fin (n + 1), d (c : ℕ)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun r _ => hd (r : ℕ)
      have hdetB : (Matrix.of (fun r c : Fin (n + 1) =>
            d (c : ℕ) * bellMatrixQ x (n + 1) r c)).det
          = (∏ c : Fin (n + 1), d (c : ℕ)) * (bellMatrixQ x (n + 1)).det :=
        Matrix.det_mul_row (fun c : Fin (n + 1) => d (c : ℕ)) (bellMatrixQ x (n + 1))
      have hdetK : (bellMatrixK x d (n + 1)).det
          = (∏ r : Fin (n + 1), (((r : ℕ).factorial : ℕ) : R)) *
            (Matrix.of (fun r c : Fin (n + 1) =>
              d (c : ℕ) * bellMatrixQ x (n + 1) r c)).det := by
        rw [hK]
        exact Matrix.det_mul_column (fun r : Fin (n + 1) => (((r : ℕ).factorial : ℕ) : R))
          (Matrix.of (fun r c : Fin (n + 1) => d (c : ℕ) * bellMatrixQ x (n + 1) r c))
      rw [hdetK, hdetB, ← mul_assoc, hprod, one_mul, det_bellMatrixQ]

end CommRing

/-! ## Reciprocal factorials -/

section Reciprocals

/-- The reciprocal factorials `1/m!` of a commutative `ℚ`-algebra. -/
def invFactorial (R : Type*) [CommRing R] [Algebra ℚ R] (m : ℕ) : R :=
  algebraMap ℚ R (1 / (m.factorial : ℚ))

/-- `m!` and `Fabius.invFactorial` are reciprocal. -/
theorem factorial_mul_invFactorial (R : Type*) [CommRing R] [Algebra ℚ R] (m : ℕ) :
    ((m.factorial : ℕ) : R) * invFactorial R m = 1 := by
  unfold invFactorial
  rw [← map_natCast (algebraMap ℚ R) m.factorial, ← map_mul, mul_one_div,
    div_self (show ((m.factorial : ℕ) : ℚ) ≠ 0 by exact_mod_cast (Nat.factorial_pos m).ne'),
    map_one]

end Reciprocals

/-! ## The trace form of the determinant -/

section RatAlgebra

variable {F : Type*} [CommRing F] [Algebra ℚ F]

/-- **The second Bell determinant over a commutative `ℚ`-algebra** (`thm:bell-determinants`,
second equality, in the manuscript's own normalization `x_{j-i+1}/(j-i)!`). -/
theorem det_bellMatrixK_invFactorial (x : ℕ → F) (N : ℕ) :
    (bellMatrixK x (invFactorial F) N).det = Bell.complete x N :=
  det_bellMatrixK x (invFactorial F) (factorial_mul_invFactorial F) N

/-- The trace weights `w_r = -(r-1)!·tr(A^r)` of `cor:det-traces-bell`, with `w_0 = 0`. -/
def traceWeight {N : ℕ} (A : Matrix (Fin N) (Fin N) F) (r : ℕ) : F :=
  if r = 0 then 0 else -(((r - 1).factorial : ℕ) : F) * (A ^ r).trace

/-- **Determinant from traces** (`cor:det-traces-bell`, `eq:det-traces-bell`):
`det A = ((-1)^N/N!)·B_N(w_1,…,w_N)` with `w_k = -(k-1)!·tr(A^k)`.

The eigenvalue family of the manuscript's proof is supplied as the hypotheses `hdet` and `htr`;
the module header explains why Mathlib cannot currently discharge them for an arbitrary matrix
over an algebraically closed field.  Given them, the proof *is* the manuscript's: apply the
symmetric-function identity `Fabius.esymm_eq_neg_bell_complete` to the family, using that the
only subset of `Fin N` of cardinality `N` is the whole of it. -/
theorem det_eq_bell_complete_traceWeight {N : ℕ} (A : Matrix (Fin N) (Fin N) F) (u : Fin N → F)
    (hdet : A.det = ∏ i, u i) (htr : ∀ k : ℕ, 1 ≤ k → (A ^ k).trace = ∑ i, u i ^ k) :
    A.det = (-1 : F) ^ N * algebraMap ℚ F (1 / (N.factorial : ℚ)) *
      Bell.complete (traceWeight A) N := by
  have hps : Finset.powersetCard N (Finset.univ : Finset (Fin N)) = {Finset.univ} := by
    have h0 := Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rwa [Finset.card_fin] at h0
  have h := esymm_eq_neg_bell_complete F (Finset.univ : Finset (Fin N)) u N
  rw [hps, Finset.sum_singleton] at h
  have hw : (fun r => if r = 0 then 0 else -(((r - 1).factorial : ℕ) : F) *
      powerSum F (Finset.univ : Finset (Fin N)) u r) = traceWeight A := by
    funext r
    unfold traceWeight powerSum
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (show r ≠ 0 by omega), if_neg (show r ≠ 0 by omega),
        htr r (by omega)]
  rw [hdet, ← hw]
  exact h

end RatAlgebra

end Fabius
