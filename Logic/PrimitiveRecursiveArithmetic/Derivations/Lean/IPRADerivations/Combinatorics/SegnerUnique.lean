import IPRADerivations.Foundations.TriangularUniqueness
import IPRADerivations.Combinatorics.CatalanConvolution

/-!
# Uniqueness of the solution of the Segner recurrence (`catalan_numbers_ipra`, `thm:segner`)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Theorem `thm:segner`: the Catalan
numbers are *the* sequence with `C_0 = 1` and `C_{n+1} = ∑_{i ≤ n} C_i C_{n−i}`.
`Combinatorics/CatalanConvolution` derives that `Cat` satisfies the recurrence; this module
derives the uniqueness.

* `conv a b m x = ∑_{i ≤ m} a_i b_{m ∸ i}`: the Cauchy convolution of two sequences given by
  terms (the summand is `cv` of `Foundations/HurwitzProduct`);
* `conv_congr`: `conv a b m` reads `a` and `b` only up to index `m`;
* `conv_cat`: `conv Cat Cat m = Cat_{m+1}` (Segner, restated for `conv`);
* `segner_unique`: if iPRA derives `y(0, x) = 1` and `y(n + 1, x) = ∑_{i ≤ n} y(i, x) y(n ∸ i, x)`
  for a term `y`, then it derives `y(n, x) = Cat_n` for every `n`.

The proof is `unique` of `Foundations/TriangularUniqueness`: the convolution is a triangular
recurrence, so the induction is on the quantifier-free bit of the bounded prefix.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.SegnerUnique

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Catalan (cat cat_zero)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (convB inst2_conv segner)
open LeanProofs.IPRA.Foundations.HurwitzProduct (cv cv_at)
open LeanProofs.IPRA.Foundations.TriangularUniqueness
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The Cauchy convolution -/

section Conv

variable (a b a' b' : PTm 2)

/-- `∑_{i ≤ m} a_i b_{m ∸ i}`. -/
abbrev conv (m x : PTm k) : PTm k := ap2 (sumF (cv a b)) (succ m) (pairT m x)

/-- The summands of two convolutions agree when the sequences agree up to `m`. -/
theorem conv_pt {j m x : PTm k} (ha : Γ ⊢[PRAAx] agree a a' (succ m) x)
    (hb : Γ ⊢[PRAAx] agree b b' (succ m) x) (hj : Γ ⊢[PRAAx] lt j (succ m)) :
    Γ ⊢[PRAAx] inst2 (cv a b) j (pairT m x) ≐ inst2 (cv a' b') j (pairT m x) := by
  have hl : Γ ⊢[PRAAx] lt (monus m j) (succ m) :=
    (succ_monus_succ (monus m j) m).eqTrans (monus_le' m j)
  refine (cv_at a b j m x).eqTrans (.eqTrans ?_ (cv_at a' b' j m x).eqSymm)
  exact congrMul (agree_elim a a' ha hj) (agree_elim b b' hb hl)

/-- The convolution reads its arguments only up to index `m`. -/
theorem conv_congr {m x : PTm k} (ha : Γ ⊢[PRAAx] agree a a' (succ m) x)
    (hb : Γ ⊢[PRAAx] agree b b' (succ m) x) : Γ ⊢[PRAAx] conv a b m x ≐ conv a' b' m x := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  have e : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
  have ha' := ha.shift
  rw [shift_agree, e] at ha'
  have hb' := hb.shift
  rw [shift_agree, e] at hb'
  have hj : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) (succ (Syn.shift m)) := by
    have h := Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift (succ m)))
    exact (congrArg (fun t => (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (var 0) t) e).mp h
  exact conv_pt a b a' b' ha'.wk hb'.wk hj

/-- The convolution as a term in `m` and `x`. -/
def convT : PTm 2 := conv a b (var 0) (var 1)

theorem inst2_convT (m x : PTm k) : inst2 (convT a b) m x = conv a b m x := by
  simp [inst2, convT]

end Conv

/-! ## The Catalan numbers -/

/-- The sequence `n ↦ Cat_n`. -/
def catB : PTm 2 := cat (var 0)

theorem inst2_catB (n x : PTm k) : inst2 catB n x = cat n := by simp [inst2, catB]

theorem cat_pt (j m x : PTm k) :
    Γ ⊢[PRAAx] inst2 (cv catB catB) j (pairT m x) ≐ inst2 convB j m := by
  have c := cv_at (Γ := Γ) catB catB j m x
  rw [inst2_catB, inst2_catB] at c
  rw [inst2_conv]
  exact c

/-- Segner's recurrence for `conv`: `∑_{i ≤ m} Cat_i Cat_{m ∸ i} = Cat_{m+1}`. -/
theorem conv_cat (m x : PTm k) : Γ ⊢[PRAAx] conv catB catB m x ≐ cat (succ m) := by
  refine .eqTrans ?_ (segner m)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  exact cat_pt _ _ _

/-- The Catalan numbers are the only solution of the Segner recurrence. -/
theorem segner_unique {y : PTm 2}
    (h₀ : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (x : PTm k), Γ ⊢[PRAAx] inst2 y zero x ≐ one)
    (hy : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (n x : PTm k),
      Γ ⊢[PRAAx] inst2 y (succ n) x ≐ conv y y n x)
    (n x : PTm k) : Γ ⊢[PRAAx] inst2 y n x ≐ cat n := by
  have u := unique (Γ := Γ) (y := y) (y' := catB) (F := convT y y) (F' := convT catB catB)
    { init := fun x => by rw [inst2_catB]; exact (h₀ x).eqTrans cat_zero.eqSymm
      step := fun n x => by rw [inst2_convT]; exact hy n x
      step' := fun n x => by rw [inst2_catB, inst2_convT]; exact (conv_cat n x).eqSymm
      tri := fun h => by rw [inst2_convT, inst2_convT]; exact conv_congr y y catB catB h h } n x
  rw [inst2_catB] at u
  exact u

end LeanProofs.IPRA.Combinatorics.SegnerUnique
