import IPRADerivations.Probability.BayesEvents

/-!
# The finite union bound of the Borel–Cantelli certificate

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/conditioning.tex`, "A finite stopping theorem
and a Borel–Cantelli fragment": "The admitted tail union `B_k = ⋃_{j ≥ C(k)} A_j` has mass at most `2^{−k}`, by
finite union bounds and the explicit residual modulus. Every later `A_j` is included in `B_k` in the
event-algebra order."

For a finite list of event columns `A_j` (cell values, union by the maximum `larger`) on a finite weighted table:

* `mem_le_union`: every `A_j` of the list is below the union, cellwise;
* `union_le_sum`: cellwise, the union is at most the sum of the members;
* `wsum_add`, `wsum_sum`: weighted sums are additive;
* `union_bound`: `P(⋃_j A_j) ≤ ∑_j P(A_j)`, and with a tail-sum bound `∑_j P(A_j) ≤ ε` (the supplied residual
  modulus) `tail_union`: `P(B) ≤ ε`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.UnionBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.EventAlgebraMetric (wsum wsum_le)
open LeanProofs.IPRA.Probability.BayesEvents (wsum_zero)
open LeanProofs.IPRA.Analysis.Observation.PrefixObject (larger larger_le le_larger_left le_larger_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

variable {α : Type}

/-- The union of a list of event columns. -/
def unionL : List (α → PTm n) → α → PTm n
  | [] => fun _ => zero
  | f :: fs => fun r => larger (f r) (unionL fs r)

/-- The cellwise sum of a list of columns. -/
def sumL : List (α → PTm n) → α → PTm n
  | [] => fun _ => zero
  | f :: fs => fun r => f r + sumL fs r

/-- `∑_j P(A_j)`. -/
def sumW (w : α → PTm n) (L : List α) : List (α → PTm n) → PTm n
  | [] => zero
  | f :: fs => wsum w f L + sumW w L fs

theorem mem_le_union (fs : List (α → PTm n)) {f : α → PTm n} (hf : f ∈ fs) (r : α) :
    Γ ⊢[PRAAx] le (f r) (unionL fs r) := by
  induction fs with
  | nil => simp at hf
  | cons g gs ih =>
    show Γ ⊢[PRAAx] le (f r) (larger (g r) (unionL gs r))
    rcases List.mem_cons.mp hf with rfl | hm
    · exact le_larger_left _ _
    · exact le_trans (ih hm) (le_larger_right _ _)

theorem union_le_sum (fs : List (α → PTm n)) (r : α) : Γ ⊢[PRAAx] le (unionL fs r) (sumL fs r) := by
  induction fs with
  | nil => exact le_refl _
  | cons g gs ih =>
    show Γ ⊢[PRAAx] le (larger (g r) (unionL gs r)) (g r + sumL gs r)
    refine larger_le ?_ ?_
    · ipra_le 𝔟 (sumL gs r)
    · ipra_le 𝔟 (g r) + sl ih

theorem wsum_add (w f g : α → PTm n) (L : List α) :
    Γ ⊢[PRAAx] wsum w (fun r => f r + g r) L ≐ wsum w f L + wsum w g L := by
  induction L with
  | nil => show Γ ⊢[PRAAx] zero ≐ zero + zero; apply deriveNat; ipra_simps; ring
  | cons r rs ih =>
    show Γ ⊢[PRAAx] w r * (f r + g r) + wsum w (fun r => f r + g r) rs ≐
      (w r * f r + wsum w f rs) + (w r * g r + wsum w g rs)
    have e := natEq ih
    apply deriveNat; ipra_simps
    rw [e]; ring

theorem wsum_sum (w : α → PTm n) (L : List α) (fs : List (α → PTm n)) :
    Γ ⊢[PRAAx] wsum w (sumL fs) L ≐ sumW w L fs := by
  induction fs with
  | nil => exact wsum_zero w L
  | cons g gs ih =>
    show Γ ⊢[PRAAx] wsum w (fun r => g r + sumL gs r) L ≐ wsum w g L + sumW w L gs
    exact (wsum_add w g (sumL gs) L).eqTrans (congrAdd (.eqRefl _) ih)

/-- The finite union bound `P(⋃_j A_j) ≤ ∑_j P(A_j)`. -/
theorem union_bound (w : α → PTm n) (L : List α) (fs : List (α → PTm n)) :
    Γ ⊢[PRAAx] le (wsum w (unionL fs) L) (sumW w L fs) := by
  have h := wsum_le (Γ := Γ) w (unionL fs) (sumL fs) (fun _ => zero) L
    fun r _ => le_congr (.eqRefl _) (add_zero _).eqSymm (union_le_sum fs r)
  have e := natEq (wsum_sum (Γ := Γ) w L fs)
  have z := natEq (wsum_zero (Γ := Γ) w L)
  ipra_le sl h with e + z

/-- The Borel–Cantelli tail certificate: a tail-sum bound `∑_j P(A_j) ≤ ε` gives `P(⋃_j A_j) ≤ ε`. -/
theorem tail_union (w : α → PTm n) (L : List α) (fs : List (α → PTm n)) {ε : PTm n}
    (h : Γ ⊢[PRAAx] le (sumW w L fs) ε) : Γ ⊢[PRAAx] le (wsum w (unionL fs) L) ε :=
  le_trans (union_bound w L fs) h

end LeanProofs.IPRA.Probability.UnionBound
