import IPRADerivations.Foundations.TermSums
import IPRADerivations.Foundations.BoundedDecision
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The colour of `eq:color`: the number of leading ones of a bit vector

Packet: `topology/dimension_invariance_ipra`, `eq:color`: `λ(v) = i − 1` for the least `i` with
`b_i(v) = 0`, and `λ(v) = d` if all bits are `1`. As a term in `D` bit variables this is
`lamPat D = Σ_{k<D} Π_{g≤k} x_g`, the number of leading ones. For `0/1` bits (in the metatheory,
for every `D`):

* `lam_le`: `λ ≤ D`;
* `lam_le_of_zero`: `x_g = 0` gives `λ ≤ g` (the lower-face condition `eq:lower`);
* `lam_ne_of_one`: `x_g = 1` gives `λ ≠ g` (the upper-face condition `eq:upper`; also: the vertex
  of colour `g` has `x_g = 0`);
* `lam_top`: `λ = D` gives `x_g = 1` for every `g`.

`rangeId`, `lowId`, `upId`, `topId` are these facts as polynomial identities over `0/1`
valuations, and `range_at`, `low_at`, `up_at`, `top_at` their iPRA forms for bit terms provably
`≤ 1`, by `Foundations/BoundedDecision`.
-/

namespace LeanProofs.IPRA.Topology.LeadingBits

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Foundations.TermSums

set_option autoImplicit false

variable {n : ℕ}

/-! ## In the metatheory -/

section Values

variable {D : ℕ} (ρ : Fin D → ℕ)

/-- `Π_{g ≤ k} ρ_g`. -/
def pre (k : Fin D) : ℕ := ∏ g : Fin (k.val + 1), ρ ⟨g.val, Nat.lt_of_lt_of_le g.isLt k.isLt⟩

/-- The number of leading ones. -/
def lam : ℕ := ∑ k : Fin D, pre ρ k

variable {ρ} (h01 : ∀ g, ρ g ≤ 1)
include h01

theorem pre_le_one (k : Fin D) : pre ρ k ≤ 1 := by
  unfold pre
  exact Finset.prod_le_one (fun _ _ => Nat.zero_le _) (fun g _ => h01 _)

omit h01 in
theorem pre_eq_zero {g k : Fin D} (hgk : g.val ≤ k.val) (hg : ρ g = 0) : pre ρ k = 0 := by
  unfold pre
  refine Finset.prod_eq_zero (Finset.mem_univ (⟨g.val, by omega⟩ : Fin (k.val + 1))) ?_
  simpa using hg

omit h01 in
theorem pre_eq_one {k : Fin D} (h : ∀ g : Fin D, g.val ≤ k.val → ρ g = 1) : pre ρ k = 1 := by
  unfold pre
  exact Finset.prod_eq_one (fun g _ => h _ (by have := g.isLt; simp only; omega))

omit h01 in
theorem count_lt (g : ℕ) (hg : g ≤ D) : ∑ k : Fin D, (if k.val < g then 1 else 0) = g := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < g then 1 else 0) D, Finset.sum_boole]
  have : (Finset.range D).filter (· < g) = Finset.range g := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this]; simp

theorem lam_le : lam ρ ≤ D := by
  unfold lam
  calc ∑ k : Fin D, pre ρ k ≤ ∑ _k : Fin D, 1 := Finset.sum_le_sum (fun k _ => pre_le_one h01 k)
    _ = D := by simp

theorem lam_le_of_zero {g : Fin D} (hg : ρ g = 0) : lam ρ ≤ g.val := by
  unfold lam
  calc ∑ k : Fin D, pre ρ k ≤ ∑ k : Fin D, (if k.val < g.val then 1 else 0) :=
        Finset.sum_le_sum (fun k _ => by
          split_ifs with hk
          · exact pre_le_one h01 k
          · rw [pre_eq_zero (by omega) hg])
    _ = g.val := by
        exact count_lt g.val (Nat.le_of_lt g.isLt)

omit h01 in
theorem lam_ge_of_ones {g : Fin D} (h : ∀ g' : Fin D, g'.val ≤ g.val → ρ g' = 1) : g.val + 1 ≤ lam ρ := by
  unfold lam
  calc g.val + 1 = ∑ k : Fin D, (if k.val < g.val + 1 then 1 else 0) :=
        (count_lt (g.val + 1) g.isLt).symm
    _ ≤ ∑ k : Fin D, pre ρ k := Finset.sum_le_sum (fun k _ => by
        split_ifs with hk
        · rw [pre_eq_one (fun g' hg' => h g' (by omega))]
        · exact Nat.zero_le _)

theorem lam_ne_of_one {g : Fin D} (hg : ρ g = 1) : lam ρ ≠ g.val := by
  by_cases hall : ∀ g' : Fin D, g'.val ≤ g.val → ρ g' = 1
  · have := lam_ge_of_ones hall; omega
  · simp only [not_forall] at hall
    obtain ⟨g', hg'g, hg'⟩ := hall
    have h0 : ρ g' = 0 := by have := h01 g'; omega
    have hne : g'.val ≠ g.val := fun e => hg' (by rw [Fin.ext e]; exact hg)
    have := lam_le_of_zero h01 h0; omega

theorem lam_top (h : lam ρ = D) (g : Fin D) : ρ g = 1 := by
  by_contra hg
  have h0 : ρ g = 0 := by have := h01 g; omega
  have := lam_le_of_zero h01 h0
  have := g.isLt
  omega

end Values

/-! ## The pattern -/

variable (D : ℕ)

/-- `λ = Σ_{k<D} Π_{g≤k} x_g` in the bit variables. -/
def lamPat : PTm D :=
  fsum D (fun k => fprod (k.val + 1) (fun g => Syn.var ⟨g.val, Nat.lt_of_lt_of_le g.isLt k.isLt⟩))

theorem ev_lamPat (ρ : Fin D → ℕ) : PTm.ev ρ (lamPat D) = lam ρ := by
  simp [lamPat, lam, pre]

variable {D}

section Transfer

variable {Γ : List (Fm PTm n)} (x : Fin D → PTm n) (hx : ∀ g, Γ ⊢[PRAAx] le (x g) one)
include hx

private theorem decide1 (s t : PTm D) (h : ∀ ρ : Fin D → ℕ, (∀ g, ρ g ≤ 1) → PTm.ev ρ s = PTm.ev ρ t) :
    Γ ⊢[PRAAx] Syn.subst x s ≐ Syn.subst x t :=
  Foundations.BoundedDecision.bounded_decide 1 s t h x hx

/-- `λ ≤ D`. -/
theorem range_at : Γ ⊢[PRAAx] le (Syn.subst x (lamPat D)) (num D) := by
  have e := decide1 x hx (monus (lamPat D) (num D)) zero (fun ρ hρ => by
    simp only [ev_monus, ev_lamPat, ev_num, ev_zero]; have := lam_le hρ; omega)
  simpa [le] using e

/-- `x_g = 0` gives `λ ≤ g`. -/
theorem low_at (g : Fin D) (hg : Γ ⊢[PRAAx] x g ≐ zero) :
    Γ ⊢[PRAAx] le (Syn.subst x (lamPat D)) (num g.val) := by
  have e := decide1 x hx (monus (lamPat D) (num g.val)) (monus (lamPat D) (num g.val) * Syn.var g)
    (fun ρ hρ => by
      simp only [ev_monus, ev_mul, ev_lamPat, ev_num, ev_var]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hρ g) with h | h
      · simp [h, Nat.sub_eq_zero_of_le (lam_le_of_zero hρ h)]
      · rw [h]; simp)
  simp only [PTm.subst_monus, PTm.subst_mul, PTm.subst_num, Syn.subst_var] at e
  exact e.eqTrans ((congrMul (.eqRefl _) hg).eqTrans (mul_zero _))

/-- `x_g = 1` gives `[λ = g] = 0`. -/
theorem up_at (g : Fin D) (hg : Γ ⊢[PRAAx] x g ≐ one) :
    Γ ⊢[PRAAx] eqb (Syn.subst x (lamPat D)) (num g.val) ≐ zero := by
  have e := decide1 x hx (eqb (lamPat D) (num g.val) * Syn.var g) zero
    (fun ρ hρ => by
      simp only [ev_eqb, ev_mul, ev_lamPat, ev_num, ev_var, ev_zero]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hρ g) with h | h
      · rw [h]; simp
      · rw [if_neg (lam_ne_of_one hρ h)]; simp)
  simp only [PTm.subst_mul, subst_eqb, PTm.subst_num, Syn.subst_var, ConciseIPRA.PTm.subst_zero] at e
  have e₁ := natEq e
  apply deriveNat
  ipra_simps
  rw [natEq hg] at e₁
  simpa using e₁

/-- `[λ = g] · x_g = 0`: the vertex of colour `g < D` has `x_g = 0`. -/
theorem colour_bit (g : Fin D) :
    Γ ⊢[PRAAx] eqb (Syn.subst x (lamPat D)) (num g.val) * x g ≐ zero := by
  have e := decide1 x hx (eqb (lamPat D) (num g.val) * Syn.var g) zero
    (fun ρ hρ => by
      simp only [ev_eqb, ev_mul, ev_lamPat, ev_num, ev_var, ev_zero]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hρ g) with h | h
      · rw [h]; simp
      · rw [if_neg (lam_ne_of_one hρ h)]; simp)
  simpa using e

/-- `[λ = D] · (1 ∸ x_g) = 0`: the vertex of colour `D` has every bit `1`. -/
theorem top_bit (g : Fin D) :
    Γ ⊢[PRAAx] eqb (Syn.subst x (lamPat D)) (num D) * monus one (x g) ≐ zero := by
  have e := decide1 x hx (eqb (lamPat D) (num D) * monus one (Syn.var g)) zero
    (fun ρ hρ => by
      simp only [ev_eqb, ev_mul, ev_monus, ev_lamPat, ev_num, ev_var, ev_zero, ev_succ]
      by_cases hl : lam ρ = D
      · rw [lam_top hρ hl g]; simp
      · rw [if_neg hl]; simp)
  simpa using e

end Transfer

end LeanProofs.IPRA.Topology.LeadingBits
