import IPRADerivations.Foundations.LeastBoundedWitness
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.BoundedSums

/-!
# The finite rise alternative

Packet: `foundations/ipra_framework`, `paper/sections/05_metastability.tex`, Lemma `lem:rise`
("A finite rise alternative"): for a natural-valued sequence `r_0, …, r_n`, either
`∃ i < n. r_{i+1} ≤ r_i`, or `r_n ≥ r_0 + n`. In particular, if `r_{B+1} ≤ B`, there is an `i ≤ B` with
`r_{i+1} ≤ r_i`.

For a sequence body `r(i, x)`:

* `riseB r`: the body `r(i + 1, x) ∸ r(i, x)`, which vanishes exactly at a nonrise;
* `rise_alternative`: `(∃ i < N. r(i + 1) ∸ r(i) = 0) ∨ r(0) + N ≤ r(N)`. The case distinction is the
  bounded decision of `Foundations/LeastBoundedWitness`; in the second case every step below `N` is a strict
  rise and the bound follows by quantifier-free induction under that bounded hypothesis;
* `nonrise_of_bound`: `r(B + 1) ≤ B` gives `∃ i < B + 1. r(i + 1) ∸ r(i) = 0`.

The nonrise index is the least one, `mu (riseB r) N x`, by the search of `Core/Search`.
-/

namespace LeanProofs.IPRA.Foundations.RiseAlternative

open_ipra exports
open LeanProofs.IPRA.Foundations.LeastBoundedWitness (ExW NoW decision)

variable {n : ℕ} {Γ : List (Fm PTm n)} (r : PTm 2)

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `r(i + 1, x)`. -/
def nxB (r : PTm 2) : PTm 2 := Syn.subst ![succ (var 0), var 1] r

theorem inst2_nxB (i x : PTm n) : inst2 (nxB r) i x = inst2 r (succ i) x := by
  simp only [inst2, nxB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- `r(i + 1, x) ∸ r(i, x)`: zero exactly when `r(i + 1) ≤ r(i)`. -/
def riseB (r : PTm 2) : PTm 2 := monus (nxB r) r

theorem inst2_riseB (i x : PTm n) :
    inst2 (riseB r) i x = monus (inst2 (nxB r) i x) (inst2 r i x) := by
  simp [inst2, riseB]

/-- One strict rise. -/
theorem rise_step {k x : PTm n} (hne : Γ ⊢[PRAAx] neg (inst2 (riseB r) k x ≐ zero))
    (ih : Γ ⊢[PRAAx] le (inst2 r zero x + k) (inst2 r k x)) :
    Γ ⊢[PRAAx] le (inst2 r zero x + succ k) (inst2 r (succ k) x) := by
  rw [inst2_riseB, inst2_nxB] at hne
  refine .orE (lt_or_le (inst2 r k x) (inst2 r (succ k) x)) ?_ ?_
  · have h : (lt (inst2 r k x) (inst2 r (succ k) x) :: Γ) ⊢[PRAAx]
        le (succ (inst2 r k x)) (inst2 r (succ k) x) := Prf.hyp0
    have ih' := ih.wk (ψ := lt (inst2 r k x) (inst2 r (succ k) x))
    ipra_le sl ih' + sl h
  · exact .botE _ (Prf.impE hne.wk Prf.hyp0)

theorem rise_guard {k x N : PTm n} (hkN : Γ ⊢[PRAAx] le (succ k) N)
    (hne : Γ ⊢[PRAAx] neg (inst2 (riseB r) k x ≐ zero))
    (ih : Γ ⊢[PRAAx] le k N ⟶ le (inst2 r zero x + k) (inst2 r k x)) :
    Γ ⊢[PRAAx] le (inst2 r zero x + succ k) (inst2 r (succ k) x) :=
  rise_step r hne (Prf.impE ih (le_trans (le_succ_self k) hkN))

/-- If every step below `N` is a strict rise, then `r(0) + k ≤ r(k)` for `k ≤ N`. -/
theorem rise_all {N x : PTm n} (hno : Γ ⊢[PRAAx] NoW (riseB r) N x) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 r zero (Syn.shift x) + var 0) (inst2 r (var 0) (Syn.shift x))) := by
  refine qfIndAllUpTo N (le_QF _ _) ?_ ?_
  · ipra_ind_simp [subst_le, subst_inst2, Syn.subst_inst_shift]
    ipra_le 0
  · ipra_ind_simp [subst_le, subst_inst2, subst_repl_shift]
    exact .impI (rise_step r (.impE hno.allOpen.wk.wk Prf.hyp0) Prf.hyp1)

/-- `lem:rise`: a nonrise below `N`, or `r(0) + N ≤ r(N)`. -/
theorem rise_alternative (N x : PTm n) :
    Γ ⊢[PRAAx] ExW (riseB r) N x ⋎ le (inst2 r zero x + N) (inst2 r N x) := by
  refine .orE (decision (f := riseB r) N x) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  have a := Prf.allE N (rise_all r (Prf.hyp0 : (NoW (riseB r) N x :: Γ) ⊢[PRAAx] NoW (riseB r) N x))
  simp only [Fm.subst_imp, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] at a
  exact .impE a (le_refl N)

/-- `lem:rise`, second part: `r(B + 1) ≤ B` forces a nonrise at some `i ≤ B`. -/
theorem nonrise_of_bound {B x : PTm n} (h : Γ ⊢[PRAAx] le (inst2 r (succ B) x) B) :
    Γ ⊢[PRAAx] ExW (riseB r) (succ B) x := by
  refine .orE (rise_alternative (Γ := Γ) r (succ B) x) Prf.hyp0 ?_
  have h₁ : (le (inst2 r zero x + succ B) (inst2 r (succ B) x) :: Γ) ⊢[PRAAx]
      le (inst2 r zero x + succ B) (inst2 r (succ B) x) := Prf.hyp0
  have h' := h.wk (ψ := le (inst2 r zero x + succ B) (inst2 r (succ B) x))
  refine not_succ_le_self B _ ?_
  ipra_le sl h₁ + sl h' + 𝔟 (inst2 r zero x)

end LeanProofs.IPRA.Foundations.RiseAlternative
