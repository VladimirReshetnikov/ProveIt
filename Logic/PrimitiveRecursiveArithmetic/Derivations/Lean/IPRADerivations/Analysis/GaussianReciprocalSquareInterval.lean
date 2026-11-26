import IPRADerivations.Analysis.GaussianRationalFiniteSum
import IPRADerivations.Analysis.GaussianMonicResidualRadius

/-!
# Reciprocal-square bounds for exact Gaussian rational sums

The sum over `N < k ≤ N+r` of rows bounded by `C/k²` is bounded by
`C*r/(N*(N+r))`. Quantifier-free induction applies to the squared norm
of the actual finite sum. The telescope adds no rounding error.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianReciprocalSquareInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_sum bound_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (N r : PTm n) : PTm n := N*(N+r)

def rowsBounded (t : PTm 2) (N C x : PTm n) : Fm PTm n := .all
  (bounded (inst2 t (var 0) (Syn.shift x)) (Syn.shift C) (succ (Syn.shift N+var 0)*succ (Syn.shift N+var 0)))

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (N r : PTm n) :
    Syn.subst σ (denominator N r) = denominator (Syn.subst σ N) (Syn.subst σ r) := by simp [denominator]

@[simp] theorem subst_rowsBounded {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (N C x : PTm n) :
    (rowsBounded t N C x).subst σ =
      rowsBounded t (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ x) := by
  simp [rowsBounded,Syn.subst_shift,Syn.shift_subst]

theorem row_bound_at (t : PTm 2) (N C x i : PTm n) (h : Γ ⊢[PRAAx] rowsBounded t N C x) :
    Γ ⊢[PRAAx] bounded (inst2 t i x) C (succ (N+i)*succ (N+i)) := by
  simpa only [rowsBounded,GaussianRationalMetric.subst_bounded,subst_inst2,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

theorem denominator_positive (N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (denominator N r) :=
  positive_product _ _ hN (le_trans hN (le_add_right _ _))

private theorem interval_zero (t : PTm 2) (N C x : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] bounded (sum t zero x) (C*zero) (denominator N zero) :=
  bound_congr (GaussianRationalFiniteSum.sum_zero t x).eqSymm (mul_zero C).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero _ (denominator_positive N zero hN))

private theorem interval_step (t : PTm 2) (N r C x : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hrow : Γ ⊢[PRAAx] rowsBounded t N C x)
    (ih : Γ ⊢[PRAAx] bounded (sum t r x) (C*r) (denominator N r)) :
    Γ ⊢[PRAAx] bounded (sum t (succ r) x) (C*succ r) (denominator N (succ r)) := by
  let k := succ (N+r)
  let D := denominator N r
  let E := k*k
  let F := denominator N (succ r)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hD := denominator_positive N r hN
  have hE := positive_product k k hk hk
  have hF := denominator_positive N (succ r) hN
  have added := bounded_sum (sum t r x) (inst2 t r x) (C*r) D C E hD hE ih (row_bound_at t N C x r hrow)
  have budget : Γ ⊢[PRAAx] le ((C*r*E+C*D)*F) ((C*succ r)*(D*E)) := by
    apply le_of_eq_add (d := C*N*N*k)
    dsimp only [D,E,F,k,denominator]
    ipra_ring
  exact bound_congr (GaussianRationalFiniteSum.sum_succ t r x).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hE) hF budget added)

theorem interval_bound (t : PTm 2) (N r C x : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hrow : Γ ⊢[PRAAx] rowsBounded t N C x) :
    Γ ⊢[PRAAx] bounded (sum t r x) (C*r) (denominator N r) := by
  let sh (u : PTm n) := Syn.shift u
  have all : Γ ⊢[PRAAx] .all (bounded (sum t (var 0) (sh x)) (sh C*var 0) (denominator (sh N) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [GaussianRationalMetric.subst_bounded,GaussianRationalFiniteSum.subst_sum,subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using interval_zero t N C x hN
    · have hN' : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
      have hrow' : Γ.map Fm.shift ⊢[PRAAx] rowsBounded t (sh N) (sh C) (sh x) := by simpa [Fm.shift,Syn.shift,sh] using hrow.shift
      simpa only [GaussianRationalMetric.subst_bounded,GaussianRationalFiniteSum.subst_sum,subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
        interval_step t (sh N) (var 0) (sh C) (sh x) hN'.wk hrow'.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_bounded,GaussianRationalFiniteSum.subst_sum,subst_denominator,
    PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE r

theorem tail_bound (t : PTm 2) (N r C x : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hrow : Γ ⊢[PRAAx] rowsBounded t N C x) : Γ ⊢[PRAAx] bounded (sum t r x) C N :=
  bounded_radius_mono _ _ _ _ _ (denominator_positive N r hN) hN
    (le_of_eq_add (d := C*N*N) (by unfold denominator; ipra_ring)) (interval_bound t N r C x hN hrow)

end LeanProofs.IPRA.Analysis.GaussianReciprocalSquareInterval
