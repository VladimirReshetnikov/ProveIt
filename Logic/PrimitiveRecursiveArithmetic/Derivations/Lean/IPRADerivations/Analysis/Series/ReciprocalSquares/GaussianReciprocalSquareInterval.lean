import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.Monic.GaussianMonicResidualRadius

/-!
# Reciprocal-square bounds for exact Gaussian rational sums

The sum over `N < k ≤ N+r` of rows bounded by `C/k²` is bounded by
`C*r/(N*(N+r))`. Quantifier-free induction applies to the squared norm
of the actual finite sum. The same proof applies when every row denominator has an additional
positive common factor. The telescope adds no rounding error.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianReciprocalSquareInterval

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_sum bound_congr)

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

def scaledRowsBounded (t : PTm 2) (N C D x : PTm n) : Fm PTm n := .all
  (bounded (inst2 t (var 0) (Syn.shift x)) (Syn.shift C)
    (Syn.shift D*(succ (Syn.shift N+var 0)*succ (Syn.shift N+var 0))))

@[simp] theorem subst_scaledRowsBounded {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (N C D x : PTm n) :
    (scaledRowsBounded t N C D x).subst σ =
      scaledRowsBounded t (Syn.subst σ N) (Syn.subst σ C) (Syn.subst σ D) (Syn.subst σ x) := by
  simp [scaledRowsBounded,Syn.subst_shift,Syn.shift_subst]

theorem scaled_row_bound_at (t : PTm 2) (N C D x i : PTm n)
    (h : Γ ⊢[PRAAx] scaledRowsBounded t N C D x) :
    Γ ⊢[PRAAx] bounded (inst2 t i x) C (D*(succ (N+i)*succ (N+i))) := by
  simpa only [scaledRowsBounded,GaussianRationalMetric.subst_bounded,subst_inst2,PTm.subst_mul,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE i

private theorem interval_zero (t : PTm 2) (N C D x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] bounded (sum t zero x) (C*zero) (D*denominator N zero) :=
  bound_congr (GaussianRationalFiniteSum.sum_zero t x).eqSymm (mul_zero C).eqSymm (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero _ (positive_product _ _ hD (denominator_positive N zero hN)))

private theorem interval_step (t : PTm 2) (N r C D x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (hrow : Γ ⊢[PRAAx] scaledRowsBounded t N C D x)
    (ih : Γ ⊢[PRAAx] bounded (sum t r x) (C*r) (D*denominator N r)) :
    Γ ⊢[PRAAx] bounded (sum t (succ r) x) (C*succ r) (D*denominator N (succ r)) := by
  let k := succ (N+r)
  let A := D*denominator N r
  let E := D*(k*k)
  let F := D*denominator N (succ r)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hA := positive_product D (denominator N r) hD (denominator_positive N r hN)
  have hE := positive_product D (k*k) hD (positive_product k k hk hk)
  have hF := positive_product D (denominator N (succ r)) hD (denominator_positive N (succ r) hN)
  have added := bounded_sum (sum t r x) (inst2 t r x) (C*r) A C E hA hE ih
    (scaled_row_bound_at t N C D x r hrow)
  have budget : Γ ⊢[PRAAx] le ((C*r*E+C*A)*F) ((C*succ r)*(A*E)) := by
    apply le_of_eq_add (d := C*D*D*N*N*k)
    dsimp only [A,E,F,k,denominator]
    ipra_ring
  exact bound_congr (GaussianRationalFiniteSum.sum_succ t r x).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ hA hE) hF budget added)

theorem scaled_interval_bound (t : PTm 2) (N r C D x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (hrow : Γ ⊢[PRAAx] scaledRowsBounded t N C D x) :
    Γ ⊢[PRAAx] bounded (sum t r x) (C*r) (D*denominator N r) := by
  let sh (u : PTm n) := Syn.shift u
  have all : Γ ⊢[PRAAx] .all (bounded (sum t (var 0) (sh x)) (sh C*var 0)
      (sh D*denominator (sh N) (var 0))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [GaussianRationalMetric.subst_bounded,GaussianRationalFiniteSum.subst_sum,subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using interval_zero t N C D x hN hD
    · have hN' : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
      have hD' : Γ.map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,one] using hD.shift
      have hrow' : Γ.map Fm.shift ⊢[PRAAx] scaledRowsBounded t (sh N) (sh C) (sh D) (sh x) :=
        by simpa [Fm.shift,Syn.shift,sh] using hrow.shift
      simpa only [GaussianRationalMetric.subst_bounded,GaussianRationalFiniteSum.subst_sum,subst_denominator,
        PTm.subst_mul,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
        interval_step t (sh N) (var 0) (sh C) (sh D) (sh x) hN'.wk hD'.wk hrow'.wk Prf.hyp0
  simpa only [GaussianRationalMetric.subst_bounded,GaussianRationalFiniteSum.subst_sum,subst_denominator,
    PTm.subst_mul,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE r

theorem scaled_tail_bound (t : PTm 2) (N r C D x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hD : Γ ⊢[PRAAx] le one D)
    (hrow : Γ ⊢[PRAAx] scaledRowsBounded t N C D x) : Γ ⊢[PRAAx] bounded (sum t r x) C (D*N) :=
  bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD (denominator_positive N r hN))
    (positive_product _ _ hD hN) (le_of_eq_add (d := C*D*N*N) (by unfold denominator; ipra_ring))
    (scaled_interval_bound t N r C D x hN hD hrow)

private theorem rows_with_unit_scale (t : PTm 2) (N C x : PTm n)
    (h : Γ ⊢[PRAAx] rowsBounded t N C x) : Γ ⊢[PRAAx] scaledRowsBounded t N C one x := by
  refine .allI ?_
  simpa only [scaledRowsBounded,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul _).eqSymm h.allOpen

theorem interval_bound (t : PTm 2) (N r C x : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hrow : Γ ⊢[PRAAx] rowsBounded t N C x) :
    Γ ⊢[PRAAx] bounded (sum t r x) (C*r) (denominator N r) :=
  bound_congr (.eqRefl _) (.eqRefl _) (one_mul _)
    (scaled_interval_bound t N r C one x hN (le_refl one) (rows_with_unit_scale t N C x hrow))

theorem tail_bound (t : PTm 2) (N r C x : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hrow : Γ ⊢[PRAAx] rowsBounded t N C x) : Γ ⊢[PRAAx] bounded (sum t r x) C N :=
  bounded_radius_mono _ _ _ _ _ (denominator_positive N r hN) hN
    (le_of_eq_add (d := C*N*N) (by unfold denominator; ipra_ring)) (interval_bound t N r C x hN hrow)

end LeanProofs.IPRA.Analysis.GaussianReciprocalSquareInterval
