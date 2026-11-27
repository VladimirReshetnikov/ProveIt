import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.Convergence.EulerCauchy
import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.Interpolation.EulerInterpolation

/-!
# The dyadic Euler polygons are Cauchy at every rational point

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Theorem
`thm:ode-produced-refinement`, `eq:ode-produced-cauchy`: "for `s ≥ r`,
`‖X_{2^r}(t) − X_{2^s}(t)‖ ≤ C (2^{−r} − 2^{−s}) ≤ C 2^{−r}`", for the interpolated polygons at every rational
`t = p/q ∈ [0,1]` (`Pn`, `Pd` of `EulerPolygons/EulerInterpolation`).

* `Pd_pos`: the denominator of the interpolation program is positive;
* `refine_at_point`: `eq:ode-produced-refine` at the point (`EulerInterpolation.euler_refinement_at`), for a mesh
  and a fine mesh given by terms provably equal to `n₀ + 1` and to its double;
* `euler_cauchy_at`: by quantifier-free induction on `k` with `EulerCauchy.tele_le`,
  `2^{r+k} |polyCross| + C Pd_r Pd_{r+k} ≤ C 2^k Pd_r Pd_{r+k}`, i.e.
  `‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C (2^{−r} − 2^{−(r+k)})`;
* `euler_cauchy_at_tail`: `2^{r+k} |polyCross| ≤ C 2^k Pd_r Pd_{r+k}`, i.e. `‖…‖ ≤ C 2^{−r}`;
  `euler_cauchy_at_norm`: the same for the maximum norm term `nrm` of the numerator vector.
-/

namespace LeanProofs.IPRA.Analysis.EulerPolygonCauchy

open_ipra
open LeanProofs.IPRA.Foundations.SignedNorms LeanProofs.IPRA.Foundations.SignedCone
  LeanProofs.IPRA.Analysis.EulerProgram LeanProofs.IPRA.Analysis.EulerNodeBound
  LeanProofs.IPRA.Analysis.EulerRefinement LeanProofs.IPRA.Analysis.EulerCauchy
  LeanProofs.IPRA.Analysis.EulerInterpolation
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The cell of a point of the interval is at most the mesh. -/
theorem cell_le (nn : PTm n) {p q' : PTm n} (hp : Γ ⊢[PRAAx] le p (succ q')) :
    Γ ⊢[PRAAx] le (quo (nn * p) (succ q')) nn := by
  have dm := div_mod (Γ := Γ) (nn * p) q'
  have w := natEq (Prf.andE₁ dm)
  have hq : Γ ⊢[PRAAx] le one (succ q') := succ_pos₀ q'
  refine Common.mul_cancel_le hq ?_
  ipra_le 𝔞 (rem (nn * p) (succ q')) + 𝔞 nn * sl hp with w

section Point

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x : PTm n}

/-- The denominator of the interpolation program is positive. -/
theorem Pd_pos {nn n₀ p q' : PTm n} (hm : Γ ⊢[PRAAx] nn ≐ succ n₀) (hK : Γ ⊢[PRAAx] KBound B x K)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hp : Γ ⊢[PRAAx] le p (succ q')) :
    Γ ⊢[PRAAx] lt zero (Pd B dv x nn p (succ q')) := by
  have hc := cell_le (Γ := Γ) nn hp
  have hnn : Γ ⊢[PRAAx] lt zero nn := le_congr (.eqRefl _) hm.eqSymm (succ_pos₀ n₀)
  obtain ⟨hb, -⟩ := kbound_use hK hnn hc
  exact mul_pos₀ (mul_pos₀ (mul_pos₀ hnn (succ_pos₀ q')) hb) (Xd_pos_at hm hK hdv hc)

/-- `eq:ode-produced-refine` at a rational point, for a mesh `nn = n₀ + 1` and the fine mesh `nn2 = 2 nn`
given up to provable equality. -/
theorem refine_at_point {nn n₀ nn2 p q' : PTm n} (hm : Γ ⊢[PRAAx] nn ≐ succ n₀)
    (hn2 : Γ ⊢[PRAAx] nn2 ≐ dbl nn) (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hp : Γ ⊢[PRAAx] le p (succ q')) (c : Fin d) :
    Bd (Nonneg Γ) (𝔞 nn2 * (ZT.toZ Γ (Pn B v x nn p (succ q') c) * 𝔞 (Pd B dv x nn2 p (succ q')) -
        ZT.toZ Γ (Pn B v x nn2 p (succ q') c) * 𝔞 (Pd B dv x nn p (succ q'))))
      (𝔞 (Cc K L U) * (𝔞 (Pd B dv x nn p (succ q')) * 𝔞 (Pd B dv x nn2 p (succ q')))) := by
  have hn2' : Γ ⊢[PRAAx] nn2 ≐ dbl (succ n₀) := hn2.eqTrans (congrDbl hm)
  have h := bd_of_le (euler_refinement_at (n₀ := n₀) hK hL hdv hv hp c)
  have cN1 := congr_Pn (Γ := Γ) B v x p (succ q') c hm
  have cN2 := congr_Pn (Γ := Γ) B v x p (succ q') c hn2'
  have cD1 := congr_Pd (Γ := Γ) B dv x p (succ q') hm
  have cD2 := congr_Pd (Γ := Γ) B dv x p (succ q') hn2'
  have cM := natEq hn2'
  refine h.congr ?_ ?_
  · rw [toZ_polyCross, cN1, cN2, cD1, cD2, cM]
  · simp only [Q.mk_mul, map_mul]
    rw [cD1, cD2]

end Point

/-! ## The telescoping -/

/-- The invariant: `2^{r+k} |polyCross| + C Pd_r Pd_{r+k} ≤ C 2^k Pd_r Pd_{r+k}`. -/
def PointInv (B : Kernel d) (v : Fin d → ZT n) (dv U K L x r p q k : PTm n) : Fm PTm n :=
  conjFin fun c =>
    le (pw two (r + k) * abs (polyCross B v dv x (pw two r) (pw two (r + k)) p q c) +
        Cc K L U * (Pd B dv x (pw two r) p q * Pd B dv x (pw two (r + k)) p q))
      (Cc K L U * pw two k * (Pd B dv x (pw two r) p q * Pd B dv x (pw two (r + k)) p q))

@[simp] theorem subst_PointInv {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n)
    (dv U K L x r p q k : PTm n) :
    (PointInv B v dv U K L x r p q k).subst σ =
      PointInv B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ U) (Syn.subst σ K) (Syn.subst σ L)
        (Syn.subst σ x) (Syn.subst σ r) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ k) := by
  simp only [PointInv, subst_le, subst_conjFin, subst_abs, subst_polyCross, subst_Cc, subst_Pd, PTm.subst_mul,
    PTm.subst_add, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem PointInv_QF (B : Kernel d) (v : Fin d → ZT n) (dv U K L x r p q k : PTm n) :
    (PointInv B v dv U K L x r p q k).QF :=
  conjFin_QF fun _ => le_QF _ _

section Step

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r p q' k : PTm n}

/-- The base of the telescoping. -/
theorem point_base (q : PTm n) (c : Fin d) :
    Γ ⊢[PRAAx] le (pw two (r + zero) * abs (polyCross B v dv x (pw two r) (pw two (r + zero)) p q c) +
        Cc K L U * (Pd B dv x (pw two r) p q * Pd B dv x (pw two (r + zero)) p q))
      (Cc K L U * pw two zero * (Pd B dv x (pw two r) p q * Pd B dv x (pw two (r + zero)) p q)) := by
  have em : Γ ⊢[PRAAx] pw two (r + zero) ≐ pw two r := congrAp2 powF (add_zero r) (.eqRefl two)
  have cN := congr_Pn (Γ := Γ) B v x p q c em
  have cD := congr_Pd (Γ := Γ) B dv x p q em
  have p0 := natEq (pw_zero (Γ := Γ) two)
  simp only [Q.mk_one, map_one] at p0
  refine le_abs_of_bd ((Bd.zero nn_zero).congr ?_ ?_)
  · rw [toZ_polyCross, cN, cD]; ring
  · simp only [Q.mk_mul, map_mul]
    rw [p0]; ring

/-- One level of the telescoping. -/
theorem point_step (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hp : Γ ⊢[PRAAx] le p (succ q'))
    (ih : ∀ c, Γ ⊢[PRAAx] le (pw two (r + k) *
        abs (polyCross B v dv x (pw two r) (pw two (r + k)) p (succ q') c) +
        Cc K L U * (Pd B dv x (pw two r) p (succ q') * Pd B dv x (pw two (r + k)) p (succ q')))
      (Cc K L U * pw two k * (Pd B dv x (pw two r) p (succ q') * Pd B dv x (pw two (r + k)) p (succ q'))))
    (c : Fin d) :
    Γ ⊢[PRAAx] le (pw two (r + succ k) *
        abs (polyCross B v dv x (pw two r) (pw two (r + succ k)) p (succ q') c) +
        Cc K L U * (Pd B dv x (pw two r) p (succ q') * Pd B dv x (pw two (r + succ k)) p (succ q')))
      (Cc K L U * pw two (succ k) *
        (Pd B dv x (pw two r) p (succ q') * Pd B dv x (pw two (r + succ k)) p (succ q'))) := by
  have hm : Γ ⊢[PRAAx] pw two (r + k) ≐ succ (pred (pw two (r + k))) := pw_pos' Common.two_pos (r + k)
  have hn2 : Γ ⊢[PRAAx] pw two (r + succ k) ≐ dbl (pw two (r + k)) := by
    have e1 : Γ ⊢[PRAAx] r + succ k ≐ succ (r + k) := by ipra_ring
    have e2 : Γ ⊢[PRAAx] pw two (r + k) * two ≐ pw two (r + k) + pw two (r + k) := by ipra_ring
    exact ((congrAp2 powF e1 (.eqRefl two)).eqTrans (pw_succ two (r + k))).eqTrans e2
  have R := refine_at_point hm hn2 hK hL hdv hv hp c
  have hpos : Γ ⊢[PRAAx] le one (pw two (r + k) * Pd B dv x (pw two (r + k)) p (succ q')) :=
    mul_pos₀ (le_congr (.eqRefl _) hm.eqSymm (succ_pos₀ _)) (Pd_pos hm hK hdv hp)
  have eN2 : (𝔞 (pw two (r + succ k)) : Groth (Q Γ)) = 2 * 𝔞 (pw two (r + k)) :=
    (natEq hn2).trans (mk_dbl _)
  exact tele_le (ih c) R eN2 (mk_pw_two_succ k) hpos

end Step

/-- `eq:ode-produced-cauchy` at every rational point `t = p/q ∈ [0,1]`, the sharp form
`‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C (2^{−r} − 2^{−(r+k)})`:
`2^{r+k} |polyCross| + C Pd_r Pd_{r+k} ≤ C 2^k Pd_r Pd_{r+k}`. -/
theorem euler_cauchy_at {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r p q' : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hp : Γ ⊢[PRAAx] le p (succ q')) (k : PTm n) :
    Γ ⊢[PRAAx] PointInv B v dv U K L x r p (succ q') k := by
  have hvs : ∀ l, Γ.map Fm.shift ⊢[PRAAx] le (abs (zshift (v l))) (Syn.shift U * Syn.shift dv) := fun l => by
    have h := (hv l).shift
    simp only [Fm.shift, subst_le, subst_abs, PTm.subst_mul] at h
    exact h
  have hdvs : Γ.map Fm.shift ⊢[PRAAx] lt zero (Syn.shift dv) := by
    have h := hdv.shift
    simp only [Fm.shift, subst_lt, ConciseIPRA.PTm.subst_zero] at h
    exact h
  have hps : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift p) (succ (Syn.shift q')) := by
    have h := hp.shift
    simp only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ] at h
    exact h
  have hall : Γ ⊢[PRAAx] Fm.all (PointInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K)
      (Syn.shift L) (Syn.shift x) (Syn.shift r) (Syn.shift p) (succ (Syn.shift q')) (var 0)) := by
    ipra_qfind (PointInv_QF _ _ _ _ _ _ _ _ _ _ _) [subst_PointInv, zshift_inst, zshift_repl]
    · exact conjFin_intro fun c => point_base _ c
    · have H0 : (PointInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K) (Syn.shift L)
          (Syn.shift x) (Syn.shift r) (Syn.shift p) (succ (Syn.shift q')) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          PointInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K) (Syn.shift L)
            (Syn.shift x) (Syn.shift r) (Syn.shift p) (succ (Syn.shift q')) (var 0) := Prf.hyp0
      exact conjFin_intro fun c =>
        point_step (kbound_shift hK).wk (lbound_shift hL).wk hdvs.wk (fun l => (hvs l).wk) hps.wk
          (conjFin_elim H0) c
  have h := Prf.allE k hall
  simp only [subst_PointInv, zshift_inst, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

/-- `eq:ode-produced-cauchy` at every rational point, the tail form `‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C 2^{−r}`:
`2^{r+k} |polyCross| ≤ C 2^k Pd_r Pd_{r+k}`. -/
theorem euler_cauchy_at_tail {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r p q' : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hp : Γ ⊢[PRAAx] le p (succ q')) (k : PTm n) (c : Fin d) :
    Γ ⊢[PRAAx] le (pw two (r + k) * abs (polyCross B v dv x (pw two r) (pw two (r + k)) p (succ q') c))
      (Cc K L U * pw two k * (Pd B dv x (pw two r) p (succ q') * Pd B dv x (pw two (r + k)) p (succ q'))) :=
  le_trans (le_add_right _ _) (conjFin_elim (euler_cauchy_at hK hL hdv hv hp k) c)

/-- `eq:ode-produced-cauchy` at every rational point, for the maximum norm of the numerator vector:
`2^{r+k} ‖polyCross‖ ≤ C 2^k Pd_r Pd_{r+k}`, i.e. `‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C 2^{−r}`. -/
theorem euler_cauchy_at_norm {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r p q' : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hp : Γ ⊢[PRAAx] le p (succ q')) (k : PTm n) :
    Γ ⊢[PRAAx] le (pw two (r + k) *
        nrm fun c => polyCross B v dv x (pw two r) (pw two (r + k)) p (succ q') c)
      (Cc K L U * pw two k * (Pd B dv x (pw two r) p (succ q') * Pd B dv x (pw two (r + k)) p (succ q'))) :=
  mul_nrm_le fun c => euler_cauchy_at_tail hK hL hdv hv hp k c

end LeanProofs.IPRA.Analysis.EulerPolygonCauchy
