import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.BoundedSums

/-!
# The gcd of a vector

The gcd of the entries `f(0, x), …, f(N − 1, x)` of a vector body `f`, by the bounded recursion
`G(0) = 0`, `G(N + 1) = gcd(G(N), f(N))`. This is the operation `g = gcd(|v_0|, …, |v_n|)` of
`diophantine_geometry_ipra`, Lemma `lem:normalize`, and the primitivity test of `thm:northcott`.

* `rem_by_zero`, `zero_dvd`: `x mod 0 = x`, so `0 ∣ x` forces `x = 0`;
* `gcd_dvd_all`: `gcd(a, b)` divides `a` and `b` for all `a, b` (also when the gcd is `0`);
* `dvd_trans_all`: divisibility is transitive, zero divisors included;
* `gv_zero`, `gv_succ`: the recursion equations;
* `gv_dvd_prefix`: `G(M + D) ∣ G(M)`;
* `gv_dvd`: `G(N)` divides every entry `f(i)`, `i < N`;
* `gv_greatest`: a positive common divisor of the entries divides `G(N)`;
* `gv_eq_zero`: `G(N) = 0` forces every entry to vanish.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.GcdList

open_ipra exports

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Division by zero and divisibility with zero -/

/-- `x mod 0 = x`. -/
theorem rem_by_zero (z : PTm k) : Γ ⊢[PRAAx] rem z zero ≐ z := by
  have hall : Γ ⊢[PRAAx] Fm.all (rem (var 0 : PTm (k + 1)) zero ≐ var 0) := by
    ipra_qfind (trivial) [subst_ap2]
    · exact rem_zero _
    · have ih : ((rem (var 0 : PTm (k + 1)) zero ≐ var 0) :: Γ.map Fm.shift) ⊢[PRAAx] rem (var 0) zero ≐ var 0 :=
        Prf.hyp0
      have e0 : ((rem (var 0 : PTm (k + 1)) zero ≐ var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          eqb (succ (rem (var 0) zero)) zero ≐ zero :=
        eqb_zero_of_gt (zero_lt_succ _)
      exact (Prf.andE₂ (Division.div_mod_succ_no_carry (z := var 0) e0)).eqTrans (congrSucc ih)
  have h := Prf.allE z hall
  simpa only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero] using h

/-- `0 ∣ x` forces `x = 0`. -/
theorem zero_dvd {x : PTm k} (h : Γ ⊢[PRAAx] dvd zero x) : Γ ⊢[PRAAx] x ≐ zero :=
  (rem_by_zero x).eqSymm.eqTrans h

theorem dvd_zero_zero : Γ ⊢[PRAAx] dvd (zero : PTm k) zero := rem_zero _

theorem dvd_zero_any (d : PTm k) : Γ ⊢[PRAAx] dvd d zero := rem_zero _

/-- `gcd(a, b)` divides `a` and `b`, also when it is `0`. -/
theorem gcd_dvd_all (a b : PTm k) : Γ ⊢[PRAAx] dvd (gcd a b) a ⋏ dvd (gcd a b) b := by
  refine .orE (zero_or_succ (gcd a b)) ?_ (gcd_dvd_at Prf.hyp0)
  have hg : ((gcd a b ≐ zero) :: Γ) ⊢[PRAAx] gcd a b ≐ zero := Prf.hyp0
  have ha : ((gcd a b ≐ zero) :: Γ) ⊢[PRAAx] a ≐ zero := gcd_eq_zero hg
  have hb : ((gcd a b ≐ zero) :: Γ) ⊢[PRAAx] b ≐ zero := by
    refine .orE (zero_or_succ b) Prf.hyp0 ?_
    exact succ_ne_zero' _ ((gcd_pos_right Prf.hyp0).eqSymm.eqTrans hg.wk)
  exact .andI (dvd_congr_left hg.eqSymm (dvd_congr ha.eqSymm dvd_zero_zero))
    (dvd_congr_left hg.eqSymm (dvd_congr hb.eqSymm dvd_zero_zero))

/-- Divisibility is transitive, zero divisors included. -/
theorem dvd_trans_all {d e z : PTm k} (h₁ : Γ ⊢[PRAAx] dvd d e) (h₂ : Γ ⊢[PRAAx] dvd e z) : Γ ⊢[PRAAx] dvd d z := by
  refine .orE (zero_or_succ e) ?_ ?_
  · have he : ((e ≐ zero) :: Γ) ⊢[PRAAx] e ≐ zero := Prf.hyp0
    have hz := zero_dvd (dvd_congr_left he h₂.wk)
    exact dvd_congr hz.eqSymm (dvd_zero_any _)
  · have he : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp0
    refine .orE (zero_or_succ d) ?_ ?_
    · have hd : ((d ≐ zero) :: (e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
      have he0 := zero_dvd (dvd_congr_left hd h₁.wk.wk)
      exact succ_ne_zero' _ (he.wk.eqSymm.eqTrans he0)
    · exact dvd_trans' Prf.hyp0 he.wk h₁.wk.wk h₂.wk.wk

/-! ## The recursion -/

/-- The step `gcd(acc, f(y, x))`, over `0 = y`, `1 = acc`, `2 = x`. -/
def gvStep (f : PTm 2) : PTm 3 := gcd (var 1) (inst2 f (var 0) (var 2))
abbrev gvF (f : PTm 2) : PR 2 := rec2 zero (gvStep f)

/-- `G(N) = gcd(f(0, x), …, f(N − 1, x))`, with `G(0) = 0`. -/
abbrev gv (f : PTm 2) (N x : PTm k) : PTm k := ap2 (gvF f) N x

theorem gv_zero (f : PTm 2) (x : PTm k) : Γ ⊢[PRAAx] gv f zero x ≐ zero := by
  simpa using rec2_zero (Γ := Γ) zero (gvStep f) x

theorem gv_succ (f : PTm 2) (N x : PTm k) : Γ ⊢[PRAAx] gv f (succ N) x ≐ gcd (gv f N x) (inst2 f N x) := by
  have h := rec2_succ (Γ := Γ) zero (gvStep f) N x
  have e : Syn.subst ![N, ap2 (gvF f) N x, x] (gvStep f) = gcd (gv f N x) (inst2 f N x) := by
    simp only [gvStep, subst_ex2, subst_inst2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ]
  rw [e] at h; exact h

/-! ## Divisibility of the entries -/

theorem gv_step_dvd (f : PTm 2) (N x : PTm k) : Γ ⊢[PRAAx] dvd (gv f (succ N) x) (gv f N x) :=
  dvd_congr_left (gv_succ f N x).eqSymm (Prf.andE₁ (gcd_dvd_all _ _))

/-- `G(M + D) ∣ G(M)`. -/
theorem gv_dvd_prefix (f : PTm 2) (M D x : PTm k) : Γ ⊢[PRAAx] dvd (gv f (M + D) x) (gv f M x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (dvd (gv f (Syn.shift M + var 0) (Syn.shift x)) (gv f (Syn.shift M) (Syn.shift x))) := by
    ipra_qfind (trivial) [subst_ap2]
    · exact dvd_congr_left (congrAp2 _ (add_zero _) (.eqRefl _)).eqSymm
        (dvd_congr (.eqRefl _) (by
          refine .orE (zero_or_succ (gv f M x)) ?_ ?_
          · exact dvd_congr_left Prf.hyp0.eqSymm (dvd_congr Prf.hyp0.eqSymm dvd_zero_zero)
          · exact dvd_congr_left Prf.hyp0.eqSymm (dvd_congr Prf.hyp0.eqSymm (dvd_self _))))
    · have ih : ((dvd (gv f (Syn.shift M + var 0) (Syn.shift x)) (gv f (Syn.shift M) (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] dvd (gv f (Syn.shift M + var 0) (Syn.shift x)) (gv f (Syn.shift M) (Syn.shift x)) :=
        Prf.hyp0
      have st := gv_step_dvd (Γ := (dvd (gv f (Syn.shift M + var 0) (Syn.shift x)) (gv f (Syn.shift M) (Syn.shift x))) ::
          Γ.map Fm.shift) f (Syn.shift M + var 0) (Syn.shift x)
      have es : ((dvd (gv f (Syn.shift M + var 0) (Syn.shift x)) (gv f (Syn.shift M) (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] gv f (Syn.shift M + succ (var 0)) (Syn.shift x) ≐
            gv f (succ (Syn.shift M + var 0)) (Syn.shift x) := congrAp2 _ (by ipra_ring) (.eqRefl _)
      exact dvd_trans_all (dvd_congr_left es.eqSymm st) ih
  have h := Prf.allE D hall
  simpa only [Fm.subst_eq, subst_ap2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero] using h

/-- `G(N)` divides `f(i)` for `i < N`. -/
theorem gv_dvd (f : PTm 2) {i N x : PTm k} (h : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] dvd (gv f N x) (inst2 f i x) := by
  have eN : Γ ⊢[PRAAx] N ≐ succ i + monus N (succ i) := eq_add_of_le h
  have p := gv_dvd_prefix (Γ := Γ) f (succ i) (monus N (succ i)) x
  have s := dvd_congr_left (gv_succ f i x).eqSymm (Prf.andE₂ (gcd_dvd_all (Γ := Γ) (gv f i x) (inst2 f i x)))
  exact dvd_congr_left (congrAp2 _ eN (.eqRefl _)).eqSymm (dvd_trans_all p s)

/-- A positive common divisor of the entries divides `G(N)`. -/
theorem gv_greatest (f : PTm 2) {d' N x : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ dvd (succ (Syn.shift d')) (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] dvd (succ d') (gv f N x) := by
  let P : Fm PTm (k + 1) := dvd (succ (Syn.shift d')) (gv f (var 0) (Syn.shift x))
  have atEnd : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simpa [P] using dvd_congr (gv_zero (Γ := Γ) f x).eqSymm (dvd_zero d')
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have hf : Δ ⊢[PRAAx] dvd (succ (Syn.shift d')) (inst2 f (var 0) (Syn.shift x)) :=
        .impE h.allOpen.wk.wk Prf.hyp0
      exact dvd_congr (gv_succ f (var 0) (Syn.shift x)).eqSymm (gcd_greatest_at Prf.hyp1 hf)
  simpa [P] using atEnd

/-- `G(N) = 0` forces `f(i) = 0` for `i < N`. -/
theorem gv_eq_zero (f : PTm 2) {i N x : PTm k} (h0 : Γ ⊢[PRAAx] gv f N x ≐ zero) (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] inst2 f i x ≐ zero :=
  zero_dvd (dvd_congr_left h0 (gv_dvd f h))

end LeanProofs.IPRA.DiophantineNumberTheory.GcdList

export_ipra DiophantineNumberTheory.GcdList (gv_greatest gv_succ gv_zero rem_by_zero)
