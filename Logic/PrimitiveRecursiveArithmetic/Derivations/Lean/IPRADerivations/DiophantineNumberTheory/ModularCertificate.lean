import IPRADerivations.DiophantineNumberTheory.GcdUnique
import IPRADerivations.Combinatorics.LegendreDigits

/-!
# Modular certificates of no rational point

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:modular` ("A checkable certificate of
no rational point"): "A rational point has a primitive integral representative `x`. Reduce every coordinate to
`x̄_i` in `[0, m − 1]`. Any common divisor of `m` and all `x̄_i` divides every `x_i`, so it is one; hence the
residue vector is unimodular. Polynomial evaluation respects congruence: each product does, by induction on its
number of factors, and a finite sum does as well."

For natural vectors (bodies `V(i, x)`):

* `unimodular`: if `gcd(V) = 1` then every positive common divisor of `m` and the residues `V_i mod m` is `1`;
* `rem_add_mul`, `rem_add_congr`, `rem_mul_congr2`: congruence mod `m` respects `+` and `×`;
* `sum_congr_mod`, `prod_congr_mod`: finite sums and products of pointwise-congruent bodies are congruent, by
  induction on the number of terms or factors.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv gv_greatest)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdUnique (sh shift_succ' shift_pred')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- A positive common divisor of `m` and all residues `V_i mod m` of a primitive vector is `1`. -/
theorem unimodular {V : PTm 2} {N x m d : PTm k} (hg : Γ ⊢[PRAAx] gv V N x ≐ one)
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hdm : Γ ⊢[PRAAx] dvd d m)
    (hdr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (Syn.shift d) (rem (inst2 V (var 0) (Syn.shift x)) (Syn.shift m)))) : Γ ⊢[PRAAx] d ≐ one := by
  have all : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (succ (Syn.shift (pred d))) (inst2 V (var 0) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    rw [shift_pred']
    have hds : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
      have e := sh hd; rw [shift_succ', shift_pred'] at e; exact e.wk
    have hms : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift m ≐ succ (pred (Syn.shift m)) := by
      have e := sh hm; rw [shift_succ', shift_pred'] at e; exact e.wk
    have hdms : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] dvd (Syn.shift d) (Syn.shift m) := by
      have e := hdm.shift; simpa [Fm.shift, Syn.shift] using e.wk
    have dv := Prf.andE₁ (dm hms (inst2 V (var 0) (Syn.shift x)))
    have d1 := dvd_add' hds (dvd_mul' hds (quo (inst2 V (var 0) (Syn.shift x)) (Syn.shift m)) hdms)
      (Prf.impE hdr.allOpen.wk Prf.hyp0)
    exact dvd_congr_left hds (dvd_congr dv.eqSymm d1)
  have g := gv_greatest V all
  exact eq_one_of_dvd_one hd (dvd_congr_left hd.eqSymm (dvd_congr hg g))

/-! ## Congruences -/

/-- `(M q + z) mod M = z mod M`. -/
theorem rem_add_mul {M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (q z : PTm k) :
    Γ ⊢[PRAAx] rem (M * q + z) M ≐ rem z M := by
  have d := dm hM z
  have e := natEq (Prf.andE₁ d)
  exact Prf.andE₂ (dmu hM (q := q + quo z M) (r := rem z M) (by apply deriveNat; ipra_simps; linear_combination e)
    (Prf.andE₂ d))

/-- Replace both summands by their remainders before taking the remainder of their sum. -/
private theorem rem_add_reduce {M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (x y : PTm k) :
    Γ ⊢[PRAAx] rem (x + y) M ≐ rem (rem x M + rem y M) M := by
  refine (congrAp2 remF ?_ (.eqRefl _)).eqTrans (rem_add_mul hM (quo x M + quo y M) _)
  ipra_lc natEq (Prf.andE₁ (dm hM x)) + natEq (Prf.andE₁ (dm hM y))

theorem rem_add_congr {M x y x' y' : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h1 : Γ ⊢[PRAAx] rem x M ≐ rem y M) (h2 : Γ ⊢[PRAAx] rem x' M ≐ rem y' M) :
    Γ ⊢[PRAAx] rem (x + x') M ≐ rem (y + y') M := by
  exact (rem_add_reduce hM x x').eqTrans
    ((congrAp2 remF (congrAdd h1 h2) (.eqRefl _)).eqTrans (rem_add_reduce hM y y').eqSymm)

theorem rem_mul_congr2 {M x y x' y' : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h1 : Γ ⊢[PRAAx] rem x M ≐ rem y M) (h2 : Γ ⊢[PRAAx] rem x' M ≐ rem y' M) :
    Γ ⊢[PRAAx] rem (x * x') M ≐ rem (y * y') M :=
  Foundations.ChineseRemainder.rem_mul_congr_both hM h1 h2

theorem shift_pos {M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) :
    Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
  have e := sh hM; rw [shift_succ', shift_pred'] at e; exact e

/-- Finite sums of pointwise-congruent bodies are congruent. -/
theorem sum_congr_mod (f g : PTm 2) {N x y M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 g (var 0) (Syn.shift y)) (Syn.shift M))) :
    Γ ⊢[PRAAx] rem (ap2 (sumF f) N x) M ≐ rem (ap2 (sumF g) N y) M :=
  Foundations.ChineseRemainder.fold_congr_mod sumF (· + ·) f g hM h ((sum_zero f x).eqTrans (sum_zero g y).eqSymm)
    (fun body i z => sum_succ body i z) (fun positive hPrefix hEntry => rem_add_congr positive hPrefix hEntry)

/-- Finite products of pointwise-congruent bodies are congruent. -/
theorem prod_congr_mod (f g : PTm 2) {N x y M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 g (var 0) (Syn.shift y)) (Syn.shift M))) :
    Γ ⊢[PRAAx] rem (ap2 (prodF f) N x) M ≐ rem (ap2 (prodF g) N y) M :=
  Foundations.ChineseRemainder.rem_prod_congr f g hM h

end LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate

export_ipra DiophantineNumberTheory.ModularCertificate (prod_congr_mod rem_add_congr rem_add_mul rem_mul_congr2)
