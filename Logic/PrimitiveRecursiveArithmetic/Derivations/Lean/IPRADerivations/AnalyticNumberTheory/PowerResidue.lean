import IPRADerivations.AnalyticNumberTheory.PowerDivisorUniform

/-!
# Residues along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`, progression rows)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "For residues, a summand `d^h m ≡ b (mod q)` with reduced `b` forces `(d,q) = 1`. For such `d`, find
the unique representative `b_d` with `d^h b_d ≡ b (mod q)` … Multiplication by `d^h` is a permutation, and `b_d` is again
reduced."

For a modulus `q ≥ 2` and a unit `D` (`gcd(D, q) = 1`):

* `inv` is the Bezout inverse of `D` modulo `q`, chosen by the indicator of the first Bezout identity (the two
  identities cannot hold together), and `inv_spec`: `D · inv ≡ 1`;
* `res D b = (inv · b) mod q` (`b_d` for `D = d^h`), `res_spec`: `D · b_d ≡ b`, `res_unique`: `D x ≡ b`, `x < q` give
  `x = b_d`, `res_cop`: `b_d` is reduced;
* `cop_pw`: `gcd(d, q) = 1` gives `gcd(d^h, q) = 1`, and `cop_of_sol`: `D m ≡ b` with `b` reduced forces `gcd(D, q) = 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (N_pos cop_mul cop_of_mul cop_rem cop_of_rem rem_rem rem_small rem_lt
  rem_mul_rem rem_decomp shift_le_two)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The inverse -/

/-- The two Bezout coefficients of `(D, q)`. -/
abbrev bS (D q : PTm n) : PTm n := Bezout.cur one zero (succ q) D q
abbrev bT (D q : PTm n) : PTm n := Bezout.cur zero one (succ q) D q
/-- Which Bezout identity holds. -/
abbrev bC (D q : PTm n) : PTm n := eqb (gcd D q + bT D q * q) (bS D q * D)

/-- The inverse of `D` modulo `q`. -/
abbrev inv (D q : PTm n) : PTm n := bC D q * bS D q + monus one (bC D q) * (pred q * bS D q)

theorem inv_spec {D q : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one) :
    Γ ⊢[PRAAx] rem (D * inv D q) q ≐ rem one q := by
  have hp := N_pos hq
  refine .orE (bezout_at D q) ?_ ?_
  · let C : List (Fm PTm n) := (gcd D q + bT D q * q ≐ bS D q * D) :: Γ
    have h1 : C ⊢[PRAAx] gcd D q + bT D q * q ≐ bS D q * D := Prf.hyp0
    have c1 : C ⊢[PRAAx] bC D q ≐ one := eqb_of_eq h1
    have ei : C ⊢[PRAAx] inv D q ≐ bS D q :=
      (congrAdd ((congrMul c1 (.eqRefl _)).eqTrans (one_mul _))
        ((congrMul ((congrMonus (.eqRefl _) c1).eqTrans (monus_self _)) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
        (add_zero _)
    refine (congrAp2 remF (congrMul (.eqRefl _) ei) (.eqRefl _)).eqTrans ?_
    refine rem_eq_of_eq hp.wk (k₁ := zero) (k₂ := bT D q) ?_
    refine withEq h1 fun e₁ => withEq hD.wk fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₂] at e₁; linear_combination -e₁
  · let C : List (Fm PTm n) := (gcd D q + bS D q * D ≐ bT D q * q) :: Γ
    have h2 : C ⊢[PRAAx] gcd D q + bS D q * D ≐ bT D q * q := Prf.hyp0
    have c0 : C ⊢[PRAAx] bC D q ≐ zero := by
      refine eqb_of_ne (.impI ?_)
      have a := (Prf.hyp0 : ((gcd D q + bT D q * q ≐ bS D q * D) :: C) ⊢[PRAAx] _)
      have f1 := natEq a
      have f2 := natEq (h2.wk : ((gcd D q + bT D q * q ≐ bS D q * D) :: C) ⊢[PRAAx] _)
      have f3 := natEq (hD.wk.wk : ((gcd D q + bT D q * q ≐ bS D q * D) :: C) ⊢[PRAAx] _)
      have z : ((gcd D q + bT D q * q ≐ bS D q * D) :: C) ⊢[PRAAx] two ≐ zero := by
        apply deriveNat; ipra_simps; rw [f3] at f1 f2; linear_combination f1 + f2
      exact succ_ne_zero' _ z
    have ei : C ⊢[PRAAx] inv D q ≐ pred q * bS D q :=
      (congrAdd ((congrMul c0 (.eqRefl _)).eqTrans (zero_mul _))
        ((congrMul ((congrMonus (.eqRefl _) c0).eqTrans (monus_zero _)) (.eqRefl _)).eqTrans (one_mul _))).eqTrans
        (zero_add _)
    refine (congrAp2 remF (congrMul (.eqRefl _) ei) (.eqRefl _)).eqTrans ?_
    refine rem_eq_of_eq hp.wk (k₁ := one) (k₂ := pred q * bT D q) ?_
    refine withEq h2 fun e₁ => withEq hD.wk fun e₂ => withEq hp.wk fun e₃ => ?_
    apply deriveNat; ipra_simps; rw [e₂] at e₁
    linear_combination Groth.ι (Q.mk _ (pred q)) * e₁ + e₃

/-! ## The representative `b_d` -/

/-- `b_D = (inv · b) mod q`. -/
abbrev res (D q b : PTm n) : PTm n := rem (inv D q * b) q

theorem mul_inv_rem {D q : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one) (x : PTm n) :
    Γ ⊢[PRAAx] rem (D * inv D q * x) q ≐ rem x q := by
  have i := inv_spec hq hD
  have c := rem_mul_congr x (N_pos hq) i
  exact c.eqTrans (congrAp2 remF (one_mul _) (.eqRefl _))

/-- `D b_D ≡ b`. -/
theorem res_spec {D q b : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one) :
    Γ ⊢[PRAAx] rem (D * res D q b) q ≐ rem b q := by
  refine (rem_mul_rem hq D (inv D q * b)).eqTrans ?_
  exact (congrAp2 remF (mul_assoc _ _ _).eqSymm (.eqRefl _)).eqTrans (mul_inv_rem hq hD b)

/-- `D x ≡ b` and `x < q` give `x = b_D`. -/
theorem res_unique {D q b x : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one)
    (hx : Γ ⊢[PRAAx] lt x q) (h : Γ ⊢[PRAAx] rem (D * x) q ≐ rem b q) : Γ ⊢[PRAAx] x ≐ res D q b := by
  have a : Γ ⊢[PRAAx] rem (inv D q * (D * x)) q ≐ rem (inv D q * b) q :=
    (rem_mul_rem hq (inv D q) (D * x)).eqSymm.eqTrans ((congrAp2 remF (congrMul (.eqRefl _) h) (.eqRefl _)).eqTrans
      (rem_mul_rem hq (inv D q) b))
  have b' : Γ ⊢[PRAAx] rem (inv D q * (D * x)) q ≐ rem x q :=
    (congrAp2 remF (by ipra_ring : Γ ⊢[PRAAx] inv D q * (D * x) ≐ D * inv D q * x)
      (.eqRefl _)).eqTrans (mul_inv_rem hq hD x)
  exact (rem_small hq hx).eqSymm.eqTrans (b'.eqSymm.eqTrans a)

theorem res_lt {D q b : PTm n} (hq : Γ ⊢[PRAAx] le two q) : Γ ⊢[PRAAx] lt (res D q b) q := rem_lt hq _

/-! ## Coprimality bookkeeping -/

theorem gcd_one_left (q : PTm n) : Γ ⊢[PRAAx] gcd one q ≐ one := by
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  exact eq_one_of_dvd_one (gcd_pos h1) (Prf.andE₁ (gcd_dvd' (b := q) h1))

/-- The inverse is a unit. -/
theorem inv_cop {D q : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one) :
    Γ ⊢[PRAAx] gcd (inv D q) q ≐ one := by
  have r1 : Γ ⊢[PRAAx] rem one q ≐ one := rem_small hq (hq : Γ ⊢[PRAAx] lt one q)
  have g1 : Γ ⊢[PRAAx] gcd (rem (D * inv D q) q) q ≐ one :=
    (congrGcd ((inv_spec hq hD).eqTrans r1) (.eqRefl _)).eqTrans (gcd_one_left q)
  exact cop_of_mul hq (cop_of_rem hq g1)

/-- `b_D` is reduced. -/
theorem res_cop {D q b : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one)
    (hb : Γ ⊢[PRAAx] gcd b q ≐ one) : Γ ⊢[PRAAx] gcd (res D q b) q ≐ one :=
  cop_rem hq (cop_mul hq (inv_cop hq hD) hb)

/-- `gcd(d, q) = 1` gives `gcd(d^h, q) = 1`. -/
theorem cop_pw {d q : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hd : Γ ⊢[PRAAx] gcd d q ≐ one) (h : PTm n) :
    Γ ⊢[PRAAx] gcd (pw d h) q ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (gcd (pw (Syn.shift d) (var 0)) (Syn.shift q) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_ex2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact (congrGcd (pw_zero _) (.eqRefl _)).eqTrans (gcd_one_left q)
    · simp only [Fm.subst_eq, subst_ap2, subst_ex2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have hq' := (shift_le_two hq).wk (ψ := gcd (pw (Syn.shift d) (var 0)) (Syn.shift q) ≐ one)
      have hd' := (Gcd.shift_coprime hd).wk (ψ := gcd (pw (Syn.shift d) (var 0)) (Syn.shift q) ≐ one)
      exact (congrGcd (pw_succ _ _) (.eqRefl _)).eqTrans (cop_mul hq' Prf.hyp0 hd')
  have e := Prf.allE h hall
  simp only [Fm.subst_eq, subst_ap2, subst_ex2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact e

/-- A solution of `D m ≡ b` with reduced `b` forces `gcd(D, q) = 1`. -/
theorem cop_of_sol {D q b m : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] gcd b q ≐ one)
    (h : Γ ⊢[PRAAx] rem (D * m) q ≐ rem b q) : Γ ⊢[PRAAx] gcd D q ≐ one := by
  have g1 : Γ ⊢[PRAAx] gcd (rem (D * m) q) q ≐ one := (congrGcd h (.eqRefl _)).eqTrans (cop_rem hq hb)
  exact cop_of_mul hq ((congrGcd (mul_comm _ _) (.eqRefl _)).eqTrans (cop_of_rem hq g1))

/-! ## Transport and composition -/

/-- `(b_D)_E = b_{DE}`. -/
theorem res_comp {D E q b : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hD : Γ ⊢[PRAAx] gcd D q ≐ one)
    (hE : Γ ⊢[PRAAx] gcd E q ≐ one) : Γ ⊢[PRAAx] res E q (res D q b) ≐ res (D * E) q b := by
  have s1 : Γ ⊢[PRAAx] rem (E * res E q (res D q b)) q ≐ res D q b :=
    (res_spec hq hE).eqTrans (rem_rem hq _)
  have ch : Γ ⊢[PRAAx] rem (D * E * res E q (res D q b)) q ≐ rem b q := by
    refine (congrAp2 remF (by ipra_ring :
      Γ ⊢[PRAAx] D * E * res E q (res D q b) ≐ D * (E * res E q (res D q b))) (.eqRefl _)).eqTrans ?_
    refine (rem_mul_rem hq D _).eqSymm.eqTrans ?_
    exact (congrAp2 remF (congrMul (.eqRefl _) s1) (.eqRefl _)).eqTrans (res_spec hq hD)
  exact res_unique hq (cop_mul hq hD hE) (res_lt hq) ch

/-- The indicator transport: for reduced `b` and `D m ≡ b`-tests, `[D m ≡ b] = [gcd(D,q) = 1]·[m ≡ b_D]`. -/
theorem ind_transport {D q b m : PTm n} (hq : Γ ⊢[PRAAx] le two q) (hb : Γ ⊢[PRAAx] gcd b q ≐ one) :
    Γ ⊢[PRAAx] eqb (rem (D * m) q) (rem b q) ≐ eqb (gcd D q) one * eqb (rem m q) (res D q b) := by
  refine .orE (eq_or_ne (gcd D q) one) ?_ ?_
  · let C : List (Fm PTm n) := (gcd D q ≐ one) :: Γ
    have hD : C ⊢[PRAAx] gcd D q ≐ one := Prf.hyp0
    have hq' : C ⊢[PRAAx] le two q := hq.wk
    refine .orE (eq_or_ne (rem m q) (res D q b)) ?_ ?_
    · let C' : List (Fm PTm n) := (rem m q ≐ res D q b) :: C
      have a : C' ⊢[PRAAx] rem (D * m) q ≐ rem b q :=
        (rem_mul_rem hq'.wk D m).eqSymm.eqTrans ((congrAp2 remF (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans
          (res_spec hq'.wk hD.wk))
      exact (eqb_of_eq a).eqTrans ((one_mul _).eqSymm.eqTrans
        (congrMul (eqb_of_eq hD.wk).eqSymm (eqb_of_eq Prf.hyp0).eqSymm))
    · let C' : List (Fm PTm n) := neg (rem m q ≐ res D q b) :: C
      have nn : C' ⊢[PRAAx] neg (rem (D * m) q ≐ rem b q) := by
        refine .impI ?_
        let C'' : List (Fm PTm n) := (rem (D * m) q ≐ rem b q) :: C'
        have hx : C'' ⊢[PRAAx] lt (rem m q) q := rem_lt hq'.wk.wk m
        have a : C'' ⊢[PRAAx] rem (D * rem m q) q ≐ rem b q := (rem_mul_rem hq'.wk.wk D m).eqTrans Prf.hyp0
        have u := res_unique hq'.wk.wk hD.wk.wk hx a
        exact .impE (Prf.hyp1 : C'' ⊢[PRAAx] neg (rem m q ≐ res D q b)) u
      exact (eqb_of_ne nn).eqTrans ((mul_zero _).eqSymm.eqTrans
        (congrMul (eqb_of_eq hD.wk).eqSymm (eqb_of_ne Prf.hyp0).eqSymm))
  · let C : List (Fm PTm n) := neg (gcd D q ≐ one) :: Γ
    have nn : C ⊢[PRAAx] neg (rem (D * m) q ≐ rem b q) := by
      refine .impI ?_
      let C' : List (Fm PTm n) := (rem (D * m) q ≐ rem b q) :: C
      exact .impE (Prf.hyp1 : C' ⊢[PRAAx] neg (gcd D q ≐ one)) (cop_of_sol hq.wk.wk hb.wk.wk Prf.hyp0)
    exact (eqb_of_ne nn).eqTrans ((zero_mul _).eqSymm.eqTrans (congrMul (eqb_of_ne Prf.hyp0).eqSymm (.eqRefl _)))

end LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue

export_ipra AnalyticNumberTheory.PowerResidue (gcd_one_left inv inv_spec res res_cop res_lt res_unique)
