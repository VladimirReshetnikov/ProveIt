import IPRADerivations.Core.Bezout
import IPRADerivations.AnalyticNumberTheory.Primes

/-!
# Euclid's lemma

`prime p → p ∣ ab → p ∣ a ∨ p ∣ b`. The proof follows the classical route: if
`p ∤ a` then `gcd(p, a) = 1`, since it divides `p`, is at most `p` and is not `p`; and
Bézout's identity `1 + v a = u p` (or `1 + u p = v a`), multiplied by `b`, exhibits
`b` as a difference of multiples of `p`.

Also derived, under arbitrary hypotheses: the gcd theorems of `Core.Gcd` and Bézout's
identity at arbitrary terms, `gcd(a, b) = 0 → a = 0`, and `d ∣ x, x ≥ 1 → d ≤ x`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The gcd theorems at arbitrary terms -/

theorem common_at (a b d' k : PTm n) :
    Γ ⊢[PRAAx] ((dvd (succ d') a ⋏ dvd (succ d') b) ⟶ (dvd (succ d') (ex k ![a, b]) ⋏ dvd (succ d') (ey k ![a, b]))) ⋏
      ((dvd (succ d') (ex k ![a, b]) ⋏ dvd (succ d') (ey k ![a, b])) ⟶ (dvd (succ d') a ⋏ dvd (succ d') b)) := by
  have h := inst (Γ := Γ) common_invariant (![k, a, b, d'] : Fin 4 → PTm n)
  simp only [Fm.subst_and, Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ex2, subst_ey2,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem terminates_at (a b : PTm n) : Γ ⊢[PRAAx] ey (succ b) ![a, b] ≐ zero := by
  have h := inst (Γ := Γ) euclid_terminates (![a, b] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ey2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem gcd_greatest_at {a b d' : PTm n} (ha : Γ ⊢[PRAAx] dvd (succ d') a) (hb : Γ ⊢[PRAAx] dvd (succ d') b) :
    Γ ⊢[PRAAx] dvd (succ d') (gcd a b) :=
  Prf.andE₁ (.impE (Prf.andE₁ (common_at a b d' (succ b))) (.andI ha hb))

theorem gcd_dvd_at {a b : PTm n} (hg : Γ ⊢[PRAAx] gcd a b ≐ succ (pred (gcd a b))) :
    Γ ⊢[PRAAx] dvd (gcd a b) a ⋏ dvd (gcd a b) b := by
  have h := Prf.andE₂ (common_at (Γ := Γ) a b (pred (gcd a b)) (succ b))
  have hX := dvd_congr hg.eqSymm (dvd_self (Γ := Γ) (pred (gcd a b)))
  have hY := dvd_congr (terminates_at a b).eqSymm (dvd_zero (Γ := Γ) (pred (gcd a b)))
  have hab := Prf.impE h (.andI hX hY)
  exact .andI ((congrAp2 remF (.eqRefl _) hg).eqTrans (Prf.andE₁ hab))
    ((congrAp2 remF (.eqRefl _) hg).eqTrans (Prf.andE₂ hab))

theorem bezout_at (a b : PTm n) :
    Γ ⊢[PRAAx] (gcd a b + Bezout.cur zero one (succ b) a b * b ≐ Bezout.cur one zero (succ b) a b * a) ⋎
      (gcd a b + Bezout.cur one zero (succ b) a b * a ≐ Bezout.cur zero one (succ b) a b * b) := by
  have h := inst (Γ := Γ) Bezout.invariant_open (![succ b, a, b] : Fin 3 → PTm n)
  simp only [Fm.subst_or, Fm.subst_and, Fm.subst_eq, PTm.subst_add, PTm.subst_mul,
    Bezout.subst_cur, Bezout.subst_nxt, Bezout.subst_eps, subst_ex2, subst_ey2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact .orE h (.orI₁ (Prf.andE₁ (Prf.andE₂ Prf.hyp0))) (.orI₂ (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))

/-- `a mod (a + 1) = a`. -/
theorem rem_self_succ (a : PTm n) : Γ ⊢[PRAAx] rem a (succ a) ≐ a :=
  Prf.andE₂ (div_mod_unique (q := zero) (r := a)
    ((zero_add _).eqSymm.eqTrans (congrAdd (mul_zero _).eqSymm (.eqRefl _))) (le_refl _))

/-- `gcd(a, b) = 0 → a = 0`. -/
theorem gcd_eq_zero {a b : PTm n} (h : Γ ⊢[PRAAx] gcd a b ≐ zero) : Γ ⊢[PRAAx] a ≐ zero := by
  have hb := Prf.andE₂ (common_at (Γ := Γ) a b a (succ b))
  have hX := dvd_congr h.eqSymm (dvd_zero (Γ := Γ) a)
  have hY := dvd_congr (terminates_at a b).eqSymm (dvd_zero (Γ := Γ) a)
  exact (rem_self_succ a).eqSymm.eqTrans (Prf.andE₁ (Prf.impE hb (.andI hX hY)))

/-- `d ∣ x` with `x ≥ 1` gives `d ≤ x`. -/
theorem dvd_le {d' x : PTm n} (h : Γ ⊢[PRAAx] dvd (succ d') x) (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) :
    Γ ⊢[PRAAx] le (succ d') x := by
  have e := eq_of_dvd h
  refine .orE (zero_or_succ (quo x (succ d'))) ?_ ?_
  · refine succ_ne_zero' _ (a := pred x) (hx.wk.eqSymm.eqTrans (e.wk.eqTrans ?_))
    exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)
  · refine le_of_eq_add (d := succ d' * pred (quo x (succ d'))) (e.wk.eqTrans ?_)
    exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_succ _ _) |>.eqTrans (add_comm _ _)

/-! ## Euclid's lemma -/

/-- A prime is `S (S (p ∸ 2))`. -/
theorem prime_eq_succ_succ {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] p ≐ succ (succ (monus p two)) := by
  unfold prime at hp
  refine (eq_add_of_le (Prf.andE₁ hp)).eqTrans ?_
  ipra_ring

theorem prime_eq_succ_pred {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
  (prime_eq_succ_succ hp).eqTrans
    (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred (prime_eq_succ_succ hp).eqSymm)))

theorem dvd_congr_left {Δ : List (Fm PTm n)} {d d' x : PTm n} (h : Δ ⊢[PRAAx] d ≐ d')
    (hx : Δ ⊢[PRAAx] dvd d x) : Δ ⊢[PRAAx] dvd d' x :=
  (congrAp2 remF (.eqRefl _) h.eqSymm).eqTrans hx

/-- A divisor at least two of a prime is the prime itself. -/
theorem prime_eq_of_dvd {p d : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hd₂ : Γ ⊢[PRAAx] le two d) (hdvd : Γ ⊢[PRAAx] dvd d p) : Γ ⊢[PRAAx] d ≐ p := by
  have hd : Γ ⊢[PRAAx] d ≐ succ (succ (monus d two)) :=
    (eq_add_of_le hd₂).eqTrans (by ipra_ring)
  have hdp := le_congr hd.eqSymm (.eqRefl _)
    (dvd_le (dvd_congr_left hd hdvd) (prime_eq_succ_pred hp))
  unfold prime at hp
  have hall := Prf.allE d (Prf.andE₂ hp)
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hall
  refine .orE (lt_or_eq_of_le hdp) ?_ Prf.hyp0
  exact .botE _ (.impE (.impE (.impE hall.wk hd₂.wk) Prf.hyp0) hdvd.wk)

/-- For a prime `p` with `p ∤ a`: `gcd(p, a) = 1`. -/
theorem gcd_prime {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p)
    (hna : Γ ⊢[PRAAx] neg (dvd p a)) : Γ ⊢[PRAAx] gcd p a ≐ one := by
  have e := prime_eq_succ_succ hp
  refine .orE (zero_or_succ (gcd p a)) ?_ ?_
  · exact succ_ne_zero' _ (a := succ (monus p two)) (e.wk.eqSymm.eqTrans (gcd_eq_zero Prf.hyp0))
  have hg : ((gcd p a ≐ succ (pred (gcd p a))) :: Γ) ⊢[PRAAx] gcd p a ≐ succ (pred (gcd p a)) :=
    Prf.hyp0
  have hd := gcd_dvd_at hg
  refine .orE (zero_or_succ (pred (gcd p a))) ?_ ?_
  · exact hg.wk.eqTrans (congrSucc Prf.hyp0)
  refine .botE _ (.impE hna.wk.wk (dvd_congr_left ?_ hd.andE₂.wk))
  refine prime_eq_of_dvd hp.wk.wk ?_ hd.andE₁.wk
  refine le_of_eq_add (d := pred (pred (gcd p a))) ?_
  exact hg.wk.eqTrans ((congrSucc Prf.hyp0).eqTrans (by ipra_ring))

/-- The algebra of case one: `g + X a = Y p`, `g = 1`, `a b = q w`, `p = q` give
`b + q (X w) = q (Y b)`. -/
theorem euclid_alg₁ {g X Y a b p q w : PTm n} (e₁ : Γ ⊢[PRAAx] g + X * a ≐ Y * p)
    (e₂ : Γ ⊢[PRAAx] g ≐ one) (e₃ : Γ ⊢[PRAAx] a * b ≐ q * w) (e₄ : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] b + q * (X * w) ≐ q * (Y * b) := by
  ipra_lc (Groth.ι (Q.mk Γ b)) * natEq e₁ - (Groth.ι (Q.mk Γ b)) * natEq e₂ - (Groth.ι (Q.mk Γ X)) * natEq e₃ +
    (Groth.ι (Q.mk Γ Y)) * (Groth.ι (Q.mk Γ b)) * natEq e₄

/-- The algebra of case two: `g + Y p = X a`, `g = 1`, `a b = q w`, `p = q` give
`b + q (Y b) = q (X w)`. -/
theorem euclid_alg₂ {g X Y a b p q w : PTm n} (e₁ : Γ ⊢[PRAAx] g + Y * p ≐ X * a)
    (e₂ : Γ ⊢[PRAAx] g ≐ one) (e₃ : Γ ⊢[PRAAx] a * b ≐ q * w) (e₄ : Γ ⊢[PRAAx] p ≐ q) :
    Γ ⊢[PRAAx] b + q * (Y * b) ≐ q * (X * w) := by
  ipra_lc (Groth.ι (Q.mk Γ b)) * natEq e₁ - (Groth.ι (Q.mk Γ b)) * natEq e₂ + (Groth.ι (Q.mk Γ X)) * natEq e₃ -
    (Groth.ι (Q.mk Γ Y)) * (Groth.ι (Q.mk Γ b)) * natEq e₄

/-- Euclid's lemma: a prime dividing `a b` divides `a` or `b`. -/
theorem euclid_lemma_at {p a b : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hab : Γ ⊢[PRAAx] dvd p (a * b)) :
    Γ ⊢[PRAAx] dvd p a ⋎ dvd p b := by
  have hq := prime_eq_succ_pred hp
  have w := eq_of_dvd (dvd_congr_left hq hab)
  refine .orE (eq_or_ne (rem a p) zero) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  have hg := gcd_prime (Γ := neg (dvd p a) :: Γ) (a := a) hp.wk Prf.hyp0
  refine dvd_congr_left hq.wk.eqSymm ?_
  -- In both Bézout cases `b` plus a multiple of `p` is a multiple of `p`.
  refine .orE (bezout_at p a) ?_ ?_
  · exact dvd_sub (dvd_of_eq (euclid_alg₁ Prf.hyp0 hg.wk w.wk.wk hq.wk.wk)) (dvd_of_eq (.eqRefl _))
  · exact dvd_sub (dvd_of_eq (euclid_alg₂ Prf.hyp0 hg.wk w.wk.wk hq.wk.wk)) (dvd_of_eq (.eqRefl _))

/-- `∀ p a b. prime p → p ∣ a b → p ∣ a ∨ p ∣ b`. Variables `0 = p`, `1 = a`, `2 = b`. -/
abbrev euclidLemmaFormula : Fm PTm 3 :=
  prime (var 0) ⟶ dvd (var 0) (var 1 * var 2) ⟶ dvd (var 0) (var 1) ⋎ dvd (var 0) (var 2)

theorem euclid_lemma : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 euclidLemmaFormula :=
  closeUniv 3 (.impI (.impI (euclid_lemma_at Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA
