import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Foundations.ChineseRemainder
import IPRADerivations.Core.SubstCommand

/-!
# Fermat's little theorem

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, the prime case of
Theorem `thm:euler` (Euler's theorem): for a prime `p`, `aᵖ ≡ a (mod p)`.

The route is the binomial one:

* `absorption`: `(j + 1) C(q + 1, j + 1) = (q + 1) C(q, j)` for `j < q`;
* `prime_dvd_binom`: `p ∣ C(p, j + 1)` for `j + 1 < p`, by Euclid's lemma, since
  `p ∤ j + 1`;
* `dvd_sum`: a bounded sum of multiples of `d` is a multiple of `d`;
* `freshman`: `(a + 1)ᵖ ≡ aᵖ + 1 (mod p)`, from the binomial theorem;
* `fermat`: induction on `a`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Fermat

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq binom_zero' binom_self' mul_cancel)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Substitution into `prime` -/

theorem subst_up_shift' {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

ipra_subst prime [subst_up_shift']

theorem prime_shift {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ.map Fm.shift ⊢[PRAAx] prime (Syn.shift p) := by
  have h := hp.shift
  simp only [Fm.shift, subst_prime] at h
  exact h

/-! ## `p ∣ C(p, k)` -/

theorem absorption_alg {Fq' Fq Fj' Fj Fm' Fm C₁ C₀ j q : PTm n}
    (e₁ : Γ ⊢[PRAAx] Fq' ≐ (Fj' * Fm') * C₁) (e₂ : Γ ⊢[PRAAx] Fq ≐ (Fj * Fm) * C₀)
    (f₁ : Γ ⊢[PRAAx] Fq' ≐ Fq * succ q) (f₂ : Γ ⊢[PRAAx] Fj' ≐ Fj * succ j)
    (f₃ : Γ ⊢[PRAAx] Fm' ≐ Fm) :
    Γ ⊢[PRAAx] (Fj * Fm) * (succ j * C₁) ≐ (Fj * Fm) * (succ q * C₀) := by
  ipra_lc -natEq e₁ - Groth.ι (IPRA.Q.mk Γ Fm') * Groth.ι (IPRA.Q.mk Γ C₁) * natEq f₂ -
    Groth.ι (IPRA.Q.mk Γ Fj) * (Groth.ι (IPRA.Q.mk Γ j) + 1) * Groth.ι (IPRA.Q.mk Γ C₁) * natEq f₃ + natEq f₁ +
    (Groth.ι (IPRA.Q.mk Γ q) + 1) * natEq e₂

/-- `(j + 1) C(q + 1, j + 1) = (q + 1) C(q, j)` for `j < q`. -/
theorem absorption {q j : PTm n} (hj : Γ ⊢[PRAAx] lt j q) :
    Γ ⊢[PRAAx] succ j * binom (succ q) (succ j) ≐ succ q * binom q j := by
  have e₁ := binom_eq (Γ := Γ) (k := succ j) (n := succ q) ((succ_monus_succ j q).eqTrans (le_of_lt hj))
  have e₂ := binom_eq (le_of_lt hj)
  have f₁ := fact_succ (Γ := Γ) q zero
  have f₂ := fact_succ (Γ := Γ) j zero
  have f₃ := congrAp2 (Γ := Γ) factF (succ_monus_succ q j) (.eqRefl zero)
  exact mul_cancel (bden_pos q j) (absorption_alg e₁ e₂ f₁ f₂ f₃)

/-- For a prime `p = q + 1` and `j < q`: `p ∣ C(p, j + 1)`. -/
theorem prime_dvd_binom {p q j : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] p ≐ succ q)
    (hj : Γ ⊢[PRAAx] lt j q) : Γ ⊢[PRAAx] dvd p (binom p (succ j)) := by
  have hab : Γ ⊢[PRAAx] dvd (succ q) (succ j * binom (succ q) (succ j)) := dvd_of_eq (absorption hj)
  have hab' : Γ ⊢[PRAAx] dvd p (succ j * binom p (succ j)) :=
    dvd_congr_left hq.eqSymm (dvd_congr (congrMul (.eqRefl _) (congrBinom hq.eqSymm (.eqRefl _))) hab)
  refine .orE (euclid_lemma_at hp hab') ?_ Prf.hyp0
  have h₁ := dvd_le (dvd_congr_left hq.wk (Prf.hyp0 : (dvd p (succ j) :: Γ) ⊢[PRAAx] dvd p (succ j)))
    (congrSucc (pred_succ j).eqSymm)
  exact le_lt_absurd _ ((succ_monus_succ q j).eqSymm.eqTrans h₁) hj.wk

/-! ## Sums of multiples -/

theorem dvd_sum (f : PTm 2) {d' N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      dvd (succ (Syn.shift d')) (inst2 f (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] dvd (succ d') (ap2 (sumF f) N x) := by
  let P : Fm PTm (n + 1) := dvd (succ (Syn.shift d')) (ap2 (sumF f) (var 0) (Syn.shift x))
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simpa [P] using dvd_congr (sum_zero (Γ := Γ) f x).eqSymm (dvd_zero d')
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact .impI (dvd_congr (sum_succ' f (var 0) _).eqSymm
        (dvd_add Prf.hyp1 (.impE h.allOpen.wk.wk Prf.hyp0)))
  simpa [P] using atBound

/-! ## The freshman's dream -/

theorem freshman_alg {L Pw T₀ Sp Sq M T₃ Ap p q w : PTm n}
    (bt : Γ ⊢[PRAAx] L ≐ Pw) (s₁ : Γ ⊢[PRAAx] L ≐ T₀ + Sp) (t₀ : Γ ⊢[PRAAx] T₀ ≐ one * one)
    (s₂ : Γ ⊢[PRAAx] Sp ≐ Sq) (s₃ : Γ ⊢[PRAAx] Sq ≐ M + T₃) (t₃ : Γ ⊢[PRAAx] T₃ ≐ one * Ap)
    (eM : Γ ⊢[PRAAx] M ≐ succ q * w) (hq : Γ ⊢[PRAAx] p ≐ succ q) :
    Γ ⊢[PRAAx] Pw + p * zero ≐ succ Ap + p * w := by
  ipra_lc -natEq bt + natEq s₁ + natEq t₀ + natEq s₂ + natEq s₃ + natEq t₃ + natEq eM -
    Groth.ι (IPRA.Q.mk Γ w) * natEq hq

/-- `(a + 1)ᵖ ≡ aᵖ + 1 (mod p)` for a prime `p`. -/
theorem freshman {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) :
    Γ ⊢[PRAAx] rem (pw (succ a) p) p ≐ rem (succ (pw a p)) p := by
  have hq := prime_eq_succ_pred hp
  have fX := fst_pair (Γ := Γ) p a
  have sX := snd_pair (Γ := Γ) p a
  have bt := binomial_at (Γ := Γ) p a
  have s₁ := sum_shift (Γ := Γ) tBody p (pairT p a)
  rw [inst2_t] at s₁
  have t₀ := congrMul (binom_zero' (Γ := Γ) (fstT (pairT p a))) (pw_zero (Γ := Γ) (sndT (pairT p a)))
  have s₂ := congrAp2 (Γ := Γ) (sumF (shiftBody tBody)) hq (.eqRefl (pairT p a))
  have s₃ := sum_succ' (Γ := Γ) (shiftBody tBody) (pred p) (pairT p a)
  rw [inst2_s] at s₃
  have t₃ := congrMul ((congrBinom fX hq.eqSymm).eqTrans (binom_self' p)) (congrPw sX hq.eqSymm)
  -- Every inner term `C(p, k + 1) aᵏ⁺¹`, `k + 1 < p`, is a multiple of `p`.
  have hd : Γ ⊢[PRAAx] dvd (succ (pred p)) (ap2 (sumF (shiftBody tBody)) (pred p) (pairT p a)) := by
    refine dvd_sum _ (.allI ?_)
    rw [inst2_s]
    have eq₁ : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
    have eq₂ : Syn.shift (pairT p a) = pairT (Syn.shift p) (Syn.shift a) := by simp [Syn.shift]
    rw [eq₁, eq₂]
    refine .impI ?_
    have hp' := (prime_shift hp).wk (ψ := lt (var 0) (pred (Syn.shift p)))
    have hq' := prime_eq_succ_pred hp'
    have pd := dvd_congr_left hq' (prime_dvd_binom hp' hq' Prf.hyp0)
    exact dvd_mul _ (dvd_congr (congrBinom (fst_pair _ _).eqSymm (.eqRefl _)) pd)
  exact rem_eq_of_eq hq (freshman_alg bt s₁ t₀ s₂ s₃ t₃ (eq_of_dvd hd) hq)

/-! ## Fermat's little theorem -/

/-- `x ≡ y (mod M)` gives `x + 1 ≡ y + 1 (mod M)`. -/
theorem rem_succ_congr {M x y : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] rem x M ≐ rem y M) : Γ ⊢[PRAAx] rem (succ x) M ≐ rem (succ y) M := by
  have dx := div_mod_at (x := x) hM
  have dy := div_mod_at (x := y) hM
  refine rem_eq_of_eq hM (k₁ := quo y M) (k₂ := quo x M) ?_
  ipra_lc natEq (Prf.andE₁ dx) - natEq (Prf.andE₁ dy) + natEq h

/-- `aᵖ ≡ a (mod p)` for a prime `p`. -/
theorem fermat_at {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a : PTm n) :
    Γ ⊢[PRAAx] rem (pw a p) p ≐ rem a p := by
  have hall : Γ ⊢[PRAAx] Fm.all (rem (pw (var 0) (Syn.shift p)) (Syn.shift p) ≐ rem (var 0) (Syn.shift p)) := by
    ipra_qfind (trivial) [subst_ap2]
    · have hq := prime_eq_succ_pred hp
      have z : Γ ⊢[PRAAx] pw zero p ≐ zero :=
        (congrPw (.eqRefl _) hq).eqTrans ((pw_succ _ _).eqTrans (mul_zero _))
      exact congrAp2 remF z (.eqRefl _)
    · have hp' := (prime_shift hp).wk
        (ψ := rem (pw (var 0) (Syn.shift p)) (Syn.shift p) ≐ rem (var 0) (Syn.shift p))
      exact (freshman hp').eqTrans (rem_succ_congr (prime_eq_succ_pred hp') Prf.hyp0)
  have h := Prf.allE a hall
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h
  exact h

/-- Fermat's little theorem; variables `0 = p`, `1 = a`. -/
abbrev fermatFormula : Fm PTm 2 :=
  prime (var 0) ⟶ rem (pw (var 1) (var 0)) (var 0) ≐ rem (var 1) (var 0)

theorem fermat : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 fermatFormula :=
  closeUniv 2 (.impI (fermat_at Prf.hyp0 _))

end LeanProofs.IPRA.AnalyticNumberTheory.Fermat

export_ipra AnalyticNumberTheory.Fermat (dvd_sum fermat_at prime_dvd_binom prime_shift)
