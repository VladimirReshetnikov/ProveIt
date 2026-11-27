import IPRADerivations.AnalyticNumberTheory.PhiPower

/-!
# Divisibility monotonicity of the totient

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-divides`:
`a ∣ b` and `a, b > 0` give `φ(a) ∣ φ(b)`.

No factorization is needed. With `X = a c″` and a prime `q`:
`φ(X q) = q φ(X)` when `q ∣ X` (`PhiPower.phi_mul_pow_at`), and `φ(X q) = φ(X) φ(q)` otherwise
(`Multiplicative.phi_mul_at`), so `φ(X) ∣ φ(Xq)` (`peel`). Strong induction on `c` — encoded as
the quantifier-free statement that the violation count `V(N) = ∑_{c<N} sg(φ(ac) mod φ(a))` is `0`
— then gives `φ(a) ∣ φ(ac)`, peeling `q = lpf(c)` with `c″ = c / q < c` (`viol_ge2`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PhiDivides

open_ipra exports
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (phi_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiPower (phi_mul_pow_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Peeling one prime -/

/-- `φ(X) ∣ φ(X q)` for a prime `q` and `X ≥ 1`. -/
theorem peel {X q : PTm n} (hX : Γ ⊢[PRAAx] X ≐ succ (pred X)) (hq : Γ ⊢[PRAAx] prime q) :
    Γ ⊢[PRAAx] dvd (phi X) (phi (X * q)) := by
  have hq' := prime_eq_succ_pred hq
  have hφ := phi_pos hX
  refine .orE (eq_or_ne (rem X q) zero) ?_ ?_
  · have hd : ((rem X q ≐ zero) :: Γ) ⊢[PRAAx] dvd q (pw X one) :=
      dvd_congr (pw_one _).eqSymm Prf.hyp0
    have e := phi_mul_pow_at hX.wk hq'.wk hd
    exact dvd_of_eq' hφ.wk (w := q) (e.eqTrans (mul_comm _ _))
  · have hg := gcd_comm_one hX.wk (gcd_prime hq.wk Prf.hyp0)
    exact dvd_of_eq' hφ.wk (w := phi q) (phi_mul_at hX.wk hq'.wk hg)

/-! ## The violation count -/

/-- `sg(φ(a c) mod φ(a))`, over `0 = c`, `1 = a`. -/
abbrev violB : PTm 2 := sg (rem (phi (var 1 * var 0)) (phi (var 1)))

theorem inst2_viol (c a : PTm n) : inst2 violB c a = sg (rem (phi (a * c)) (phi a)) := by simp [inst2]

theorem sg_zero_inv {x : PTm n} (h : Γ ⊢[PRAAx] sg x ≐ zero) : Γ ⊢[PRAAx] x ≐ zero := by
  refine .orE (zero_or_succ x) Prf.hyp0 ?_
  exact succ_ne_zero' _ (a := zero) ((sg_succ _).eqSymm.eqTrans
    ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0.eqSymm)).eqTrans h.wk))

section Viol

variable {A : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
include hA

omit hA in
theorem viol_zero (A : PTm n) : Γ ⊢[PRAAx] rem (phi (A * zero)) (phi A) ≐ zero :=
  (congrAp2 remF ((congrAp2 (sumF totBody) (mul_zero _) (mul_zero _)).eqTrans (sum_zero _ _)) (.eqRefl _)).eqTrans
    (rem_zero _)

theorem viol_one : Γ ⊢[PRAAx] rem (phi (A * one)) (phi A) ≐ zero := by
  have hφ := phi_pos hA
  have e : Γ ⊢[PRAAx] A * one ≐ A := by ipra_ring
  refine (congrAp2 remF (congrAp2 (sumF totBody) e e) (.eqRefl _)).eqTrans ?_
  exact rem_eq' hφ (q := one) (by ipra_ring) (zero_lt' hφ)

/-- The step for `c ≥ 2`: peel `q = lpf(c)` off `c`. -/
theorem viol_ge2 (z' : PTm n) (hV : Γ ⊢[PRAAx] ap2 (sumF violB) (succ (succ z')) A ≐ zero) :
    Γ ⊢[PRAAx] dvd (phi A) (phi (A * succ (succ z'))) := by
  have hq := lpf_prime (Γ := Γ) z'
  have hq' := prime_eq_succ_pred hq
  have hq2 : Γ ⊢[PRAAx] le two (lpf (succ (succ z'))) := by unfold prime at hq; exact Prf.andE₁ hq
  have hNe := eq_of_dvd' hq' (Prf.andE₁ (lpf_dvd (Γ := Γ) z'))
  -- `c″ = c / q ≥ 1` and `c″ < c`.
  have hc : Γ ⊢[PRAAx] quo (succ (succ z')) (lpf (succ (succ z'))) ≐
      succ (pred (quo (succ (succ z')) (lpf (succ (succ z'))))) := by
    refine .orE (zero_or_succ (quo (succ (succ z')) (lpf (succ (succ z'))))) ?_ Prf.hyp0
    exact succ_ne_zero' _ (hNe.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))
  have hlt : Γ ⊢[PRAAx] lt (quo (succ (succ z')) (lpf (succ (succ z')))) (succ (succ z')) := by
    refine le_of_eq_add (d := pred (quo (succ (succ z')) (lpf (succ (succ z')))) +
      monus (lpf (succ (succ z'))) two * quo (succ (succ z')) (lpf (succ (succ z')))) ?_
    have h₁ := natEq hNe; have h₂ := natEq hc; have h₃ := natEq (eq_add_of_le hq2)
    ipra_lc h₁ + h₂ + Groth.ι (Q.mk _ (quo (succ (succ z')) (lpf (succ (succ z'))))) * h₃
  -- `φ(a) ∣ φ(a c″)` from the count.
  have h₀ := sum_zero_elim violB hV hlt
  rw [inst2_viol] at h₀
  have d₁ : Γ ⊢[PRAAx] dvd (phi A) (phi (A * quo (succ (succ z')) (lpf (succ (succ z'))))) := sg_zero_inv h₀
  -- `φ(a c″) ∣ φ(a c)`.
  have hX := pos_mul hA hc
  have d₂ := peel hX hq
  have e : Γ ⊢[PRAAx] A * quo (succ (succ z')) (lpf (succ (succ z'))) * lpf (succ (succ z')) ≐
      A * succ (succ z') := by
    ipra_lc -Groth.ι (Q.mk _ A) * natEq hNe
  exact dvd_trans' (phi_pos hA) (phi_pos hX) d₁ (dvd_congr (congrAp2 (sumF totBody) e e) d₂)

theorem viol_step {N : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF violB) N A ≐ zero) :
    Γ ⊢[PRAAx] inst2 violB N A ≐ zero := by
  rw [inst2_viol]
  refine (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) ?_)).eqTrans sg_zero
  refine .orE (zero_or_succ N) ?_ ?_
  · have hz : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    exact (congrAp2 remF (congrAp2 (sumF totBody) (congrMul (.eqRefl _) hz) (congrMul (.eqRefl _) hz))
      (.eqRefl _)).eqTrans (viol_zero A)
  · refine .orE (zero_or_succ (pred N)) ?_ ?_
    · have e : ((pred N ≐ zero) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      exact (congrAp2 remF (congrAp2 (sumF totBody) (congrMul (.eqRefl _) e) (congrMul (.eqRefl _) e))
        (.eqRefl _)).eqTrans (viol_one hA.wk.wk)
    · have e : ((pred N ≐ succ (pred (pred N))) :: (N ≐ succ (pred N)) :: Γ) ⊢[PRAAx]
          N ≐ succ (succ (pred (pred N))) := Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      have hV' := (congrAp2 (sumF violB) e.eqSymm (.eqRefl _)).eqTrans hV.wk.wk
      exact (congrAp2 remF (congrAp2 (sumF totBody) (congrMul (.eqRefl _) e) (congrMul (.eqRefl _) e))
        (.eqRefl _)).eqTrans (viol_ge2 hA.wk.wk _ hV')

end Viol

/-- Variables: `0 = N`, `1 = a`. -/
private abbrev violF : Fm PTm 2 := (var 1 ≐ succ (pred (var 1))) ⟶ ap2 (sumF violB) (var 0) (var 1) ≐ zero

private theorem viol₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] violF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2]
  · exact .impI (sum_zero _ _)
  · refine .impI ((sum_succ' _ _ _).eqTrans ?_)
    exact (congrAdd (.impE Prf.hyp1 Prf.hyp0) (viol_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))).eqTrans (add_zero _)

/-- `φ(a) ∣ φ(a c)` for `a ≥ 1`. -/
theorem phi_dvd_mul {A : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (c : PTm n) :
    Γ ⊢[PRAAx] dvd (phi A) (phi (A * c)) := by
  have h := inst (Γ := Γ) viol₀ (![succ c, A] : Fin 2 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_pred, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  have z := sum_zero_elim_last violB (.impE h hA)
  rw [inst2_viol] at z
  exact sg_zero_inv z

/-- `thm:phi-divides` at arbitrary terms. -/
theorem phi_divides_at {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (h : Γ ⊢[PRAAx] dvd a b) :
    Γ ⊢[PRAAx] dvd (phi a) (phi b) := by
  have e := eq_of_dvd' ha h
  exact dvd_congr (congrAp2 (sumF totBody) e e).eqSymm (phi_dvd_mul ha _)

/-- `thm:phi-divides`: `a ∣ b → φ(a) ∣ φ(b)` for `a ≥ 1`; variables `0 = a − 1`, `1 = b`. -/
abbrev phiDividesFormula : Fm PTm 2 := dvd (succ (var 0)) (var 1) ⟶ dvd (phi (succ (var 0))) (phi (var 1))

theorem phi_divides : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 phiDividesFormula :=
  closeUniv 2 (.impI (phi_divides_at (congrSucc (pred_succ _).eqSymm) Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.PhiDivides

export_ipra AnalyticNumberTheory.PhiDivides (sg_zero_inv)
