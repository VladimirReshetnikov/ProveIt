import IPRADerivations.AnalyticNumberTheory.SumReindex

/-!
# Every `m ≤ N` divides a power of the primorial

For `A(N) = ∏_{p < N} p` (`PowerCleared.A`): `1 ≤ m ≤ N → m ∣ A(N + 1)^N` (`smooth_all`). This is the
finite factorisation fact behind Lemma `lem:euler-domination` of `prime_reciprocal_ipra_2026-11-15`,
replacing the paper's factor-vector injection.

* `A_dvd_mono`: `M ≤ N → A(M) ∣ A(N)`; `prime_dvd_A`: a prime `p < N` divides `A(N)`;
* `pw_dvd_base`, `pw_dvd_exp`, `dvd_mul_mul`: divisibility of powers and products;
* `smooth_self`: `m ≥ 1 → m ∣ A(m + 1)^m`, by strong induction (the vanishing violation count
  `∑_{m<K} sg(m) · sg(A(m+1)^m mod m) = 0`): for `m ≥ 2` with least prime factor `p` and `m = p m'`,
  `m' ∣ A(m' + 1)^{m'} ∣ A(m + 1)^{m'}` and `p ∣ A(m + 1)` give `m ∣ A(m + 1)^{m'+1} ∣ A(m + 1)^m`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Smooth

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrSg)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (A pB pBt A_succ A_pos pBt_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Divisibility of powers and products -/

theorem dvd_mul_mul {a b x y : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (h₁ : Γ ⊢[PRAAx] dvd a x) (h₂ : Γ ⊢[PRAAx] dvd b y) : Γ ⊢[PRAAx] dvd (a * b) (x * y) := by
  refine dvd_of_eq' (pos_mul ha hb) (w := quo x a * quo y b) ?_
  ipra_lc Groth.ι (IPRA.Q.mk Γ y) * natEq (eq_of_dvd' ha h₁) +
    Groth.ι (IPRA.Q.mk Γ a) * Groth.ι (IPRA.Q.mk Γ (quo x a)) * natEq (eq_of_dvd' hb h₂)

theorem pw_dvd_base {x y : PTm n} (e : PTm n) (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (h : Γ ⊢[PRAAx] dvd x y) :
    Γ ⊢[PRAAx] dvd (pw x e) (pw y e) :=
  dvd_of_eq' (pw_pos' hx e) (w := pw (quo y x) e)
    ((congrPw (eq_of_dvd' hx h) (.eqRefl _)).eqTrans (pw_mul_base _ _ _))

theorem pw_dvd_exp {x e₁ e₂ : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) (h : Γ ⊢[PRAAx] le e₁ e₂) :
    Γ ⊢[PRAAx] dvd (pw x e₁) (pw x e₂) :=
  dvd_of_eq' (pw_pos' hx e₁) (w := pw x (monus e₂ e₁))
    ((congrPw (.eqRefl _) (eq_add_of_le h)).eqTrans (pw_add _ _ _))

/-! ## The primorial -/

theorem A_dvd_step {M d : PTm n} (ih : Γ ⊢[PRAAx] dvd (A M) (A (M + d))) :
    Γ ⊢[PRAAx] dvd (A M) (A (M + succ d)) :=
  dvd_congr ((A_succ (M + d)).eqSymm.eqTrans (congrAp2 (prodF pB) (add_succ _ _).eqSymm (.eqRefl _)))
    (dvd_mul' (A_pos M) (pBt (M + d)) ih)

/-- Variables: `0 = d`, `1 = M`. -/
private abbrev monoF : Fm PTm 2 := dvd (A (var 1)) (A (var 1 + var 0))

private theorem mono₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] monoF := by
  ipra_ind [subst_ap2]
  · exact dvd_congr (congrAp2 (prodF pB) (add_zero _) (.eqRefl _)).eqSymm (dvd_self' (A_pos _))
  · exact A_dvd_step Prf.hyp0

/-- `M ≤ N → A(M) ∣ A(N)`. -/
theorem A_dvd_mono {M N : PTm n} (h : Γ ⊢[PRAAx] le M N) : Γ ⊢[PRAAx] dvd (A M) (A N) := by
  have i := inst (Γ := Γ) mono₀ (![monus N M, M] : Fin 2 → PTm n)
  simp at i
  exact dvd_congr (congrAp2 (prodF pB) (eq_add_of_le h).eqSymm (.eqRefl _)) i

/-- A prime `p < N` divides `A(N)`. -/
theorem prime_dvd_A {p N : PTm n} (hp : Γ ⊢[PRAAx] prime p) (h : Γ ⊢[PRAAx] lt p N) : Γ ⊢[PRAAx] dvd p (A N) := by
  have hpos := prime_eq_succ_pred hp
  have e : Γ ⊢[PRAAx] A (succ p) ≐ p * A p :=
    (A_succ p).eqTrans ((congrMul (.eqRefl _) (pBt_one (isP_of_prime hp))).eqTrans (mul_comm _ _))
  exact dvd_trans' hpos (A_pos _) (dvd_of_eq' hpos (w := A p) e) (A_dvd_mono h)

/-! ## Peeling the least prime factor -/

section Peel

variable {K : PTm n} (hK : Γ ⊢[PRAAx] le two K)
include hK

theorem K_eq : Γ ⊢[PRAAx] K ≐ succ (succ (monus K two)) := by
  refine (eq_add_of_le hK).eqTrans ?_
  ipra_ring

theorem lpf_two : Γ ⊢[PRAAx] prime (lpf K) ⋏ dvd (lpf K) K := by
  have e := K_eq hK
  exact .andI (prime_congr (lpf_congr e.eqSymm) (lpf_prime _))
    (dvd_congr e.eqSymm (dvd_congr_left (lpf_congr e.eqSymm) (Prf.andE₁ (lpf_dvd (monus K two)))))

theorem K_split : Γ ⊢[PRAAx] K ≐ lpf K * quo K (lpf K) :=
  eq_of_dvd' (prime_eq_succ_pred (Prf.andE₁ (lpf_two hK))) (Prf.andE₂ (lpf_two hK))

theorem cof_pos : Γ ⊢[PRAAx] quo K (lpf K) ≐ succ (pred (quo K (lpf K))) := by
  refine .orE (zero_or_succ (quo K (lpf K))) ?_ Prf.hyp0
  refine succ_ne_zero' _ (a := succ (monus K two)) ?_
  exact (K_eq hK).wk.eqSymm.eqTrans ((K_split hK).wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

theorem cof_lt : Γ ⊢[PRAAx] le (succ (quo K (lpf K))) K := by
  have hp2 : Γ ⊢[PRAAx] le two (lpf K) := by
    have h := Prf.andE₁ (lpf_two hK); unfold prime at h; exact Prf.andE₁ h
  refine le_of_eq_add (d := pred (quo K (lpf K)) + monus (lpf K) two * quo K (lpf K)) ?_
  ipra_lc natEq (K_split hK) + Groth.ι (IPRA.Q.mk Γ (quo K (lpf K))) * natEq (eq_add_of_le hp2) + natEq (cof_pos hK)

/-- Recombine the least prime factor and its cofactor in the larger power. -/
theorem dvd_pow_of_lpf_and_cofactor {B C : PTm n}
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hC : Γ ⊢[PRAAx] C ≐ succ (pred C))
    (hp : Γ ⊢[PRAAx] dvd (lpf K) C)
    (hm : Γ ⊢[PRAAx] dvd (quo K (lpf K)) (pw B (quo K (lpf K))))
    (hBC : Γ ⊢[PRAAx] dvd B C) : Γ ⊢[PRAAx] dvd K (pw C K) := by
  let m := quo K (lpf K)
  have hmC : Γ ⊢[PRAAx] dvd m (pw C m) :=
    dvd_trans' (cof_pos hK) (pw_pos' hB m) hm (pw_dvd_base m hB hBC)
  have hd := dvd_mul_mul (prime_eq_succ_pred (lpf_two hK).andE₁) (cof_pos hK) hp hmC
  have hStep : Γ ⊢[PRAAx] dvd K (pw C (succ m)) :=
    dvd_congr ((mul_comm _ _).eqTrans (pw_succ _ _).eqSymm) (dvd_congr_left (K_split hK).eqSymm hd)
  exact dvd_trans' (eq_succ_pred (K_eq hK)) (pw_pos' hC _) hStep (pw_dvd_exp hC (cof_lt hK))

/-- The step of the strong induction. -/
theorem sm_core (hm : Γ ⊢[PRAAx] dvd (quo K (lpf K)) (pw (A (succ (quo K (lpf K)))) (quo K (lpf K)))) :
    Γ ⊢[PRAAx] dvd K (pw (A (succ K)) K) := by
  have split := lpf_two hK
  have hp := split.andE₁
  have hpK := dvd_le' (prime_eq_succ_pred hp) split.andE₂ (eq_succ_pred (K_eq hK))
  exact dvd_pow_of_lpf_and_cofactor hK (A_pos _) (A_pos _)
    (prime_dvd_A hp (Order.lt_succ_of_le hpK)) hm
    (A_dvd_mono (Order.lt_succ_of_le (le_of_lt (cof_lt hK))))

end Peel

/-! ## The strong induction -/

/-- The violation `sg(m) · sg(A(m+1)^m mod m)`. -/
abbrev vB : PTm 2 := sg (var 0) * sg (rem (pw (A (succ (var 0))) (var 0)) (var 0))

theorem inst2_v (m x : PTm n) : inst2 vB m x = sg m * sg (rem (pw (A (succ m)) m) m) := by simp [inst2]

theorem of_viol {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (h : Γ ⊢[PRAAx] sg m * sg (rem (pw (A (succ m)) m) m) ≐ zero) : Γ ⊢[PRAAx] dvd m (pw (A (succ m)) m) :=
  sg_zero_inv ((one_mul _).eqSymm.eqTrans ((congrMul ((congrSg hm).eqTrans (sg_succ _)).eqSymm (.eqRefl _)).eqTrans h))

theorem viol_of {m : PTm n} (h : Γ ⊢[PRAAx] dvd m (pw (A (succ m)) m)) :
    Γ ⊢[PRAAx] sg m * sg (rem (pw (A (succ m)) m) m) ≐ zero :=
  (congrMul (.eqRefl _) ((congrSg h).eqTrans sg_zero)).eqTrans (mul_zero _)

theorem sm_step {K : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) K zero ≐ zero) :
    Γ ⊢[PRAAx] sg K * sg (rem (pw (A (succ K)) K) K) ≐ zero := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact (congrMul ((congrSg Prf.hyp0).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)
  · refine .orE (zero_or_succ (pred K)) ?_ ?_
    · -- `K = 1`.
      have e1 : ((pred K ≐ zero) :: (K ≐ succ (pred K)) :: Γ) ⊢[PRAAx] K ≐ one :=
        Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
      refine viol_of (dvd_congr_left e1.eqSymm (dvd_of_eq' (congrSucc (pred_succ _).eqSymm)
        (w := pw (A (succ K)) K) (one_mul _).eqSymm))
    · -- `K ≥ 2`.
      have hK : ((pred K ≐ succ (pred (pred K))) :: (K ≐ succ (pred K)) :: Γ) ⊢[PRAAx] le two K := by
        refine le_of_eq_add (d := pred (pred K)) (Prf.hyp1.eqTrans ((congrSucc Prf.hyp0).eqTrans ?_))
        ipra_ring
      have z := sum_zero_elim vB ih.wk.wk (cof_lt hK)
      rw [inst2_v] at z
      exact viol_of (sm_core hK (of_viol (cof_pos hK) z))

private abbrev smF : Fm PTm 1 := ap2 (sumF vB) (var 0) zero ≐ zero

private theorem sm₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] smF := by
  ipra_ind [subst_ap2]
  · exact sum_zero _ _
  · refine (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 ?_).eqTrans (add_zero _))
    rw [inst2_v]
    exact sm_step Prf.hyp0

/-- `m ≥ 1 → m ∣ A(m + 1)^m`. -/
theorem smooth_self {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] dvd m (pw (A (succ m)) m) := by
  have v := inst (Γ := Γ) sm₀ (![succ m] : Fin 1 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero] at v
  have z := sum_zero_elim vB v (le_refl (succ m))
  rw [inst2_v] at z
  exact of_viol hm z

/-- `1 ≤ m ≤ N → m ∣ A(N + 1)^N`. -/
theorem smooth_all {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] le m N) :
    Γ ⊢[PRAAx] dvd m (pw (A (succ N)) N) :=
  dvd_trans' hm (pw_pos' (A_pos _) _)
    (dvd_trans' hm (pw_pos' (A_pos _) _) (smooth_self hm)
      (pw_dvd_base _ (A_pos _) (A_dvd_mono ((succ_monus_succ _ _).eqTrans h))))
    (pw_dvd_exp (A_pos _) h)

end LeanProofs.IPRA.AnalyticNumberTheory.Smooth

export_ipra AnalyticNumberTheory.Smooth (pw_dvd_base)
