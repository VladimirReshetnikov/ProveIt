import IPRADerivations.Core.Permutation
import IPRADerivations.AnalyticNumberTheory.Totient
import IPRADerivations.DiophantineNumberTheory.FLTMultiples

/-!
# Euler's theorem

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:euler`:
if `n > 0` and `gcd(a, n) = 1`, then `a^{φ(n)} ≡ 1 (mod n)`.

As in the paper, multiplication by `a` modulo `n` permutes the residues `[0, n)`, with
inverse multiplication by a Bézout inverse `b` of `a`. With `h(j) = j` for `j` coprime to `n`
and `h(j) = 1` otherwise, and `P = ∏_{j<n} h(j)`:

* `∏_{i<n} h(a i mod n) = P` (`Permutation.prod_perm`);
* `h(a i mod n) ≡ a^{[gcd(i, n) = 1]} h(i) (mod n)`, so `∏_{i<n} h(a i mod n) ≡ a^{φ(n)} P`;
* `gcd(n, P) = 1`, so cancelling `P` gives `a^{φ(n)} ≡ 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Euler

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos rem_eq_of_eq dvd_of_rem_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot quo_eq pred_lt)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Coprimality modulo `n ≥ 2` -/

section Coprime

variable {N : PTm n} (hN : Γ ⊢[PRAAx] le two N)
include hN

theorem N_pos : Γ ⊢[PRAAx] N ≐ succ (pred N) :=
  AnalyticNumberTheory.Primes.eq_succ_pred (y := succ (monus N two))
    ((eq_add_of_le hN).eqTrans (by ipra_ring))

/-- `gcd(0, N) ≠ 1`, and `gcd(N, 0) ≠ 1`. -/
theorem not_one_zero (φ : Fm PTm n) (h : Γ ⊢[PRAAx] gcd zero N ≐ one ⋎ (gcd N zero ≐ one)) :
    Γ ⊢[PRAAx] φ := by
  have hp := N_pos hN
  have d₀ : Γ ⊢[PRAAx] dvd N zero := dvd_of_eq' hp (w := zero) (mul_zero _).eqSymm
  have d₁ := dvd_self' hp
  have n1 : Γ ⊢[PRAAx] neg (N ≐ one) := .impI (lt_irrefl one _ (le_congr (.eqRefl _) Prf.hyp0 hN.wk))
  refine .orE h ?_ ?_
  · exact .botE _ (.impE n1.wk (eq_one_of_dvd_one hp.wk (dvd_congr Prf.hyp0 (gcd_greatest' hp.wk d₀.wk d₁.wk))))
  · exact .botE _ (.impE n1.wk (eq_one_of_dvd_one hp.wk (dvd_congr Prf.hyp0 (gcd_greatest' hp.wk d₁.wk d₀.wk))))

theorem pos_of_cop {x : PTm n} (h : Γ ⊢[PRAAx] gcd x N ≐ one) : Γ ⊢[PRAAx] x ≐ succ (pred x) := by
  refine .orE (zero_or_succ x) ?_ Prf.hyp0
  exact not_one_zero hN.wk _ (.orI₁ ((congrGcd Prf.hyp0.eqSymm (.eqRefl _)).eqTrans h.wk))

theorem cop_comm {x : PTm n} (h : Γ ⊢[PRAAx] gcd x N ≐ one) : Γ ⊢[PRAAx] gcd N x ≐ one :=
  gcd_comm_one (N_pos hN) h

theorem cop_comm' {x : PTm n} (h : Γ ⊢[PRAAx] gcd N x ≐ one) : Γ ⊢[PRAAx] gcd x N ≐ one := by
  refine .orE (zero_or_succ x) ?_ (gcd_comm_one Prf.hyp0 h.wk)
  exact not_one_zero hN.wk _ (.orI₂ ((congrGcd (.eqRefl _) Prf.hyp0.eqSymm).eqTrans h.wk))

/-- `y = N q + r` relates the common divisors of `(y, N)` and `(r, N)`. -/
theorem rem_decomp (y : PTm n) : Γ ⊢[PRAAx] y ≐ N * quo y N + rem y N :=
  Prf.andE₁ (div_mod_at (x := y) (N_pos hN))

theorem cop_rem {y : PTm n} (h : Γ ⊢[PRAAx] gcd y N ≐ one) : Γ ⊢[PRAAx] gcd (rem y N) N ≐ one := by
  have hp := N_pos hN
  refine cop_comm' hN ?_
  have hd := gcd_pos (B := rem y N) hp
  have hdd := gcd_dvd' (b := rem y N) hp
  have dy := dvd_congr (rem_decomp hN y).eqSymm (dvd_add' hd (dvd_mul' hd _ (Prf.andE₁ hdd)) (Prf.andE₂ hdd))
  exact eq_one_of_dvd_one hd (dvd_congr (cop_comm hN h) (gcd_greatest' hd (Prf.andE₁ hdd) dy))

theorem cop_of_rem {y : PTm n} (h : Γ ⊢[PRAAx] gcd (rem y N) N ≐ one) : Γ ⊢[PRAAx] gcd y N ≐ one := by
  have hp := N_pos hN
  refine cop_comm' hN ?_
  have hd := gcd_pos (B := y) hp
  have hdd := gcd_dvd' (b := y) hp
  have dr := dvd_sub' hd (dvd_congr ((rem_decomp hN y).eqTrans (add_comm _ _)) (Prf.andE₂ hdd))
    (dvd_mul' hd _ (Prf.andE₁ hdd))
  exact eq_one_of_dvd_one hd (dvd_congr (cop_comm hN h) (gcd_greatest' hd (Prf.andE₁ hdd) dr))

theorem cop_mul {a i : PTm n} (ha : Γ ⊢[PRAAx] gcd a N ≐ one) (hi : Γ ⊢[PRAAx] gcd i N ≐ one) :
    Γ ⊢[PRAAx] gcd (a * i) N ≐ one :=
  cop_comm' hN (coprime_mul (N_pos hN) (cop_comm hN ha) (cop_comm hN hi))

theorem cop_of_mul {a i : PTm n} (h : Γ ⊢[PRAAx] gcd (a * i) N ≐ one) : Γ ⊢[PRAAx] gcd i N ≐ one := by
  have hp := N_pos hN
  refine cop_comm' hN ?_
  have hd := gcd_pos (B := i) hp
  have hdd := gcd_dvd' (b := i) hp
  have dai := dvd_congr (mul_comm _ _) (dvd_mul' hd a (Prf.andE₂ hdd))
  exact eq_one_of_dvd_one hd (dvd_congr (cop_comm hN h) (gcd_greatest' hd (Prf.andE₁ hdd) dai))

/-- `rem (rem y N) N = rem y N`. -/
theorem rem_rem (y : PTm n) : Γ ⊢[PRAAx] rem (rem y N) N ≐ rem y N :=
  rem_eq_of_eq (N_pos hN) (k₁ := quo y N) (k₂ := zero) (by
    refine withEq (rem_decomp hN y) fun e => ?_
    ipra_lc -e)

/-- `rem j N = j` for `j < N`. -/
theorem rem_small {j : PTm n} (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] rem j N ≐ j := by
  have hp := N_pos hN
  exact (congrAp2 remF (.eqRefl _) hp).eqTrans (Prf.andE₂ (div_mod_unique (q := zero)
    ((by ipra_ring) : Γ ⊢[PRAAx] j ≐ succ (pred N) * zero + j)
    (lt_congr (.eqRefl _) hp hj)))

theorem rem_lt (y : PTm n) : Γ ⊢[PRAAx] lt (rem y N) N := by
  have hp := N_pos hN
  exact lt_congr (congrAp2 remF (.eqRefl _) hp.eqSymm) hp.eqSymm (Prf.andE₂ (div_mod y (pred N)))

end Coprime

/-! ## Bodies over `0 = y`, `1 = a`, `2 = n`, read from the pair `x = ⟨a, n⟩` -/

/-- A body over `(y, a, n)` as a body over `(y, ⟨a, n⟩)`. -/
def lift3 (b : PTm 3) : PTm 2 := Syn.subst ![var 0, fstT (var 1), sndT (var 1)] b

theorem inst2_lift3 (b : PTm 3) (y x : PTm n) : inst2 (lift3 b) y x = inst3 b y (fstT x) (sndT x) := by
  simp only [inst2, inst3, lift3, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

theorem at_pair (b : PTm 3) (y a N : PTm n) : Γ ⊢[PRAAx] inst2 (lift3 b) y (pairT a N) ≐ inst3 b y a N := by
  rw [inst2_lift3]; exact congrInst3 b (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

/-- `[gcd(y, n) = 1]`. -/
abbrev e3 : PTm 3 := eqb (gcd (var 0) (var 2)) one
/-- `h(y)`. -/
abbrev h3 : PTm 3 := e3 * var 0 + monus one e3
/-- `σ(y) = a y mod n`. -/
abbrev s3 : PTm 3 := rem (var 1 * var 0) (var 2)
/-- `τ(y) = b y mod n`, for `b` over `0 = a`, `1 = n`. -/
def t3 (b : PTm 2) : PTm 3 := rem (Syn.subst ![var 1, var 2] b * var 0) (var 2)
/-- `a^{[gcd(y, n) = 1]}`. -/
abbrev q3 : PTm 3 := pw (var 1) e3

/-- `h(y)` evaluated. -/
abbrev hv (y N : PTm n) : PTm n := eqb (gcd y N) one * y + monus one (eqb (gcd y N) one)

theorem inst3_e (y a N : PTm n) : inst3 e3 y a N = eqb (gcd y N) one := by
  simp only [inst3, subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
theorem inst3_h (y a N : PTm n) : inst3 h3 y a N = hv y N := by
  simp only [inst3, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_eqb, subst_ex2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]
theorem inst3_s (y a N : PTm n) : inst3 s3 y a N = rem (a * y) N := by
  simp [inst3]
theorem inst3_t (b : PTm 2) (y a N : PTm n) : inst3 (t3 b) y a N = rem (inst2 b a N * y) N := by
  simp only [inst3, t3, inst2, subst_ap2, PTm.subst_mul, Syn.subst_subst, Syn.subst_var]
  congr 3; funext k; fin_cases k <;> rfl
theorem inst3_q (y a N : PTm n) : inst3 q3 y a N = pw a (eqb (gcd y N) one) := by
  simp only [inst3, subst_ap2, subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem hv_of_cop {y N : PTm n} (h : Γ ⊢[PRAAx] gcd y N ≐ one) : Γ ⊢[PRAAx] hv y N ≐ y := by
  have e := eqb_of_eq h
  have m := (congrMonus (Γ := Γ) (.eqRefl one) e).eqTrans (monus_self _)
  refine withEq e fun h₁ => withEq m fun h₂ => ?_
  apply deriveNat; ipra_simps; rw [h₁, h₂]; ring

theorem hv_of_ncop {y N : PTm n} (h : Γ ⊢[PRAAx] neg (gcd y N ≐ one)) : Γ ⊢[PRAAx] hv y N ≐ one := by
  have e := eqb_of_ne h
  have m := (congrMonus (Γ := Γ) (.eqRefl one) e).eqTrans (monus_zero _)
  refine withEq e fun h₁ => withEq m fun h₂ => ?_
  apply deriveNat; ipra_simps; rw [h₁, h₂]; ring

/-! ## The permutation -/

/-- `rem (a · rem y N) N = rem (a y) N`. -/
theorem rem_mul_rem {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) (c y : PTm n) : Γ ⊢[PRAAx] rem (c * rem y N) N ≐ rem (c * y) N :=
  (congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans ((rem_mul_congr c (N_pos hN) (rem_rem hN y)).eqTrans
    (congrAp2 remF (mul_comm _ _) (.eqRefl _)))

section Perm

variable {a N : PTm n} {b : PTm 2} (hN : Γ ⊢[PRAAx] le two N)
  (hb : Γ ⊢[PRAAx] rem (a * inst2 b a N) N ≐ rem one N)
include hN hb

/-- `σ(τ(j)) = j` and `τ(σ(j)) = j` for `j < N`. -/
theorem sigma_tau {j : PTm n} (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] rem (a * rem (inst2 b a N * j) N) N ≐ j := by
  refine (rem_mul_rem hN _ _).eqTrans ?_
  have e : Γ ⊢[PRAAx] rem ((a * inst2 b a N) * j) N ≐ rem (one * j) N := rem_mul_congr j (N_pos hN) hb
  exact (congrAp2 remF (mul_assoc _ _ _).eqSymm (.eqRefl _)).eqTrans (e.eqTrans
    ((congrAp2 remF (one_mul _) (.eqRefl _)).eqTrans (rem_small hN hj)))

theorem tau_sigma {j : PTm n} (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] rem (inst2 b a N * rem (a * j) N) N ≐ j := by
  refine (rem_mul_rem hN _ _).eqTrans ?_
  have e : Γ ⊢[PRAAx] rem ((a * inst2 b a N) * j) N ≐ rem (one * j) N := rem_mul_congr j (N_pos hN) hb
  exact (congrAp2 remF ((mul_assoc _ _ _).eqSymm.eqTrans (congrMul (mul_comm _ _) (.eqRefl _))) (.eqRefl _)).eqTrans
    (e.eqTrans ((congrAp2 remF (one_mul _) (.eqRefl _)).eqTrans (rem_small hN hj)))

end Perm

/-! ## Products: congruence modulo `M`, products of products, products of powers -/

theorem prod_rem_congr (f g : PTm 2) {x N M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 g (var 0) (Syn.shift x)) (Syn.shift M)))) :
    Γ ⊢[PRAAx] rem (ap2 (prodF f) N x) M ≐ rem (ap2 (prodF g) N x) M :=
  Foundations.ChineseRemainder.rem_prod_congr f g hM h

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev prodMul1F (f g : PTm 2) : Fm PTm 2 :=
  ap2 (prodF (f * g)) (var 0) (var 1) ≐ ap2 (prodF f) (var 0) (var 1) * ap2 (prodF g) (var 0) (var 1)

private theorem prod_mul1₀ (f g : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] prodMul1F f g :=
  prod_mul_body f g (var 0) (var 1)

theorem prod_mul1 (f g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (f * g)) N x ≐ ap2 (prodF f) N x * ap2 (prodF g) N x := by
  simpa using inst (Γ := Γ) (prod_mul1₀ f g) (![N, x] : Fin 2 → PTm n)

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev prodPwF (e : PTm 2) : Fm PTm 2 :=
  ap2 (prodF (pw (fstT (var 1)) e)) (var 0) (var 1) ≐ pw (fstT (var 1)) (ap2 (sumF e) (var 0) (var 1))

private theorem prod_pw₀ (e : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] prodPwF e := by
  ipra_ind [subst_ap2, subst_fstT]
  · exact (prod_zero _ _).eqTrans ((pw_zero _).eqSymm.eqTrans (congrAp2 powF (sum_zero _ _).eqSymm (.eqRefl _)))
  · refine (prod_succ _ (var 0) _).eqTrans ?_
    have ee : Syn.subst (![var 0, var 1] : Fin 2 → PTm 2) (pw (fstT (var 1)) e) = pw (fstT (var 1)) (Syn.subst (![var 0, var 1] : Fin 2 → PTm 2) e) := by
      simp
    rw [ee]
    refine (congrMul Prf.hyp0 (.eqRefl _)).eqTrans ((pw_add _ _ _).eqSymm.eqTrans ?_)
    exact congrAp2 powF (sum_succ _ _ _).eqSymm (.eqRefl _)

theorem prod_pw (e : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (pw (fstT (var 1)) e)) N x ≐ pw (fstT x) (ap2 (sumF e) N x) := by
  have h := inst (Γ := Γ) (prod_pw₀ e) (![N, x] : Fin 2 → PTm n)
  simpa using h

/-! ## Euler's theorem -/

alias congrEqb := Common.congrEqb

theorem congrHv {y y' N : PTm n} (h : Γ ⊢[PRAAx] y ≐ y') : Γ ⊢[PRAAx] hv y N ≐ hv y' N := by
  have e := congrEqb (congrGcd h (.eqRefl N)) (.eqRefl one)
  exact congrAdd (congrMul e h) (congrMonus (.eqRefl _) e)

theorem shift_le_two {N : PTm n} (hN : Γ ⊢[PRAAx] le two N) : Γ.map Fm.shift ⊢[PRAAx] le two (Syn.shift N) := by
  have e := hN.shift
  simp only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact e

theorem shift_cop {a N : PTm n} (h : Γ ⊢[PRAAx] gcd a N ≐ one) :
    Γ.map Fm.shift ⊢[PRAAx] gcd (Syn.shift a) (Syn.shift N) ≐ one := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_ex2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact e

theorem shift_inv {a N : PTm n} {b : PTm 2} (h : Γ ⊢[PRAAx] rem (a * inst2 b a N) N ≐ rem one N) :
    Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift a * inst2 b (Syn.shift a) (Syn.shift N)) (Syn.shift N) ≐
      rem one (Syn.shift N) := by
  have e := h.shift
  simp only [Fm.shift, Fm.subst_eq, subst_ap2, PTm.subst_mul, subst_inst2, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at e
  exact e

theorem shift_pair (a N : PTm n) : Syn.shift (pairT a N) = pairT (Syn.shift a) (Syn.shift N) := by
  simp [Syn.shift]

/-- The pointwise congruence `h(a i mod N) ≡ a^{[gcd(i, N) = 1]} h(i)`. -/
theorem pointwise {a N i : PTm n} (hN : Γ ⊢[PRAAx] le two N) (ha : Γ ⊢[PRAAx] gcd a N ≐ one) :
    Γ ⊢[PRAAx] rem (inst2 (Permutation.FS (lift3 h3) (lift3 s3)) i (pairT a N)) N ≐
      rem (inst2 (lift3 q3 * lift3 h3) i (pairT a N)) N := by
  rw [Permutation.inst2_FS]
  have l₁ : Γ ⊢[PRAAx] inst2 (lift3 h3) (inst2 (lift3 s3) i (pairT a N)) (pairT a N) ≐ hv (rem (a * i) N) N := by
    refine (at_pair h3 _ _ _).eqTrans ?_
    rw [inst3_h]
    exact congrHv ((at_pair s3 _ _ _).eqTrans (by rw [inst3_s]; exact .eqRefl _))
  have l₂ : Γ ⊢[PRAAx] inst2 (lift3 q3 * lift3 h3) i (pairT a N) ≐ pw a (eqb (gcd i N) one) * hv i N := by
    have e : inst2 (lift3 q3 * lift3 h3) i (pairT a N) = inst2 (lift3 q3) i (pairT a N) * inst2 (lift3 h3) i (pairT a N) := by
      simp [inst2]
    rw [e]
    refine congrMul ((at_pair q3 _ _ _).eqTrans ?_) ((at_pair h3 _ _ _).eqTrans ?_)
    · rw [inst3_q]; exact .eqRefl _
    · rw [inst3_h]; exact .eqRefl _
  refine (congrAp2 remF l₁ (.eqRefl _)).eqTrans (.eqTrans ?_ (congrAp2 remF l₂ (.eqRefl _)).eqSymm)
  refine .orE (eq_or_ne (gcd i N) one) ?_ ?_
  · have c := cop_rem (y := a * i) hN.wk (cop_mul (i := i) hN.wk ha.wk (Prf.hyp0 : ((gcd i N ≐ one) :: Γ) ⊢[PRAAx] _))
    refine (congrAp2 remF (hv_of_cop c) (.eqRefl _)).eqTrans ((rem_rem hN.wk _).eqTrans ?_)
    refine congrAp2 remF ?_ (.eqRefl _)
    exact (congrMul ((congrAp2 powF (eqb_of_eq Prf.hyp0) (.eqRefl _)).eqTrans (pw_one _)) (hv_of_cop Prf.hyp0)).eqSymm
  · have nc : (neg (gcd i N ≐ one) :: Γ) ⊢[PRAAx] neg (gcd (rem (a * i) N) N ≐ one) :=
      .impI (.impE Prf.hyp1 (cop_of_mul hN.wk.wk (cop_of_rem hN.wk.wk Prf.hyp0)))
    refine congrAp2 remF ((hv_of_ncop nc).eqTrans ?_) (.eqRefl _)
    exact ((one_mul _).eqSymm.eqTrans (congrMul ((congrAp2 powF (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans
      (pw_zero _)).eqSymm (hv_of_ncop Prf.hyp0).eqSymm))

/-- `gcd(N, ∏_{j<M} h(j)) = 1`. -/
theorem cop_prod {a N : PTm n} (hN : Γ ⊢[PRAAx] le two N) (M : PTm n) :
    Γ ⊢[PRAAx] gcd N (ap2 (prodF (lift3 h3)) M (pairT a N)) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (gcd (Syn.shift N) (ap2 (prodF (lift3 h3)) (var 0)
      (pairT (Syn.shift a) (Syn.shift N))) ≐ one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ex2, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have hp := N_pos hN
      refine (congrGcd (.eqRefl _) (prod_zero _ _)).eqTrans ?_
      exact eq_one_of_dvd_one (gcd_pos (B := one) hp) (Prf.andE₂ (gcd_dvd' (b := one) hp))
    · simp only [Fm.subst_eq, subst_ex2, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      have hN' := (shift_le_two hN).wk (ψ := gcd (Syn.shift N) (ap2 (prodF (lift3 h3)) (var 0)
        (pairT (Syn.shift a) (Syn.shift N))) ≐ one)
      have hp := N_pos hN'
      refine (congrGcd (.eqRefl _) (prod_succ _ _ _)).eqTrans (coprime_mul hp Prf.hyp0 ?_)
      have e : Syn.subst ![var 0, pairT (Syn.shift a) (Syn.shift N)] (lift3 h3) =
        inst2 (lift3 h3) (var 0) (pairT (Syn.shift a) (Syn.shift N)) := rfl
      rw [e]
      refine (congrGcd (.eqRefl _) ((at_pair h3 _ _ _).eqTrans (by rw [inst3_h]; exact .eqRefl _))).eqTrans ?_
      refine .orE (eq_or_ne (gcd (var 0) (Syn.shift N)) one) ?_ ?_
      · exact (congrGcd (.eqRefl _) (hv_of_cop Prf.hyp0)).eqTrans (cop_comm hN'.wk Prf.hyp0)
      · refine (congrGcd (.eqRefl _) (hv_of_ncop Prf.hyp0)).eqTrans ?_
        exact eq_one_of_dvd_one (gcd_pos (B := one) hp.wk) (Prf.andE₂ (gcd_dvd' (b := one) hp.wk))
  have h := Prf.allE M hall
  simp only [Fm.subst_eq, subst_ex2, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

/-- Euler's theorem for `N ≥ 2`, given an inverse `b` of `a` modulo `N`. -/
theorem euler_core {a N : PTm n} {b : PTm 2} (hN : Γ ⊢[PRAAx] le two N) (ha : Γ ⊢[PRAAx] gcd a N ≐ one)
    (hb : Γ ⊢[PRAAx] rem (a * inst2 b a N) N ≐ rem one N) :
    Γ ⊢[PRAAx] rem (pw a (phi N)) N ≐ rem one N := by
  have hp := N_pos hN
  have hN' := shift_le_two hN
  have hb' := shift_inv hb
  -- The permutation hypotheses.
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll (lift3 s3) N (pairT a N) := by
    refine .allI ?_
    rw [shift_pair]
    refine lt_congr (at_pair s3 _ _ _).eqSymm (.eqRefl _) ?_
    rw [inst3_s]; exact rem_lt hN' _
  have hinv : Γ ⊢[PRAAx] Permutation.invAll (lift3 s3) (lift3 (t3 b)) N (pairT a N) := by
    refine .allI (.impI (.andI ?_ ?_))
    · rw [shift_pair]
      refine lt_congr (at_pair (t3 b) _ _ _).eqSymm (.eqRefl _) ?_
      rw [inst3_t]; exact rem_lt hN'.wk _
    · rw [shift_pair]
      refine (at_pair s3 _ _ _).eqTrans ?_
      rw [inst3_s]
      refine (congrAp2 remF (congrMul (.eqRefl _) (at_pair (t3 b) _ _ _)) (.eqRefl _)).eqTrans ?_
      rw [inst3_t]
      exact sigma_tau hN'.wk hb'.wk Prf.hyp0
  have hret : Γ ⊢[PRAAx] Permutation.retAll (lift3 s3) (lift3 (t3 b)) N (pairT a N) := by
    refine .allI (.impI ?_)
    rw [shift_pair]
    refine (at_pair (t3 b) _ _ _).eqTrans ?_
    rw [inst3_t]
    refine (congrAp2 remF (congrMul (.eqRefl _) (at_pair s3 _ _ _)) (.eqRefl _)).eqTrans ?_
    rw [inst3_s]
    exact tau_sigma hN'.wk hb'.wk Prf.hyp0
  have hperm := Permutation.prod_perm (F := lift3 h3) hr hinv hret
  -- `∏ h(σ i) ≡ a^{φ(N)} P`.
  have hcong := prod_rem_congr (Permutation.FS (lift3 h3) (lift3 s3)) (lift3 q3 * lift3 h3)
    (x := pairT a N) (N := N) hp (.allI (.impI (by
      rw [shift_pair]
      exact pointwise hN'.wk (shift_cop ha).wk)))
  have hsplit := prod_mul1 (Γ := Γ) (lift3 q3) (lift3 h3) N (pairT a N)
  have hq : lift3 q3 = pw (fstT (var 1)) (lift3 e3) := by simp [lift3]
  have hpw := prod_pw (Γ := Γ) (lift3 e3) N (pairT a N)
  rw [← hq] at hpw
  have hphi : Γ ⊢[PRAAx] ap2 (sumF (lift3 e3)) N (pairT a N) ≐ phi N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pair]
    refine (at_pair e3 _ _ _).eqTrans ?_
    rw [inst3_e, inst2_tot]
    exact .eqRefl _
  have hA : Γ ⊢[PRAAx] pw (fstT (pairT a N)) (ap2 (sumF (lift3 e3)) N (pairT a N)) ≐ pw a (phi N) :=
    congrAp2 powF hphi (fst_pair _ _)
  -- `rem P N = rem (A P) N`.
  have key : Γ ⊢[PRAAx] rem (ap2 (prodF (lift3 h3)) N (pairT a N)) N ≐
      rem (pw a (phi N) * ap2 (prodF (lift3 h3)) N (pairT a N)) N :=
    (congrAp2 remF hperm.eqSymm (.eqRefl _)).eqTrans (hcong.eqTrans (congrAp2 remF (hsplit.eqTrans
      (congrMul (hpw.eqTrans hA) (.eqRefl _))) (.eqRefl _)))
  -- Cancel `P`.
  have hapos := pos_of_cop hN ha
  have hApos : Γ ⊢[PRAAx] pw a (phi N) ≐ succ (pred (pw a (phi N))) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := pred (pw (succ (pred a)) (phi N)))
      ((congrAp2 powF (.eqRefl _) hapos).eqTrans (DiophantineNumberTheory.FLTMultiples.pw_pos _ _))
  have key' : Γ ⊢[PRAAx] rem (ap2 (prodF (lift3 h3)) N (pairT a N)) (succ (pred N)) ≐
      rem (ap2 (prodF (lift3 h3)) N (pairT a N) + ap2 (prodF (lift3 h3)) N (pairT a N) * pred (pw a (phi N)))
        (succ (pred N)) := by
    refine (congrAp2 remF (.eqRefl _) hp.eqSymm).eqTrans (key.eqTrans ((congrAp2 remF ?_ hp)))
    refine withEq hApos fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  have d := dvd_congr_left hp.eqSymm (dvd_of_rem_eq key')
  have dA := gauss hp (cop_prod hN N) d
  refine rem_eq_of_eq hp (k₁ := zero) (k₂ := quo (pred (pw a (phi N))) N) ?_
  refine withEq hApos fun e₁ => withEq (eq_of_dvd' hp dA) fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [e₁]; linear_combination e₂

/-- `rem z 1 = 0`. -/
theorem rem_one (z : PTm n) : Γ ⊢[PRAAx] rem z one ≐ zero :=
  Prf.andE₂ (div_mod_unique (K' := zero) (q := z) (r := zero)
    ((add_zero _).eqSymm.eqTrans (congrAdd (one_mul _).eqSymm (.eqRefl _))) (zero_lt_succ _))

/-- The Bézout inverse, in the two cases; over `0 = a`, `1 = n`. -/
abbrev b₁ : PTm 2 := Bezout.cur one zero (succ (var 1)) (var 0) (var 1)
abbrev b₂ : PTm 2 := pred (var 1) * b₁

theorem inst2_b₁ (a N : PTm n) : inst2 b₁ a N = Bezout.cur one zero (succ N) a N := by
  simp only [inst2, Bezout.subst_cur, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    ConciseIPRA.PTm.subst_succ]
theorem inst2_b₂ (a N : PTm n) : inst2 b₂ a N = pred N * Bezout.cur one zero (succ N) a N := by
  simp only [inst2, PTm.subst_mul, PTm.subst_pred, Bezout.subst_cur, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ]

/-- `thm:euler` at arbitrary terms. -/
theorem euler_at {a N : PTm n} (ha : Γ ⊢[PRAAx] gcd a N ≐ one) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] rem (pw a (phi N)) N ≐ rem one N := by
  refine .orE (zero_or_succ (pred N)) ?_ ?_
  · -- `N = 1`.
    have e : ((pred N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ one := hN.wk.eqTrans (congrSucc Prf.hyp0)
    exact (congrAp2 remF (.eqRefl _) e).eqTrans ((rem_one _).eqTrans ((rem_one _).eqSymm.eqTrans
      (congrAp2 remF (.eqRefl _) e.eqSymm)))
  · have h2 : ((pred N ≐ succ (pred (pred N))) :: Γ) ⊢[PRAAx] le two N :=
      le_of_eq_add (d := pred (pred N)) (hN.wk.eqTrans ((congrSucc Prf.hyp0).eqTrans
        (by ipra_ring)))
    have hg := ha.wk (ψ := pred N ≐ succ (pred (pred N)))
    refine .orE (bezout_at a N) ?_ ?_
    · refine euler_core (b := b₁) h2.wk hg.wk ?_
      rw [inst2_b₁]
      refine rem_eq_of_eq hN.wk.wk (k₁ := zero) (k₂ := Bezout.cur zero one (succ N) a N) ?_
      refine withEq Prf.hyp0 fun e₁ => withEq hg.wk fun e₂ => ?_
      apply deriveNat; ipra_simps; rw [e₂] at e₁; linear_combination -e₁
    · refine euler_core (b := b₂) h2.wk hg.wk ?_
      rw [inst2_b₂]
      refine rem_eq_of_eq hN.wk.wk (k₁ := one) (k₂ := pred N * Bezout.cur zero one (succ N) a N) ?_
      refine withEq Prf.hyp0 fun e₁ => withEq hg.wk fun e₂ => withEq hN.wk.wk fun e₃ => ?_
      apply deriveNat; ipra_simps; rw [e₂] at e₁
      linear_combination Groth.ι (Q.mk _ (pred N)) * e₁ + e₃

/-- `thm:euler`: `gcd(a, n) = 1 → n ≥ 1 → a^{φ(n)} ≡ 1 (mod n)`; variables `0 = a`, `1 = n`. -/
abbrev eulerFormula : Fm PTm 2 :=
  gcd (var 0) (var 1) ≐ one ⟶ (var 1 ≐ succ (pred (var 1))) ⟶
    rem (pw (var 0) (phi (var 1))) (var 1) ≐ rem one (var 1)

theorem euler : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 eulerFormula :=
  closeUniv 2 (.impI (.impI (euler_at Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.AnalyticNumberTheory.Euler

export_ipra AnalyticNumberTheory.Euler (euler_at rem_lt)
