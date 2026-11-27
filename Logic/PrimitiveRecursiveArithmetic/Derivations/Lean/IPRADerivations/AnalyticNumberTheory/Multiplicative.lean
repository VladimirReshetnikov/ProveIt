import IPRADerivations.AnalyticNumberTheory.SumPhi

/-!
# Multiplicativity of the totient

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:phi-product`
(first part): `gcd(m, n) = 1 → φ(mn) = φ(m) φ(n)`.

With `e_m(a) = [gcd(a, m) = 1]`:

* `block_sum`: `∑_{j<mn} e_m(j mod m) e_n(j div m) = φ(m) φ(n)`, from the closed form at an
  arbitrary bound `K` (induction on `K`, `block_step`);
* the CRT map `σ(k) = (k mod m) + m (k mod n)` sends `[0, mn)` into itself, every `j < mn` is hit
  (`Foundations.ChineseRemainder.crt_exists_at`), and the fiber counts add up to `mn`
  (`SumPhi.sum_fiber` with `f = 1`), so each fiber has exactly one element (`all_one`);
* `e_m(k mod m) e_n(k mod n) = e_{mn}(k)` pointwise, and `SumPhi.sum_fiber` transports the sum.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq eqb_iff shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Division by a positive modulus -/

theorem rem_lt' {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (y : PTm n) : Γ ⊢[PRAAx] lt (rem y M) M :=
  lt_congr (congrAp2 remF (.eqRefl _) hM.eqSymm) hM.eqSymm (Prf.andE₂ (div_mod y (pred M)))

theorem rem_eq' {z q r M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hz : Γ ⊢[PRAAx] z ≐ M * q + r)
    (hr : Γ ⊢[PRAAx] lt r M) : Γ ⊢[PRAAx] rem z M ≐ r :=
  (congrAp2 remF (.eqRefl _) hM).eqTrans (Prf.andE₂ (div_mod_unique
    (hz.eqTrans (congrAdd (congrMul hM (.eqRefl _)) (.eqRefl _))) (lt_congr (.eqRefl _) hM hr)))

theorem zero_lt' {M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) : Γ ⊢[PRAAx] lt zero M :=
  lt_congr (.eqRefl _) hM.eqSymm (zero_lt_succ _)

/-! ## Block sums -/

/-- `e_m(j mod m) e_n(j div m)`, over `0 = j`, `1 = m`, `2 = n`. -/
abbrev hB : PTm 3 := eqb (gcd (rem (var 0) (var 1)) (var 1)) one * eqb (gcd (quo (var 0) (var 1)) (var 2)) one

theorem inst3_hB (j m N : PTm n) :
    inst3 hB j m N = eqb (gcd (rem j m) m) one * eqb (gcd (quo j m) N) one := by
  simp only [inst3, PTm.subst_mul, subst_eqb, subst_ex2, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- The closed form `φ(m) ∑_{b<K div m} e_n(b) + e_n(K div m) ∑_{a<K mod m} e_m(a)`. -/
abbrev blockR (K m N : PTm n) : PTm n :=
  phi m * ap2 (sumF totBody) (quo K m) N + eqb (gcd (quo K m) N) one * ap2 (sumF totBody) (rem K m) m

theorem block_zero {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap3 (sum2F hB) zero m N ≐ blockR zero m N := by
  have q₀ : Γ ⊢[PRAAx] quo zero m ≐ zero :=
    quo_eq hm (q := zero) (r := zero) (by ipra_ring) (zero_lt' hm)
  have r₀ : Γ ⊢[PRAAx] rem zero m ≐ zero := rem_zero _
  have s₁ := (congrAp2 (sumF totBody) q₀ (.eqRefl N)).eqTrans (sum_zero (Γ := Γ) _ N)
  have s₂ := (congrAp2 (sumF totBody) r₀ (.eqRefl m)).eqTrans (sum_zero (Γ := Γ) _ m)
  refine (sum2_zero _ _ _).eqTrans ?_
  refine .eqTrans ?_ (congrAdd (congrMul (.eqRefl _) s₁) (congrMul (.eqRefl _) s₂)).eqSymm
  ipra_ring

theorem block_step {K m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (ih : Γ ⊢[PRAAx] ap3 (sum2F hB) K m N ≐ blockR K m N) :
    Γ ⊢[PRAAx] ap3 (sum2F hB) (succ K) m N ≐ blockR (succ K) m N := by
  have hT := (sum2_succ hB K m N).eqTrans (congrAdd ih (.eqRefl _))
  rw [inst3_hB] at hT
  have hd := div_eq (j := K) hm
  have hr := rem_lt' hm K
  have hSm : Γ ⊢[PRAAx] ap2 (sumF totBody) (succ (rem K m)) m ≐
      ap2 (sumF totBody) (rem K m) m + eqb (gcd (rem K m) m) one := by
    have e := sum_succ' (Γ := Γ) totBody (rem K m) m
    rw [inst2_tot] at e; exact e
  have hSn : Γ ⊢[PRAAx] ap2 (sumF totBody) (succ (quo K m)) N ≐
      ap2 (sumF totBody) (quo K m) N + eqb (gcd (quo K m) N) one := by
    have e := sum_succ' (Γ := Γ) totBody (quo K m) N
    rw [inst2_tot] at e; exact e
  refine .orE (lt_or_eq_of_le hr) ?_ ?_
  · -- `K mod m + 1 < m`: same block.
    have hlt : (lt (succ (rem K m)) m :: Γ) ⊢[PRAAx] lt (succ (rem K m)) m := Prf.hyp0
    have hz : (lt (succ (rem K m)) m :: Γ) ⊢[PRAAx] succ K ≐ m * quo K m + succ (rem K m) :=
      withEq hd.wk fun e => by apply deriveNat; ipra_simps; rw [e]; ring
    have rq := quo_eq hm.wk hz hlt
    have rr := rem_eq' hm.wk hz hlt
    have e₁ : (lt (succ (rem K m)) m :: Γ) ⊢[PRAAx] blockR (succ K) m N ≐
        phi m * ap2 (sumF totBody) (quo K m) N + eqb (gcd (quo K m) N) one *
          (ap2 (sumF totBody) (rem K m) m + eqb (gcd (rem K m) m) one) :=
      congrAdd (congrMul (.eqRefl _) (congrAp2 (sumF totBody) rq (.eqRefl _)))
        (congrMul (congrEqb (congrGcd rq (.eqRefl _)) (.eqRefl _))
          ((congrAp2 (sumF totBody) rr (.eqRefl _)).eqTrans hSm.wk))
    refine hT.wk.eqTrans (.eqTrans ?_ e₁.eqSymm)
    ipra_ring
  · -- `K mod m + 1 = m`: the next block starts.
    have heq : ((succ (rem K m) ≐ m) :: Γ) ⊢[PRAAx] succ (rem K m) ≐ m := Prf.hyp0
    have hz : ((succ (rem K m) ≐ m) :: Γ) ⊢[PRAAx] succ K ≐ m * succ (quo K m) + zero :=
      withEq hd.wk fun e₁ => withEq heq fun e₂ => by
        apply deriveNat; ipra_simps; rw [e₁]; linear_combination e₂
    have rq := quo_eq hm.wk hz (zero_lt' hm.wk)
    have rr := rem_eq' hm.wk hz (zero_lt' hm.wk)
    have hφ : ((succ (rem K m) ≐ m) :: Γ) ⊢[PRAAx] phi m ≐
        ap2 (sumF totBody) (rem K m) m + eqb (gcd (rem K m) m) one :=
      (congrAp2 (sumF totBody) heq.eqSymm (.eqRefl _)).eqTrans hSm.wk
    have e₁ : ((succ (rem K m) ≐ m) :: Γ) ⊢[PRAAx] blockR (succ K) m N ≐
        phi m * (ap2 (sumF totBody) (quo K m) N + eqb (gcd (quo K m) N) one) +
          eqb (gcd (quo (succ K) m) N) one * zero :=
      congrAdd (congrMul (.eqRefl _) ((congrAp2 (sumF totBody) rq (.eqRefl _)).eqTrans hSn.wk))
        (congrMul (.eqRefl _) ((congrAp2 (sumF totBody) rr (.eqRefl _)).eqTrans (sum_zero _ _)))
    refine hT.wk.eqTrans (.eqTrans ?_ e₁.eqSymm)
    refine withEq hφ fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring

/-- Variables: `0 = K`, `1 = m`, `2 = n`. -/
private abbrev blockF : Fm PTm 3 :=
  (var 1 ≐ succ (pred (var 1))) ⟶ ap3 (sum2F hB) (var 0) (var 1) (var 2) ≐ blockR (var 0) (var 1) (var 2)

private theorem block₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] blockF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2, subst_ap3, subst_eqb, subst_ex2]
  · exact .impI (block_zero Prf.hyp0)
  · exact .impI (block_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

theorem block_at {K m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap3 (sum2F hB) K m N ≐ blockR K m N := by
  have h := inst (Γ := Γ) block₀ (![K, m, N] : Fin 3 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_ap2, subst_ap3, PTm.subst_add, PTm.subst_mul, PTm.subst_pred,
    subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact .impE h hm

/-- `∑_{j<mn} e_m(j mod m) e_n(j div m) = φ(m) φ(n)`. -/
theorem block_sum {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap3 (sum2F hB) (m * N) m N ≐ phi m * phi N := by
  have hz : Γ ⊢[PRAAx] m * N ≐ m * N + zero := (add_zero _).eqSymm
  have rq := quo_eq hm hz (zero_lt' hm)
  have rr := rem_eq' hm hz (zero_lt' hm)
  refine (block_at hm).eqTrans ?_
  refine (congrAdd (congrMul (.eqRefl _) (congrAp2 (sumF totBody) rq (.eqRefl _)))
    (congrMul (.eqRefl _) ((congrAp2 (sumF totBody) rr (.eqRefl _)).eqTrans (sum_zero _ _)))).eqTrans ?_
  ipra_ring

/-! ## Bridging two-parameter sums to paired sums -/

open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 inst2_lift3 at_pair shift_pair shift_cop)

theorem sum2_lift (f : PTm 3) (N p q : PTm n) :
    Γ ⊢[PRAAx] ap3 (sum2F f) N p q ≐ ap2 (sumF (lift3 f)) N (pairT p q) := by
  refine (sum2_congr_bounded f (Syn.subst ![var 0, var 2] (lift3 f)) p q p (pairT p q) N (.allI (.impI ?_))).eqTrans
    (sum2_eq_sum _ _ _ _)
  have e : inst3 (Syn.subst ![var 0, var 2] (lift3 f)) (var 0 : PTm (n + 1)) (Syn.shift p) (Syn.shift (pairT p q)) =
      inst2 (lift3 f) (var 0) (Syn.shift (pairT p q)) := by
    simp only [inst3, inst2, Syn.subst_subst]
    congr 1; funext k; fin_cases k <;> rfl
  rw [e, shift_pair]
  exact (at_pair f _ _ _).eqSymm

theorem term_le_sum2 (f : PTm 3) {i N p q : PTm n} (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (inst3 f i p q) (ap3 (sum2F f) N p q) :=
  le_congr (at_pair f i p q) (sum2_lift f N p q).eqSymm (term_le_sum (lift3 f) hi)

/-- A sum of `N` terms, each `≥ 1` below `N`, that equals `N` has all terms `= 1`. -/
theorem all_one (c : PTm 2) {N x j : PTm n} (hs : Γ ⊢[PRAAx] ap2 (sumF c) N x ≐ N)
    (hge : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le one (inst2 c (var 0) (Syn.shift x))))
    (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] inst2 c j x ≐ one := by
  have eD : ∀ {k : ℕ} (y z : PTm k), inst2 (monus c one) y z = monus (inst2 c y z) one := by
    intro k y z; simp [inst2]
  have e₁ : ∀ {k : ℕ} (y z : PTm k), inst2 (one : PTm 2) y z = one := by intro k y z; simp [inst2]
  have hpt : Γ ⊢[PRAAx] ap2 (sumF (addBody (monus c one) one)) N x ≐ ap2 (sumF c) N x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, eD, e₁]
    have h := eq_add_of_le (.impE hge.allOpen.wk Prf.hyp0)
    exact (add_comm _ _).eqTrans h.eqSymm
  have hD : Γ ⊢[PRAAx] ap2 (sumF (monus c one)) N x ≐ zero := by
    ipra_lc natEq ((sum_add (monus c one) one N x).eqSymm.eqTrans (hpt.eqTrans hs)) - natEq (sum_ones N x)
  have hz := sum_zero_elim (monus c one) hD hj
  rw [eD] at hz
  have hg := Prf.allE j hge
  simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hg
  exact le_antisymm hz (.impE hg hj)

/-! ## The CRT map -/

/-- `σ(k) = (k mod m) + m (k mod n)`, over `0 = k`, `1 = m`, `2 = n`. -/
abbrev sig3 : PTm 3 := rem (var 0) (var 1) + var 1 * rem (var 0) (var 2)

abbrev crtS : PTm 2 := lift3 sig3
abbrev crtF : PTm 2 := lift3 hB

theorem inst3_sig (k m N : PTm n) : inst3 sig3 k m N = rem k m + m * rem k N := by
  simp only [inst3, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem shift_quo' (a b : PTm n) : Syn.shift (quo a b) = quo (Syn.shift a) (Syn.shift b) := by simp [Syn.shift]

theorem shift_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_lt h

/-- `gcd(k mod m, m) = gcd(k, m)`. -/
theorem gcd_rem {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (k : PTm n) :
    Γ ⊢[PRAAx] gcd (rem k m) m ≐ gcd k m := by
  have hk : Γ ⊢[PRAAx] k ≐ rem k m + m * quo k m := (div_eq hm).eqTrans (add_comm _ _)
  have g₁ := gcd_pos_right (a := rem k m) hm
  have g₂ := gcd_pos_right (a := k) hm
  have d₁ := gcd_dvd_at g₁
  have d₂ := gcd_dvd_at g₂
  refine le_antisymm (dvd_le' g₁ ?_ g₂) (dvd_le' g₂ ?_ g₁)
  · refine gcd_greatest' g₁ (dvd_congr hk.eqSymm (dvd_add' g₁ (Prf.andE₁ d₁) ?_)) (Prf.andE₂ d₁)
    exact dvd_mul' g₁ _ (Prf.andE₂ d₁)
  · exact gcd_greatest' g₂ (dvd_sub' g₂ (dvd_congr hk (Prf.andE₁ d₂)) (dvd_mul' g₂ _ (Prf.andE₂ d₂)))
      (Prf.andE₂ d₂)

section CRT

variable {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
include hm hN

omit hm hN in
theorem sig_eq (k : PTm n) : Γ ⊢[PRAAx] inst2 crtS k (pairT m N) ≐ rem k m + m * rem k N :=
  (at_pair sig3 k m N).eqTrans (by rw [inst3_sig]; exact .eqRefl _)

theorem sig_lt (k : PTm n) : Γ ⊢[PRAAx] lt (rem k m + m * rem k N) (m * N) := by
  refine le_of_eq_add (d := monus m (succ (rem k m)) + m * monus N (succ (rem k N))) ?_
  ipra_lc Groth.ι (Q.mk _ m) * natEq (eq_add_of_le (rem_lt' hN k)) + natEq (eq_add_of_le (rem_lt' hm k))

omit hN in
theorem cop_left {k : PTm n} (h : Γ ⊢[PRAAx] gcd k (m * N) ≐ one) : Γ ⊢[PRAAx] gcd k m ≐ one := by
  have g := gcd_pos_right (a := k) hm
  have d := gcd_dvd_at g
  have dm : Γ ⊢[PRAAx] dvd (gcd k m) (m * N) := dvd_mul' g _ (Prf.andE₂ d)
  exact eq_one_of_dvd_one g (dvd_congr h (gcd_greatest' g (Prf.andE₁ d) dm))

omit hm in
theorem cop_right {k : PTm n} (h : Γ ⊢[PRAAx] gcd k (m * N) ≐ one) : Γ ⊢[PRAAx] gcd k N ≐ one := by
  have g := gcd_pos_right (a := k) hN
  have d := gcd_dvd_at g
  have dm : Γ ⊢[PRAAx] dvd (gcd k N) (m * N) := dvd_congr (mul_comm _ _) (dvd_mul' g _ (Prf.andE₂ d))
  exact eq_one_of_dvd_one g (dvd_congr h (gcd_greatest' g (Prf.andE₁ d) dm))

theorem cop_both {k : PTm n} (h₁ : Γ ⊢[PRAAx] gcd k m ≐ one) (h₂ : Γ ⊢[PRAAx] gcd k N ≐ one) :
    Γ ⊢[PRAAx] gcd k (m * N) ≐ one := by
  have hG := gcd_pos_right (a := k) (pos_mul hm hN)
  have dG := gcd_dvd_at hG
  have hg := gcd_pos (B := m) hG
  have dg := gcd_dvd' (b := m) hG
  have gk := dvd_trans' hg hG (Prf.andE₁ dg) (Prf.andE₁ dG)
  have g1 := eq_one_of_dvd_one hg (dvd_congr h₁ (gcd_greatest' hg gk (Prf.andE₂ dg)))
  have dn := gauss hG g1 (Prf.andE₂ dG)
  exact eq_one_of_dvd_one hG (dvd_congr h₂ (gcd_greatest' hG (Prf.andE₁ dG) dn))

/-- `e_m(k) e_n(k) = e_{mn}(k)`. -/
theorem cop_split (k : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd k m) one * eqb (gcd k N) one ≐ eqb (gcd k (m * N)) one := by
  refine .orE (eq_or_ne (gcd k m) one) ?_ ?_
  · refine .orE (eq_or_ne (gcd k N) one) ?_ ?_
    · refine (congrMul (eqb_of_eq Prf.hyp1) (eqb_of_eq Prf.hyp0)).eqTrans ((one_mul _).eqTrans ?_)
      exact (eqb_of_eq (cop_both hm.wk.wk hN.wk.wk Prf.hyp1 Prf.hyp0)).eqSymm
    · refine (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans ((mul_zero _).eqTrans ?_)
      exact (eqb_of_ne (.impI (.impE Prf.hyp1 (cop_right hN.wk.wk.wk Prf.hyp0)))).eqSymm
  · refine (congrMul (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans ((zero_mul _).eqTrans ?_)
    exact (eqb_of_ne (.impI (.impE Prf.hyp1 (cop_left hm.wk.wk Prf.hyp0)))).eqSymm

/-- `e_{mn}(k) = f(σ(k))` with `f(j) = e_m(j mod m) e_n(j div m)`. -/
theorem point1 (k : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd k (m * N)) one ≐ inst2 (Permutation.FS crtF crtS) k (pairT m N) := by
  rw [Permutation.inst2_FS]
  have hz : Γ ⊢[PRAAx] rem k m + m * rem k N ≐ m * rem k N + rem k m := add_comm _ _
  have rr := rem_eq' hm hz (rem_lt' hm k)
  have rq := quo_eq hm hz (rem_lt' hm k)
  refine (cop_split hm hN k).eqSymm.eqTrans ?_
  refine .eqTrans ?_ (congrInst2 crtF (sig_eq (m := m) (N := N) k).eqSymm (.eqRefl _))
  refine .eqTrans ?_ (at_pair hB _ m N).eqSymm
  rw [inst3_hB]
  refine congrMul ?_ ?_
  · exact congrEqb ((gcd_rem hm k).eqSymm.eqTrans (congrGcd rr.eqSymm (.eqRefl _))) (.eqRefl _)
  · exact congrEqb ((gcd_rem hN k).eqSymm.eqTrans (congrGcd rq.eqSymm (.eqRefl _))) (.eqRefl _)

theorem rem_rem_mul (x : PTm n) :
    Γ ⊢[PRAAx] rem (rem x (m * N)) m ≐ rem x m ⋏ rem (rem x (m * N)) N ≐ rem x N := by
  refine .andI (rem_eq_of_eq hm (k₁ := N * quo x (m * N)) (k₂ := zero) ?_)
    (rem_eq_of_eq hN (k₁ := m * quo x (m * N)) (k₂ := zero) ?_)
  · ipra_lc -natEq (div_eq (j := x) (pos_mul hm hN))
  · ipra_lc -natEq (div_eq (j := x) (pos_mul hm hN))

omit hN in
theorem quo_lt {j : PTm n} (hj : Γ ⊢[PRAAx] lt j (m * N)) : Γ ⊢[PRAAx] lt (quo j m) N := by
  refine .orE (lt_or_le (quo j m) N) Prf.hyp0 ?_
  refine succ_ne_zero' _ (a := m * monus (quo j m) N + rem j m + monus (m * N) (succ j)) ?_
  ipra_lc -Groth.ι (Q.mk _ m) * natEq (eq_add_of_le (Prf.hyp0 : (le N (quo j m) :: Γ) ⊢[PRAAx] le N (quo j m))) -
    natEq ((div_eq (j := j) hm).wk (ψ := le N (quo j m))) - natEq ((eq_add_of_le hj).wk (ψ := le N (quo j m)))

/-- Every `j < mn` has a preimage, given a simultaneous solution `x`. -/
theorem ge_witness {j x r s : PTm n} (hj : Γ ⊢[PRAAx] lt j (m * N)) (hr : Γ ⊢[PRAAx] r ≐ rem j m)
    (hs : Γ ⊢[PRAAx] s ≐ quo j m) (hx : Γ ⊢[PRAAx] rem x m ≐ rem r m ⋏ rem x N ≐ rem s N) :
    Γ ⊢[PRAAx] le one (ap3 (sum2F (Permutation.mB crtS)) (m * N) j (pairT m N)) := by
  have hk := rem_lt' (pos_mul hm hN) x
  have rr := rem_rem_mul hm hN x
  have hr' : Γ ⊢[PRAAx] rem r m ≐ rem j m :=
    (congrAp2 remF hr (.eqRefl _)).eqTrans
      (rem_eq' hm (q := zero) (by ipra_ring) (rem_lt' hm j))
  have hs' : Γ ⊢[PRAAx] rem s N ≐ quo j m :=
    (congrAp2 remF hs (.eqRefl _)).eqTrans
      (rem_eq' hN (q := zero) (by ipra_ring) (quo_lt hm hj))
  have rkm := (Prf.andE₁ rr).eqTrans ((Prf.andE₁ hx).eqTrans hr')
  have rkn := (Prf.andE₂ rr).eqTrans ((Prf.andE₂ hx).eqTrans hs')
  have hσ : Γ ⊢[PRAAx] inst2 crtS (rem x (m * N)) (pairT m N) ≐ j :=
    (sig_eq (m := m) (N := N) _).eqTrans ((congrAdd rkm (congrMul (.eqRefl _) rkn)).eqTrans
      ((add_comm _ _).eqTrans (div_eq hm).eqSymm))
  have t := term_le_sum2 (Permutation.mB crtS) (p := j) (q := pairT m N) hk
  rw [Permutation.inst3_mB] at t
  exact le_congr (eqb_of_eq hσ) (.eqRefl _) t

end CRT

/-! ## Each CRT fiber is a singleton -/

/-- The count `#{k < mn : σ(k) = j}`. -/
abbrev crtC (m N j : PTm n) : PTm n := ap3 (sum2F (Permutation.mB crtS)) (m * N) j (pairT m N)

section Fibers

variable {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
  (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
include hm hN hc

theorem count_ge {j : PTm n} (hj : Γ ⊢[PRAAx] lt j (m * N)) : Γ ⊢[PRAAx] le one (crtC m N j) := by
  have hc' : Γ ⊢[PRAAx] rem (rem j m) (gcd m N) ≐ rem (quo j m) (gcd m N) :=
    (congrAp2 remF (.eqRefl _) hc).eqTrans ((Euler.rem_one _).eqTrans
      ((Euler.rem_one _).eqSymm.eqTrans (congrAp2 remF (.eqRefl _) hc.eqSymm)))
  refine Prf.exE (crt_exists_at hm hN hc') ?_
  have hj' := shift_lt hj
  rw [shift_mul'] at hj'
  have hr : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (rem j m) ≐ rem (Syn.shift j) (Syn.shift m) := by
    rw [shift_rem']; exact .eqRefl _
  have hs : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (quo j m) ≐ quo (Syn.shift j) (Syn.shift m) := by
    rw [shift_quo']; exact .eqRefl _
  have g := ge_witness (x := var 0) (shift_pos hm).wk (shift_pos hN).wk hj'.wk hr.wk hs.wk Prf.hyp0
  have e : Fm.shift (le one (crtC m N j)) = le one (crtC (Syn.shift m) (Syn.shift N) (Syn.shift j)) := by
    simp [Fm.shift, Syn.shift]
  rw [e]; exact g

theorem count_one {j : PTm n} (hj : Γ ⊢[PRAAx] lt j (m * N)) : Γ ⊢[PRAAx] crtC m N j ≐ one := by
  have e₁ : ∀ {k : ℕ} (y z : PTm k), inst2 (one : PTm 2) y z = one := by intro k y z; simp [inst2]
  -- The counts add up to `mn`.
  have eFS : Permutation.FS (one : PTm 2) crtS = one := by simp [Permutation.FS]
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll crtS (m * N) (pairT m N) := by
    refine .allI ?_
    rw [shift_pair, shift_mul']
    exact lt_congr (sig_eq _).eqSymm (.eqRefl _) (sig_lt (shift_pos hm) (shift_pos hN) _)
  have hf := sum_fiber (f := one) hr (m * N)
  rw [eFS] at hf
  have hs := (sum2_lift (cB one crtS) (m * N) (m * N) (pairT m N)).eqSymm.eqTrans
    (hf.eqSymm.eqTrans (sum_ones _ _))
  -- Every count is at least one.
  have hge : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (m * N)) ⟶
      le one (inst2 (lift3 (cB one crtS)) (var 0) (Syn.shift (pairT (m * N) (pairT m N))))) := by
    simp only [shift_pair, shift_mul']
    refine .allI (.impI ?_)
    rw [inst2_lift3, inst3_cB, e₁]
    refine le_congr (.eqRefl _) ((one_mul _).eqTrans (congrAp3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _))).eqSymm ?_
    exact count_ge (shift_pos hm).wk (shift_pos hN).wk (shift_cop hc).wk Prf.hyp0
  have h := all_one (lift3 (cB one crtS)) hs hge hj
  rw [inst2_lift3, inst3_cB, e₁] at h
  exact (congrAp3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqSymm.eqTrans ((one_mul _).eqSymm.eqTrans h)

/-- `φ(mn) = φ(m) φ(n)` for coprime `m, n ≥ 1`. -/
theorem phi_mul_at : Γ ⊢[PRAAx] phi (m * N) ≐ phi m * phi N := by
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll crtS (m * N) (pairT m N) := by
    refine .allI ?_
    rw [shift_pair, shift_mul']
    exact lt_congr (sig_eq _).eqSymm (.eqRefl _) (sig_lt (shift_pos hm) (shift_pos hN) _)
  have s₁ : Γ ⊢[PRAAx] phi (m * N) ≐ ap2 (sumF (Permutation.FS crtF crtS)) (m * N) (pairT m N) := by
    refine sum_congr_bounded _ _ _ _ _ ?_
    simp only [shift_pair, shift_mul']
    refine .allI (.impI ?_)
    rw [inst2_tot]
    exact point1 (shift_pos hm).wk (shift_pos hN).wk _
  have s₂ := sum_fiber (f := crtF) hr (m * N)
  have s₃ : Γ ⊢[PRAAx] ap3 (sum2F (cB crtF crtS)) (m * N) (m * N) (pairT m N) ≐ ap3 (sum2F hB) (m * N) m N := by
    refine sum2_congr_bounded _ _ _ _ _ _ _ ?_
    simp only [shift_pair, shift_mul']
    refine .allI (.impI ?_)
    rw [inst3_cB]
    have c := count_one (j := var 0) (shift_pos hm).wk (shift_pos hN).wk (shift_cop hc).wk Prf.hyp0
    exact (congrMul (at_pair hB _ _ _) c).eqTrans (by ipra_ring)
  exact s₁.eqTrans (s₂.eqTrans (s₃.eqTrans (block_sum hm)))

end Fibers

/-- `thm:phi-product` (multiplicativity): `gcd(m, n) = 1 → φ(mn) = φ(m) φ(n)`;
variables `0 = m − 1`, `1 = n − 1`. -/
abbrev phiMulFormula : Fm PTm 2 :=
  gcd (succ (var 0)) (succ (var 1)) ≐ one ⟶
    phi (succ (var 0) * succ (var 1)) ≐ phi (succ (var 0)) * phi (succ (var 1))

theorem phi_mul : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 phiMulFormula :=
  closeUniv 2 (.impI (phi_mul_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm) Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative

export_ipra AnalyticNumberTheory.Multiplicative (gcd_rem phi_mul_at rem_eq' rem_lt' sum2_lift zero_lt')
