import IPRADerivations.AnalyticNumberTheory.OrderPower
import IPRADerivations.Analysis.RationalArithmetic.PowerSums
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic

/-!
# The totatives under `a ↦ n − a`

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorems
`thm:sum-totatives` and `thm:phi-even`.

The involution `σ(a) = (n − a) mod n` of `[0, n)` preserves coprimality to `n`. With
`e(a) = [gcd(a, n) = 1]`:

* `sum_totatives`: for `n ≥ 2`, `2 ∑_{a<n} a e(a) = n φ(n)`, since `a e(a) + σ(a) e(σ(a)) = n e(a)`
  and the sum is invariant under `σ`;
* `phi_even`: for `n ≥ 3`, `φ(n) = 2 T` with `T = ∑_{a<n} e(a) [a < σ(a)]`, since `σ` swaps
  `[a < σ(a)]` and `[σ(a) < a]` and its fixed points are not units.

Sums are permuted by exponentiating: `∏ 2^{f(σ i)} = ∏ 2^{f(i)}` (`Permutation.prod_perm`) and
`x ↦ 2^x` is injective (`sum_perm`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.Totatives

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos rem_eq_of_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (N_pos not_one_zero cop_comm cop_comm' rem_small rem_lt
  congrEqb)
open LeanProofs.IPRA.AnalyticNumberTheory.OrderPower (rem_self_eq)
open LeanProofs.IPRA.Analysis.PowerSums (mulParam inst2_mulParam sum_mul_param)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Permuting sums -/

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev prodPwTwoF (e : PTm 2) : Fm PTm 2 :=
  ap2 (prodF (pw two e)) (var 0) (var 1) ≐ pw two (ap2 (sumF e) (var 0) (var 1))

private theorem prod_pw_two₀ (e : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] prodPwTwoF e := by
  ipra_ind [subst_ap2]
  · exact (prod_zero _ _).eqTrans ((pw_zero _).eqSymm.eqTrans (congrAp2 powF (sum_zero _ _).eqSymm (.eqRefl _)))
  · refine (prod_succ _ (var 0) _).eqTrans ?_
    have ee : Syn.subst (![var 0, var 1] : Fin 2 → PTm 2) (pw two e) =
        pw two (Syn.subst (![var 0, var 1] : Fin 2 → PTm 2) e) := by simp
    rw [ee]
    refine (congrMul Prf.hyp0 (.eqRefl _)).eqTrans ((pw_add _ _ _).eqSymm.eqTrans ?_)
    exact congrAp2 powF (sum_succ _ _ _).eqSymm (.eqRefl _)

theorem prod_pw_two (e : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF (pw two e)) N x ≐ pw two (ap2 (sumF e) N x) := by
  have h := inst (Γ := Γ) (prod_pw_two₀ e) (![N, x] : Fin 2 → PTm n)
  simpa using h

theorem pw_two_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] lt (pw two a) (pw two b) := by
  have w := eq_add_of_le h
  have q := eq_add_of_le (le_self_pw (Γ := Γ) one (monus b (succ a)))
  have p := DiophantineNumberTheory.FLTMultiples.pw_pos (Γ := Γ) one a
  have eb : Γ ⊢[PRAAx] pw two b ≐ pw two a * pw two (succ (monus b (succ a))) :=
    (congrPw (.eqRefl _) (w.eqTrans (by ipra_ring))).eqTrans (pw_add _ _ _)
  refine le_of_eq_add (d := pred (pw two a) + monus (pw two (succ (monus b (succ a)))) two * pw two a) ?_
  ipra_lc natEq eb + Groth.ι (Q.mk Γ (pw two a)) * natEq q + natEq p

theorem pw_two_inj {a b : PTm n} (h : Γ ⊢[PRAAx] pw two a ≐ pw two b) : Γ ⊢[PRAAx] a ≐ b := by
  refine le_antisymm ?_ ?_
  · refine .orE (lt_or_le b a) ?_ Prf.hyp0
    exact lt_irrefl (pw two b) _ (lt_congr (.eqRefl _) h.wk (pw_two_lt Prf.hyp0))
  · refine .orE (lt_or_le a b) ?_ Prf.hyp0
    exact lt_irrefl (pw two a) _ (lt_congr (.eqRefl _) h.wk.eqSymm (pw_two_lt Prf.hyp0))

/-- `∑_{i<N} f(σ(i)) = ∑_{i<N} f(i)` for a permutation `σ` of `[0, N)` with inverse `τ`. -/
theorem sum_perm {f S τ : PTm 2} {N x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll S N x)
    (hinv : Γ ⊢[PRAAx] Permutation.invAll S τ N x) (hret : Γ ⊢[PRAAx] Permutation.retAll S τ N x) :
    Γ ⊢[PRAAx] ap2 (sumF (Permutation.FS f S)) N x ≐ ap2 (sumF f) N x := by
  have p := Permutation.prod_perm (F := pw two f) hr hinv hret
  have e : Permutation.FS (pw two f) S = pw two (Permutation.FS f S) := by
    simp [Permutation.FS]
  rw [e] at p
  exact pw_two_inj ((prod_pw_two _ _ _).eqSymm.eqTrans (p.eqTrans (prod_pw_two _ _ _)))

/-! ## The involution `a ↦ (n − a) mod n` -/

/-- `σ(y) = (n − y) mod n`, over `0 = y`, `1 = n`. -/
abbrev sB : PTm 2 := rem (monus (var 1) (var 0)) (var 1)

theorem inst2_s (y N : PTm n) : inst2 sB y N = rem (monus N y) N := by simp [inst2]

/-- `N = (N − (j+1)) + 1 + j` for `j < N`. -/
theorem split_lt {j N : PTm n} (h : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] N ≐ succ (monus N (succ j)) + j :=
  (eq_add_of_le h).eqTrans (by ipra_ring)

/-- `N − j = (N − (j+1)) + 1` for `j < N`. -/
theorem monus_succ_of_lt {j N : PTm n} (h : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] monus N j ≐ succ (monus N (succ j)) :=
  (congrMonus (split_lt h) (.eqRefl j)).eqTrans (add_monus _ _)

theorem monus_pos {j N : PTm n} (h : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx] monus N j ≐ succ (pred (monus N j)) :=
  AnalyticNumberTheory.Primes.eq_succ_pred (monus_succ_of_lt h)

/-- `N − j < N` for `1 ≤ j < N`. -/
theorem monus_lt {j N : PTm n} (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) (h : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] lt (monus N j) N := by
  refine le_of_eq_add (d := pred j) ?_
  ipra_lc natEq (split_lt h) + natEq hj - natEq (monus_succ_of_lt h)

/-- `gcd(N − j, N) = gcd(j, N)` for `1 ≤ j < N`. -/
theorem gcd_reflect {j N : PTm n} (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) (h : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] gcd (monus N j) N ≐ gcd j N := by
  have hm := monus_pos h
  have w₁ : Γ ⊢[PRAAx] N ≐ monus N j + j :=
    withEq (split_lt h) fun e₁ => withEq (monus_succ_of_lt h) fun e₂ => by
      apply deriveNat; ipra_simps; rw [e₁, e₂]
  have w₂ : Γ ⊢[PRAAx] N ≐ j + monus N j := w₁.eqTrans (add_comm _ _)
  have g₁ := gcd_pos (B := N) hj
  have g₂ := gcd_pos (B := N) hm
  have d₁ := gcd_dvd' (b := N) hj
  have d₂ := gcd_dvd' (b := N) hm
  refine le_antisymm (dvd_le' g₂ ?_ g₁) (dvd_le' g₁ ?_ g₂)
  · exact gcd_greatest' g₂ (dvd_sub' g₂ (dvd_congr w₂ (Prf.andE₂ d₂)) (Prf.andE₁ d₂)) (Prf.andE₂ d₂)
  · exact gcd_greatest' g₁ (dvd_sub' g₁ (dvd_congr w₁ (Prf.andE₂ d₁)) (Prf.andE₁ d₁)) (Prf.andE₂ d₁)

section Inv

variable {N : PTm n} (hN : Γ ⊢[PRAAx] le two N)
include hN

/-- `σ(0) = 0`. -/
theorem sigma_zero : Γ ⊢[PRAAx] rem (monus N zero) N ≐ zero :=
  (congrAp2 remF (monus_zero _) (.eqRefl _)).eqTrans (rem_self_eq hN)

/-- `σ(j) = N − j` for `1 ≤ j < N`. -/
theorem sigma_pos {j : PTm n} (hj : Γ ⊢[PRAAx] j ≐ succ (pred j)) (hjN : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] rem (monus N j) N ≐ monus N j :=
  rem_small hN (monus_lt hj hjN)

/-- `σ(σ(j)) = j` for `j < N`. -/
theorem sigma_sigma {j : PTm n} (hjN : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] rem (monus N (rem (monus N j) N)) N ≐ j := by
  refine .orE (zero_or_succ j) ?_ ?_
  · have z : ((j ≐ zero) :: Γ) ⊢[PRAAx] rem (monus N j) N ≐ zero :=
      (congrAp2 remF (congrMonus (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans (sigma_zero hN.wk)
    exact (congrAp2 remF (congrMonus (.eqRefl _) z) (.eqRefl _)).eqTrans
      ((sigma_zero hN.wk).eqTrans Prf.hyp0.eqSymm)
  · have hj : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have s₁ := sigma_pos hN.wk hj hjN.wk
    have hm : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] _ := monus_pos hjN.wk
    have hmN := monus_lt hj hjN.wk
    have s₂ := sigma_pos hN.wk hm hmN
    have w : ((j ≐ succ (pred j)) :: Γ) ⊢[PRAAx] N ≐ j + monus N j :=
      withEq (split_lt hjN.wk) fun e₁ => withEq (monus_succ_of_lt hjN.wk) fun e₂ => by
        apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
    refine (congrAp2 remF (congrMonus (.eqRefl _) s₁) (.eqRefl _)).eqTrans (s₂.eqTrans ?_)
    exact (congrMonus w (.eqRefl _)).eqTrans (add_monus _ _)

/-- `[gcd(0, N) = 1] = 0`. -/
theorem e_zero : Γ ⊢[PRAAx] eqb (gcd zero N) one ≐ zero :=
  eqb_of_ne (.impI (not_one_zero hN.wk _ (.orI₁ Prf.hyp0)))

/-- The pointwise identity `a e(a) + σ(a) e(σ(a)) = N e(a)` for `a < N`. -/
theorem pointwise {a : PTm n} (ha : Γ ⊢[PRAAx] lt a N) :
    Γ ⊢[PRAAx] a * eqb (gcd a N) one + rem (monus N a) N * eqb (gcd (rem (monus N a) N) N) one ≐
      N * eqb (gcd a N) one := by
  refine .orE (zero_or_succ a) ?_ ?_
  · have hz : ((a ≐ zero) :: Γ) ⊢[PRAAx] a ≐ zero := Prf.hyp0
    have hs : ((a ≐ zero) :: Γ) ⊢[PRAAx] rem (monus N a) N ≐ zero :=
      (congrAp2 remF (congrMonus (.eqRefl _) hz) (.eqRefl _)).eqTrans (sigma_zero hN.wk)
    have he : ((a ≐ zero) :: Γ) ⊢[PRAAx] eqb (gcd a N) one ≐ zero :=
      (congrEqb (congrGcd hz (.eqRefl _)) (.eqRefl _)).eqTrans (e_zero hN.wk)
    have h₁ := natEq hz; have h₂ := natEq hs; have h₃ := natEq he
    apply deriveNat; ipra_simps
    linear_combination Groth.ι (Q.mk _ (eqb (gcd a N) one)) * h₁ +
      Groth.ι (Q.mk _ (eqb (gcd (rem (monus N a) N) N) one)) * h₂ - Groth.ι (Q.mk _ N) * h₃
  · have hj : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
    have s := sigma_pos hN.wk hj ha.wk
    have hg := (congrEqb ((congrGcd s (.eqRefl _)).eqTrans (gcd_reflect hj ha.wk)) (.eqRefl one) :
      ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] eqb (gcd (rem (monus N a) N) N) one ≐ eqb (gcd a N) one)
    have w : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] N ≐ a + monus N a :=
      withEq (split_lt ha.wk) fun e₁ => withEq (monus_succ_of_lt ha.wk) fun e₂ => by
        apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
    have h₁ := natEq s; have h₂ := natEq hg; have h₃ := natEq w
    apply deriveNat; ipra_simps
    linear_combination Groth.ι (Q.mk _ (eqb (gcd a N) one)) * (h₁ - h₃) +
      Groth.ι (Q.mk _ (rem (monus N a) N)) * h₂

end Inv

/-! ## `2 S(N) = N φ(N)` -/

/-- `a · [gcd(a, n) = 1]`, over `0 = a`, `1 = n`. -/
abbrev aeB : PTm 2 := var 0 * totBody

/-- `S(N) = ∑_{a<N, gcd(a,N)=1} a`. -/
abbrev totSum (N : PTm n) : PTm n := ap2 (sumF aeB) N N

theorem inst2_ae (y x : PTm n) : inst2 aeB y x = y * eqb (gcd y x) one := by
  simp only [inst2, PTm.subst_mul, subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

section Perm

variable {N : PTm n} (hN : Γ ⊢[PRAAx] le two N)
include hN

theorem s_range : Γ ⊢[PRAAx] Permutation.rangeAll sB N N := by
  refine .allI ?_
  rw [inst2_s]; exact rem_lt (Euler.shift_le_two hN) _

theorem s_inv : Γ ⊢[PRAAx] Permutation.invAll sB sB N N := by
  refine .allI (.impI (.andI ?_ ?_))
  · rw [inst2_s]; exact rem_lt (Euler.shift_le_two hN).wk _
  · rw [inst2_s, inst2_s]; exact sigma_sigma (Euler.shift_le_two hN).wk Prf.hyp0

theorem s_ret : Γ ⊢[PRAAx] Permutation.retAll sB sB N N := by
  refine .allI (.impI ?_)
  rw [inst2_s, inst2_s]; exact sigma_sigma (Euler.shift_le_two hN).wk Prf.hyp0

/-- `thm:sum-totatives` at an arbitrary `N ≥ 2`. -/
theorem sum_totatives_at : Γ ⊢[PRAAx] two * totSum N ≐ N * phi N := by
  have hp := sum_perm (f := aeB) (s_range hN) (s_inv hN) (s_ret hN)
  have hadd := sum_add (Γ := Γ) aeB (Permutation.FS aeB sB) N N
  have hpt : Γ ⊢[PRAAx] ap2 (sumF (addBody aeB (Permutation.FS aeB sB))) N N ≐
      ap2 (sumF (mulParam (var 0) totBody)) N N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, Permutation.inst2_FS, inst2_mulParam, inst2_s, inst2_ae, inst2_ae, inst2_tot]
    exact pointwise (Euler.shift_le_two hN).wk Prf.hyp0
  have hm := sum_mul_param (Γ := Γ) (var 0) totBody N N
  have e := hadd.eqSymm.eqTrans (hpt.eqTrans hm)
  have d : Γ ⊢[PRAAx] two * totSum N ≐ totSum N + totSum N := by ipra_ring
  exact d.eqTrans ((congrAdd (.eqRefl _) hp.eqSymm).eqTrans e)

end Perm

/-- `thm:sum-totatives`: `2 ∑_{a<n, gcd(a,n)=1} a = n φ(n)` for `n ≥ 2`; variable `0 = n − 2`.
(The summand `a = 0` contributes nothing, so this is the packet's sum over `1 ≤ a < n`.) -/
abbrev sumTotativesFormula : Fm PTm 1 :=
  two * totSum (succ (succ (var 0))) ≐ succ (succ (var 0)) * phi (succ (succ (var 0)))

theorem sum_totatives : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 sumTotativesFormula :=
  closeUniv 1 (sum_totatives_at (le_of_eq_add (d := var 0) (by ipra_ring)))

/-! ## `φ(N)` is even for `N ≥ 3` -/

theorem sg_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] sg (monus b a) ≐ one :=
  (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (monus_succ_of_lt h))).eqTrans (sg_succ _)

theorem sg_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] sg (monus a b) ≐ zero :=
  (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero

/-- `e(a) · [a < σ(a)]`, over `0 = a`, `1 = n`. -/
abbrev evB : PTm 2 := totBody * sg (monus sB (var 0))

theorem inst2_ev (y x : PTm n) :
    inst2 evB y x = eqb (gcd y x) one * sg (monus (rem (monus x y) x) y) := by
  rw [← inst2_tot, ← inst2_s]; simp [inst2]

theorem shift_le_three {N : PTm n} (hN : Γ ⊢[PRAAx] le (succ two) N) :
    Γ.map Fm.shift ⊢[PRAAx] le (succ two) (Syn.shift N) := by
  have e := hN.shift
  simp only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e
  exact e

section Even

variable {N : PTm n} (hN : Γ ⊢[PRAAx] le (succ two) N)
include hN

omit hN in
/-- `e(σ(a)) = e(a)` for `a < N`. -/
theorem e_sigma (hN : Γ ⊢[PRAAx] le two N) {a : PTm n} (ha : Γ ⊢[PRAAx] lt a N) :
    Γ ⊢[PRAAx] eqb (gcd (rem (monus N a) N) N) one ≐ eqb (gcd a N) one := by
  refine .orE (zero_or_succ a) ?_ ?_
  · have hz : ((a ≐ zero) :: Γ) ⊢[PRAAx] a ≐ zero := Prf.hyp0
    have hs : ((a ≐ zero) :: Γ) ⊢[PRAAx] rem (monus N a) N ≐ zero :=
      (congrAp2 remF (congrMonus (.eqRefl _) hz) (.eqRefl _)).eqTrans (sigma_zero hN.wk)
    exact congrEqb (congrGcd (hs.eqTrans hz.eqSymm) (.eqRefl _)) (.eqRefl _)
  · have hj : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
    exact congrEqb ((congrGcd (sigma_pos hN.wk hj ha.wk) (.eqRefl _)).eqTrans (gcd_reflect hj ha.wk)) (.eqRefl _)

/-- A fixed point of `σ` below `N ≥ 3` is not a unit. -/
theorem e_fixed {a : PTm n} (ha : Γ ⊢[PRAAx] lt a N) (hfix : Γ ⊢[PRAAx] rem (monus N a) N ≐ a) :
    Γ ⊢[PRAAx] eqb (gcd a N) one ≐ zero := by
  have hN2 : Γ ⊢[PRAAx] le two N := le_trans (le_succ_self _) hN
  refine .orE (zero_or_succ a) ?_ ?_
  · exact (congrEqb (congrGcd Prf.hyp0 (.eqRefl _)) (.eqRefl _)).eqTrans (e_zero hN2.wk)
  · have hj : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] a ≐ succ (pred a) := Prf.hyp0
    have hm : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] monus N a ≐ a :=
      (sigma_pos hN2.wk hj ha.wk).eqSymm.eqTrans hfix.wk
    have w : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] N ≐ a * two :=
      withEq (split_lt ha.wk) fun e₁ => withEq (monus_succ_of_lt ha.wk) fun e₂ => withEq hm fun e₃ => by
        apply deriveNat; ipra_simps; rw [e₁]; linear_combination e₃ - e₂
    refine .orE (eq_or_ne (gcd a N) one) ?_ (eqb_of_ne Prf.hyp0)
    refine .botE _ ?_
    have hj' := hj.wk (ψ := gcd a N ≐ one)
    have d₁ := dvd_self' hj'
    have d₂ := dvd_of_eq' hj' (w := two) w.wk
    have d := dvd_congr Prf.hyp0 (gcd_greatest' hj' d₁ d₂)
    have l := eq_add_of_le (dvd_le' hj' d (congrSucc (pred_succ _).eqSymm))
    have l₃ := eq_add_of_le (hN.wk.wk : ((gcd a N ≐ one) :: (a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] _)
    refine succ_ne_zero (a := monus N (succ two) + monus one a + monus one a) ?_
    ipra_lc -2 * natEq l - natEq l₃ + natEq (w.wk : ((gcd a N ≐ one) :: (a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] _)

omit hN in
/-- `E = E [a < b] + E [b < a]` when `b = a` forces `E = 0`. -/
theorem split3 {a b E : PTm n} (hfix : Γ ⊢[PRAAx] (b ≐ a) ⟶ (E ≐ zero)) :
    Γ ⊢[PRAAx] E ≐ E * sg (monus b a) + E * sg (monus a b) := by
  have r : ∀ {Δ : List (Fm PTm n)}, Δ ⊢[PRAAx] E ≐ E * one + E * zero := by
    intro Δ; ipra_ring
  have r' : ∀ {Δ : List (Fm PTm n)}, Δ ⊢[PRAAx] E ≐ E * zero + E * one := by
    intro Δ; ipra_ring
  refine .orE (lt_or_le a b) ?_ ?_
  · have h : (lt a b :: Γ) ⊢[PRAAx] lt a b := Prf.hyp0
    exact r.eqTrans (congrAdd (congrMul (.eqRefl _) (sg_lt h)) (congrMul (.eqRefl _) (sg_le (le_of_lt h)))).eqSymm
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have h : (lt b a :: le b a :: Γ) ⊢[PRAAx] lt b a := Prf.hyp0
      exact r'.eqTrans (congrAdd (congrMul (.eqRefl _) (sg_le (le_of_lt h)))
        (congrMul (.eqRefl _) (sg_lt h))).eqSymm
    · have hE : ((b ≐ a) :: le b a :: Γ) ⊢[PRAAx] E ≐ zero := .impE hfix.wk.wk Prf.hyp0
      refine hE.eqTrans (.eqTrans ?_ (congrAdd (congrMul hE (.eqRefl _)) (congrMul hE (.eqRefl _))).eqSymm)
      ipra_ring

/-- `e(a) = e(a)[a < σ(a)] + e(σ(a))[σ(a) < σ(σ(a))]` for `a < N`. -/
theorem even_pointwise {a : PTm n} (ha : Γ ⊢[PRAAx] lt a N) :
    Γ ⊢[PRAAx] eqb (gcd a N) one ≐ eqb (gcd a N) one * sg (monus (rem (monus N a) N) a) +
      eqb (gcd (rem (monus N a) N) N) one *
        sg (monus (rem (monus N (rem (monus N a) N)) N) (rem (monus N a) N)) := by
  have hN2 : Γ ⊢[PRAAx] le two N := le_trans (le_succ_self _) hN
  have hY : Γ ⊢[PRAAx] sg (monus (rem (monus N (rem (monus N a) N)) N) (rem (monus N a) N)) ≐
      sg (monus a (rem (monus N a) N)) :=
    congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (congrMonus (sigma_sigma hN2 ha) (.eqRefl _)))
  refine (split3 (.impI (e_fixed hN.wk ha.wk Prf.hyp0))).eqTrans
    (congrAdd (.eqRefl _) (congrMul (e_sigma hN2 ha).eqSymm hY.eqSymm))

/-- `thm:phi-even` (evenness) at an arbitrary `N ≥ 3`: `φ(N) = 2 ∑_{a<N} e(a)[a < N − a]`. -/
theorem phi_even_at : Γ ⊢[PRAAx] phi N ≐ two * ap2 (sumF evB) N N := by
  have hN2 : Γ ⊢[PRAAx] le two N := le_trans (le_succ_self _) hN
  have hp := sum_perm (f := evB) (s_range hN2) (s_inv hN2) (s_ret hN2)
  have hadd := sum_add (Γ := Γ) evB (Permutation.FS evB sB) N N
  have hpt : Γ ⊢[PRAAx] phi N ≐ ap2 (sumF (addBody evB (Permutation.FS evB sB))) N N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_tot, inst2_addBody, Permutation.inst2_FS, inst2_ev, inst2_s, inst2_ev]
    exact even_pointwise (shift_le_three hN).wk Prf.hyp0
  have d : Γ ⊢[PRAAx] ap2 (sumF evB) N N + ap2 (sumF evB) N N ≐ two * ap2 (sumF evB) N N := by
    ipra_ring
  exact hpt.eqTrans (hadd.eqTrans ((congrAdd (.eqRefl _) hp).eqTrans d))

end Even

/-- `thm:phi-even` (evenness): `φ(n) = 2 T(n)` for `n ≥ 3`, with the explicit
`T(n) = #{a < n : gcd(a, n) = 1, a < n − a}`; variable `0 = n − 3`. -/
abbrev phiEvenFormula : Fm PTm 1 :=
  phi (succ (succ (succ (var 0)))) ≐ two * ap2 (sumF evB) (succ (succ (succ (var 0)))) (succ (succ (succ (var 0))))

theorem phi_even : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 phiEvenFormula :=
  closeUniv 1 (phi_even_at (le_of_eq_add (d := var 0) (by ipra_ring)))

end LeanProofs.IPRA.AnalyticNumberTheory.Totatives
