import IPRADerivations.Combinatorics.FibonacciPeriod
import IPRADerivations.Combinatorics.BinomialTransform
import IPRADerivations.Combinatorics.LucasIdentities
import IPRADerivations.Combinatorics.BellPascalInversion
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# The prime-index Lucas congruence

Packet: `combinatorics/fibonacci_lucas_ipra` (theorem "Prime-index Lucas congruence"): `L_p ≡ 1 (mod p)`
for every prime `p`.

The packet's proof expands `(1 + √5)^p` modulo `p` (the binomial congruence), with Fermat's little
theorem. Without `√5`, with `W(n) = ∑_k C(n, k) [k even] 5^{⌊k/2⌋}` and
`V(n) = ∑_k C(n, k) [k odd] 5^{⌊k/2⌋}` (so `(1 + √5)^n = W(n) + V(n) √5`):

* `W_succ`, `V_succ`: `W(n + 1) = W(n) + 5 V(n)` and `V(n + 1) = V(n) + W(n)`, by the Pascal step of
  `Combinatorics/BinomialTransform` and the parity shift `[k + 1 even] 5^{⌊(k+1)/2⌋} = 5 [k odd] 5^{⌊k/2⌋}`;
* `binet`: `2^n L_n = 2 W(n)` and `2^n F_n = 2 V(n)`, from `2 L_{n+1} = L_n + 5 F_n` and
  `2 F_{n+1} = L_n + F_n`;
* `W_prime`: `W(p) = 1 + p w + [p even] 5^{⌊p/2⌋}`, since `p ∣ C(p, k)` for `0 < k < p`;
* `lucas_prime`: for odd `p = 2s + 1`, `2^p L_p ≡ 2` and Fermat's `2^p ≡ 2` give `2 L_p ≡ 2`, and
  multiplying by `s + 1` gives `L_p ≡ 1`; for `p = 2`, `L_2 = 3`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LucasPrime

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialTransform (bgB inst2_bg inst2_sbg inst2_bgs pascal_sum)
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.LucasIdentities (luc_zero luc_one)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (ev od ev_succ od_succ ev_zero congrEv congrOd)
open LeanProofs.IPRA.Combinatorics.FibonacciPeriod (cong_lin)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_dvd_binom dvd_sum fermat_at prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Foundations.ChineseRemainder (rem_eq_of_eq)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_of_eq')
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The weights -/

/-- `[k even] x^{⌊k/2⌋}`, over `0 = k`, `1 = x`. -/
abbrev gE : PTm 2 := ev (var 0) * pw (var 1) (half (var 0))
/-- `[k odd] x^{⌊k/2⌋}`. -/
abbrev gO : PTm 2 := od (var 0) * pw (var 1) (half (var 0))

theorem inst2_gE (k x : PTm n) : inst2 gE k x = ev k * pw x (half k) := by simp [inst2]
theorem inst2_gO (k x : PTm n) : inst2 gO k x = od k * pw x (half k) := by simp [inst2]

/-- `[k + 1 even] x^{⌊(k+1)/2⌋} = x · [k odd] x^{⌊k/2⌋}`. -/
theorem gE_succ (k x : PTm n) : Γ ⊢[PRAAx] ev (succ k) * pw x (half (succ k)) ≐ x * (od k * pw x (half k)) := by
  refine (congrMul (ev_succ k) (congrPw (.eqRefl _) (half_succ k))).eqTrans ?_
  refine .orE (par_cases k) ?_ ?_
  · have h : ((par k ≐ zero) :: Γ) ⊢[PRAAx] od k ≐ zero := Prf.hyp0
    exact ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)).eqTrans
      ((congrMul (.eqRefl _) ((congrMul h (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)).eqSymm
  · have h : ((par k ≐ one) :: Γ) ⊢[PRAAx] od k ≐ one := Prf.hyp0
    have e : ((par k ≐ one) :: Γ) ⊢[PRAAx] half k + par k ≐ succ (half k) :=
      (congrAdd (.eqRefl _) Prf.hyp0).eqTrans (by ipra_ring)
    refine (congrMul h (congrPw (.eqRefl _) e)).eqTrans ?_
    refine ((one_mul _).eqTrans (pw_succ _ _)).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (congrMul h (.eqRefl _))).eqSymm)
    ipra_ring

/-- `[k + 1 odd] x^{⌊(k+1)/2⌋} = [k even] x^{⌊k/2⌋}`. -/
theorem gO_succ (k x : PTm n) : Γ ⊢[PRAAx] od (succ k) * pw x (half (succ k)) ≐ ev k * pw x (half k) := by
  refine (congrMul (od_succ k) (congrPw (.eqRefl _) (half_succ k))).eqTrans ?_
  refine .orE (par_cases k) ?_ ?_
  · have h : ((par k ≐ zero) :: Γ) ⊢[PRAAx] par k ≐ zero := Prf.hyp0
    exact congrMul (.eqRefl _) (congrPw (.eqRefl _) ((congrAdd (.eqRefl _) h).eqTrans (add_zero _)))
  · have h : ((par k ≐ one) :: Γ) ⊢[PRAAx] ev k ≐ zero := (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_self _)
    exact ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)).eqTrans ((congrMul h (.eqRefl _)).eqTrans (zero_mul _)).eqSymm

/-! ## `W(n) + V(n) √5 = (1 + √5)^n` -/

abbrev W {n : ℕ} (m x : PTm n) : PTm n := ap2 (sumF (bgB gE)) (succ m) (pairT m x)
abbrev V {n : ℕ} (m x : PTm n) : PTm n := ap2 (sumF (bgB gO)) (succ m) (pairT m x)

theorem W_succ (m x : PTm n) : Γ ⊢[PRAAx] W (succ m) x ≐ W m x + x * V m x := by
  refine (pascal_sum gE m x).eqTrans (congrAdd (.eqRefl _) ?_)
  refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
  simp only [LeanProofs.IPRA.Combinatorics.StirlingBinomial.shift_y]
  rw [inst2_bgs, inst2_bg, inst2_gE, inst2_gO]
  refine (congrMul (.eqRefl _) ((gE_succ _ _).eqTrans (congrMul (snd_pair _ _) (.eqRefl _)))).eqTrans ?_
  ipra_ring

theorem V_succ (m x : PTm n) : Γ ⊢[PRAAx] V (succ m) x ≐ V m x + W m x := by
  refine (pascal_sum gO m x).eqTrans (congrAdd (.eqRefl _) ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [LeanProofs.IPRA.Combinatorics.StirlingBinomial.shift_y]
  rw [inst2_bgs, inst2_bg, inst2_gO, inst2_gE]
  exact congrMul (.eqRefl _) (gO_succ _ _)

/-! ## `2^n L_n = 2 W(n)`, `2^n F_n = 2 V(n)` -/

abbrev five {n : ℕ} : PTm n := num 5

abbrev binetF : Fm PTm 1 :=
  pairT (pw two (var 0) * luc (var 0)) (pw two (var 0) * fib (var 0)) ≐
    pairT (two * W (var 0) five) (two * V (var 0) five)

theorem W_zero (x : PTm n) : Γ ⊢[PRAAx] W zero x ≐ one := by
  refine (sum_singleton _ _).eqTrans ?_
  rw [inst2_bg, inst2_gE]
  exact (congrMul (binom_zero' _) ((congrMul ev_zero (congrPw (.eqRefl _) half_zero)).eqTrans
    ((one_mul _).eqTrans (pw_zero _)))).eqTrans (one_mul _)

theorem V_zero (x : PTm n) : Γ ⊢[PRAAx] V zero x ≐ zero := by
  refine (sum_singleton _ _).eqTrans ?_
  rw [inst2_bg, inst2_gO]
  exact (congrMul (.eqRefl _) ((congrMul par_zero (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)

theorem binet_base : Γ ⊢[PRAAx] pairT (pw two (zero : PTm n) * luc zero) (pw two zero * fib zero) ≐
    pairT (two * W zero five) (two * V zero five) := by
  have a := natEq (pw_zero (Γ := Γ) (two : PTm n)); have b := natEq (luc_zero (Γ := Γ) (n := n))
  have c := natEq (fib_zero (Γ := Γ) (n := n)); have d := natEq (W_zero (Γ := Γ) (five : PTm n))
  refine congrPair ?_ ?_
  · ipra_lc (𝔞 (fibS (zero : PTm n)) + 𝔞 (monus (fibS (zero : PTm n)) (fib (zero : PTm n)))) * a + b - 2 * d
  · ipra_lc 𝔞 (fib (zero : PTm n)) * a + c - 2 * natEq (V_zero (Γ := Γ) (five : PTm n))
where
  congrPair {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
      Γ ⊢[PRAAx] pairT a b ≐ pairT a' b' := LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic.congrPair h₁ h₂

theorem binet_step {m : PTm n} (ih : Γ ⊢[PRAAx] pairT (pw two m * luc m) (pw two m * fib m) ≐
    pairT (two * W m five) (two * V m five)) :
    Γ ⊢[PRAAx] pairT (pw two (succ m) * luc (succ m)) (pw two (succ m) * fib (succ m)) ≐
      pairT (two * W (succ m) five) (two * V (succ m) five) := by
  have l₀ := natEq (luc_eq (Γ := Γ) m); have l₁ := natEq (luc_eq (Γ := Γ) (succ m))
  have f₀ := natEq (fib_succ (Γ := Γ) m); have f₁ := natEq (fibS_succ (Γ := Γ) m)
  have w := natEq (W_succ (Γ := Γ) m five); have v := natEq (V_succ (Γ := Γ) m five)
  refine LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic.congrPair ?_ ?_
  · ipra_lc (𝔞 (fibS (succ m)) + 𝔞 (monus (fibS (succ m)) (fib (succ m)))) * natEq (pw_succ (Γ := Γ) two m) +
      2 * 𝔞 (pw two m) * l₁ - 2 * 𝔞 (pw two m) * f₀ + 4 * 𝔞 (pw two m) * f₁ - 𝔞 (pw two m) * l₀ +
      natEq ((fst_pair _ _).eqSymm.eqTrans ih.fstE) +
      5 * natEq ((snd_pair _ _).eqSymm.eqTrans ih.sndE) - 2 * w
  · ipra_lc 𝔞 (fib (succ m)) * natEq (pw_succ (Γ := Γ) two m) + 2 * 𝔞 (pw two m) * f₀ - 𝔞 (pw two m) * l₀ +
      natEq ((fst_pair _ _).eqSymm.eqTrans ih.fstE) +
      natEq ((snd_pair _ _).eqSymm.eqTrans ih.sndE) - 2 * v

private theorem binet₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] binetF := by
  ipra_ind [subst_ap2, subst_pairT, subst_fib, subst_fibS]
  · exact binet_base
  · exact binet_step Prf.hyp0

/-- `2^n L_n = 2 W(n)` and `2^n F_n = 2 V(n)` (the pair form). -/
theorem binet (m : PTm n) : Γ ⊢[PRAAx] pairT (pw two m * luc m) (pw two m * fib m) ≐
    pairT (two * W m five) (two * V m five) := by
  have h := inst (Γ := Γ) binet₀ (![m] : Fin 1 → PTm n)
  simpa using h

theorem binet_luc (m : PTm n) : Γ ⊢[PRAAx] pw two m * luc m ≐ two * W m five :=
  (fst_pair _ _).eqSymm.eqTrans (binet m).fstE

/-! ## `W(p)` modulo `p` -/

/-- `W(p) = 1 + p w + [p even] x^{⌊p/2⌋}` with `w = (∑_{0<k<p} C(p, k) ⋯) / p`. -/
theorem W_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (x : PTm n) :
    Γ ⊢[PRAAx] W p x ≐ one + p * quo (ap2 (sumF (shiftBody (bgB gE))) (pred p) (pairT p x)) p +
      ev p * pw x (half p) := by
  have hq := LeanProofs.IPRA.prime_eq_succ_pred hp
  -- The middle terms are multiples of `p`.
  have hd : Γ ⊢[PRAAx] dvd (succ (pred p)) (ap2 (sumF (shiftBody (bgB gE))) (pred p) (pairT p x)) := by
    refine dvd_sum _ (.allI (.impI ?_))
    rw [inst2_sbg, inst2_gE]
    have e : Syn.shift (pairT p x) = pairT (Syn.shift p) (Syn.shift x) := by simp [Syn.shift]
    have ep : Syn.shift (pred p) = pred (Syn.shift p) := by simp [Syn.shift]
    rw [e, ep]
    have hp' := (prime_shift hp).wk (ψ := lt (var 0) (pred (Syn.shift p)))
    have hq' := LeanProofs.IPRA.prime_eq_succ_pred hp'
    have db' := dvd_congr_left hq' (prime_dvd_binom hp' hq' Prf.hyp0)
    refine dvd_congr ?_ (dvd_mul (ev (succ (var 0)) * pw (sndT (pairT (Syn.shift p) (Syn.shift x)))
      (half (succ (var 0)))) db')
    exact congrMul (congrBinom (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)
  have em := eq_of_dvd' hq (dvd_congr_left hq.eqSymm hd)
  -- `W(p) = term(0) + middle + term(p)`.
  have s₁ := sum_succ' (Γ := Γ) (bgB gE) p (pairT p x)
  have s₂ := sum_shift (Γ := Γ) (bgB gE) (pred p) (pairT p x)
  rw [inst2_bg, inst2_gE] at s₁ s₂
  have t₀ : Γ ⊢[PRAAx] binom (fstT (pairT p x)) zero * (ev zero * pw (sndT (pairT p x)) (half zero)) ≐ one :=
    (congrMul (binom_zero' _) ((congrMul ev_zero (congrPw (.eqRefl _) half_zero)).eqTrans
      ((one_mul _).eqTrans (pw_zero _)))).eqTrans (one_mul _)
  have tp : Γ ⊢[PRAAx] binom (fstT (pairT p x)) p * (ev p * pw (sndT (pairT p x)) (half p)) ≐ ev p * pw x (half p) :=
    (congrMul ((congrBinom (fst_pair _ _) (.eqRefl _)).eqTrans (binom_self' _))
      (congrMul (.eqRefl _) (congrPw (snd_pair _ _) (.eqRefl _)))).eqTrans (one_mul _)
  ipra_lc natEq s₁ + natEq ((congrAp2 (sumF (bgB gE)) hq (.eqRefl _)).eqTrans s₂) + natEq t₀ + natEq tp + natEq em

/-! ## The congruence -/

theorem luc_two : Γ ⊢[PRAAx] luc (two : PTm n) ≐ succ two := by
  ipra_lc natEq (luc_rec (Γ := Γ) (zero : PTm n)) + natEq (luc_one (Γ := Γ) (n := n)) +
    natEq (luc_zero (Γ := Γ) (n := n))

theorem congrLuc {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] luc a ≐ luc b :=
  congrAdd (congrFibS h) (congrMonus (congrFibS h) (congrFib h))

/-- An even prime is `2`. -/
theorem even_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (he : Γ ⊢[PRAAx] par p ≐ zero) : Γ ⊢[PRAAx] p ≐ two := by
  have d2 : Γ ⊢[PRAAx] dvd two p :=
    dvd_of_eq' two_pos ((half_par p).eqTrans ((congrAdd (.eqRefl _) he).eqTrans (add_zero _)))
  exact (prime_eq_of_dvd hp (le_refl two) d2).eqSymm

/-- The odd case: `L_p ≡ 1` from `2^p L_p ≡ 2` and `2^p ≡ 2`. -/
theorem lucas_odd {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (ho : Γ ⊢[PRAAx] par p ≐ one) :
    Γ ⊢[PRAAx] rem (luc p) p ≐ rem one p := by
  have hq := LeanProofs.IPRA.prime_eq_succ_pred hp
  have e₄ := natEq (half_par (Γ := Γ) p); have h₁ := natEq ho
  refine rem_eq_of_eq hq (k₁ := luc p + succ (half p) * (quo (pw two p) p * luc p))
    (k₂ := one + succ (half p) * (two * quo (ap2 (sumF (shiftBody (bgB gE))) (pred p) (pairT p five)) p +
      quo two p * luc p)) ?_
  ipra_lc (𝔞 (half p) + 1) * (natEq (binet_luc (Γ := Γ) p) + 2 * natEq (W_prime hp (five : PTm n)) + 2 * 𝔞 (pw five (half p)) * natEq ((congrMonus (.eqRefl (one : PTm n)) ho).eqTrans (monus_self one) : Γ ⊢[PRAAx] ev p ≐ zero)) -
    (𝔞 (half p) + 1) * (𝔞 (fibS p) + 𝔞 (monus (fibS p) (fib p))) * natEq (cong_lin hq (fermat_at hp two)) +
    ((𝔞 (fibS p) + 𝔞 (monus (fibS p) (fib p))) - 1) * (e₄ + h₁)

/-- The prime-index Lucas congruence: `L_p ≡ 1 (mod p)`. -/
theorem lucas_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] rem (luc p) p ≐ rem one p := by
  refine .orE (par_cases p) ?_ (lucas_odd hp.wk Prf.hyp0)
  have e2 := even_prime hp.wk Prf.hyp0
  refine (congrAp2 remF ((congrLuc e2).eqTrans luc_two) e2).eqTrans (.eqTrans ?_ (congrAp2 remF (.eqRefl _) e2).eqSymm)
  exact rem_eq_of_eq two_pos (k₁ := zero) (k₂ := one) (by ipra_ring)

/-- Variables: `0 = p`. -/
abbrev lucasPrimeFormula : Fm PTm 1 := prime (var 0) ⟶ rem (luc (var 0)) (var 0) ≐ rem one (var 0)

theorem lucas_prime_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 lucasPrimeFormula :=
  closeUniv 1 (.impI (lucas_prime Prf.hyp0))

end LeanProofs.IPRA.Combinatorics.LucasPrime
