import IPRADerivations.AnalyticNumberTheory.SigmaPrimePower
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.Order

/-!
# The divisor functions `τ` and `σ_r`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem
`el:divisorfunc`: "`τ(n) = ∏ (e_i + 1)`, `σ_r(n) = ∏ (∑_{j=0}^{e_i} p_i^{rj})`. The functions `τ` and `σ_r` are
multiplicative."

`σ_r(K) = ∑_{d ≤ K} [d ∣ K] d^r` (`sigr r K`), with the exponent `r` a term; `τ = σ_0`.

* **`sigr_mul`**: `σ_r(mN) = σ_r(m) σ_r(N)` for coprime `m, N ≥ 1` (`DivisorFactor.divisor_factor` at `g(d) = d^r`,
  and `(ab)^r = a^r b^r`);
* **`sigr_step`**: `σ_r(p · p^a) = p^r σ_r(p^a) + 1` for a prime `p` (the multiples of `p` reindexed, the other
  divisors reduce to `d = 1`, `SigmaPrimePower.rest_pt`);
* `sigr_one`: `σ_r(1) = 1`; **`tau_pow`**: `τ(p^a) = a + 1`;
* `geo x a = ∑_{j ≤ a} x^j`, `geo_rev` (`geo x (a+1) = x · geo x a + 1`);
  **`sigr_pow`**: `σ_r(p^a) = ∑_{j ≤ a} (p^r)^j`;
* `sigr_one_exp`: `σ_1 = σ` (`SigmaMult.sig`).

With multiplicativity these give the value at every `n` from its prime powers; the single displayed product over
the factorization is derived for `σ` in `SigmaProduct.sigma_product`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SigmaR

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaMult (sB sig inst2_sB)
open LeanProofs.IPRA.AnalyticNumberTheory.SigmaPrimePower (dvd_scale rest_pt pos_pw sh_pw sh_P)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor (Xp lB_at riB_at rB_at divisor_factor inst2_v1)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (one_le_of_pos)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul eq_of_rem_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (rem_by_zero)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (inst2_riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (multiples_upto)
open LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement (quo_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (rem_one)
open LeanProofs.IPRA.AnalyticNumberTheory.SumPhi (shift_mul')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The bodies -/

/-- `g(d, r) = d^r`. -/
abbrev gP : PTm 2 := pw (var 0) (var 1)

theorem inst2_gP (d r : PTm n) : inst2 gP d r = pw d r := by simp [inst2]

/-- `[d ∣ K] d^r` over `0 = d`, `1 = ⟨K, r⟩`. -/
def srB : PTm 2 := eqb (rem (fstT (var 1)) (var 0)) zero * pw (var 0) (sndT (var 1))

/-- `σ_r(K) = ∑_{d < K+1} [d ∣ K] d^r`. -/
abbrev sigr (r K : PTm n) : PTm n := ap2 (sumF srB) (succ K) (pairT K r)

theorem inst2_srB (d z : PTm n) : inst2 srB d z = eqb (rem (fstT z) d) zero * pw d (sndT z) := by
  simp [inst2, srB]

theorem srB_at (d K r : PTm n) : Γ ⊢[PRAAx] inst2 srB d (pairT K r) ≐ eqb (rem K d) zero * pw d r := by
  rw [inst2_srB]
  exact congrMul (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _))
    (congrAp2 powF (snd_pair _ _) (.eqRefl _))

theorem sh_sigr (r K : PTm n) : Syn.shift (sigr r K) = sigr (Syn.shift r) (Syn.shift K) := by simp [Syn.shift]

theorem sh_one : Syn.shift (one : PTm n) = one := by simp [Syn.shift]

theorem sigr_congr {r K K' : PTm n} (h : Γ ⊢[PRAAx] K ≐ K') : Γ ⊢[PRAAx] sigr r K ≐ sigr r K' :=
  congrAp2 _ (congrSucc h) (congrPairT h (.eqRefl _))

/-- A term of `c · σ_r(K)`. -/
theorem cm_at (k c K r : PTm n) :
    Γ ⊢[PRAAx] inst2 (cmB srB) k (pairT c (pairT K r)) ≐ c * (eqb (rem K k) zero * pw k r) := by
  rw [inst2_cmB, inst2_srB]
  have s : Γ ⊢[PRAAx] sndT (pairT c (pairT K r)) ≐ pairT K r := snd_pair _ _
  exact congrMul (fst_pair _ _) (congrMul
    (congrEqb' (congrAp2 remF ((congrFst s).eqTrans (fst_pair _ _)) (.eqRefl _)) (.eqRefl _))
    (congrAp2 powF ((congrSnd s).eqTrans (snd_pair _ _)) (.eqRefl _)))

theorem scale_alg {E A B C : PTm n} (h : Γ ⊢[PRAAx] A ≐ B * C) : Γ ⊢[PRAAx] E * A ≐ B * (E * C) := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination 𝔞 E * x

/-! ## Multiplicativity -/

theorem inner_pt (b a m N r : PTm n) :
    Γ ⊢[PRAAx] inst2 (DivisorFactor.riB gP) b (pairT a (Xp m N r)) ≐
      inst2 (cmB srB) b (pairT (pw a r) (pairT N r)) := by
  have h := riB_at (Γ := Γ) gP b a m N r
  rw [inst2_gP] at h
  exact h.eqTrans ((scale_alg (pw_mul_base a b r)).eqTrans (cm_at b (pw a r) N r).eqSymm)

/-- `∑_{b < N+1} [b ∣ N] (ab)^r = a^r σ_r(N)`. -/
theorem inner_sum (a m N r : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (DivisorFactor.riB gP)) (succ N) (pairT a (Xp m N r)) ≐ pw a r * sigr r N := by
  refine Prf.eqTrans ?_ (sum_const_mul srB (succ N) (pw a r) (pairT N r))
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, sh_pw]
  exact inner_pt _ _ _ _ _

theorem left_pt (d m N r : PTm n) :
    Γ ⊢[PRAAx] inst2 srB d (pairT (m * N) r) ≐ inst2 (DivisorFactor.lB gP) d (Xp m N r) := by
  have h := lB_at (Γ := Γ) gP d m N r
  rw [inst2_gP] at h
  exact (srB_at d (m * N) r).eqTrans h.eqSymm

theorem assoc_alg {E P S : PTm n} : Γ ⊢[PRAAx] E * (P * S) ≐ S * (E * P) := by
  apply deriveNat; ipra_simps; ring

theorem right_pt (a m N r : PTm n) :
    Γ ⊢[PRAAx] inst2 (DivisorFactor.rB gP) a (Xp m N r) ≐ inst2 (cmB srB) a (pairT (sigr r N) (pairT m r)) :=
  (rB_at gP a m N r).eqTrans ((congrMul (.eqRefl _) (inner_sum a m N r)).eqTrans
    (assoc_alg.eqTrans (cm_at a (sigr r N) m r).eqSymm))

/-- **`σ_r(mN) = σ_r(m) σ_r(N)`** for coprime `m, N ≥ 1`. -/
theorem sigr_mul {m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) (r : PTm n) : Γ ⊢[PRAAx] sigr r (m * N) ≐ sigr r m * sigr r N := by
  have l : Γ ⊢[PRAAx] sigr r (m * N) ≐ ap2 (sumF (DivisorFactor.lB gP)) (succ (m * N)) (Xp m N r) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, shift_mul']
    exact left_pt _ _ _ _
  have rr : Γ ⊢[PRAAx] ap2 (sumF (DivisorFactor.rB gP)) (succ m) (Xp m N r) ≐
      ap2 (sumF (cmB srB)) (succ m) (pairT (sigr r N) (pairT m r)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, sh_sigr]
    exact right_pt _ _ _ _
  have f := divisor_factor gP hm hN hc r
  exact l.eqTrans (f.eqTrans (rr.eqTrans ((sum_const_mul srB (succ m) (sigr r N) (pairT m r)).eqTrans
    (mul_comm _ _))))

/-! ## Prime powers: the bodies -/

/-- `[pk ∣ pQ] (pk)^r` over `0 = k`, `1 = ⟨p, ⟨Q, r⟩⟩`. -/
def hrB : PTm 2 := eqb (rem (fstT (var 1) * fstT (sndT (var 1))) (fstT (var 1) * var 0)) zero *
  pw (fstT (var 1) * var 0) (sndT (sndT (var 1)))

/-- `(1 − [p ∣ d]) [d ∣ P] d^r` over `0 = d`, `1 = ⟨p, ⟨P, r⟩⟩`. -/
def nrB : PTm 2 := monus one (eqb (rem (var 0) (fstT (var 1))) zero) *
  (eqb (rem (fstT (sndT (var 1))) (var 0)) zero * pw (var 0) (sndT (sndT (var 1))))

theorem hrB_at (k p Q r : PTm n) :
    Γ ⊢[PRAAx] inst2 hrB k (pairT p (pairT Q r)) ≐ eqb (rem (p * Q) (p * k)) zero * pw (p * k) r := by
  have e : inst2 hrB k (pairT p (pairT Q r)) =
      eqb (rem (fstT (pairT p (pairT Q r)) * fstT (sndT (pairT p (pairT Q r))))
        (fstT (pairT p (pairT Q r)) * k)) zero *
      pw (fstT (pairT p (pairT Q r)) * k) (sndT (sndT (pairT p (pairT Q r)))) := by simp [inst2, hrB]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT p (pairT Q r)) ≐ pairT Q r := snd_pair _ _
  have f : Γ ⊢[PRAAx] fstT (pairT p (pairT Q r)) ≐ p := fst_pair _ _
  exact congrMul (congrEqb' (congrAp2 remF (congrMul f ((congrFst s).eqTrans (fst_pair _ _)))
    (congrMul f (.eqRefl _))) (.eqRefl _))
    (congrAp2 powF ((congrSnd s).eqTrans (snd_pair _ _)) (congrMul f (.eqRefl _)))

theorem nrB_at (d p P r : PTm n) :
    Γ ⊢[PRAAx] inst2 nrB d (pairT p (pairT P r)) ≐
      monus one (eqb (rem d p) zero) * (eqb (rem P d) zero * pw d r) := by
  have e : inst2 nrB d (pairT p (pairT P r)) = monus one (eqb (rem d (fstT (pairT p (pairT P r)))) zero) *
      (eqb (rem (fstT (sndT (pairT p (pairT P r)))) d) zero * pw d (sndT (sndT (pairT p (pairT P r))))) := by
    simp [inst2, nrB]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT p (pairT P r)) ≐ pairT P r := snd_pair _ _
  exact congrMul (congrMonus (.eqRefl _) (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _)))
    (congrMul (congrEqb' (congrAp2 remF ((congrFst s).eqTrans (fst_pair _ _)) (.eqRefl _)) (.eqRefl _))
      (congrAp2 powF ((congrSnd s).eqTrans (snd_pair _ _)) (.eqRefl _)))

/-! ## Prime powers: pointwise -/

theorem split_alg0 {X b mb H : PTm n} (hb : Γ ⊢[PRAAx] b ≐ zero) (hm : Γ ⊢[PRAAx] mb ≐ one) :
    Γ ⊢[PRAAx] X ≐ b * H + mb * X := by
  have eb := natEq hb; have em := natEq hm
  apply deriveNat; ipra_simps; linear_combination -(𝔞 H * eb) - 𝔞 X * em

theorem split_alg1 {X b mb H : PTm n} (hb : Γ ⊢[PRAAx] b ≐ one) (hm : Γ ⊢[PRAAx] mb ≐ zero)
    (hH : Γ ⊢[PRAAx] H ≐ X) : Γ ⊢[PRAAx] X ≐ b * H + mb * X := by
  have eb := natEq hb; have em := natEq hm; have eh := natEq hH
  apply deriveNat; ipra_simps; linear_combination -(𝔞 H * eb) - eh - 𝔞 X * em

/-- `[d ∣ pQ] d^r = [p ∣ d] h(d/p) + (1 − [p ∣ d]) [d ∣ pQ] d^r`. -/
theorem split_core {p Q : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (d r : PTm n) :
    Γ ⊢[PRAAx] eqb (rem (p * Q) d) zero * pw d r ≐
      eqb (rem d p) zero * inst2 hrB (quo d p) (pairT p (pairT Q r)) +
        monus one (eqb (rem d p) zero) * (eqb (rem (p * Q) d) zero * pw d r) := by
  refine .orE (eqb_cases (Γ := Γ) (rem d p) zero) ?_ ?_
  · have m1 : ((eqb (rem d p) zero ≐ zero) :: Γ) ⊢[PRAAx] monus one (eqb (rem d p) zero) ≐ one :=
      (congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _)
    exact split_alg0 Prf.hyp0 m1
  · let C : List (Fm PTm n) := (eqb (rem d p) zero ≐ one) :: Γ
    have hb : C ⊢[PRAAx] eqb (rem d p) zero ≐ one := Prf.hyp0
    have m0 : C ⊢[PRAAx] monus one (eqb (rem d p) zero) ≐ zero :=
      (congrMonus (.eqRefl _) hb).eqTrans (monus_self _)
    have ed : C ⊢[PRAAx] d ≐ p * quo d p := eq_of_rem_zero hp.wk (eq_of_eqb hb)
    have h1 : C ⊢[PRAAx] inst2 hrB (quo d p) (pairT p (pairT Q r)) ≐ eqb (rem (p * Q) d) zero * pw d r :=
      (hrB_at _ _ _ _).eqTrans (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) ed.eqSymm) (.eqRefl _))
        (congrAp2 powF (.eqRefl _) ed.eqSymm))
    exact split_alg1 hb m0 h1

theorem split_r {p Q : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (d r : PTm n) :
    Γ ⊢[PRAAx] inst2 srB d (pairT (p * Q) r) ≐
      inst2 (SumReindex.riB hrB) d (pairT p (pairT p (pairT Q r))) + inst2 nrB d (pairT p (pairT (p * Q) r)) := by
  rw [inst2_riB]
  refine (srB_at d (p * Q) r).eqTrans ((split_core hp d r).eqTrans (congrAdd ?_ (nrB_at _ _ _ _).eqSymm))
  exact (congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (.eqRefl _))
    (congrInst2 hrB (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))).eqSymm

theorem mult_pt {p Q : PTm n} (hp : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q))
    (k r : PTm n) :
    Γ ⊢[PRAAx] inst2 hrB k (pairT p (pairT Q r)) ≐ inst2 (cmB srB) k (pairT (pw p r) (pairT Q r)) :=
  (hrB_at k p Q r).eqTrans ((congrMul (dvd_scale hp hQ k) (.eqRefl _)).eqTrans
    ((scale_alg (pw_mul_base p k r)).eqTrans (cm_at k (pw p r) Q r).eqSymm))

theorem bit_alg {m E d w : PTm n} (h : Γ ⊢[PRAAx] d ≐ w) : Γ ⊢[PRAAx] m * (E * w) ≐ m * (E * d) := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination -(𝔞 m * 𝔞 E * x)

theorem zero_alg {m E w : PTm n} (h : Γ ⊢[PRAAx] m * E ≐ zero) : Γ ⊢[PRAAx] m * (E * w) ≐ zero := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination 𝔞 w * x

theorem rot_alg {m E d : PTm n} (h : Γ ⊢[PRAAx] m * (E * d) ≐ zero) : Γ ⊢[PRAAx] (m * E) * d ≐ zero := by
  have x := natEq h
  apply deriveNat; ipra_simps; linear_combination x

/-- The non-multiples of `p` dividing `p · p^a`, with the weight `d^r`: only `d = 1`. -/
theorem rest_w {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a d r : PTm n) :
    Γ ⊢[PRAAx] monus one (eqb (rem d p) zero) * (eqb (rem (p * pw p a) d) zero * pw d r) ≐ eqb one d * one := by
  have hp1 := prime_eq_succ_pred hp
  have hP := pos_mul hp1 (pos_pw hp1 a)
  have R := rest_pt hp a d
  refine .orE (eqb_cases (Γ := Γ) one d) ?_ ?_
  · -- `d ≠ 1`: the bit `m E` vanishes
    let C : List (Fm PTm n) := (eqb one d ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] eqb one d ≐ zero := Prf.hyp0
    have Rz : C ⊢[PRAAx] monus one (eqb (rem d p) zero) * (eqb (rem (p * pw p a) d) zero * d) ≐ zero :=
      R.wk.eqTrans ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _))
    have rz : C ⊢[PRAAx] eqb one d * one ≐ zero := (congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)
    refine Prf.eqTrans ?_ rz.eqSymm
    refine .orE (zero_or_succ d) ?_ ?_
    · -- `d = 0` does not divide `P ≥ 1`
      let C' : List (Fm PTm n) := (d ≐ zero) :: C
      have hd : C' ⊢[PRAAx] d ≐ zero := Prf.hyp0
      have rP : C' ⊢[PRAAx] rem (p * pw p a) d ≐ p * pw p a :=
        (congrAp2 remF (.eqRefl _) hd).eqTrans (rem_by_zero _)
      have ne : C' ⊢[PRAAx] neg (rem (p * pw p a) d ≐ zero) :=
        .impI (succ_ne_zero' _ (hP.wk.wk.wk.eqSymm.eqTrans (rP.wk.eqSymm.eqTrans Prf.hyp0)))
      have E0 : C' ⊢[PRAAx] eqb (rem (p * pw p a) d) zero ≐ zero := eqb_of_ne ne
      exact (congrMul (.eqRefl _) ((congrMul E0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
    · let C' : List (Fm PTm n) := (d ≐ succ (pred d)) :: C
      have hd : C' ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
      refine .orE (zero_or_zero_of_mul (rot_alg Rz.wk)) ?_ ?_
      · exact zero_alg Prf.hyp0
      · exact succ_ne_zero' _ (hd.wk.eqSymm.eqTrans Prf.hyp0)
  · -- `d = 1`: `d^r = 1 = d`
    let C : List (Fm PTm n) := (eqb one d ≐ one) :: Γ
    have d1 : C ⊢[PRAAx] one ≐ d := eq_of_eqb Prf.hyp0
    have w : C ⊢[PRAAx] d ≐ pw d r :=
      d1.eqSymm.eqTrans ((pw_one_base r).eqSymm.eqTrans (congrAp2 powF (.eqRefl _) d1))
    exact (bit_alg w).eqTrans R.wk

theorem rest_r {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a d r : PTm n) :
    Γ ⊢[PRAAx] inst2 nrB d (pairT p (pairT (p * pw p a) r)) ≐ inst2 (dB (var 1 : PTm 2)) d (pairT one one) := by
  rw [inst2_dB, inst2_v1]
  refine (nrB_at d p _ r).eqTrans ((rest_w hp a d r).eqTrans ?_)
  exact congrMul (congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)) (snd_pair _ _).eqSymm

/-! ## The recursion `σ_r(p^{a+1}) = p^r σ_r(p^a) + 1` -/

/-- **`σ_r(p · p^a) = p^r σ_r(p^a) + 1`** for a prime `p`. -/
theorem sigr_step {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a r : PTm n) :
    Γ ⊢[PRAAx] sigr r (p * pw p a) ≐ pw p r * sigr r (pw p a) + one := by
  have hp1 := prime_eq_succ_pred hp
  have hQ := pos_pw hp1 a
  have hP := pos_mul hp1 hQ
  have hp1' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift p ≐ succ (pred (Syn.shift p)) := by
    simpa [Fm.shift, Syn.shift] using hp1.shift
  have hQ' : Γ.map Fm.shift ⊢[PRAAx] pw (Syn.shift p) (Syn.shift a) ≐ succ (pred (pw (Syn.shift p) (Syn.shift a))) :=
    pos_pw hp1' _
  have hpr' := prime_shift hp
  -- split every term
  have sp := sum_add2 (Γ := Γ) (SumReindex.riB hrB) nrB srB (K := succ (p * pw p a))
    (x := pairT p (pairT p (pairT (pw p a) r))) (x' := pairT p (pairT (p * pw p a) r))
    (z := pairT (p * pw p a) r) (.allI (.impI (by
      simp only [shift_pairT, sh_P, sh_pw]
      exact split_r hp1'.wk _ _)))
  -- the multiples of `p`
  have cm : Γ ⊢[PRAAx] cM (succ (p * pw p a)) p ≐ succ (pw p a) :=
    (multiples_upto hp1).eqTrans (congrSucc (quo_mul hp1 (.eqRefl _)))
  have p1 : Γ ⊢[PRAAx] ap2 (sumF (SumReindex.riB hrB)) (succ (p * pw p a)) (pairT p (pairT p (pairT (pw p a) r))) ≐
      pw p r * sigr r (pw p a) := by
    refine (reindex_eq hrB (succ (p * pw p a)) hp1).eqTrans ((congrAp2 _ cm (.eqRefl _)).eqTrans ?_)
    refine Prf.eqTrans ?_ (sum_const_mul srB (succ (pw p a)) (pw p r) (pairT (pw p a) r))
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, sh_pw]
    exact mult_pt hp1'.wk hQ'.wk _ _
  -- the rest: only `d = 1`
  have p2 : Γ ⊢[PRAAx] ap2 (sumF nrB) (succ (p * pw p a)) (pairT p (pairT (p * pw p a) r)) ≐ one := by
    have h1 : Γ ⊢[PRAAx] lt one (succ (p * pw p a)) := by
      have l := one_le_of_pos hP
      ipra_le sl l
    refine Prf.eqTrans ?_ ((sum_delta (var 1) (x := one) h1).eqTrans (by rw [inst2_v1]; exact .eqRefl _))
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, sh_P, sh_one]
    exact rest_r hpr'.wk _ _ _
  exact sp.eqTrans (congrAdd p1 p2)

/-! ## Values at `1` and at prime powers -/

/-- `σ_r(1) = 1`. -/
theorem sigr_one (r : PTm n) : Γ ⊢[PRAAx] sigr r one ≐ one := by
  refine (sum_succ _ _ _).eqTrans ?_
  refine (congrAdd ((sum_succ _ _ _).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans (zero_add _)))
    (.eqRefl _)).eqTrans ?_
  have e0 : Γ ⊢[PRAAx] Syn.subst ![zero, pairT one r] srB ≐ zero := by
    show Γ ⊢[PRAAx] inst2 srB zero (pairT one r) ≐ zero
    have ne : Γ ⊢[PRAAx] neg (rem (one : PTm n) zero ≐ zero) :=
      .impI (succ_ne_zero' _ ((rem_by_zero (one : PTm n)).wk.eqSymm.eqTrans Prf.hyp0))
    exact (srB_at _ _ _).eqTrans ((congrMul (eqb_of_ne ne) (.eqRefl _)).eqTrans (zero_mul _))
  have e1 : Γ ⊢[PRAAx] Syn.subst ![one, pairT one r] srB ≐ one := by
    show Γ ⊢[PRAAx] inst2 srB one (pairT one r) ≐ one
    exact (srB_at _ _ _).eqTrans ((congrMul (eqb_of_eq (rem_one _)) (pw_one_base r)).eqTrans (one_mul _))
  exact (congrAdd e0 e1).eqTrans (zero_add _)

/-- `σ_r(p^{a+1}) = p^r σ_r(p^a) + 1`. -/
theorem sigr_succ {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a r : PTm n) :
    Γ ⊢[PRAAx] sigr r (pw p (succ a)) ≐ pw p r * sigr r (pw p a) + one :=
  (sigr_congr ((pw_succ _ _).eqTrans (mul_comm _ _))).eqTrans (sigr_step hp a r)

theorem tau_alg {S S1 P a : PTm n} (h : Γ ⊢[PRAAx] S1 ≐ P * S + one) (hP : Γ ⊢[PRAAx] P ≐ one)
    (ih : Γ ⊢[PRAAx] S ≐ succ a) : Γ ⊢[PRAAx] S1 ≐ succ (succ a) := by
  have x := natEq h; have y := natEq hP; have z := natEq ih
  apply deriveNat; ipra_simps; linear_combination x + 𝔞 S * y + z

/-- **`τ(p^a) = a + 1`** for a prime `p` (`τ = σ_0`). -/
theorem tau_pow {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a : PTm n) : Γ ⊢[PRAAx] sigr zero (pw p a) ≐ succ a := by
  have hall : Γ ⊢[PRAAx] Fm.all (sigr zero (pw (Syn.shift p) (var 0)) ≐ succ (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (sigr_congr (pw_zero p)).eqTrans (sigr_one zero)
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := (sigr zero (pw (Syn.shift p) (var 0)) ≐ succ (var 0)) :: Γ.map Fm.shift
      have hpr : Δ ⊢[PRAAx] prime (Syn.shift p) := (prime_shift hp).wk
      exact tau_alg (sigr_succ hpr (var 0) zero) (pw_zero _) Prf.hyp0
  have h2 := Prf.allE a hall
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact h2

/-! ## The geometric sum -/

/-- `x^j` over `0 = j`, `1 = x`. -/
abbrev geoB : PTm 2 := pw (var 1) (var 0)

/-- `geo x a = ∑_{j ≤ a} x^j`. -/
abbrev geo (x a : PTm n) : PTm n := ap2 (sumF geoB) (succ a) x

theorem geo_succ (x a : PTm n) : Γ ⊢[PRAAx] geo x (succ a) ≐ geo x a + pw x (succ a) := by
  have h := sum_succ (Γ := Γ) geoB (succ a) x
  have e : Syn.subst ![succ a, x] (geoB : PTm 2) = pw x (succ a) := by simp
  rw [e] at h; exact h

theorem geo_zero (x : PTm n) : Γ ⊢[PRAAx] geo x zero ≐ one := by
  have h := sum_succ (Γ := Γ) geoB zero x
  have e : Syn.subst ![zero, x] (geoB : PTm 2) = pw x zero := by simp
  rw [e] at h
  exact h.eqTrans ((congrAdd (sum_zero _ _) (pw_zero x)).eqTrans (zero_add _))

theorem rev_base_alg {G0 G1 P1 P0 x : PTm n} (s1 : Γ ⊢[PRAAx] G1 ≐ G0 + P1) (g0 : Γ ⊢[PRAAx] G0 ≐ one)
    (p1 : Γ ⊢[PRAAx] P1 ≐ P0 * x) (p0 : Γ ⊢[PRAAx] P0 ≐ one) : Γ ⊢[PRAAx] G1 ≐ x * G0 + one := by
  have a := natEq s1; have b := natEq g0; have c := natEq p1; have d := natEq p0
  apply deriveNat; ipra_simps; linear_combination a + (1 - 𝔞 x) * b + c + 𝔞 x * d

theorem rev_step_alg {G0 G1 G2 P1 P2 x : PTm n} (s2 : Γ ⊢[PRAAx] G2 ≐ G1 + P2) (p2 : Γ ⊢[PRAAx] P2 ≐ P1 * x)
    (ih : Γ ⊢[PRAAx] G1 ≐ x * G0 + one) (s1 : Γ ⊢[PRAAx] G1 ≐ G0 + P1) : Γ ⊢[PRAAx] G2 ≐ x * G1 + one := by
  have a := natEq s2; have b := natEq p2; have c := natEq ih; have d := natEq s1
  apply deriveNat; ipra_simps; linear_combination a + b + c - 𝔞 x * d

/-- `geo x (a + 1) = x · geo x a + 1`. -/
theorem geo_rev (x a : PTm n) : Γ ⊢[PRAAx] geo x (succ a) ≐ x * geo x a + one := by
  have hall : Γ ⊢[PRAAx] Fm.all (geo (Syn.shift x) (succ (var 0)) ≐ Syn.shift x * geo (Syn.shift x) (var 0) + one) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact rev_base_alg (geo_succ x zero) (geo_zero x) (pw_succ x zero) (pw_zero x)
    · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact rev_step_alg (geo_succ _ _) (pw_succ _ _) Prf.hyp0 (geo_succ _ _)
  have h2 := Prf.allE a hall
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact h2

/-- **`σ_r(p^a) = ∑_{j ≤ a} (p^r)^j`** for a prime `p`. -/
theorem sigr_pow {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a r : PTm n) :
    Γ ⊢[PRAAx] sigr r (pw p a) ≐ geo (pw p r) a := by
  have hall : Γ ⊢[PRAAx] Fm.all (sigr (Syn.shift r) (pw (Syn.shift p) (var 0)) ≐
      geo (pw (Syn.shift p) (Syn.shift r)) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact (sigr_congr (pw_zero p)).eqTrans ((sigr_one r).eqTrans (geo_zero _).eqSymm)
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let Δ : List (Fm PTm (n + 1)) := (sigr (Syn.shift r) (pw (Syn.shift p) (var 0)) ≐
        geo (pw (Syn.shift p) (Syn.shift r)) (var 0)) :: Γ.map Fm.shift
      have hpr : Δ ⊢[PRAAx] prime (Syn.shift p) := (prime_shift hp).wk
      have ih : Δ ⊢[PRAAx] sigr (Syn.shift r) (pw (Syn.shift p) (var 0)) ≐
          geo (pw (Syn.shift p) (Syn.shift r)) (var 0) := Prf.hyp0
      exact (sigr_succ hpr (var 0) (Syn.shift r)).eqTrans ((congrAdd (congrMul (.eqRefl _) ih) (.eqRefl _)).eqTrans
        (geo_rev _ _).eqSymm)
  have h2 := Prf.allE a hall
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact h2

/-! ## `σ_1 = σ` -/

theorem pw_one_exp (d : PTm n) : Γ ⊢[PRAAx] pw d one ≐ d :=
  (pw_succ d zero).eqTrans ((congrMul (pw_zero d) (.eqRefl _)).eqTrans (one_mul _))

theorem one_pt (d K : PTm n) : Γ ⊢[PRAAx] inst2 srB d (pairT K one) ≐ inst2 sB d K := by
  rw [inst2_sB]
  exact (srB_at d K one).eqTrans (congrMul (.eqRefl _) (pw_one_exp d))

/-- `σ_1(K) = σ(K)`. -/
theorem sigr_one_exp (K : PTm n) : Γ ⊢[PRAAx] sigr one K ≐ sig K := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, sh_one]
  exact one_pt _ _

end LeanProofs.IPRA.AnalyticNumberTheory.SigmaR
