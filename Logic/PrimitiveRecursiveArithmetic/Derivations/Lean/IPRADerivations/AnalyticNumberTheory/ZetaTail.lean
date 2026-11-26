import IPRADerivations.AnalyticNumberTheory.SquareReciprocal
import IPRADerivations.AnalyticNumberTheory.Smooth
import IPRADerivations.AnalyticNumberTheory.PhiDivides
import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The rational tail estimate for `∑ 1/n^s`, every `s ≥ 2`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, `an:zetatail`:

  "For `M ≥ N ≥ 1` and `s ≥ 2`, `0 ≤ Z_s(M) − Z_s(N) ≤ N^{1−s} − M^{1−s} ≤ N^{1−s}`", with `Z_s(N) = ∑_{n ≤ N} 1/n^s`.

The packet's proof is the pointwise telescoping inequality `1/n^s ≤ 1/(n−1)^{s−1} − 1/n^{s−1}`, from the
difference of powers. Here `s = t + 1` with `t = u + 1 ≥ 1`, and the rationals are cleared by a common numerator `F`
(for instance `F = (M!)^s`, which makes every quotient below exact):

* `key`: `m^t (m + 2) ≤ (m + 1)^{t+1}` for `t ≥ 1` (induction on `t`);
* **`pt`**: for `m ≥ 1`, `n = m + 1` and `n^t ∣ F`, `m^t ∣ F`: `⌊F/n^s⌋ + F/n^t ≤ F/m^t`, the cleared form of
  `1/n^s ≤ 1/(n−1)^{s−1} − 1/n^{s−1}`. The proof multiplies by `n · m^t · n^t` and uses the certificate
  `n (n^t F − m^t F − n^t m^t Q) = F (n^{t+1} − m^t (n + 1)) + m^t (F − n^{t+1} Q)`;
* `Ex`, `exact_at`: the exactness hypothesis `n^t ∣ F` for `1 ≤ n ≤ M` as one quantifier-free equation;
* **`zeta_tail`**: for `N ≥ 1`, `M = N + K` and `n^t ∣ F` for `n ≤ M`,
  `∑_{n=N+1}^{M} ⌊F/n^s⌋ + F/M^{s−1} ≤ F/N^{s−1}` (telescoping, induction on `K`);
* `exact_t`, `exact_s`: for `F = (M!)^s` every `n^{s−1}` and every `n^s` with `n ≤ M` divides `F`, so all the
  quotients are exact and **`zeta_tail_fact`** is the packet's inequality `Z_s(M) − Z_s(N) ≤ N^{1−s} − M^{1−s}` times
  `F`. The lower bound `0 ≤ Z_s(M) − Z_s(N)` holds because the left sum has natural terms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ZetaTail

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos dvd_fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.Smooth (pw_dvd_base pw_dvd_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiDivides (sg_zero_inv)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' dvd_trans')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The difference of powers -/

theorem key_base (m : PTm n) :
    Γ ⊢[PRAAx] le (pw m one * succ (succ m)) (pw (succ m) (succ one)) := by
  refine le_of_eq_add (d := one) ?_
  ipra_lc natEq (pw_succ (Γ := Γ) (succ m) one) + (𝔞 m + 1) * natEq (pw_one (Γ := Γ) (succ m)) -
    (𝔞 m + 2) * natEq (pw_one (Γ := Γ) m)

theorem key_step {m u : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw m (succ u) * succ (succ m)) (pw (succ m) (succ (succ u)))) :
    Γ ⊢[PRAAx] le (pw m (succ (succ u)) * succ (succ m)) (pw (succ m) (succ (succ (succ u)))) := by
  have e1 := natEq (pw_succ (Γ := Γ) m (succ u))
  have e2 := natEq (pw_succ (Γ := Γ) (succ m) (succ (succ u)))
  ipra_le 𝔞 m * sl ih + 𝔞 (pw (succ m) (succ (succ u))) with e2 - (𝔞 m + 2) * e1

/-- Variables: `0 = u`, `1 = m`. -/
abbrev keyF : Fm PTm 2 :=
  le (pw (var 1) (succ (var 0)) * succ (succ (var 1))) (pw (succ (var 1)) (succ (succ (var 0))))

theorem key_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] keyF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact key_base _
  · exact key_step Prf.hyp0

/-- `m^t (m + 2) ≤ (m + 1)^{t+1}` for `t = u + 1 ≥ 1`. -/
theorem key (m u : PTm n) :
    Γ ⊢[PRAAx] le (pw m (succ u) * succ (succ m)) (pw (succ m) (succ (succ u))) := by
  have i := inst (Γ := Γ) key_open (![u, m] : Fin 2 → PTm n)
  simp only [keyF, subst_le, PTm.subst_mul, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact i

/-! ## The pointwise telescoping inequality -/

alias succ_pos' := Common.succ_pos

theorem core_mul {m u F Q : PTm n}
    (h1 : Γ ⊢[PRAAx] le (pw (succ m) (succ (succ u)) * Q) F) :
    Γ ⊢[PRAAx] le (succ m * (pw (succ m) (succ u) * pw m (succ u) * Q + pw m (succ u) * F))
      (succ m * (pw (succ m) (succ u) * F)) := by
  have k := key (Γ := Γ) m u
  have eP := natEq (pw_succ (Γ := Γ) (succ m) (succ u))
  ipra_le 𝔞 F * sl k + 𝔞 (pw m (succ u)) * sl h1 with
    (𝔞 F - 𝔞 (pw m (succ u)) * 𝔞 Q) * eP

theorem conv_alg {X Y Q Gn Gm F : PTm n} (e1 : Γ ⊢[PRAAx] F ≐ X * Gn) (e2 : Γ ⊢[PRAAx] F ≐ Y * Gm) :
    (Γ ⊢[PRAAx] X * Y * Q + Y * F ≐ (X * Y) * (Q + Gn)) ∧ (Γ ⊢[PRAAx] X * F ≐ (X * Y) * Gm) := by
  have a := natEq e1; have b := natEq e2
  exact ⟨by apply deriveNat; ipra_simps; linear_combination 𝔞 Y * a,
    by apply deriveNat; ipra_simps; linear_combination 𝔞 X * b⟩

/-- **The pointwise inequality**: for `m ≥ 1`, `n = m + 1`, `t = u + 1`, `n^t ∣ F` and `m^t ∣ F`,
`⌊F/n^{t+1}⌋ + F/n^t ≤ F/m^t`. -/
theorem pt {m u F : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hn : Γ ⊢[PRAAx] rem F (pw (succ m) (succ u)) ≐ zero) (hk : Γ ⊢[PRAAx] rem F (pw m (succ u)) ≐ zero) :
    Γ ⊢[PRAAx] le (quo F (pw (succ m) (succ (succ u))) + quo F (pw (succ m) (succ u)))
      (quo F (pw m (succ u))) := by
  have Xp := pw_pos' (succ_pos' (Γ := Γ) m) (succ u)
  have Yp := pw_pos' hm (succ u)
  have Pp := pw_pos' (succ_pos' (Γ := Γ) m) (succ (succ u))
  have e1 : Γ ⊢[PRAAx] F ≐ pw (succ m) (succ u) * quo F (pw (succ m) (succ u)) := eq_of_dvd' Xp hn
  have e2 : Γ ⊢[PRAAx] F ≐ pw m (succ u) * quo F (pw m (succ u)) := eq_of_dvd' Yp hk
  have h1 : Γ ⊢[PRAAx] le (pw (succ m) (succ (succ u)) * quo F (pw (succ m) (succ (succ u)))) F :=
    le_of_eq_add (d := rem F (pw (succ m) (succ (succ u)))) (div_eq Pp)
  have c := cancel_le (succ_pos' m) (core_mul h1)
  have cv := conv_alg (Q := quo F (pw (succ m) (succ (succ u)))) e1 e2
  exact cancel_le (Combinatorics.Binomial.pos_mul Xp Yp) (le_congr cv.1 cv.2 c)

/-! ## Exactness as one equation -/

/-- `[F mod (i + 1)^t ≠ 0]`, over `0 = i`, `1 = ⟨F, u⟩`, `t = u + 1`. -/
abbrev vB : PTm 2 := sg (rem (fstT (var 1)) (pw (succ (var 0)) (succ (sndT (var 1)))))

theorem inst2_v (i y : PTm n) : inst2 vB i y = sg (rem (fstT y) (pw (succ i) (succ (sndT y)))) := by
  simp [inst2]

theorem v_at (i F u : PTm n) :
    Γ ⊢[PRAAx] inst2 vB i (pairT F u) ≐ sg (rem F (pw (succ i) (succ u))) := by
  rw [inst2_v]
  exact congrSg (congrAp2 remF (fst_pair _ _) (congrPw (.eqRefl _) (congrSucc (snd_pair _ _))))

/-- `Ex(M) = ∑_{i < M} [F mod (i + 1)^t ≠ 0]`: zero when `n^t ∣ F` for `1 ≤ n ≤ M`. -/
abbrev Ex (F u M : PTm n) : PTm n := ap2 (sumF vB) M (pairT F u)

theorem exact_at {F u M i : PTm n} (h : Γ ⊢[PRAAx] Ex F u M ≐ zero) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] rem F (pw (succ i) (succ u)) ≐ zero :=
  sg_zero_inv ((v_at i F u).eqSymm.eqTrans (sum_zero_elim vB h hi))

alias left_zero := Common.add_eq_zero_left

alias right_zero := Common.add_eq_zero_right

/-! ## Telescoping -/

/-- The tail term `⌊F/(N + k + 1)^{t+1}⌋`, over `0 = k`, `1 = ⟨N, ⟨F, u⟩⟩`. -/
abbrev zB : PTm 2 :=
  quo (fstT (sndT (var 1))) (pw (succ (fstT (var 1) + var 0)) (succ (succ (sndT (sndT (var 1))))))

theorem inst2_z (k y : PTm n) :
    inst2 zB k y = quo (fstT (sndT y)) (pw (succ (fstT y + k)) (succ (succ (sndT (sndT y))))) := by
  simp [inst2]

abbrev P3 (N F u : PTm n) : PTm n := pairT N (pairT F u)

theorem z_at (k N F u : PTm n) :
    Γ ⊢[PRAAx] inst2 zB k (P3 N F u) ≐ quo F (pw (succ (N + k)) (succ (succ u))) := by
  rw [inst2_z]
  exact congrAp2 quoF ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrPw (congrSucc (congrAdd (fst_pair _ _) (.eqRefl _)))
      (congrSucc (congrSucc ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))))

/-- `S(K) = ∑_{k < K} ⌊F/(N + k + 1)^{t+1}⌋ = ∑_{n=N+1}^{N+K} ⌊F/n^s⌋`. -/
abbrev S (N F u K : PTm n) : PTm n := ap2 (sumF zB) K (P3 N F u)

/-- `G(x) = ⌊F/x^t⌋`. -/
abbrev G (F u x : PTm n) : PTm n := quo F (pw x (succ u))

theorem tele_alg {S0 Q Gs Gm GN : PTm n} (h1 : Γ ⊢[PRAAx] le (Q + Gs) Gm) (h2 : Γ ⊢[PRAAx] le (S0 + Gm) GN) :
    Γ ⊢[PRAAx] le ((S0 + Q) + Gs) GN := by
  ipra_le sl h1 + sl h2

theorem tele_step {N F u K : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (ih : Γ ⊢[PRAAx] (Ex F u (N + K) ≐ zero) ⟶ le (S N F u K + G F u (N + K)) (G F u N))
    (hE : Γ ⊢[PRAAx] Ex F u (N + succ K) ≐ zero) :
    Γ ⊢[PRAAx] le (S N F u (succ K) + G F u (N + succ K)) (G F u N) := by
  have eK : Γ ⊢[PRAAx] N + succ K ≐ succ (N + K) := add_succ N K
  have hE' : Γ ⊢[PRAAx] Ex F u (N + K) + inst2 vB (N + K) (pairT F u) ≐ zero :=
    (sum_succ' vB (N + K) (pairT F u)).eqSymm.eqTrans
      ((congrAp2 (sumF vB) eK (.eqRefl _)).eqSymm.eqTrans hE)
  have ih' := Prf.impE ih (left_zero hE')
  have hn : Γ ⊢[PRAAx] rem F (pw (succ (N + K)) (succ u)) ≐ zero :=
    sg_zero_inv ((v_at (N + K) F u).eqSymm.eqTrans (right_zero hE'))
  have mpos : Γ ⊢[PRAAx] N + K ≐ succ (pred (N + K)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (y := pred N + K)
      ((congrAdd hN (.eqRefl _)).eqTrans (by ipra_ring))
  have lt0 : Γ ⊢[PRAAx] lt (pred (N + K)) (N + K) :=
    le_congr (.eqRefl _) mpos.eqSymm (le_refl _)
  have hk0 := exact_at (left_zero hE') lt0
  have hk : Γ ⊢[PRAAx] rem F (pw (N + K) (succ u)) ≐ zero :=
    (congrAp2 remF (.eqRefl _) (congrPw mpos (.eqRefl _))).eqTrans hk0
  have p := pt mpos hn hk
  have eS : Γ ⊢[PRAAx] S N F u (succ K) ≐ S N F u K + quo F (pw (succ (N + K)) (succ (succ u))) :=
    (sum_succ' zB K (P3 N F u)).eqTrans (congrAdd (.eqRefl _) (z_at K N F u))
  have eG : Γ ⊢[PRAAx] G F u (N + succ K) ≐ G F u (succ (N + K)) :=
    congrAp2 quoF (.eqRefl _) (congrPw eK (.eqRefl _))
  exact le_congr (congrAdd eS eG).eqSymm (.eqRefl _) (tele_alg p ih')

/-- **`an:zetatail`, cleared**: for `N ≥ 1`, `t = u + 1`, `s = t + 1` and `n^t ∣ F` for `1 ≤ n ≤ N + K`,
`∑_{n=N+1}^{N+K} ⌊F/n^s⌋ + F/(N+K)^t ≤ F/N^t`. -/
theorem zeta_tail {N F u : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (K : PTm n)
    (hE : Γ ⊢[PRAAx] Ex F u (N + K) ≐ zero) :
    Γ ⊢[PRAAx] le (S N F u K + G F u (N + K)) (G F u N) := by
  have hN' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift N ≐ succ (pred (Syn.shift N)) := by
    simpa [Fm.shift, Syn.shift] using hN.shift
  have hall : Γ ⊢[PRAAx] Fm.all ((Ex (Syn.shift F) (Syn.shift u) (Syn.shift N + var 0) ≐ zero) ⟶
      le (S (Syn.shift N) (Syn.shift F) (Syn.shift u) (var 0) +
        G (Syn.shift F) (Syn.shift u) (Syn.shift N + var 0)) (G (Syn.shift F) (Syn.shift u) (Syn.shift N))) := by
    refine PRA.qfInd _ ⟨trivial, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have e0 : (Ex F u (N + zero) ≐ zero) :: Γ ⊢[PRAAx] S N F u zero + G F u (N + zero) ≐ G F u N :=
        (congrAdd (sum_zero _ _) (congrAp2 quoF (.eqRefl _) (congrPw (add_zero N) (.eqRefl _)))).eqTrans
          (zero_add _)
      exact le_congr e0.eqSymm (.eqRefl _) (le_refl _)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
        Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero,
        ConciseIPRA.PTm.subst_succ]
      exact .impI (tele_step hN'.wk.wk Prf.hyp1 Prf.hyp0)
  have h2 := Prf.allE K hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 hE

/-! ## The exact numerator `F = (M!)^s` -/

/-- `n^e ∣ (M!)^{e'}` for `1 ≤ n ≤ M` and `e ≤ e'`. -/
theorem dvd_fact_pw {i M e e' : PTm n} (hi : Γ ⊢[PRAAx] lt i M) (he : Γ ⊢[PRAAx] le e e') :
    Γ ⊢[PRAAx] dvd (pw (succ i) e) (pw (fact M) e') :=
  dvd_trans' (pw_pos' (succ_pos' i) e) (pw_pos' (fact_pos M) e)
    (pw_dvd_base e (succ_pos' i) (dvd_fact hi)) (pw_dvd_exp (fact_pos M) he)

/-- For `F = (M!)^{t+1}`: `n^t ∣ F` for `1 ≤ n ≤ M`. -/
theorem exact_t (M u : PTm n) : Γ ⊢[PRAAx] Ex (pw (fact M) (succ (succ u))) u M ≐ zero := by
  refine sum_zero_of_bounded vB (pairT (pw (fact M) (succ (succ u))) u) M (.allI (.impI ?_))
  have sY : Syn.shift (pairT (pw (fact M) (succ (succ u))) u) =
      pairT (pw (fact (Syn.shift M)) (succ (succ (Syn.shift u)))) (Syn.shift u) := by simp [Syn.shift]
  rw [sY]
  have d := dvd_fact_pw (e := succ (Syn.shift u)) (e' := succ (succ (Syn.shift u)))
    (Prf.hyp0 : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift M))
    (le_succ_self _)
  exact (v_at _ _ _).eqTrans ((congrSg d).eqTrans sg_zero)

/-- For `F = (M!)^{t+1}` the quotients `⌊F/n^{t+1}⌋`, `1 ≤ n ≤ M`, are exact. -/
theorem exact_s {M u i : PTm n} (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] rem (pw (fact M) (succ (succ u))) (pw (succ i) (succ (succ u))) ≐ zero :=
  dvd_fact_pw hi (le_refl _)

/-- **`an:zetatail`**: with `F = (M!)^s`, `M = N + K`, `s = u + 2 ≥ 2` and `N ≥ 1`, all quotients exact,
`F (Z_s(M) − Z_s(N)) + F/M^{s−1} ≤ F/N^{s−1}`. -/
theorem zeta_tail_fact {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (K u : PTm n) :
    Γ ⊢[PRAAx] le (S N (pw (fact (N + K)) (succ (succ u))) u K +
        G (pw (fact (N + K)) (succ (succ u))) u (N + K))
      (G (pw (fact (N + K)) (succ (succ u))) u N) :=
  zeta_tail hN K (exact_t (N + K) u)

end LeanProofs.IPRA.AnalyticNumberTheory.ZetaTail
