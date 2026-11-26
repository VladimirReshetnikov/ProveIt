import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The weighted von Mangoldt function

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Definition `def:weighted-lambda`
and Theorem `thm:lambda-divsum`.

For a weight body `w(q, y)` on primes:

* `Lw m y = L_w(m) = ∑_{q ≤ m} [q prime] v_q(m) w(q)`, the completely additive weight;
* `Lam d y = Λ_w(d) = ∑_{q ≤ d} [q prime][d = q^a, a ≥ 1] w(q)`, the weight of the base of a prime
  power and `0` otherwise (a prime power has one prime base, so this is the packet's `w(ppBase(d))`);
* powers: `p^a < p^b` for `a < b` (`pw_lt_exp`), `v_p(p^j) = j` (`val_pw`), and
  `p^j ∣ m ⟺ j ≤ v_p(m)` (`dvd_iff_le_val`);
* `count_cnt`: the divisors of `m ≥ 1` that are positive powers of a prime `p` number exactly `v_p(m)`:
  each is `∑_{k < v_p(m)} [d = p^{k+1}]` (`pp_pt`, via `[p^j = p^{k+1}] = [j = k + 1]` and `jsum`),
  and after exchanging the two sums each `k` contributes the single divisor `p^{k+1}` (`col_one`);
* `lambda_divsum` (`thm:lambda-divsum`): `∑_{d ∣ m} Λ_w(d) = L_w(m)` for `m ≥ 1`, by exchanging the sum over
  divisors and the sum over primes (`row_lam`, `col_lam`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos val_big)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP isP_01 isP_of_prime prime_of_isP pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_unique not_dvd_one p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_trans' dvd_le' one_le_of_pos)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eqb_comm')
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (shift_inst2)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Powers of a fixed base -/

section Powers

variable {p : PTm n}

/-- `a < b → p^a < p^b` for `p ≥ 2`. -/
theorem pw_lt_exp {a b : PTm n} (hp : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] lt (pw p a) (pw p b) := by
  have hp1 := p_pos hp
  have hX := pw_pos' hp1 a
  have x := natEq hX; have w := natEq (eq_add_of_le hp); have s := natEq (pw_succ (Γ := Γ) p a)
  have l : Γ ⊢[PRAAx] le (succ (pw p a)) (pw p (succ a)) := by
    refine le_of_eq_add (d := pred (pw p a) + pw p a * monus p two) ?_
    ipra_lc s + 𝔞 (pw p a) * w + x
  exact le_trans l (pw_le_exp hp1 h)

/-- `p^a = p^b → a = b` for `p ≥ 2`. -/
theorem pw_inj_exp {a b : PTm n} (hp : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] pw p a ≐ pw p b) :
    Γ ⊢[PRAAx] a ≐ b := by
  refine .orE (lt_or_le a b) ?_ ?_
  · exact not_succ_le_self _ _ (le_congr (.eqRefl _) h.wk.eqSymm (pw_lt_exp hp.wk Prf.hyp0))
  · refine .orE (lt_or_le b a) ?_ (le_antisymm Prf.hyp0 Prf.hyp1)
    exact not_succ_le_self _ _ (le_congr (.eqRefl _) h.wk.wk (pw_lt_exp hp.wk.wk Prf.hyp0))

/-- `v_p(p^j) = j`. -/
theorem val_pw (j : PTm n) (hp : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] val p (pw p j) ≐ j :=
  val_unique hp (pw_pos' (p_pos hp) j) (c := one) (by ipra_ring) (not_dvd_one hp)

/-- `p^a ∣ p^b` for `a ≤ b`. -/
theorem pw_dvd_pw {a b : PTm n} (hp : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] dvd (pw p a) (pw p b) :=
  dvd_of_eq' (pw_pos' (p_pos hp) a) (w := pw p (monus b a))
    ((congrPw (.eqRefl p) (eq_add_of_le h)).eqTrans (pw_add p a (monus b a)))

/-- `p^j ∣ m ⟺ j ≤ v_p(m)` for `m ≥ 1`. -/
theorem dvd_iff_le_val {j m : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    ((Γ ⊢[PRAAx] dvd (pw p j) m) → (Γ ⊢[PRAAx] le j (val p m))) ∧
      ((Γ ⊢[PRAAx] le j (val p m)) → (Γ ⊢[PRAAx] dvd (pw p j) m)) := by
  have hp1 := p_pos hp
  constructor
  · intro h
    refine .orE (lt_or_le (val p m) j) ?_ Prf.hyp0
    have d₁ := pw_dvd_pw hp.wk (Prf.hyp0 : (lt (val p m) j :: Γ) ⊢[PRAAx] le (succ (val p m)) j)
    have d₂ := dvd_trans' (pw_pos' hp1.wk _) (pw_pos' hp1.wk _) d₁ h.wk
    exact .botE _ (Prf.impE (Valuation.val_not_dvd hp.wk hm.wk) d₂)
  · intro h
    exact dvd_trans' (pw_pos' hp1 _) (pw_pos' hp1 _) (pw_dvd_pw hp h) Valuation.val_dvd

end Powers

/-! ## Prime-power divisors -/

/-- `[d is a positive power of p]`: `sg(v_p(d)) [p^{v_p(d)} = d]`. -/
abbrev ppI (p d : PTm n) : PTm n := sg (val p d) * eqb (pw p (val p d)) d

theorem eqb_succ_succ (a b : PTm n) : Γ ⊢[PRAAx] eqb (succ a) (succ b) ≐ eqb a b := by
  unfold eqb
  exact congrMonus (.eqRefl _) (congrAdd (succ_monus_succ _ _) (succ_monus_succ _ _))

theorem eqb_one_le {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] eqb (monus a b) zero ≐ one := eqb_of_eq h

theorem eqb_zero_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt b a) : Γ ⊢[PRAAx] eqb (monus a b) zero ≐ zero :=
  eqb_of_ne (.impI (not_succ_le_self b _ (le_trans h.wk Prf.hyp0)))

/-- `[p^j = p^{k+1}] = [j = k + 1]`. -/
theorem kterm_pw {p j k : PTm n} (hp : Γ ⊢[PRAAx] le two p) :
    Γ ⊢[PRAAx] eqb (pw p j) (pw p (succ k)) ≐ eqb j (succ k) := by
  refine .orE (eq_or_ne j (succ k)) ?_ ?_
  · exact (eqb_of_eq (congrPw (.eqRefl p) Prf.hyp0)).eqTrans (eqb_of_eq Prf.hyp0).eqSymm
  · have ne : (neg (j ≐ succ k) :: Γ) ⊢[PRAAx] neg (pw p j ≐ pw p (succ k)) :=
      .impI (Prf.impE Prf.hyp1 (pw_inj_exp hp.wk.wk Prf.hyp0))
    exact (eqb_of_ne ne).eqTrans (eqb_of_ne Prf.hyp0).eqSymm

/-- If `d` is not a power of `p`, then `[d = p^{k+1}] = 0`. -/
theorem kterm_not {p d k : PTm n} (hp : Γ ⊢[PRAAx] le two p) (hne : Γ ⊢[PRAAx] neg (pw p (val p d) ≐ d)) :
    Γ ⊢[PRAAx] eqb d (pw p (succ k)) ≐ zero := by
  refine eqb_of_ne (.impI ?_)
  have h : ((d ≐ pw p (succ k)) :: Γ) ⊢[PRAAx] d ≐ pw p (succ k) := Prf.hyp0
  have v : ((d ≐ pw p (succ k)) :: Γ) ⊢[PRAAx] val p d ≐ succ k := (congrVal (.eqRefl p) h).eqTrans (val_pw _ hp.wk)
  exact Prf.impE hne.wk ((congrPw (.eqRefl p) v).eqTrans h.eqSymm)

/-- `[d = p^{k+1}]` over `0 = k`, `1 = ⟨p, d⟩`. -/
abbrev kB : PTm 2 := eqb (sndT (var 1)) (pw (fstT (var 1)) (succ (var 0)))

theorem inst2_kB (k z : PTm n) : inst2 kB k z = eqb (sndT z) (pw (fstT z) (succ k)) := by simp [inst2]

theorem kB_at (k p d : PTm n) : Γ ⊢[PRAAx] inst2 kB k (pairT p d) ≐ eqb d (pw p (succ k)) := by
  rw [inst2_kB]; exact congrEqb' (snd_pair _ _) (congrPw (fst_pair _ _) (.eqRefl _))

/-- `[j = k + 1]`, over `0 = k`, `1 = j`. -/
abbrev jB : PTm 2 := eqb (var 1) (succ (var 0))

theorem inst2_jB (k j : PTm n) : inst2 jB k j = eqb j (succ k) := by simp [inst2]

/-- `∑_{k<v} [j = k + 1] = [1 ≤ j ≤ v]`, as `sg j [j ∸ v = 0]`. -/
theorem jsum (j v : PTm n) : Γ ⊢[PRAAx] ap2 (sumF jB) v j ≐ sg j * eqb (monus j v) zero := by
  refine .orE (zero_or_succ j) ?_ ?_
  · let C : List (Fm PTm n) := (j ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] j ≐ zero := Prf.hyp0
    have z : C ⊢[PRAAx] ap2 (sumF jB) v zero ≐ zero := by
      refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
      rw [inst2_jB]
      have hz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
      rw [hz]
      exact eqb_of_ne (.impI (succ_ne_zero' _ Prf.hyp0.eqSymm))
    exact (congrAp2 (sumF jB) (.eqRefl v) h0).eqTrans (z.eqTrans
      (zero_mul_l ((congrSg h0).eqTrans sg_zero) _).eqSymm)
  · let C : List (Fm PTm n) := (j ≐ succ (pred j)) :: Γ
    have hj : C ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
    have sj : C ⊢[PRAAx] sg j ≐ one := (congrSg hj).eqTrans (sg_succ _)
    have toD : C ⊢[PRAAx] ap2 (sumF jB) v j ≐ ap2 (sumF (dB (one : PTm 2))) v (pairT (pred j) zero) := by
      refine (congrAp2 (sumF jB) (.eqRefl v) hj).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
      rw [inst2_jB, inst2_dB, shift_pairT, one_inst]
      have hs : Syn.shift (succ (pred j)) = succ (Syn.shift (pred j)) := by simp [Syn.shift]
      rw [hs]
      exact (eqb_succ_succ _ _).eqTrans ((congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)).eqTrans
        (by ipra_ring))
    refine toD.eqTrans ?_
    refine .orE (lt_or_le (pred j) v) ?_ ?_
    · let D : List (Fm PTm n) := lt (pred j) v :: C
      have hl : D ⊢[PRAAx] lt (pred j) v := Prf.hyp0
      have e1 : D ⊢[PRAAx] eqb (monus j v) zero ≐ one :=
        eqb_one_le ((congrMonus hj.wk (.eqRefl _)).eqTrans hl)
      refine (sum_delta (one : PTm 2) hl).eqTrans ?_
      rw [one_inst]
      exact (by ipra_ring : D ⊢[PRAAx] one ≐ one * one).eqTrans (congrMul sj.wk e1).eqSymm
    · let D : List (Fm PTm n) := le v (pred j) :: C
      have hv : D ⊢[PRAAx] le v (pred j) := Prf.hyp0
      have e0 : D ⊢[PRAAx] eqb (monus j v) zero ≐ zero :=
        eqb_zero_lt (le_congr (.eqRefl _) hj.wk.eqSymm ((succ_monus_succ _ _).eqTrans hv))
      have hv' : (D.map Fm.shift) ⊢[PRAAx] le (Syn.shift v) (Syn.shift (pred j)) := by
        simpa [Fm.shift, Syn.shift] using hv.shift
      have z : D ⊢[PRAAx] ap2 (sumF (dB (one : PTm 2))) v (pairT (pred j) zero) ≐ zero := by
        refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
        rw [inst2_dB, shift_pairT, one_inst]
        refine (congrMul (congrEqb' (fst_pair _ _) (.eqRefl _)) (.eqRefl _)).eqTrans (zero_mul_l ?_ _)
        refine eqb_of_ne (.impI ?_)
        exact le_lt_absurd _ (le_congr (.eqRefl _) Prf.hyp0 hv'.wk.wk) Prf.hyp1
      exact z.eqTrans ((congrMul sj.wk e0).eqTrans (by ipra_ring)).eqSymm

/-! ## Counting the prime-power divisors -/

theorem congrPpI {p p' d d' : PTm n} (h₁ : Γ ⊢[PRAAx] p ≐ p') (h₂ : Γ ⊢[PRAAx] d ≐ d') :
    Γ ⊢[PRAAx] ppI p d ≐ ppI p' d' :=
  congrMul (congrSg (congrVal h₁ h₂)) (congrEqb' (congrPw h₁ (congrVal h₁ h₂)) h₂)

theorem prime_shift {p : PTm n} (hp : Γ ⊢[PRAAx] Primes.prime p) :
    (Γ.map Fm.shift) ⊢[PRAAx] Primes.prime (Syn.shift p) := by
  simpa [Fm.shift, Syn.shift] using hp.shift

/-- `[d ∣ n] [d is a positive power of p] = ∑_{k < v_p(n)} [d = p^{k+1}]` for `d, n ≥ 1`, `p` prime. -/
theorem pp_pt {p m d : PTm n} (hp : Γ ⊢[PRAAx] Primes.prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] eqb (rem m d) zero * ppI p d ≐ ap2 (sumF kB) (val p m) (pairT p d) := by
  have hp2 := prime_two hp
  have hp2' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift p) := prime_two (prime_shift hp)
  refine .orE (eq_or_ne (pw p (val p d)) d) ?_ ?_
  · let C : List (Fm PTm n) := (pw p (val p d) ≐ d) :: Γ
    have h : C ⊢[PRAAx] pw p (val p d) ≐ d := Prf.hyp0
    -- the right side is `∑_{k<v} [j = k + 1]`
    have r₁ : C ⊢[PRAAx] ap2 (sumF kB) (val p m) (pairT p d) ≐ ap2 (sumF jB) (val p m) (val p d) := by
      refine (congrAp2 (sumF kB) (.eqRefl _) (congrPairT (.eqRefl p) h.eqSymm)).eqTrans
        (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
      rw [inst2_jB, shift_pairT]
      have e : Syn.shift (pw p (val p d)) = pw (Syn.shift p) (val (Syn.shift p) (Syn.shift d)) := by simp [Syn.shift]
      have e' : Syn.shift (val p d) = val (Syn.shift p) (Syn.shift d) := by simp [Syn.shift]
      rw [e, e']
      exact (kB_at _ _ _).eqTrans (kterm_pw hp2'.wk.wk)
    have r₂ := r₁.eqTrans (jsum _ _)
    -- the left side
    have l₁ : C ⊢[PRAAx] eqb (rem m d) zero ≐ eqb (monus (val p d) (val p m)) zero := by
      refine .orE (lt_or_le (val p m) (val p d)) ?_ ?_
      · let D : List (Fm PTm n) := lt (val p m) (val p d) :: C
        have ne : D ⊢[PRAAx] neg (dvd d m) := by
          refine .impI ?_
          have dd : (dvd d m :: D) ⊢[PRAAx] dvd (pw p (val p d)) m :=
            (congrAp2 remF (.eqRefl _) h.wk.wk).eqTrans Prf.hyp0
          have l := (dvd_iff_le_val (j := val p d) hp2.wk.wk.wk hm.wk.wk.wk).1 dd
          exact le_lt_absurd _ l Prf.hyp1
        exact (eqb_of_ne ne).eqTrans (eqb_zero_lt Prf.hyp0).eqSymm
      · let D : List (Fm PTm n) := le (val p d) (val p m) :: C
        have dd : D ⊢[PRAAx] dvd (pw p (val p d)) m :=
          (dvd_iff_le_val (Γ := D) (j := val p d) hp2.wk.wk hm.wk.wk).2 Prf.hyp0
        have dm : D ⊢[PRAAx] dvd d m := (congrAp2 remF (.eqRefl _) h.wk.eqSymm).eqTrans dd
        exact (eqb_of_eq dm).eqTrans (eqb_one_le Prf.hyp0).eqSymm
    have l₂ : C ⊢[PRAAx] ppI p d ≐ sg (val p d) := (congrMul (.eqRefl _) (eqb_of_eq h)).eqTrans
      (by ipra_ring)
    exact (congrMul l₁ l₂).eqTrans ((mul_comm _ _).eqTrans r₂.eqSymm)
  · let C : List (Fm PTm n) := neg (pw p (val p d) ≐ d) :: Γ
    have hne : C ⊢[PRAAx] neg (pw p (val p d) ≐ d) := Prf.hyp0
    have l : C ⊢[PRAAx] eqb (rem m d) zero * ppI p d ≐ zero :=
      (congrMul (.eqRefl _) ((congrMul (.eqRefl _) (eqb_of_ne hne)).eqTrans (mul_zero _))).eqTrans (mul_zero _)
    have hne' : (C.map Fm.shift) ⊢[PRAAx] neg (pw (Syn.shift p) (val (Syn.shift p) (Syn.shift d)) ≐ Syn.shift d) := by
      simpa [Fm.shift, Syn.shift] using hne.shift
    have r : C ⊢[PRAAx] ap2 (sumF kB) (val p m) (pairT p d) ≐ zero := by
      refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
      rw [shift_pairT]
      exact (kB_at _ _ _).eqTrans (kterm_not (hp2'.weaken (fun x hx => List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_map.mp hx).choose_spec.1,
          (List.mem_map.mp hx).choose_spec.2⟩))) hne'.wk)
    exact l.eqTrans r.eqSymm

/-- `[d = p^{k+1}]` over `0 = d`, `1 = k`, `2 = ⟨p, m⟩`. -/
abbrev a3 : PTm 3 := eqb (var 0) (pw (fstT (var 2)) (succ (var 1)))

theorem inst3_a3 (d k x : PTm n) : inst3 a3 d k x = eqb d (pw (fstT x) (succ k)) := by simp [inst3]

/-- A row of `a3` is the `k`-sum `∑_{k<v} [d = p^{k+1}]`. -/
theorem row_kB (d p m v : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB a3)) v (pairT d (pairT p m)) ≐ ap2 (sumF kB) v (pairT p d) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_rowB, inst3_a3]
  simp only [shift_pairT]
  exact (congrEqb' (fst_pair _ _) (congrPw ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))).eqTrans
    (kB_at _ _ _).eqSymm

/-- `∑_{k<v} [0 = p^{k+1}] = 0`. -/
theorem kB_zero {p v : PTm n} (hp : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] ap2 (sumF kB) v (pairT p zero) ≐ zero := by
  have hp' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift p) := by simpa [Fm.shift, Syn.shift] using hp.shift
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [shift_pairT]
  have hz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [hz]
  refine (kB_at _ _ _).eqTrans (eqb_of_ne (.impI ?_))
  exact succ_ne_zero' _ ((pw_pos' (p_pos hp'.wk.wk) _).eqSymm.eqTrans Prf.hyp0.eqSymm)

/-- The pointwise form: `[d ≥ 1][d ∣ m] [d is a positive power of p] = ∑_{k<v_p(m)} [d = p^{k+1}]`. -/
theorem cnt_pt {p m d : PTm n} (hp : Γ ⊢[PRAAx] Primes.prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] (sg d * eqb (rem m d) zero) * ppI p d ≐ ap2 (sumF kB) (val p m) (pairT p d) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    exact (zero_mul_l (zero_mul_l ((congrSg h0).eqTrans sg_zero) _) _).eqTrans
      ((congrAp2 (sumF kB) (.eqRefl _) (congrPairT (.eqRefl p) h0)).eqTrans (kB_zero (prime_two hp.wk))).eqSymm
  · have hd : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine (congrMul ((congrMul ((congrSg hd).eqTrans (sg_succ _)) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)).eqTrans ?_
    exact pp_pt hp.wk hm.wk hd

/-- A column of `a3` is `1` for `k < v_p(m)`: the single divisor `p^{k+1}`. -/
theorem col_one {p m k : PTm n} (hp : Γ ⊢[PRAAx] Primes.prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hk : Γ ⊢[PRAAx] lt k (val p m)) :
    Γ ⊢[PRAAx] ap2 (sumF (colB a3)) (succ m) (pairT k (pairT p m)) ≐ one := by
  have hp2 := prime_two hp
  have dd := (dvd_iff_le_val (j := succ k) hp2 hm).2 hk
  have le' := dvd_le' (pw_pos' (p_pos hp2) _) dd hm
  have hlt : Γ ⊢[PRAAx] lt (pw p (succ k)) (succ m) := (succ_monus_succ _ _).eqTrans le'
  refine (sum_congr_bounded (colB a3) (dB (one : PTm 2)) _ (pairT (pw p (succ k)) zero) _ (.allI (.impI ?_))).eqTrans
    ((sum_delta (one : PTm 2) hlt).eqTrans (by rw [one_inst]; exact .eqRefl _))
  rw [inst2_colB, inst3_a3, inst2_dB, one_inst]
  simp only [shift_pairT]
  have e : Syn.shift (pw p (succ k)) = pw (Syn.shift p) (succ (Syn.shift k)) := by simp [Syn.shift]
  have hz : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [e, hz]
  refine (congrEqb' (.eqRefl _) (congrPw ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    (congrSucc (fst_pair _ _)))).eqTrans ?_
  exact (eqb_comm' _ _).eqTrans ((congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)).eqTrans
    (by ipra_ring))

/-- The number of divisors of `m ≥ 1` that are positive powers of the prime `p` is `v_p(m)`. -/
theorem count_pp {p m : PTm n} (hp : Γ ⊢[PRAAx] Primes.prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap2 (sumF (oB a3)) (succ m) (pairT (val p m) (pairT p m)) ≐ val p m := by
  have hp' := prime_shift hp
  have hm' := shift_pos hm
  refine (fubini a3 (succ m) (val p m) (pairT p m)).eqTrans ?_
  refine (sum_congr_bounded (pB a3) (one : PTm 2) _ zero _ (.allI (.impI ?_))).eqTrans (SumPhi.sum_ones _ _)
  rw [inst2_pB, shift_pairT, shift_pairT, one_inst]
  have hv : Syn.shift (val p m) = val (Syn.shift p) (Syn.shift m) := by simp [Syn.shift]
  have hs : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
  rw [hs]
  refine (congrAp2 (sumF (colB a3)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  have hk : (lt (var 0) (Syn.shift (val p m)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (val (Syn.shift p) (Syn.shift m)) := by
    rw [← hv]; exact Prf.hyp0
  exact col_one hp'.wk hm'.wk hk

/-- `[d ≥ 1][d ∣ m][d is a positive power of p]`, over `0 = d`, `1 = ⟨p, m⟩`. -/
abbrev cntB : PTm 2 := (sg (var 0) * eqb (rem (sndT (var 1)) (var 0)) zero) * ppI (fstT (var 1)) (var 0)

theorem cnt_at (d p m : PTm n) :
    Γ ⊢[PRAAx] inst2 cntB d (pairT p m) ≐ (sg d * eqb (rem m d) zero) * ppI p d := by
  have e : inst2 cntB d (pairT p m) = (sg d * eqb (rem (sndT (pairT p m)) d) zero) * ppI (fstT (pairT p m)) d := by
    simp [inst2]
  rw [e]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (snd_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (congrPpI (fst_pair _ _) (.eqRefl _))

/-- `∑_{d ≤ m} [d ∣ m][d is a positive power of p] = v_p(m)` for a prime `p` and `m ≥ 1`. -/
theorem count_cnt {p m : PTm n} (hp : Γ ⊢[PRAAx] Primes.prime p) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap2 (sumF cntB) (succ m) (pairT p m) ≐ val p m := by
  have hp' := prime_shift hp
  have hm' := shift_pos hm
  refine (sum_congr_bounded cntB (oB a3) _ (pairT (val p m) (pairT p m)) _ (.allI (.impI ?_))).eqTrans (count_pp hp hm)
  rw [inst2_oB]
  simp only [shift_pairT]
  have hv : Syn.shift (val p m) = val (Syn.shift p) (Syn.shift m) := by simp [Syn.shift]
  rw [hv]
  refine (cnt_at _ _ _).eqTrans ((cnt_pt hp'.wk hm'.wk).eqTrans ?_)
  refine .eqTrans ?_ (congrAp2 (sumF (rowB a3)) (fst_pair _ _).eqSymm (congrPairT (.eqRefl _) (snd_pair _ _).eqSymm))
  exact (row_kB _ _ _ _).eqSymm

/-! ## The weighted von Mangoldt function and the divisor sum -/

section Weighted

variable (w : PTm 2)

/-- `[q prime][d is a positive power of q] w(q, y)`, over `0 = q`, `1 = ⟨d, y⟩`. -/
def lamB : PTm 2 := (isP (var 0) * ppI (var 0) (fstT (var 1))) * Syn.subst ![var 0, sndT (var 1)] w

/-- `Λ_w(d) = ∑_{q ≤ d} [q prime][d = q^a, a ≥ 1] w(q)`: the weight of the base of a prime power. -/
abbrev Lam (d y : PTm n) : PTm n := ap2 (sumF (lamB w)) (succ d) (pairT d y)

/-- `[q prime] v_q(m) w(q, y)`, over `0 = q`, `1 = ⟨m, y⟩`. -/
def ellB : PTm 2 := (isP (var 0) * val (var 0) (fstT (var 1))) * Syn.subst ![var 0, sndT (var 1)] w

/-- `L_w(m) = ∑_{q ≤ m} [q prime] v_q(m) w(q)`, the completely additive weight. -/
abbrev Lw (m y : PTm n) : PTm n := ap2 (sumF (ellB w)) (succ m) (pairT m y)

theorem inst2_lam (q z : PTm n) : inst2 (lamB w) q z = (isP q * ppI q (fstT z)) * inst2 w q (sndT z) := by
  have hf : Syn.subst ![q, z] (Syn.subst ![var 0, sndT (var 1)] w) = inst2 w q (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, lamB, PTm.subst_mul, hf]
  simp

theorem inst2_ell (q z : PTm n) : inst2 (ellB w) q z = (isP q * val q (fstT z)) * inst2 w q (sndT z) := by
  have hf : Syn.subst ![q, z] (Syn.subst ![var 0, sndT (var 1)] w) = inst2 w q (sndT z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, ellB, PTm.subst_mul, hf]
  simp

end Weighted

section Divsum

variable (w : PTm 2)

/-- `[d ∣ m] [q prime][d is a positive power of q] w(q, y)`, over `0 = d`, `1 = q`, `2 = ⟨m, y⟩`. -/
def a4 : PTm 3 := (sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) *
  ((isP (var 1) * ppI (var 1) (var 0)) * Syn.subst ![var 1, sndT (var 2)] w)

theorem inst3_a4 (d q x : PTm n) : inst3 (a4 w) d q x =
    (sg d * eqb (rem (fstT x) d) zero) * ((isP q * ppI q d) * inst2 w q (sndT x)) := by
  have hf : Syn.subst ![d, q, x] (Syn.subst ![var 1, sndT (var 2)] w) = inst2 w q (sndT x) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, a4, PTm.subst_mul, hf]
  simp

theorem a4_at (d q m y : PTm n) : Γ ⊢[PRAAx] inst3 (a4 w) d q (pairT m y) ≐
    (sg d * eqb (rem m d) zero) * ((isP q * ppI q d) * inst2 w q y) := by
  rw [inst3_a4]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (congrMul (.eqRefl _) (congrInst2 w (.eqRefl _) (snd_pair _ _)))

/-- `[d ∣ m] Λ_w(d)`, over `0 = d`, `1 = ⟨m, y⟩`. -/
abbrev DB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) *
  ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (sndT (var 1)))

theorem inst2_DB (d x : PTm n) : inst2 (DB w) d x = (sg d * eqb (rem (fstT x) d) zero) * Lam w d (sndT x) := by
  simp [inst2]

/-- A row: `[d ∣ m] Λ_w(d) = ∑_{q ≤ m} a4(d, q)`, for `d ≤ m`. -/
theorem row_lam {d m y : PTm n} (hdm : Γ ⊢[PRAAx] lt d (succ m)) :
    Γ ⊢[PRAAx] (sg d * eqb (rem m d) zero) * Lam w d y ≐
      ap2 (sumF (rowB (a4 w))) (succ m) (pairT d (pairT m y)) := by
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB (a4 w))) (succ m) (pairT d (pairT m y)) ≐
      (sg d * eqb (rem m d) zero) * ap2 (sumF (lamB w)) (succ m) (pairT d y) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, inst2_lam]
    simp only [shift_pairT]
    have hc : Syn.shift (sg d * eqb (rem m d) zero) = sg (Syn.shift d) * eqb (rem (Syn.shift m) (Syn.shift d)) zero := by
      simp [Syn.shift]
    rw [hc]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ((a4_at w _ _ _ _).eqTrans ?_)
    exact congrMul (.eqRefl _) (congrMul (congrMul (.eqRefl _) (congrPpI (.eqRefl _) (fst_pair _ _)).eqSymm)
      (congrInst2 w (.eqRefl _) (snd_pair _ _).eqSymm))
  refine .eqTrans ?_ sc.eqSymm
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    exact (zero_mul_l (zero_mul_l ((congrSg h0).eqTrans sg_zero) _) _).eqTrans
      (zero_mul_l (zero_mul_l ((congrSg h0).eqTrans sg_zero) _) _).eqSymm
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have hd' := shift_pos hd
    have cut : C ⊢[PRAAx] ap2 (sumF (lamB w)) (succ m) (pairT d y) ≐ Lam w d y := by
      refine sum_ext (lamB w) (fun Δ a hs hl => ?_) (le_congr (.eqRefl _) (.eqRefl _) hdm.wk)
      rw [inst2_lam, shift_pairT]
      have pz : Δ ⊢[PRAAx] ppI a (fstT (pairT (Syn.shift d) (Syn.shift y))) ≐ zero :=
        (congrPpI (.eqRefl _) (fst_pair _ _)).eqTrans
          (zero_mul_l ((congrSg (val_big (hd'.weaken hs) hl)).eqTrans sg_zero) _)
      exact (congrMul ((congrMul (.eqRefl _) pz).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_mul_l (.eqRefl _) _)
    exact congrMul (.eqRefl _) cut.eqSymm

/-- A column: `∑_{d ≤ m} a4(d, q) = [q prime] v_q(m) w(q)`, for `m ≥ 1`. -/
theorem col_lam {q m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (a4 w))) (succ m) (pairT q (pairT m y)) ≐ inst2 (ellB w) q (pairT m y) := by
  have sc : Γ ⊢[PRAAx] ap2 (sumF (colB (a4 w))) (succ m) (pairT q (pairT m y)) ≐
      (isP q * inst2 w q y) * ap2 (sumF cntB) (succ m) (pairT q m) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_colB]
    simp only [shift_pairT]
    have hc : Syn.shift (isP q * inst2 w q y) = isP (Syn.shift q) * inst2 w (Syn.shift q) (Syn.shift y) := by
      rw [shift_mul', shift_inst2]; simp [Syn.shift]
    rw [hc]
    refine (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ((a4_at w _ _ _ _).eqTrans ?_)
    refine .eqTrans ?_ (congrMul (.eqRefl _) (cnt_at _ _ _).eqSymm)
    ipra_ring
  rw [inst2_ell]
  refine sc.eqTrans ?_
  have v : Γ ⊢[PRAAx] isP q * val q (fstT (pairT m y)) * inst2 w q (sndT (pairT m y)) ≐ isP q * val q m * inst2 w q y :=
    congrMul (congrMul (.eqRefl _) (congrVal (.eqRefl _) (fst_pair _ _))) (congrInst2 w (.eqRefl _) (snd_pair _ _))
  refine .eqTrans ?_ v.eqSymm
  refine .orE (isP_01 q) ?_ ?_
  · have h0 : ((isP q ≐ zero) :: Γ) ⊢[PRAAx] isP q ≐ zero := Prf.hyp0
    exact (zero_mul_l (zero_mul_l h0 _) _).eqTrans (zero_mul_l (zero_mul_l h0 _) _).eqSymm
  · have h1 : ((isP q ≐ one) :: Γ) ⊢[PRAAx] isP q ≐ one := Prf.hyp0
    exact (congrMul (.eqRefl _) (count_cnt (prime_of_isP h1) hm.wk)).eqTrans
      (by ipra_ring)

/-- `thm:lambda-divsum`: `∑_{d ∣ m} Λ_w(d) = L_w(m)` for every weight `w` and `m ≥ 1`. -/
theorem lambda_divsum {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] ap2 (sumF (DB w)) (succ m) (pairT m y) ≐ Lw w m y := by
  have hm' := shift_pos hm
  have hs : Syn.shift (succ m) = succ (Syn.shift m) := by simp [Syn.shift]
  have r : Γ ⊢[PRAAx] ap2 (sumF (DB w)) (succ m) (pairT m y) ≐
      ap2 (sumF (oB (a4 w))) (succ m) (pairT (succ m) (pairT m y)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_DB, inst2_oB]
    simp only [shift_pairT]
    rw [hs]
    refine (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
      (congrAp2 (sumF (lamB w)) (.eqRefl _) (congrPairT (.eqRefl _) (snd_pair _ _)))).eqTrans ?_
    have hl : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift m)) := by
      rw [← hs]; exact Prf.hyp0
    refine (row_lam w hl).eqTrans ?_
    exact (congrAp2 (sumF (rowB (a4 w))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  refine r.eqTrans ((fubini (a4 w) (succ m) (succ m) (pairT m y)).eqTrans ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_pB]
  simp only [shift_pairT]
  rw [hs]
  refine (congrAp2 (sumF (colB (a4 w))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  exact col_lam w hm'.wk

end Divsum

end LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
