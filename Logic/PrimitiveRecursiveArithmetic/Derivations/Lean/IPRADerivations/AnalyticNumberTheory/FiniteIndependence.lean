import IPRADerivations.AnalyticNumberTheory.SievePeriod

/-!
# Exact finite independence of divisibility events

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, Theorem
`an:independence`: in the uniform sample `0 ≤ n < M`, `M = ∏ p_i`, the events `p_i ∣ n` are independent; for
disjoint index sets `A`, `B`,

    #{n < M : p_i ∣ n (i ∈ A), p_j ∤ n (j ∈ B)} / M = ∏_{i ∈ A} 1/p_i · ∏_{j ∈ B} (1 − 1/p_j).

The two sets of primes are replaced by two coprime moduli `a` (the product over `A`) and `b` (the product over
`B`; "no `p_j` divides `n`" is `gcd(n, b) = 1`, and `∏ (p_j − 1) = φ(b)`), and the sample by any multiple
`N = a b c` of the period. For `a, b ≥ 1` with `gcd(a, b) = 1`:

* `tot_period`, `tot_blocks`: `∑_{k < N + b} [gcd(k, b) = 1] = ∑_{k < N} [gcd(k, b) = 1] + φ(b)`, hence
  `#{k < b c : gcd(k, b) = 1} = c φ(b)`;
* `cM_mul`: `#{n < a M : a ∣ n} = M`;
* `cop_mul_bit`: `[gcd(a k, b) = 1] = [gcd(k, b) = 1]`;
* **`joint_count`**: `#{n < a b c : a ∣ n, gcd(n, b) = 1} = c φ(b)`;
* `coprime_count`: `#{n < a b c : gcd(n, b) = 1} = a c φ(b)`;
* **`independence`**: `#(A ∩ B) · N = #A · #B`, with `#A = b c` the number of multiples of `a`.

The packet's proof is the Chinese remainder bijection; here the multiples of `a` are reindexed
(`SumReindex.reindex_eq`) and the residues modulo `b` are counted by periodicity.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.FiniteIndependence

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody inst2_tot count_multiples quo_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb' zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB inst2_riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRecursion (shift_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePeriod (cop_period step_alg)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Residues coprime to `b` -/

/-- `T(N; b) = #{k < N : gcd(k, b) = 1}`. -/
abbrev Tot (N b : PTm n) : PTm n := ap2 (sumF totBody) N b

theorem tp_zero (b : PTm n) : Γ ⊢[PRAAx] Tot (zero + b) b ≐ Tot zero b + phi b :=
  (congrAp2 (sumF totBody) (zero_add b) (.eqRefl _)).eqTrans
    ((zero_add _).eqSymm.eqTrans (congrAdd (sum_zero totBody b).eqSymm (.eqRefl _)))

theorem tp_succ {x b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (ih : Γ ⊢[PRAAx] Tot (x + b) b ≐ Tot x b + phi b) :
    Γ ⊢[PRAAx] Tot (succ x + b) b ≐ Tot (succ x) b + phi b := by
  have e1 : Γ ⊢[PRAAx] Tot (succ x + b) b ≐ Tot (succ (x + b)) b :=
    congrAp2 (sumF totBody) (succ_add x b) (.eqRefl _)
  have s1 := sum_succ' (Γ := Γ) totBody (x + b) b
  have s2 := sum_succ' (Γ := Γ) totBody x b
  rw [inst2_tot] at s1 s2
  exact e1.eqTrans (step_alg s1 s2 ih (cop_period hb x))

/-- Variables: `0 = x`, `1 = b`. -/
abbrev tpF : Fm PTm 2 :=
  (var 1 ≐ succ (pred (var 1))) ⟶
    (ap2 (sumF totBody) (var 0 + var 1) (var 1) ≐ ap2 (sumF totBody) (var 0) (var 1) + phi (var 1))

theorem tp_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] tpF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2]
  · exact .impI (tp_zero _)
  · exact .impI (tp_succ Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `T(N + b; b) = T(N; b) + φ(b)` for `b ≥ 1`. -/
theorem tot_period {b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (x : PTm n) :
    Γ ⊢[PRAAx] Tot (x + b) b ≐ Tot x b + phi b := by
  have i := inst (Γ := Γ) tp_open (![x, b] : Fin 2 → PTm n)
  simp only [tpF, Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_pred, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hb

alias mul_succ_alg := LeanProofs.IPRA.mul_succ

theorem blk_alg {U' U ph c : PTm n} (a : Γ ⊢[PRAAx] U' ≐ U + ph) (ih : Γ ⊢[PRAAx] U ≐ c * ph) :
    Γ ⊢[PRAAx] U' ≐ succ c * ph := by
  ipra_lc natEq a + natEq ih

theorem tb_zero (b : PTm n) : Γ ⊢[PRAAx] Tot (b * zero) b ≐ zero * phi b :=
  (congrAp2 (sumF totBody) (mul_zero b) (.eqRefl _)).eqTrans ((sum_zero totBody b).eqTrans (zero_mul _).eqSymm)

theorem tb_succ {c b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (ih : Γ ⊢[PRAAx] Tot (b * c) b ≐ c * phi b) : Γ ⊢[PRAAx] Tot (b * succ c) b ≐ succ c * phi b :=
  blk_alg ((congrAp2 (sumF totBody) (mul_succ_alg b c) (.eqRefl _)).eqTrans (tot_period hb (b * c))) ih

/-- Variables: `0 = c`, `1 = b`. -/
abbrev tbF : Fm PTm 2 :=
  (var 1 ≐ succ (pred (var 1))) ⟶ (ap2 (sumF totBody) (var 1 * var 0) (var 1) ≐ var 0 * phi (var 1))

theorem tb_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] tbF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_ap2]
  · exact .impI (tb_zero _)
  · exact .impI (tb_succ Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `#{k < b c : gcd(k, b) = 1} = c φ(b)` for `b ≥ 1`. -/
theorem tot_blocks {b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (c : PTm n) :
    Γ ⊢[PRAAx] Tot (b * c) b ≐ c * phi b := by
  have i := inst (Γ := Γ) tb_open (![c, b] : Fin 2 → PTm n)
  simp only [tbF, Fm.subst_imp, Fm.subst_eq, subst_ap2, PTm.subst_mul, PTm.subst_pred, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hb

/-! ## Multiples of `a` -/

/-- `#{n < a M : a ∣ n} = M` for `a ≥ 1`. -/
theorem cM_mul {a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (M : PTm n) : Γ ⊢[PRAAx] cM (a * M) a ≐ M :=
  (count_multiples (j := a * M) ha).eqTrans
    (quo_eq ha (.eqRefl _) (le_congr (.eqRefl _) ha.eqSymm (le_refl (succ (pred a)))))

/-- `[gcd(a k, b) = 1] = [gcd(k, b) = 1]` for `a, b ≥ 1` with `gcd(a, b) = 1`. -/
theorem cop_mul_bit {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] gcd a b ≐ one) (k : PTm n) :
    Γ ⊢[PRAAx] eqb (gcd (a * k) b) one ≐ eqb (gcd k b) one := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have h0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    exact congrEqb' (congrGcd (((congrMul (.eqRefl _) h0).eqTrans (mul_zero a)).eqTrans h0.eqSymm) (.eqRefl _))
      (.eqRefl _)
  · let C : List (Fm PTm n) := (k ≐ succ (pred k)) :: Γ
    have hk : C ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have hba : C ⊢[PRAAx] gcd b a ≐ one := gcd_comm_one hb.wk hc.wk
    refine .orE (eqb_cases (gcd k b) one) ?_ ?_
    · let E : List (Fm PTm n) := (eqb (gcd k b) one ≐ zero) :: C
      have z : E ⊢[PRAAx] eqb (gcd k b) one ≐ zero := Prf.hyp0
      have nn : E ⊢[PRAAx] neg (gcd (a * k) b ≐ one) := by
        refine .impI ?_
        have g : ((gcd (a * k) b ≐ one) :: E) ⊢[PRAAx] gcd (a * k) b ≐ one := Prf.hyp0
        have du : ((gcd (a * k) b ≐ one) :: E) ⊢[PRAAx] dvd k (a * k) :=
          dvd_of_eq' hk.wk.wk (mul_comm a k)
        have gu := coprime_dvd_left hk.wk.wk du g
        exact one_ne_zero _ ((eqb_of_eq gu).eqSymm.eqTrans z.wk)
      exact (eqb_of_ne nn).eqTrans z.eqSymm
    · let E : List (Fm PTm n) := (eqb (gcd k b) one ≐ one) :: C
      have o : E ⊢[PRAAx] eqb (gcd k b) one ≐ one := Prf.hyp0
      have gbk : E ⊢[PRAAx] gcd b k ≐ one := gcd_comm_one hb.wk.wk (eq_of_eqb o)
      have gb : E ⊢[PRAAx] gcd b (a * k) ≐ one := coprime_mul hb.wk.wk hba.wk gbk
      have g : E ⊢[PRAAx] gcd (a * k) b ≐ one := gcd_comm_one (pos_mul ha.wk.wk hk.wk) gb
      exact (eqb_of_eq g).eqTrans o.eqSymm

/-! ## The joint count -/

/-- `[a ∣ m][gcd(m, b) = 1]`, over `0 = m`, `1 = ⟨a, b⟩`. -/
abbrev evB : PTm 2 := eqb (rem (var 0) (fstT (var 1))) zero * eqb (gcd (var 0) (sndT (var 1))) one

theorem ev_at (m a b : PTm n) :
    Γ ⊢[PRAAx] inst2 evB m (pairT a b) ≐ eqb (rem m a) zero * eqb (gcd m b) one := by
  have e : inst2 evB m (pairT a b) =
      eqb (rem m (fstT (pairT a b))) zero * eqb (gcd m (sndT (pairT a b))) one := by
    simp only [inst2, PTm.subst_mul, subst_eqb, subst_ex2, subst_ap2, subst_fstT, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  rw [e]
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair a b)) (.eqRefl _))
    (congrEqb' (congrGcd (.eqRefl _) (snd_pair a b)) (.eqRefl _))

theorem ri_at (m a b : PTm n) :
    Γ ⊢[PRAAx] inst2 (riB totBody) m (pairT a b) ≐ eqb (rem m a) zero * eqb (gcd (quo m a) b) one := by
  rw [inst2_riB, inst2_tot]
  exact congrMul (congrEqb' (congrAp2 remF (.eqRefl _) (fst_pair a b)) (.eqRefl _))
    (congrEqb' (congrGcd (congrAp2 quoF (.eqRefl _) (fst_pair a b)) (snd_pair a b)) (.eqRefl _))

/-- At each `m`: `[a ∣ m][gcd(m, b) = 1] = [a ∣ m][gcd(m/a, b) = 1]`. -/
theorem ev_pt {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] gcd a b ≐ one) (m : PTm n) :
    Γ ⊢[PRAAx] inst2 evB m (pairT a b) ≐ inst2 (riB totBody) m (pairT a b) := by
  refine (ev_at m a b).eqTrans (.eqTrans ?_ (ri_at m a b).eqSymm)
  refine .orE (eq_or_ne (rem m a) zero) ?_ ?_
  · have hd : ((rem m a ≐ zero) :: Γ) ⊢[PRAAx] dvd a m := Prf.hyp0
    have e := eq_of_dvd' ha.wk hd
    exact congrMul (.eqRefl _)
      ((congrEqb' (congrGcd e (.eqRefl _)) (.eqRefl _)).eqTrans (cop_mul_bit ha.wk hb.wk hc.wk (quo m a)))
  · have hn : (neg (rem m a ≐ zero) :: Γ) ⊢[PRAAx] neg (rem m a ≐ zero) := Prf.hyp0
    exact (zero_mul_l (eqb_of_ne hn) _).eqTrans (zero_mul_l (eqb_of_ne hn) _).eqSymm

/-- **The joint count**: `#{m < a b c : a ∣ m, gcd(m, b) = 1} = c φ(b)`. -/
theorem joint_count {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] gcd a b ≐ one) (c : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF evB) (a * (b * c)) (pairT a b) ≐ c * phi b := by
  have ha' := shift_pos ha
  have hb' := shift_pos hb
  have hc' := shift_cop hc
  have s : Γ ⊢[PRAAx] ap2 (sumF evB) (a * (b * c)) (pairT a b) ≐
      ap2 (sumF (riB totBody)) (a * (b * c)) (pairT a b) := by
    refine sum_congr_bounded evB (riB totBody) (pairT a b) (pairT a b) (a * (b * c)) (.allI (.impI ?_))
    rw [shift_pairT]
    exact ev_pt ha'.wk hb'.wk hc'.wk _
  exact s.eqTrans ((reindex_eq totBody (a * (b * c)) ha).eqTrans
    ((congrAp2 (sumF totBody) (cM_mul ha (b * c)) (.eqRefl _)).eqTrans (tot_blocks hb c)))

alias comm_alg := LeanProofs.IPRA.DiophantineNumberTheory.GaussProduct.shuffle

/-- `#{m < a b c : gcd(m, b) = 1} = a c φ(b)`. -/
theorem coprime_count {b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (a c : PTm n) :
    Γ ⊢[PRAAx] Tot (a * (b * c)) b ≐ (a * c) * phi b :=
  (congrAp2 (sumF totBody) (comm_alg a b c) (.eqRefl _)).eqTrans (tot_blocks hb (a * c))

theorem ind_alg {J N A B a b c ph : PTm n} (hJ : Γ ⊢[PRAAx] J ≐ c * ph) (hN : Γ ⊢[PRAAx] N ≐ a * (b * c))
    (hA : Γ ⊢[PRAAx] A ≐ b * c) (hB : Γ ⊢[PRAAx] B ≐ (a * c) * ph) : Γ ⊢[PRAAx] J * N ≐ A * B := by
  ipra_lc 𝔞 N * natEq hJ + 𝔞 c * 𝔞 ph * natEq hN - 𝔞 B * natEq hA - 𝔞 b * 𝔞 c * natEq hB

/-- **Independence**: in the sample `m < N = a b c`, with `#A = #{a ∣ m}`, `#B = #{gcd(m, b) = 1}`,
`#(A ∩ B) · N = #A · #B`. -/
theorem independence {a b : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hc : Γ ⊢[PRAAx] gcd a b ≐ one) (c : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF evB) (a * (b * c)) (pairT a b) * (a * (b * c)) ≐
      cM (a * (b * c)) a * Tot (a * (b * c)) b :=
  ind_alg (joint_count ha hb hc c) (.eqRefl _) (cM_mul ha (b * c)) (coprime_count hb a c)

end LeanProofs.IPRA.AnalyticNumberTheory.FiniteIndependence
