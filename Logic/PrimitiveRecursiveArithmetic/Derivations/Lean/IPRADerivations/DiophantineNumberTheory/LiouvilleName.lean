import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.PlusPower
import IPRADerivations.DiophantineNumberTheory.ModularCertificate

/-!
# The rational name of Liouville's number

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/transcendence.tex`, Theorem
`tr:name`, for the truncations

    r_n = ∑_{j=1}^{n} 10^{−j!} = P_n / q_n,        q_n = 10^{n!},        P_n = ∑_{j=1}^{n} 10^{n! − j!}.

`P_n` is defined by the recursion `P_0 = 0`, `P_{n+1} = P_n · q_n^n + 1` (`Pn`), which is the displayed sum
because `10^{(n+1)! − j!} = 10^{n! − j!} · (10^{n!})^n`; and `q_{n+1} = q_n^n · q_n` (`q_succ`). All statements
are cleared of denominators.

* `incr`: `P_{n+1} q_n = P_n q_{n+1} + q_n`, i.e. `r_{n+1} − r_n = 1/q_{n+1}`; `increasing`: `r_n < r_{n+1}`;
* **`below_ninth`**: `9 P_n + 1 ≤ q_n`, i.e. `r_n < 1/9 < 1`;
* **`tail_bound`**: for `n < m`,
  `(P_m q_n + q_n) q_{n+1} ≤ 2 q_m q_n + P_n q_m q_{n+1}`, i.e. `r_m − r_n + 1/q_m ≤ 2/q_{n+1} = 2 · 10^{−(n+1)!}`.
  The invariant is the packet's geometric estimate in the form "the remaining tail is at most the last term":
  `2/q_{m+1} ≤ 1/q_m` because `q_{m+1} = q_m^m · q_m` and `q_m^m ≥ 2`.

* `P_mod`, **`lowest_terms`**: `P_{k+1} ≡ 1 (mod 10)`, hence `gcd(P_{k+1}, q_{k+1}) = 1`.
* **`modulus_bound`**: `2 · 2^k ≤ q_{k+1}`, i.e. `2 · 10^{−(k+1)!} ≤ 2^{−k}` (the Cauchy modulus);
* **`liouville_gap`**: `2 q_k^h < q_{k+1}` for `h ≤ k`, i.e. `2 · 10^{−(k+1)!} < q_k^{−h}`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.LiouvilleName

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The definitions -/

/-- The numeral `9`. -/
abbrev nine : PTm n := succ (succ (succ (succ (succ (succ (succ two))))))

/-- The numeral `10`. -/
abbrev ten : PTm n := succ nine

/-- `q_k = 10^{k!}`. -/
abbrev qn (k : PTm n) : PTm n := pw ten (fact k)

/-- The step of `P`: variables `0 = k`, `1 = P_k`. -/
abbrev lvStep : PTm 2 := var 1 * pw (pw ten (fact (var 0))) (var 0) + one

/-- `P`. -/
abbrev PF : PR 1 := rec1 zero lvStep

/-- `P_k`. -/
abbrev Pn (k : PTm n) : PTm n := ap1 PF k

theorem P_zero : Γ ⊢[PRAAx] Pn (zero : PTm n) ≐ zero := by
  simpa using rec1_zero (Γ := Γ) zero lvStep

theorem P_succ (k : PTm n) : Γ ⊢[PRAAx] Pn (succ k) ≐ Pn k * pw (qn k) k + one := by
  have h := rec1_succ (Γ := Γ) zero lvStep k
  simp only [PTm.subst_add, PTm.subst_mul, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-- `q_{k+1} = q_k^k · q_k`. -/
theorem q_succ (k : PTm n) : Γ ⊢[PRAAx] qn (succ k) ≐ pw (qn k) k * qn k :=
  (congrPw (.eqRefl _) (fact_succ k zero)).eqTrans ((pw_mul ten (fact k) (succ k)).eqSymm.eqTrans (pw_succ _ _))

theorem congrP {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] Pn a ≐ Pn b := congrAp1 PF h

theorem congrQ {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] qn a ≐ qn b :=
  congrPw (.eqRefl _) (congrAp2 factF h (.eqRefl _))

/-! ## Sizes -/

theorem ten_pos : Γ ⊢[PRAAx] (ten : PTm n) ≐ succ (pred ten) := congrSucc (pred_succ _).eqSymm

theorem q_pos (k : PTm n) : Γ ⊢[PRAAx] qn k ≐ succ (pred (qn k)) := pw_pos' ten_pos (fact k)

/-- `10 ≤ q_k`. -/
theorem q_ge (k : PTm n) : Γ ⊢[PRAAx] le ten (qn k) :=
  le_congr (.eqRefl _) (congrPw (.eqRefl _) (fact_pos k).eqSymm) (le_self_pw nine (pred (fact k)))

theorem le_pw_self {a : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (j : PTm n) :
    Γ ⊢[PRAAx] le a (pw a (succ j)) :=
  le_congr ha.eqSymm (congrPw ha.eqSymm (.eqRefl _)) (le_self_pw (pred a) j)

theorem two_le_ten : Γ ⊢[PRAAx] le (two : PTm n) ten :=
  le_of_eq_add (d := succ (succ (succ (succ (succ (succ two)))))) (by ipra_ring)

theorem one_le_ten : Γ ⊢[PRAAx] le (one : PTm n) ten :=
  le_of_eq_add (d := nine) (by ipra_ring)

/-! ## The increments -/

theorem incr_alg {P P' q q' Q : PTm n} (eP : Γ ⊢[PRAAx] P' ≐ P * Q + one) (eq : Γ ⊢[PRAAx] q' ≐ Q * q) :
    Γ ⊢[PRAAx] P' * q ≐ P * q' + q := by
  ipra_lc 𝔞 q * natEq eP - 𝔞 P * natEq eq

/-- `P_{k+1} q_k = P_k q_{k+1} + q_k`: `r_{k+1} − r_k = 1/q_{k+1}`. -/
theorem incr (k : PTm n) : Γ ⊢[PRAAx] Pn (succ k) * qn k ≐ Pn k * qn (succ k) + qn k :=
  incr_alg (P_succ k) (q_succ k)

/-- `r_k < r_{k+1}`. -/
theorem increasing (k : PTm n) : Γ ⊢[PRAAx] lt (Pn k * qn (succ k)) (Pn (succ k) * qn k) := by
  have x := natEq (incr (Γ := Γ) k)
  have h1 : Γ ⊢[PRAAx] le one (qn k) := le_trans one_le_ten (q_ge k)
  ipra_le sl h1 with x

/-! ## `r_k < 1/9` -/

theorem ninth_step {P P' q q' Q : PTm n} (ih : Γ ⊢[PRAAx] le (nine * P + one) q) (hQ : Γ ⊢[PRAAx] le ten Q)
    (eP : Γ ⊢[PRAAx] P' ≐ P * Q + one) (eq : Γ ⊢[PRAAx] q' ≐ Q * q) :
    Γ ⊢[PRAAx] le (nine * P' + one) q' := by
  have a := natEq eP; have b := natEq eq
  ipra_le 𝔞 Q * sl ih + sl hQ with b - 9 * a

theorem ninth_first {P P' q q' Q : PTm n} (hP : Γ ⊢[PRAAx] P ≐ zero) (hq : Γ ⊢[PRAAx] q ≐ ten)
    (hQ : Γ ⊢[PRAAx] Q ≐ one) (eP : Γ ⊢[PRAAx] P' ≐ P * Q + one) (eq : Γ ⊢[PRAAx] q' ≐ Q * q) :
    Γ ⊢[PRAAx] le (nine * P' + one) q' := by
  have a := natEq eP; have b := natEq eq; have c := natEq hP; have d := natEq hq; have e := natEq hQ
  refine le_of_eq_add (d := zero) ?_
  ipra_lc b - 9 * a + (𝔞 q - 9 * 𝔞 P) * e + d - 9 * c

theorem q_zero : Γ ⊢[PRAAx] qn (zero : PTm n) ≐ ten :=
  (congrPw (.eqRefl _) (fact_zero zero)).eqTrans (pw_one ten)

/-- Variable: `0 = k`. -/
abbrev ninthF : Fm PTm 1 := le (nine * Pn (var 0) + one) (qn (var 0))

theorem ninth_zero : Γ ⊢[PRAAx] le (nine * Pn (zero : PTm n) + one) (qn zero) := by
  have e : Γ ⊢[PRAAx] nine * Pn (zero : PTm n) + one ≐ one :=
    (congrAdd ((congrMul (.eqRefl _) P_zero).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_add one)
  exact le_congr e.eqSymm q_zero.eqSymm one_le_ten

theorem ninth_succ {k : PTm n} (ih : Γ ⊢[PRAAx] le (nine * Pn k + one) (qn k)) :
    Γ ⊢[PRAAx] le (nine * Pn (succ k) + one) (qn (succ k)) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have h0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    exact ninth_first ((congrP h0).eqTrans P_zero) ((congrQ h0).eqTrans q_zero)
      ((congrPw (.eqRefl _) h0).eqTrans (pw_zero _)) (P_succ k) (q_succ k)
  · have hk : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have hQ : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] le ten (pw (qn k) k) :=
      le_trans (q_ge k) (le_congr (.eqRefl _) (congrPw (.eqRefl _) hk.eqSymm) (le_pw_self (q_pos k) (pred k)))
    exact ninth_step ih.wk hQ (P_succ k) (q_succ k)

theorem ninth_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] ninthF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap1, subst_ap2]
  · exact ninth_zero
  · exact ninth_succ Prf.hyp0

/-- **`r_k < 1/9`**: `9 P_k + 1 ≤ q_k`. -/
theorem below_ninth (k : PTm n) : Γ ⊢[PRAAx] le (nine * Pn k + one) (qn k) := by
  have i := inst (Γ := Γ) ninth_open (![k] : Fin 1 → PTm n)
  simp only [ninthF, subst_le, subst_ap1, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact i

/-! ## The tail -/

/-- The tail inequality at the pair `(m, k)`: `(P_m q_k + q_k) q_{k+1} ≤ 2 q_m q_k + P_k q_m q_{k+1}`. -/
abbrev Tail (m k : PTm n) : Fm PTm n :=
  le ((Pn m * qn k + qn k) * qn (succ k)) (two * (qn m * qn k) + Pn k * (qn m * qn (succ k)))

theorem tail_step {Pm Pm' qm qm' Q Pk qk qk1 : PTm n}
    (ih : Γ ⊢[PRAAx] le ((Pm * qk + qk) * qk1) (two * (qm * qk) + Pk * (qm * qk1)))
    (hQ : Γ ⊢[PRAAx] le two Q) (eP : Γ ⊢[PRAAx] Pm' ≐ Pm * Q + one) (eq : Γ ⊢[PRAAx] qm' ≐ Q * qm) :
    Γ ⊢[PRAAx] le ((Pm' * qk + qk) * qk1) (two * (qm' * qk) + Pk * (qm' * qk1)) := by
  have a := natEq eP; have b := natEq eq
  ipra_le 𝔞 Q * sl ih + sl hQ * 𝔞 qk * 𝔞 qk1 with (2 * 𝔞 qk + 𝔞 Pk * 𝔞 qk1) * b - 𝔞 qk * 𝔞 qk1 * a

/-- The first tail: `m = k + 1`, with equality. -/
theorem tail_first (k : PTm n) : Γ ⊢[PRAAx] Tail (succ k) k := by
  have x := natEq (incr (Γ := Γ) k)
  ipra_le 0 with -𝔞 (qn (succ k)) * x

/-- From `m` to `m + 1`, for `m = j + 1`. -/
theorem tail_next {j k : PTm n} (ih : Γ ⊢[PRAAx] Tail (succ j) k) : Γ ⊢[PRAAx] Tail (succ (succ j)) k :=
  tail_step ih (le_trans two_le_ten (le_trans (q_ge (succ j)) (le_pw_self (q_pos (succ j)) j)))
    (P_succ (succ j)) (q_succ (succ j))

theorem tail_congr {m m' k : PTm n} (e : Γ ⊢[PRAAx] m ≐ m') (h : Γ ⊢[PRAAx] Tail m k) :
    Γ ⊢[PRAAx] Tail m' k :=
  le_congr (congrMul (congrAdd (congrMul (congrP e) (.eqRefl _)) (.eqRefl _)) (.eqRefl _))
    (congrAdd (congrMul (.eqRefl _) (congrMul (congrQ e) (.eqRefl _)))
      (congrMul (.eqRefl _) (congrMul (congrQ e) (.eqRefl _)))) h

/-- Variables: `0 = t`, `1 = k`; the pair `(k + 1 + t, k)`. -/
abbrev tailF : Fm PTm 2 :=
  le ((Pn (succ (var 1 + var 0)) * qn (var 1) + qn (var 1)) * qn (succ (var 1)))
    (two * (qn (succ (var 1 + var 0)) * qn (var 1)) +
      Pn (var 1) * (qn (succ (var 1 + var 0)) * qn (succ (var 1))))

theorem tail_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] tailF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap1, subst_ap2]
  · exact tail_congr (congrSucc (add_zero (var 0)).eqSymm) (tail_first (var 0))
  · exact tail_congr (congrSucc (add_succ (var 1) (var 0)).eqSymm)
      (tail_next (Prf.hyp0 (Γ := []) (φ := tailF)))

theorem m_alg {m k t : PTm n} (e : Γ ⊢[PRAAx] m ≐ succ k + t) : Γ ⊢[PRAAx] succ (k + t) ≐ m := by
  ipra_lc -natEq e

/-- **The tail bound**: for `k < m`, `(P_m q_k + q_k) q_{k+1} ≤ 2 q_m q_k + P_k q_m q_{k+1}`, that is
`r_m − r_k + 1/q_m ≤ 2/q_{k+1}`. -/
theorem tail_bound {m k : PTm n} (h : Γ ⊢[PRAAx] lt k m) : Γ ⊢[PRAAx] Tail m k := by
  have i := inst (Γ := Γ) tail_open (![monus m (succ k), k] : Fin 2 → PTm n)
  simp only [tailF, subst_le, subst_ap1, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact tail_congr (m_alg (eq_add_of_le h)) i

/-! ## Lowest terms -/

theorem P_pos (k : PTm n) : Γ ⊢[PRAAx] Pn (succ k) ≐ succ (pred (Pn (succ k))) :=
  pos_of_eq_succ (c := Pn k * pw (qn k) k) ((P_succ k).eqTrans (succ_eq_add_one _).eqSymm)

/-- `q_k = 10 · 10^{k! − 1}`. -/
theorem q_ten (k : PTm n) : Γ ⊢[PRAAx] qn k ≐ ten * pw ten (pred (fact k)) :=
  (congrPw (.eqRefl _) (fact_pos k)).eqTrans ((pw_succ _ _).eqTrans (mul_comm _ _))

theorem first_alg {Ps P Q : PTm n} (eP : Γ ⊢[PRAAx] Ps ≐ P * Q + one) (hP : Γ ⊢[PRAAx] P ≐ zero) :
    Γ ⊢[PRAAx] Ps ≐ ten * zero + one := by
  ipra_lc natEq eP + 𝔞 Q * natEq hP

theorem later_alg {Ps P Q R q X : PTm n} (eP : Γ ⊢[PRAAx] Ps ≐ P * Q + one) (eQ : Γ ⊢[PRAAx] Q ≐ R * q)
    (eq : Γ ⊢[PRAAx] q ≐ ten * X) : Γ ⊢[PRAAx] Ps ≐ ten * (P * (R * X)) + one := by
  ipra_lc natEq eP + 𝔞 P * natEq eQ + 𝔞 P * 𝔞 R * natEq eq

theorem rem_one_ten : Γ ⊢[PRAAx] rem (one : PTm n) ten ≐ one := rem_small two_le_ten

/-- `P_{k+1} ≡ 1 (mod 10)`. -/
theorem P_mod (k : PTm n) : Γ ⊢[PRAAx] rem (Pn (succ k)) ten ≐ one := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have h0 : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    exact (congrAp2 remF (first_alg (P_succ k) ((congrP h0).eqTrans P_zero)) (.eqRefl _)).eqTrans
      ((rem_add_mul ten_pos zero one).eqTrans rem_one_ten)
  · have hk : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have eQ : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] pw (qn k) k ≐ pw (qn k) (pred k) * qn k :=
      (congrPw (.eqRefl _) hk).eqTrans (pw_succ _ _)
    exact (congrAp2 remF (later_alg (P_succ k) eQ (q_ten k)) (.eqRefl _)).eqTrans
      ((rem_add_mul ten_pos _ one).eqTrans rem_one_ten)

/-- **Lowest terms**: `gcd(P_{k+1}, q_{k+1}) = 1`. -/
theorem lowest_terms (k : PTm n) : Γ ⊢[PRAAx] gcd (Pn (succ k)) (qn (succ k)) ≐ one := by
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  have g0 : Γ ⊢[PRAAx] gcd (one : PTm n) ten ≐ one :=
    eq_one_of_dvd_one (gcd_pos h1) (Prf.andE₁ (gcd_dvd' (b := ten) h1))
  have g : Γ ⊢[PRAAx] gcd (Pn (succ k)) ten ≐ one :=
    (gcd_rem ten_pos (Pn (succ k))).eqSymm.eqTrans ((congrGcd (P_mod k) (.eqRefl _)).eqTrans g0)
  exact cop_pow (P_pos k) g (fact (succ k))

/-! ## The modulus and the Liouville gap -/

theorem q_succ_pw (k : PTm n) : Γ ⊢[PRAAx] qn (succ k) ≐ pw (qn k) (succ k) :=
  (q_succ k).eqTrans (pw_succ _ _).eqSymm

/-- `k + 1 ≤ (k + 1)!`. -/
theorem succ_le_fact (k : PTm n) : Γ ⊢[PRAAx] le (succ k) (fact (succ k)) := by
  have e := natEq (fact_succ (Γ := Γ) k zero)
  have h1 : Γ ⊢[PRAAx] le one (fact k) := one_le_pos (fact_pos k)
  ipra_le sl h1 * 𝔞 (succ k) with e

/-- **The Cauchy modulus**: `2 · 2^k ≤ q_{k+1}`. -/
theorem modulus_bound (k : PTm n) : Γ ⊢[PRAAx] le (two * pw two k) (qn (succ k)) :=
  le_congr ((pw_succ two k).eqTrans (mul_comm _ _)) (.eqRefl _)
    (le_trans (pw_le_pw (succ k) two_le_ten) (pw_le_exp ten_pos (succ_le_fact k)))

/-- **The Liouville gap**: `2 q_k^h < q_{k+1}` for `h ≤ k`. -/
theorem liouville_gap {h k : PTm n} (hk : Γ ⊢[PRAAx] le h k) :
    Γ ⊢[PRAAx] lt (two * pw (qn k) h) (qn (succ k)) := by
  have l1 : Γ ⊢[PRAAx] le (pw (qn k) (succ h)) (pw (qn k) (succ k)) :=
    pw_le_exp (q_pos k) ((succ_monus_succ _ _).eqTrans hk)
  have e1 := natEq (pw_succ (Γ := Γ) (qn k) h)
  have e2 := natEq (q_succ_pw (Γ := Γ) k)
  have hq := q_ge (Γ := Γ) k
  have hpos : Γ ⊢[PRAAx] le one (pw (qn k) h) := one_le_pos (pw_pos' (q_pos k) h)
  ipra_le sl l1 + 𝔞 (pw (qn k) h) * sl hq + 7 * 𝔞 (pw (qn k) h) + sl hpos with e2 + e1

end LeanProofs.IPRA.DiophantineNumberTheory.LiouvilleName
