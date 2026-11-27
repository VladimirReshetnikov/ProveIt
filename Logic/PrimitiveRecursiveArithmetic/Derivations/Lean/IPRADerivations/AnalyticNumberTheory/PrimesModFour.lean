import IPRADerivations.DiophantineNumberTheory.FourSquares

/-!
# Primes in the classes `1` and `3` modulo `4`, with bounds

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, `an:progressions`:
for every `N` there is a prime `q > N` with `q ≡ 3 (mod 4)` and `q ≤ 4 N! − 1`, and for every `N ≥ 2` there is
a prime `p > N` with `p ≡ 1 (mod 4)` and `p ≤ (N!)² + 1`; both selections are explicit terms.

* `gt_of_dvd`, `gt_of_dvd'`: a number `p ≥ 2` dividing `N! c + 1`, or `T` with `T + 1 = N! c`, exceeds `N`;
* the class `1`: `P1 N = ℓ((N!)² + 1)`, the least prime factor. `N!` is a square root of `−1` modulo it, so the
  bounded search for a root of the residue `p − 1` succeeds and the first supplementary law
  (`QuadraticSupplements.minus_one_law`) gives `⌊p/2⌋` even (`prime_one_mod_four`);
* the class `3`: `Q3 n` is the bit of the bounded search for a prime divisor `d ≡ 3 (mod 4)` of `n`, and
  `q3_all`: the search succeeds for every `n ≡ 3 (mod 4)`. The paper argues that a product of primes
  `≡ 1 (mod 4)` is `≡ 1`; here this is a strong induction (`Foundations/StrongInduction`): with `ℓ = ℓ(n)`,
  either `ℓ ≡ 3`, or `ℓ ≡ 1` and the cofactor `n/ℓ ≡ 3` is smaller (`ℓ` even is impossible for odd `n`);
* `prime_three_mod_four`: `q3 (4 N! ∸ 1)` is a prime `> N`, `≡ 3 (mod 4)`, and at most `4 N! − 1`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimesModFour

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime lpf dvd_fact fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos lpf_prime' lpf_dvd' subst_isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (sqB sq_at)
open LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma (rb)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatTwoSquares (four_pos one_lt_four even_absurd
  odd_of_prime_ne_two)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresDescent (dvd_of_eq_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquares (cofactor_pos)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_intro ex_elim eqb_cases eq_of_eqb
  one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Divisors of `N! c ± 1` exceed `N` -/

theorem one_lt_of_two_le {p : PTm k} (hp2 : Γ ⊢[PRAAx] le two p) : Γ ⊢[PRAAx] lt one p := hp2

/-- `p ≤ N` gives `N! c ≡ 0 (mod p)`. -/
theorem fact_mul_zero {p N c : PTm k} (hp2 : Γ ⊢[PRAAx] le two p) (h : Γ ⊢[PRAAx] le p N) :
    Γ ⊢[PRAAx] rem (fact N * c) p ≐ zero := by
  have hp1 := p_pos hp2
  have d : Γ ⊢[PRAAx] dvd p (fact N) :=
    dvd_congr_left hp1.eqSymm (dvd_fact (le_congr hp1 (.eqRefl _) h))
  have d' : Γ ⊢[PRAAx] rem (fact N) p ≐ rem zero p := d.eqTrans (rem_zero p).eqSymm
  exact (rem_mul_congr2 hp1 d' (.eqRefl (rem c p))).eqTrans
    ((congrAp2 remF (zero_mul c) (.eqRefl _)).eqTrans (rem_zero p))

/-- A number `p ≥ 2` dividing `N! c + 1` exceeds `N`. -/
theorem gt_of_dvd {p N c : PTm k} (hp2 : Γ ⊢[PRAAx] le two p)
    (hd : Γ ⊢[PRAAx] dvd p (fact N * c + one)) : Γ ⊢[PRAAx] lt N p := by
  have hp1 := p_pos hp2
  refine .orE (lt_or_le N p) Prf.hyp0 ?_
  have z := fact_mul_zero (c := c) hp2.wk (Prf.hyp0 (Γ := Γ) (φ := le p N))
  have a := rem_add_congr hp1.wk (z.eqTrans (rem_zero p).eqSymm) (.eqRefl (rem one p))
  have b : (le p N :: Γ) ⊢[PRAAx] rem (zero + one) p ≐ one :=
    (congrAp2 remF (zero_add one) (.eqRefl _)).eqTrans (rem_small (one_lt_of_two_le hp2.wk))
  exact one_ne_zero _ ((a.eqTrans b).eqSymm.eqTrans hd.wk)

/-- A number `p ≥ 2` dividing `T`, where `T + 1 = N! c`, exceeds `N`. -/
theorem gt_of_dvd' {p N c T : PTm k} (hp2 : Γ ⊢[PRAAx] le two p) (hd : Γ ⊢[PRAAx] dvd p T)
    (e : Γ ⊢[PRAAx] T + one ≐ fact N * c) : Γ ⊢[PRAAx] lt N p := by
  have hp1 := p_pos hp2
  refine .orE (lt_or_le N p) Prf.hyp0 ?_
  have z := fact_mul_zero (c := c) hp2.wk (Prf.hyp0 (Γ := Γ) (φ := le p N))
  have a := rem_add_congr (Γ := le p N :: Γ) hp1.wk (hd.wk.eqTrans (rem_zero p).eqSymm) (.eqRefl (rem one p))
  have b : (le p N :: Γ) ⊢[PRAAx] rem (zero + one) p ≐ one :=
    (congrAp2 remF (zero_add one) (.eqRefl _)).eqTrans (rem_small (one_lt_of_two_le hp2.wk))
  exact one_ne_zero _ ((a.eqTrans b).eqSymm.eqTrans ((congrAp2 remF e.wk (.eqRefl _)).eqTrans z))

/-! ## The class `1` -/

theorem mod4_of_parities {p : PTm k} (po : Γ ⊢[PRAAx] par p ≐ one) (hz : Γ ⊢[PRAAx] par (half p) ≐ zero) :
    Γ ⊢[PRAAx] rem p (two * two) ≐ one := by
  have a := natEq (half_par (Γ := Γ) p); have b := natEq (half_par (Γ := Γ) (half p))
  have c := natEq po; have d := natEq hz
  have e : Γ ⊢[PRAAx] p ≐ (two * two) * half (half p) + one := by
    ipra_lc a + 2 * b + c + 2 * d
  exact Prf.andE₂ (dmu four_pos e one_lt_four)

/-- `(N!)² + 1`. -/
abbrev T1 (N : PTm k) : PTm k := fact N * fact N + one

/-- The selected prime of the class `1`: the least prime factor of `(N!)² + 1`. -/
abbrev P1 (N : PTm k) : PTm k := lpf (T1 N)

theorem pred_alg {p : PTm k} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) :
    Γ ⊢[PRAAx] pred p + one ≐ p * one + zero := by
  ipra_lc -natEq hp1

/-- For `N ≥ 2`: `P1 N` is a prime `> N`, `≡ 1 (mod 4)`, and at most `(N!)² + 1`. -/
theorem prime_one_mod_four {N : PTm k} (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] prime (P1 N) ⋏ (lt N (P1 N) ⋏ ((rem (P1 N) (two * two) ≐ one) ⋏ le (P1 N) (T1 N))) := by
  have fp := natEq (fact_pos (Γ := Γ) N)
  have hT : Γ ⊢[PRAAx] le two (T1 N) := by
    ipra_le 𝔞 (pred (fact N)) * 𝔞 (pred (fact N)) + 2 * 𝔞 (pred (fact N)) with
      (𝔞 (fact N) + 𝔞 (pred (fact N)) + 1) * fp
  have hp := lpf_prime' hT
  have hd := lpf_dvd' hT
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have hgt := gt_of_dvd hp2 hd
  have hle := dvd_le' hp1 hd (p_pos hT)
  -- `P1 N ≠ 2`, hence odd
  have hne : Γ ⊢[PRAAx] neg (P1 N ≐ two) :=
    .impI (le_lt_absurd _ hN.wk (lt_congr (.eqRefl _) Prf.hyp0 hgt.wk))
  have po := odd_of_prime_ne_two hp hne
  -- `N!` is a root of `−1`
  have e1 : Γ ⊢[PRAAx] rem (fact N * fact N + one) (P1 N) ≐ rem (pred (P1 N) + one) (P1 N) :=
    hd.eqTrans (((congrAp2 remF (pred_alg hp1) (.eqRefl _)).eqTrans
      ((rem_add_mul hp1 one zero).eqTrans (rem_zero _))).eqSymm)
  have e2 : Γ ⊢[PRAAx] rem (fact N * fact N) (P1 N) ≐ rem (pred (P1 N)) (P1 N) :=
    rem_cancel hp1 ((congrAp2 remF (add_comm _ _) (.eqRefl _)).eqTrans
      (e1.eqTrans (congrAp2 remF (add_comm _ _) (.eqRefl _))))
  have rr : Γ ⊢[PRAAx] rem (rem (fact N) (P1 N)) (P1 N) ≐ rem (fact N) (P1 N) :=
    rem_small (rem_lt' hp1 _)
  have val : Γ ⊢[PRAAx] inst2 sqB (rem (fact N) (P1 N)) (pairT (P1 N) (pred (P1 N))) ≐ one :=
    (sq_at _ _ _).eqTrans (eqb_of_eq ((rem_mul_congr2 hp1 rr rr).eqTrans e2))
  have r1 : Γ ⊢[PRAAx] rb (P1 N) (pred (P1 N)) ≐ one :=
    ex_intro sqB (.impI (one_ne_zero _ (val.wk.eqSymm.eqTrans Prf.hyp0))) (rem_lt' hp1 _)
  have s0 : Γ ⊢[PRAAx] signBit (P1 N) (pred (P1 N)) ≐ zero :=
    (sign_eq _ _).eqTrans ((congrMonus (.eqRefl _) r1).eqTrans (monus_self one))
  have hz := (minus_one_law hp po).eqSymm.eqTrans s0
  exact .andI hp (.andI hgt (.andI (mod4_of_parities po hz) hle))

/-! ## The class `3` -/

/-- `[d prime][d ∣ n][d ≡ 3 (mod 4)]`, over `0 = d`, `1 = n`. -/
abbrev qB : PTm 2 :=
  isP (var 0) * (eqb (rem (var 1) (var 0)) zero * eqb (rem (var 0) (two * two)) (succ two))

theorem inst2_qB (d n : PTm k) : inst2 qB d n =
    isP d * (eqb (rem n d) zero * eqb (rem d (two * two)) (succ two)) := by
  simp [inst2]

/-- The bit of "`n` has a prime divisor `≡ 3 (mod 4)`". -/
abbrev Q3 (n : PTm k) : PTm k := exB qB (succ n) n

/-- The least prime divisor `≡ 3 (mod 4)`. -/
abbrev q3 (n : PTm k) : PTm k := wit qB (succ n) n

theorem bits_alg {a b c : PTm k} (ha : Γ ⊢[PRAAx] a ≐ one) (hb : Γ ⊢[PRAAx] b ≐ one)
    (hc : Γ ⊢[PRAAx] c ≐ one) : Γ ⊢[PRAAx] a * (b * c) ≐ one := by
  ipra_lc 𝔞 b * 𝔞 c * natEq ha + 𝔞 c * natEq hb + natEq hc

/-- A prime divisor `≡ 3 (mod 4)` at most `n` makes the bit `1`. -/
theorem q3_intro {n d : PTm k} (hd : Γ ⊢[PRAAx] prime d) (hdv : Γ ⊢[PRAAx] dvd d n)
    (h3 : Γ ⊢[PRAAx] rem d (two * two) ≐ succ two) (hle : Γ ⊢[PRAAx] le d n) : Γ ⊢[PRAAx] Q3 n ≐ one := by
  have val : Γ ⊢[PRAAx] inst2 qB d n ≐ one := by
    rw [inst2_qB]
    exact bits_alg (isP_of_prime hd) (eqb_of_eq hdv) (eqb_of_eq h3)
  exact ex_intro qB (.impI (one_ne_zero _ (val.wk.eqSymm.eqTrans Prf.hyp0)))
    ((succ_monus_succ _ _).eqTrans hle)

theorem ne_left {a b : PTm k} (h : Γ ⊢[PRAAx] neg (a * b ≐ zero)) : Γ ⊢[PRAAx] neg (a ≐ zero) :=
  .impI (.impE h.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))

theorem ne_right {a b : PTm k} (h : Γ ⊢[PRAAx] neg (a * b ≐ zero)) : Γ ⊢[PRAAx] neg (b ≐ zero) :=
  .impI (.impE h.wk ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))

theorem eq_of_eqb_ne {a b : PTm k} (h : Γ ⊢[PRAAx] neg (eqb a b ≐ zero)) : Γ ⊢[PRAAx] a ≐ b := by
  refine .orE (eqb_cases a b) ?_ ?_
  · exact .botE _ (.impE h.wk Prf.hyp0)
  · exact eq_of_eqb Prf.hyp0

/-- The bit `1` gives the prime divisor `q3 n ≡ 3 (mod 4)` of `n`, with `q3 n ≤ n`. -/
theorem q3_elim {n : PTm k} (h : Γ ⊢[PRAAx] Q3 n ≐ one) :
    Γ ⊢[PRAAx] prime (q3 n) ⋏ (dvd (q3 n) n ⋏ ((rem (q3 n) (two * two) ≐ succ two) ⋏ le (q3 n) n)) := by
  have ee := ex_elim qB h
  have ne := Prf.andE₂ ee
  rw [inst2_qB] at ne
  have hP : Γ ⊢[PRAAx] isP (q3 n) ≐ one := by
    refine .orE (isP_01 (q3 n)) ?_ Prf.hyp0
    exact .botE _ (.impE (ne_left ne).wk Prf.hyp0)
  exact .andI (prime_of_isP hP) (.andI (eq_of_eqb_ne (ne_left (ne_right ne)))
    (.andI (eq_of_eqb_ne (ne_right (ne_right ne))) ((succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₁ ee))))

/-! ### The step of the strong induction -/

theorem ge_two_of_three {n q : PTm k} (e : Γ ⊢[PRAAx] n ≐ (two * two) * q + succ two) :
    Γ ⊢[PRAAx] le two n := by
  have a := natEq e
  ipra_le 4 * 𝔞 q + 1 with a

theorem odd_of_three {n q : PTm k} (e : Γ ⊢[PRAAx] n ≐ (two * two) * q + succ two) :
    Γ ⊢[PRAAx] par n ≐ one := by
  have e' : Γ ⊢[PRAAx] n ≐ two * (two * q + one) + one := by
    ipra_lc natEq e
  exact (congrAp1 parF e').eqTrans (par_double_succ _)

theorem even_mul {n l c a r' : PTm k} (eN : Γ ⊢[PRAAx] n ≐ l * c + zero)
    (el : Γ ⊢[PRAAx] l ≐ (two * two) * a + two * r') : Γ ⊢[PRAAx] n ≐ two * ((two * a + r') * c) := by
  ipra_lc natEq eN + 𝔞 c * natEq el

theorem one_mul_alg {n l c a : PTm k} (eN : Γ ⊢[PRAAx] n ≐ l * c + zero)
    (el : Γ ⊢[PRAAx] l ≐ (two * two) * a + one) : Γ ⊢[PRAAx] n ≐ (two * two) * (a * c) + c := by
  ipra_lc natEq eN + 𝔞 c * natEq el

theorem two_one : Γ ⊢[PRAAx] (two : PTm k) ≐ two * one := by ipra_ring

theorem cofactor_lt {N L c : PTm k} (hL : Γ ⊢[PRAAx] le two L) (c1 : Γ ⊢[PRAAx] le one c)
    (eN : Γ ⊢[PRAAx] N ≐ L * c + zero) : Γ ⊢[PRAAx] lt c N := by
  have a := natEq eN
  ipra_le sl hL * 𝔞 c + sl c1 with a

theorem dvd_chain {n l c d e : PTm k} (hd1 : Γ ⊢[PRAAx] d ≐ succ (pred d)) (eN : Γ ⊢[PRAAx] n ≐ l * c + zero)
    (ec : Γ ⊢[PRAAx] c ≐ d * e + zero) : Γ ⊢[PRAAx] dvd d n := by
  exact dvd_of_eq_mul (K := e * l) hd1 (by ipra_lc natEq eN + 𝔞 l * natEq ec)

/-- The violation `[n ≡ 3 (mod 4)] (1 ∸ Q3 n)`, over `0 = n`. -/
abbrev vQ : PTm 2 := eqb (rem (var 0) (two * two)) (succ two) * monus one (Q3 (var 0))

theorem inst2_vQ (N x : PTm k) : inst2 vQ N x = eqb (rem N (two * two)) (succ two) * monus one (Q3 N) := by
  simp [inst2]

theorem bit_of_viol {c : PTm k} (h3 : Γ ⊢[PRAAx] rem c (two * two) ≐ succ two)
    (hv : Γ ⊢[PRAAx] eqb (rem c (two * two)) (succ two) * monus one (Q3 c) ≐ zero) : Γ ⊢[PRAAx] Q3 c ≐ one := by
  refine .orE (ex_cases qB (succ c) c) ?_ Prf.hyp0
  have m1 := (congrMonus (.eqRefl (one : PTm k)) (Prf.hyp0 (Γ := Γ) (φ := Q3 c ≐ zero))).eqTrans (monus_zero one)
  exact one_ne_zero _ (((congrMul (eqb_of_eq h3.wk) m1).eqTrans (one_mul one)).eqSymm.eqTrans hv.wk)

/-- If the search succeeds at every smaller number `≡ 3 (mod 4)`, it succeeds at `N ≡ 3 (mod 4)`. -/
theorem q3_step {N x : PTm k} (hS : Γ ⊢[PRAAx] ap2 (sumF vQ) N x ≐ zero)
    (h3 : Γ ⊢[PRAAx] rem N (two * two) ≐ succ two) : Γ ⊢[PRAAx] Q3 N ≐ one := by
  have dN := (Prf.andE₁ (dm (Γ := Γ) four_pos N)).eqTrans (congrAdd (.eqRefl _) h3)
  have hN2 := ge_two_of_three dN
  have po := odd_of_three dN
  have hp := lpf_prime' hN2
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have eN : Γ ⊢[PRAAx] N ≐ lpf N * quo N (lpf N) + zero :=
    (Prf.andE₁ (dm hp1 N)).eqTrans (congrAdd (.eqRefl _) (lpf_dvd' hN2))
  have dl := dm (Γ := Γ) four_pos (lpf N)
  have e4 : Γ ⊢[PRAAx] (two * two : PTm k) ≐ succ (succ two) := by ipra_ring
  have hr : Γ ⊢[PRAAx] lt (rem (lpf N) (two * two)) (succ (succ two)) := lt_congr (.eqRefl _) e4 (Prf.andE₂ dl)
  refine .orE (lt_succ_cases hr) ?_ ?_
  · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := Γ) (φ := lt (rem (lpf N) (two * two)) (succ two)))) ?_ ?_
    · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt (rem (lpf N) (two * two)) (succ two) :: Γ)
        (φ := lt (rem (lpf N) (two * two)) two))) ?_ ?_
      · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt (rem (lpf N) (two * two)) two ::
          lt (rem (lpf N) (two * two)) (succ two) :: Γ) (φ := lt (rem (lpf N) (two * two)) one)))
          (lt_zero_absurd _ Prf.hyp0) ?_
        -- remainder `0`: `ℓ` even, impossible
        have el := (Prf.andE₁ dl).wk.wk.wk.wk.eqTrans (congrAdd (.eqRefl _)
          ((Prf.hyp0 (Γ := lt (rem (lpf N) (two * two)) one :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) (φ := rem (lpf N) (two * two) ≐ zero)).eqTrans
            (mul_zero two).eqSymm))
        exact even_absurd _ po.wk.wk.wk.wk (even_mul eN.wk.wk.wk.wk el)
      · -- remainder `1`: pass to the cofactor
        have r1 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx] rem (lpf N) (two * two) ≐ one := Prf.hyp0
        have dl3 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx]
            lpf N ≐ (two * two) * quo (lpf N) (two * two) + rem (lpf N) (two * two) := (Prf.andE₁ dl).wk.wk.wk
        have el := dl3.eqTrans (congrAdd (.eqRefl _) r1)
        have eN3 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx]
            N ≐ lpf N * quo N (lpf N) + zero := eN.wk.wk.wk
        have hN23 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx] le two N := hN2.wk.wk.wk
        have hp23 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx] le two (lpf N) := hp2.wk.wk.wk
        have h33 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx] rem N (two * two) ≐ succ two := h3.wk.wk.wk
        have hS3 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx] ap2 (sumF vQ) N x ≐ zero := hS.wk.wk.wk
        have ec := one_mul_alg eN3 el
        have c3 : ((rem (lpf N) (two * two) ≐ one) :: lt (rem (lpf N) (two * two)) two ::
            lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx]
            rem (quo N (lpf N)) (two * two) ≐ succ two :=
          (rem_add_mul four_pos _ _).eqSymm.eqTrans ((congrAp2 remF ec.eqSymm (.eqRefl _)).eqTrans h33)
        have c1 := cofactor_pos hN23 eN3
        have cN := cofactor_lt hp23 c1 eN3
        have vc := sum_zero_elim vQ hS3 cN
        rw [inst2_vQ] at vc
        have qc := q3_elim (bit_of_viol c3 vc)
        have hd := Prf.andE₁ qc
        have hd1 := p_pos (prime_two hd)
        have ecd := (Prf.andE₁ (dm hd1 (quo N (lpf N)))).eqTrans
          (congrAdd (.eqRefl _) (Prf.andE₁ (Prf.andE₂ qc)))
        exact q3_intro hd (dvd_chain hd1 eN3 ecd) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ qc)))
          (le_trans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ qc))) (le_of_lt cN))
    · -- remainder `2`: `ℓ` even, impossible
      have r2 : ((rem (lpf N) (two * two) ≐ two) :: lt (rem (lpf N) (two * two)) (succ two) :: Γ) ⊢[PRAAx]
          rem (lpf N) (two * two) ≐ two := Prf.hyp0
      have el := (Prf.andE₁ dl).wk.wk.eqTrans (congrAdd (.eqRefl _) (r2.eqTrans two_one))
      exact even_absurd _ po.wk.wk (even_mul eN.wk.wk el)
  · -- remainder `3`: `ℓ` is the divisor
    exact q3_intro hp.wk (lpf_dvd' hN2).wk Prf.hyp0 (dvd_le' hp1 (lpf_dvd' hN2) (p_pos hN2)).wk

/-- Every `n ≡ 3 (mod 4)` has a prime divisor `≡ 3 (mod 4)`: the search succeeds. -/
theorem q3_all {n : PTm k} (h3 : Γ ⊢[PRAAx] rem n (two * two) ≐ succ two) : Γ ⊢[PRAAx] Q3 n ≐ one := by
  have h := strong_ind (Γ := Γ) vQ (fun N x hS => by
    rw [inst2_vQ]
    refine .orE (eqb_cases (rem N (two * two)) (succ two)) ?_ ?_
    · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    · have q := q3_step hS.wk (eq_of_eqb Prf.hyp0)
      exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) q).eqTrans (monus_self one))).eqTrans (mul_zero _)) n zero
  rw [inst2_vQ] at h
  exact bit_of_viol h3 h

/-! ### The selected prime -/

/-- `4 N! − 1`. -/
abbrev T3 (N : PTm k) : PTm k := monus ((two * two) * fact N) one

/-- The selected prime of the class `3`. -/
abbrev P3 (N : PTm k) : PTm k := q3 (T3 N)

/-- `P3 N` is a prime `> N`, `≡ 3 (mod 4)`, and at most `4 N! − 1`. -/
theorem prime_three_mod_four (N : PTm k) :
    Γ ⊢[PRAAx] prime (P3 N) ⋏ (lt N (P3 N) ⋏ ((rem (P3 N) (two * two) ≐ succ two) ⋏ le (P3 N) (T3 N))) := by
  have fp := natEq (fact_pos (Γ := Γ) N)
  have h1 : Γ ⊢[PRAAx] le one ((two * two) * fact N) := by
    ipra_le 4 * 𝔞 (pred (fact N)) + 3 with 4 * fp
  have eT := eq_add_of_le h1
  have e3 : Γ ⊢[PRAAx] T3 N ≐ (two * two) * pred (fact N) + succ two := by
    ipra_lc 4 * fp - natEq eT
  have l3 : Γ ⊢[PRAAx] lt (succ two : PTm k) (two * two) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  have r3 := Prf.andE₂ (dmu four_pos e3 l3)
  have qc := q3_elim (q3_all r3)
  have hd := Prf.andE₁ qc
  have e' : Γ ⊢[PRAAx] T3 N + one ≐ fact N * (two * two) := by
    ipra_lc -natEq eT
  exact .andI hd (.andI (gt_of_dvd' (prime_two hd) (Prf.andE₁ (Prf.andE₂ qc)) e')
    (.andI (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ qc))) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ qc)))))

end LeanProofs.IPRA.AnalyticNumberTheory.PrimesModFour
