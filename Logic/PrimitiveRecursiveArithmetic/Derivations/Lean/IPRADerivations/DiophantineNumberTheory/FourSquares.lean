import IPRADerivations.DiophantineNumberTheory.FourSquaresDescent
import IPRADerivations.DiophantineNumberTheory.FourSquaresSeed
import IPRADerivations.DiophantineNumberTheory.FermatTwoSquares

/-!
# Lagrange's four-square theorem with primitive recursive witnesses

Packet: `diophantine-number-theory/lagrange_four_squares_ipra_2026-11-22`, `thm:main` ("Witnessed four-square
theorem in iPRA"): there are four explicit terms `W_i(n)` with

    ∀ n. W₀(n)² + W₁(n)² + W₂(n)² + W₃(n)² = n,        W_i(n) ≤ n.

The witnesses are the base-`(n + 1)` digits of the least code `c < (n + 1)⁴` whose digits have squares
summing to `n` (a bounded search); the theorem is that the search succeeds for every `n`.

* `code4`, `D0`–`D3`, `digs`, `code_lt`: four digits and their code;
* `rB`, `R n`: the body and the bit of the search; `rep_intro` (any representation makes the bit `1`),
  `rep_elim` (bit `1` gives `N(W(n)) = n`);
* `rep_mul_eq`: representable numbers are closed under products (`FourSquaresAlgebra.euler4`);
* `rep_odd_prime`, `rep_prime`: every prime is representable. For an odd prime `p` the seed
  (`FourSquaresSeed.seed`) gives a multiplier `1 ≤ m₀ < p` with `m₀ p` representable; let `m*` be the least
  `m ≥ 1` below `p` with `m p` representable (a bounded search, `ms`). If `m* ≥ 2`, one step of the descent
  (`FourSquaresDescent.descent`) gives a smaller one, against leastness (`BoundedReflection.ex_least`). So
  `m* = 1`. The paper iterates the descent with fuel; the least-multiplier form needs no iteration;
* `step`, `rep_all`: every `n` is representable, by strong induction (`Foundations/StrongInduction`) through
  the least prime factor: `n = ℓ(n) · c` with `c < n`;
* `four_squares`, `W_le`, and the closed sentence **`lagrange`**.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FourSquares

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos lpf_prime' lpf_dvd')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two congrEqb')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresDescent (Af sf Uf mq descent)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresSeed (sa sb seed)
open LeanProofs.IPRA.Foundations.BoundedReflection (wit one_ne_zero signum_guard_nonzero least_positive_witness)
open LeanProofs.IPRA.Signum (sg)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Four digits -/

abbrev D0 (c B : PTm k) : PTm k := rem c B
abbrev D1 (c B : PTm k) : PTm k := rem (quo c B) B
abbrev D2 (c B : PTm k) : PTm k := rem (quo (quo c B) B) B
abbrev D3 (c B : PTm k) : PTm k := quo (quo (quo c B) B) B

/-- The code of the digits `a, b, c, d` in base `B`. -/
abbrev code4 (B a b c d : PTm k) : PTm k := B * (B * (B * d + c) + b) + a

theorem digs {B a b c d : PTm k} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (ha : Γ ⊢[PRAAx] lt a B)
    (hb : Γ ⊢[PRAAx] lt b B) (hc : Γ ⊢[PRAAx] lt c B) :
    Γ ⊢[PRAAx] (D0 (code4 B a b c d) B ≐ a) ⋏ ((D1 (code4 B a b c d) B ≐ b) ⋏
      ((D2 (code4 B a b c d) B ≐ c) ⋏ (D3 (code4 B a b c d) B ≐ d))) := by
  have s1 := dmu hB (.eqRefl (code4 B a b c d)) ha
  have s2 := dmu hB (.eqRefl (B * (B * d + c) + b)) hb
  have s3 := dmu hB (.eqRefl (B * d + c)) hc
  have qq := (congrAp2 quoF (Prf.andE₁ s1) (.eqRefl B)).eqTrans (Prf.andE₁ s2)
  exact .andI (Prf.andE₂ s1) (.andI ((congrAp2 remF (Prf.andE₁ s1) (.eqRefl B)).eqTrans (Prf.andE₂ s2))
    (.andI ((congrAp2 remF qq (.eqRefl B)).eqTrans (Prf.andE₂ s3))
      ((congrAp2 quoF qq (.eqRefl B)).eqTrans (Prf.andE₁ s3))))

theorem code_lt {B a b c d : PTm k} (ha : Γ ⊢[PRAAx] lt a B) (hb : Γ ⊢[PRAAx] lt b B)
    (hc : Γ ⊢[PRAAx] lt c B) (hd : Γ ⊢[PRAAx] lt d B) :
    Γ ⊢[PRAAx] lt (code4 B a b c d) ((B * B) * (B * B)) := by
  ipra_le 𝔞 B * 𝔞 B * 𝔞 B * sl hd + 𝔞 B * 𝔞 B * sl hc + 𝔞 B * sl hb + sl ha

/-! ## The search -/

/-- `[N(digits of c in base n + 1) = n]`, over `0 = c`, `1 = n`. -/
abbrev rB : PTm 2 :=
  eqb (N4 (D0 (var 0) (succ (var 1))) (D1 (var 0) (succ (var 1))) (D2 (var 0) (succ (var 1)))
    (D3 (var 0) (succ (var 1)))) (var 1)

theorem inst2_rB (c n : PTm k) : inst2 rB c n =
    eqb (N4 (D0 c (succ n)) (D1 c (succ n)) (D2 c (succ n)) (D3 c (succ n))) n := by simp [inst2]

/-- The bound `(n + 1)⁴` of the search. -/
abbrev bd (n : PTm k) : PTm k := (succ n * succ n) * (succ n * succ n)

/-- The bit of "`n` is a sum of four squares of numbers `≤ n`". -/
abbrev R (n : PTm k) : PTm k := exB rB (bd n) n

/-- The four witnesses. -/
abbrev Wf (n : PTm k) : Fin 4 → PTm k :=
  ![D0 (wit rB (bd n) n) (succ n), D1 (wit rB (bd n) n) (succ n), D2 (wit rB (bd n) n) (succ n),
    D3 (wit rB (bd n) n) (succ n)]

theorem lt_succ_of_le {a n : PTm k} (h : Γ ⊢[PRAAx] le a n) : Γ ⊢[PRAAx] lt a (succ n) :=
  (succ_monus_succ _ _).eqTrans h

/-- Any representation makes the bit `1`. -/
theorem rep_intro {n a b c d : PTm k} (e : Γ ⊢[PRAAx] N4 a b c d ≐ n) : Γ ⊢[PRAAx] R n ≐ one := by
  have hB : Γ ⊢[PRAAx] succ n ≐ succ (pred (succ n)) := congrSucc (pred_succ _).eqSymm
  have la := lt_succ_of_le (le_N4_1 e); have lb := lt_succ_of_le (le_N4_2 e)
  have lc := lt_succ_of_le (le_N4_3 e); have ld := lt_succ_of_le (le_N4_4 e)
  have dg := digs (d := d) hB la lb lc
  have d0 := Prf.andE₁ dg; have d1 := Prf.andE₁ (Prf.andE₂ dg)
  have d2 := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ dg)); have d3 := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ dg))
  have val : Γ ⊢[PRAAx] inst2 rB (code4 (succ n) a b c d) n ≐ one := by
    rw [inst2_rB]
    exact (congrEqb' (congrAdd (congrAdd (congrMul d0 d0) (congrMul d1 d1))
      (congrAdd (congrMul d2 d2) (congrMul d3 d3))) (.eqRefl n)).eqTrans (eqb_of_eq e)
  exact ex_intro rB (.impI (one_ne_zero _ (val.wk.eqSymm.eqTrans Prf.hyp0))) (code_lt la lb lc ld)

/-- The bit `1` gives the witnesses. -/
theorem rep_elim {n : PTm k} (h : Γ ⊢[PRAAx] R n ≐ one) :
    Γ ⊢[PRAAx] N4 (Wf n 0) (Wf n 1) (Wf n 2) (Wf n 3) ≐ n := by
  have ne := Prf.andE₂ (ex_elim rB h)
  rw [inst2_rB] at ne
  refine .orE (eqb_cases (N4 (D0 (wit rB (bd n) n) (succ n)) (D1 (wit rB (bd n) n) (succ n))
    (D2 (wit rB (bd n) n) (succ n)) (D3 (wit rB (bd n) n) (succ n))) n) ?_ ?_
  · exact .botE _ (.impE ne.wk Prf.hyp0)
  · exact eq_of_eqb Prf.hyp0

/-- The witnesses are at most `n`. -/
theorem W_le {n : PTm k} (h : Γ ⊢[PRAAx] R n ≐ one) (i : Fin 4) : Γ ⊢[PRAAx] le (Wf n i) n := by
  have e := rep_elim h
  fin_cases i
  · exact le_N4_1 e
  · exact le_N4_2 e
  · exact le_N4_3 e
  · exact le_N4_4 e

/-- Representable numbers are closed under products. -/
theorem rep_mul_eq {a b n : PTm k} (ha : Γ ⊢[PRAAx] R a ≐ one) (hb : Γ ⊢[PRAAx] R b ≐ one)
    (e : Γ ⊢[PRAAx] n ≐ a * b) : Γ ⊢[PRAAx] R n ≐ one :=
  rep_intro ((euler4 (Wf a 0) (Wf a 1) (Wf a 2) (Wf a 3) (Wf b 0) (Wf b 1) (Wf b 2) (Wf b 3)).eqTrans
    ((congrMul (rep_elim ha) (rep_elim hb)).eqTrans e.eqSymm))

/-! ## Primes -/

/-- `[i ≥ 1][i p is representable]`, over `0 = i`, `1 = p`. -/
abbrev lB : PTm 2 := sg (var 0) * R (var 0 * var 1)

theorem inst2_lB (i p : PTm k) : inst2 lB i p = sg i * R (i * p) := by simp [inst2]

/-- The least multiplier `m ≥ 1` below `p` with `m p` representable. -/
abbrev ms (p : PTm k) : PTm k := wit lB p p

theorem l_one {i p : PTm k} (hi : Γ ⊢[PRAAx] le one i) (hr : Γ ⊢[PRAAx] R (i * p) ≐ one) :
    Γ ⊢[PRAAx] neg (inst2 lB i p ≐ zero) :=
  signum_guard_nonzero (inst2_lB i p) hi hr

theorem seed_alg {a b p m0 : PTm k} (es : Γ ⊢[PRAAx] a * a + (b * b + one) ≐ p * m0 + zero) :
    Γ ⊢[PRAAx] N4 a b one zero ≐ m0 * p := by
  ipra_lc natEq es

/-- Every odd prime is a sum of four squares. -/
theorem rep_odd_prime {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (ep : Γ ⊢[PRAAx] p ≐ two * half p + one) :
    Γ ⊢[PRAAx] R p ≐ one := by
  have hp2 := prime_two hp
  have hp1 := p_pos hp2
  have sd := seed hp ep
  have ha := Prf.andE₁ (Prf.andE₂ sd); have hb := Prf.andE₂ (Prf.andE₂ sd)
  have es : Γ ⊢[PRAAx] sa p * sa p + (sb p * sb p + one) ≐
      p * quo (sa p * sa p + (sb p * sb p + one)) p + zero :=
    (Prf.andE₁ (dm hp1 _)).eqTrans (congrAdd (.eqRefl _) (Prf.andE₁ sd))
  have m0pos : Γ ⊢[PRAAx] le one (quo (sa p * sa p + (sb p * sb p + one)) p) := by
    refine .orE (zero_or_succ (quo (sa p * sa p + (sb p * sb p + one)) p)) ?_ (one_le_pos Prf.hyp0)
    have esn' := natEq (es.wk (ψ := quo (sa p * sa p + (sb p * sb p + one)) p ≐ zero))
    refine succ_ne_zero' (a := sa p * sa p + sb p * sb p) _ ?_
    ipra_lc esn' + 𝔞 p * natEq (Prf.hyp0 (φ := quo (sa p * sa p + (sb p * sb p + one)) p ≐ zero))
  have m0lt : Γ ⊢[PRAAx] lt (quo (sa p * sa p + (sb p * sb p + one)) p) p := by
    refine .orE (lt_or_le (quo (sa p * sa p + (sb p * sb p + one)) p) p) Prf.hyp0 ?_
    have hle : (le p (quo (sa p * sa p + (sb p * sb p + one)) p) :: Γ) ⊢[PRAAx]
        le p (quo (sa p * sa p + (sb p * sb p + one)) p) := Prf.hyp0
    have ha' := ha.wk (ψ := le p (quo (sa p * sa p + (sb p * sb p + one)) p))
    have hb' := hb.wk (ψ := le p (quo (sa p * sa p + (sb p * sb p + one)) p))
    have hp2' := hp2.wk (ψ := le p (quo (sa p * sa p + (sb p * sb p + one)) p))
    have esn' := natEq (es.wk (ψ := le p (quo (sa p * sa p + (sb p * sb p + one)) p)))
    have epn' := natEq (ep.wk (ψ := le p (quo (sa p * sa p + (sb p * sb p + one)) p)))
    have bad : (le p (quo (sa p * sa p + (sb p * sb p + one)) p) :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le sl ha' * (𝔞 (half p) + 𝔞 (sa p)) + sl hb' * (𝔞 (half p) + 𝔞 (sb p)) +
        2 * 𝔞 (half p) * 𝔞 (half p) + 2 * 𝔞 (half p) + sl hp2' + 𝔞 p * sl hle with
        esn' + (𝔞 p + 2 * 𝔞 (half p)) * epn'
    exact lt_zero_absurd _ bad
  have r0 := rep_intro (seed_alg es)
  have least := least_positive_witness lB (fun i => R (i * p)) (N := p) (x := p) (fun i => inst2_lB i p)
    (ex_cases rB (bd (ms p * p)) (ms p * p)) m0pos m0lt r0 (fun hlt hpass =>
      let d := descent (x := Wf (ms p * p)) hp.wk Prf.hyp0 hlt (rep_elim hpass)
      .andI (rep_intro d.andE₁) d.andE₂)
  exact rep_intro ((rep_elim least.andE₂).eqTrans ((congrMul least.andE₁ (.eqRefl p)).eqTrans (one_mul p)))

/-- Every prime is a sum of four squares. -/
theorem rep_prime {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] R p ≐ one := by
  refine .orE (eqb_cases p two) ?_ ?_
  · have e0 : ((eqb p two ≐ zero) :: Γ) ⊢[PRAAx] eqb p two ≐ zero := Prf.hyp0
    have hne : ((eqb p two ≐ zero) :: Γ) ⊢[PRAAx] neg (p ≐ two) :=
      .impI (one_ne_zero _ ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans e0.wk))
    have po := odd_of_prime_ne_two hp.wk hne
    exact rep_odd_prime hp.wk ((half_par p).eqTrans (congrAdd (.eqRefl _) po))
  · have e2 := natEq (eq_of_eqb (Prf.hyp0 (Γ := Γ) (φ := eqb p two ≐ one)))
    exact rep_intro (a := one) (b := one) (c := zero) (d := zero)
      (by ipra_lc -e2)

/-! ## Every number -/

/-- The violation `1 ∸ R(n)`, over `0 = n`. -/
abbrev vR : PTm 2 := monus one (R (var 0))

theorem inst2_vR (N x : PTm k) : inst2 vR N x = monus one (R N) := by simp [inst2]

theorem bit_of_viol {n : PTm k} (h : Γ ⊢[PRAAx] monus one (R n) ≐ zero) : Γ ⊢[PRAAx] R n ≐ one := by
  refine .orE (ex_cases rB (bd n) n) ?_ Prf.hyp0
  exact one_ne_zero _ (((congrMonus (.eqRefl (one : PTm k)) Prf.hyp0).eqTrans (monus_zero one)).eqSymm.eqTrans
    h.wk)

/-- The cofactor of a divisor of a number `≥ 2` is positive. -/
theorem cofactor_pos {N L c : PTm k} (hN2 : Γ ⊢[PRAAx] le two N) (eN : Γ ⊢[PRAAx] N ≐ L * c + zero) :
    Γ ⊢[PRAAx] le one c := by
  refine .orE (zero_or_succ c) ?_ (one_le_pos Prf.hyp0)
  have c0 := natEq (Prf.hyp0 (Γ := Γ) (φ := c ≐ zero))
  have eNn := natEq (eN.wk (ψ := c ≐ zero))
  have hN2' := hN2.wk (ψ := c ≐ zero)
  have bad : ((c ≐ zero) :: Γ) ⊢[PRAAx] le two zero := by
    ipra_le sl hN2' with eNn + 𝔞 L * c0
  exact lt_zero_absurd _ bad

theorem step {N x : PTm k} (hS : Γ ⊢[PRAAx] ap2 (sumF vR) N x ≐ zero) : Γ ⊢[PRAAx] R N ≐ one := by
  refine .orE (lt_or_le N two) ?_ ?_
  · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := Γ) (φ := lt N two))) ?_ ?_
    · refine .orE (lt_succ_cases (Prf.hyp0 (Γ := lt N two :: Γ) (φ := lt N one))) (lt_zero_absurd _ Prf.hyp0) ?_
      have nz := natEq (Prf.hyp0 (Γ := lt N one :: lt N two :: Γ) (φ := N ≐ zero))
      exact rep_intro (a := zero) (b := zero) (c := zero) (d := zero)
        (by ipra_lc -nz)
    · have n1 := natEq (Prf.hyp0 (Γ := lt N two :: Γ) (φ := N ≐ one))
      exact rep_intro (a := one) (b := zero) (c := zero) (d := zero)
        (by ipra_lc -n1)
  · have hN2 : (le two N :: Γ) ⊢[PRAAx] le two N := Prf.hyp0
    have hp := lpf_prime' hN2
    have hp2 := prime_two hp
    have hp1 := p_pos hp2
    have eN : (le two N :: Γ) ⊢[PRAAx] N ≐ lpf N * quo N (lpf N) + zero :=
      (Prf.andE₁ (dm hp1 N)).eqTrans (congrAdd (.eqRefl _) (lpf_dvd' hN2))
    have eNn := natEq eN
    have c1 : (le two N :: Γ) ⊢[PRAAx] le one (quo N (lpf N)) := cofactor_pos hN2 eN
    have cN : (le two N :: Γ) ⊢[PRAAx] lt (quo N (lpf N)) N := by
      ipra_le sl hp2 * 𝔞 (quo N (lpf N)) + sl c1 with eNn
    have vc := sum_zero_elim vR hS.wk cN
    rw [inst2_vR] at vc
    have e' : (le two N :: Γ) ⊢[PRAAx] N ≐ lpf N * quo N (lpf N) := eN.eqTrans (add_zero _)
    exact rep_mul_eq (rep_prime hp) (bit_of_viol vc) e'

/-- Every number is a sum of four squares: the search succeeds. -/
theorem rep_all (n : PTm k) : Γ ⊢[PRAAx] R n ≐ one := by
  have h := strong_ind (Γ := Γ) vR (fun N x hS => by
    rw [inst2_vR]
    exact (congrMonus (.eqRefl _) (step hS)).eqTrans (monus_self one)) n zero
  rw [inst2_vR] at h
  exact bit_of_viol h

/-- `thm:main`: `W₀(n)² + W₁(n)² + W₂(n)² + W₃(n)² = n`. -/
theorem four_squares (n : PTm k) : Γ ⊢[PRAAx] N4 (Wf n 0) (Wf n 1) (Wf n 2) (Wf n 3) ≐ n :=
  rep_elim (rep_all n)

/-- `W_i(n) ≤ n`. -/
theorem witness_le (n : PTm k) (i : Fin 4) : Γ ⊢[PRAAx] le (Wf n i) n := W_le (rep_all n) i

/-- `∀ n. W₀(n)² + W₁(n)² + W₂(n)² + W₃(n)² = n`. -/
abbrev sentence : Fm PTm 0 :=
  univ 1 (N4 (Wf (var 0) 0) (Wf (var 0) 1) (Wf (var 0) 2) (Wf (var 0) 3) ≐ var 0)

/-- **Lagrange's four-square theorem** as a closed sentence of iPRA, with explicit witness terms. -/
theorem lagrange : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence := closeUniv 1 (four_squares (var 0))

end LeanProofs.IPRA.DiophantineNumberTheory.FourSquares
