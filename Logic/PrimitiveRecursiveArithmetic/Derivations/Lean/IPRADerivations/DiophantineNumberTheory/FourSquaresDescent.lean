import IPRADerivations.DiophantineNumberTheory.FourSquaresAlgebra
import IPRADerivations.AnalyticNumberTheory.Mobius

/-!
# Four squares: one step of the descent

Packet: `diophantine-number-theory/lagrange_four_squares_ipra_2026-11-22`, `sections/03_descent.tex`
("One-step descent"): from `m p = x₁² + x₂² + x₃² + x₄²` with a prime `p` and `2 ≤ m < p` to
`m' p = w₁² + w₂² + w₃² + w₄²` with `1 ≤ m' < m`, the new tuple and the new multiplier being explicit terms.

For each coordinate, `r = x mod m`, and the signed residue of least absolute value is `y = a (1 − 2s)` with
`s = [r > ⌊m/2⌋]` (`sgn`), `a = r` or `m − r` (`av`), and `x + 2 s a = a + m U` with `U = ⌊x/m⌋ + s` (`uv`):

* `res_eq`, `sgn_idem`, `av_le` (`a ≤ ⌊m/2⌋`), `av_tie` (for even `m`, `a = m/2` forces `r = m/2`);
* `presum`, `dvd_of_add_mul`: `m ∣ N(a)`; the new multiplier is `m' = N(a)/m` (`mq`);
* `mq_pos`: `m' ≥ 1`, since `N(a) = 0` gives `m ∣ x_i` and then `m ∣ p`;
* `mq_lt`: `m' < m`. Here `N(a) ≤ 4 ⌊m/2⌋² ≤ m²`, and `m' ≥ m` forces `m` even and every `a_i = m/2`, so every
  `x_i ≡ m/2 (mod m)`, `N(x) = m² K` and again `m ∣ p` (`tie_norm`). The paper halves the tuple when `m` is
  even instead; the residue step is used here for every `m`, with this tie excluded;
* `descent`: the statement, with the tuple of `FourSquaresAlgebra.descent_alg`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresDescent

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lpf_of_prime)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra
open LeanProofs.IPRA.Signum (sg)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The signed residue of least absolute value -/

/-- `s = [x mod m > ⌊m/2⌋]`. -/
abbrev sgn (x m : PTm k) : PTm k := sg (monus (rem x m) (half m))

/-- `a = |y|`: `x mod m` or `m − x mod m`. -/
abbrev av (x m : PTm k) : PTm k := monus one (sgn x m) * rem x m + sgn x m * monus m (rem x m)

/-- `U = ⌊x/m⌋ + s`. -/
abbrev uv (x m : PTm k) : PTm k := quo x m + sgn x m

theorem av0 {S M1 r mr : PTm k} (s0 : Γ ⊢[PRAAx] S ≐ zero) (m1 : Γ ⊢[PRAAx] M1 ≐ one) :
    Γ ⊢[PRAAx] M1 * r + S * mr ≐ r := by
  ipra_lc 𝔞 r * natEq m1 + 𝔞 mr * natEq s0

theorem av1 {S M1 r mr : PTm k} (s1 : Γ ⊢[PRAAx] S ≐ one) (m0 : Γ ⊢[PRAAx] M1 ≐ zero) :
    Γ ⊢[PRAAx] M1 * r + S * mr ≐ mr := by
  ipra_lc 𝔞 r * natEq m0 + 𝔞 mr * natEq s1

theorem res_low {x m : PTm k} (h : Γ ⊢[PRAAx] le (rem x m) (half m)) :
    Γ ⊢[PRAAx] (sgn x m ≐ zero) ⋏ (av x m ≐ rem x m) := by
  have s0 : Γ ⊢[PRAAx] sgn x m ≐ zero := sg_le h
  exact .andI s0 (av0 s0 ((congrMonus (.eqRefl (one : PTm k)) s0).eqTrans (monus_zero one)))

theorem res_high {x m : PTm k} (h : Γ ⊢[PRAAx] lt (half m) (rem x m)) :
    Γ ⊢[PRAAx] (sgn x m ≐ one) ⋏ (av x m ≐ monus m (rem x m)) := by
  have s1 : Γ ⊢[PRAAx] sgn x m ≐ one := sg_lt h
  exact .andI s1 (av1 s1 ((congrMonus (.eqRefl (one : PTm k)) s1).eqTrans (monus_self one)))

theorem r1_low {x m q r S a : PTm k} (dx : Γ ⊢[PRAAx] x ≐ m * q + r) (s0 : Γ ⊢[PRAAx] S ≐ zero)
    (ea : Γ ⊢[PRAAx] a ≐ r) : Γ ⊢[PRAAx] x + two * (S * a) ≐ a + m * (q + S) := by
  ipra_lc natEq dx - natEq ea + (2 * 𝔞 a - 𝔞 m) * natEq s0

theorem r1_high {x m q r S a mr : PTm k} (dx : Γ ⊢[PRAAx] x ≐ m * q + r) (s1 : Γ ⊢[PRAAx] S ≐ one)
    (ea : Γ ⊢[PRAAx] a ≐ mr) (em : Γ ⊢[PRAAx] m ≐ r + mr) :
    Γ ⊢[PRAAx] x + two * (S * a) ≐ a + m * (q + S) := by
  ipra_lc natEq dx + natEq ea - natEq em + (2 * 𝔞 a - 𝔞 m) * natEq s1

/-- `x + 2 s a = a + m U`. -/
theorem res_eq {m : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (x : PTm k) :
    Γ ⊢[PRAAx] x + two * (sgn x m * av x m) ≐ av x m + m * uv x m := by
  have d := dm hm x
  refine .orE (lt_or_le (half m) (rem x m)) ?_ ?_
  · have hh := res_high (Γ := lt (half m) (rem x m) :: Γ) (x := x) (m := m) Prf.hyp0
    exact r1_high (Prf.andE₁ d).wk (Prf.andE₁ hh) (Prf.andE₂ hh) (eq_add_of_le (le_of_lt (Prf.andE₂ d))).wk
  · have hl := res_low (Γ := le (rem x m) (half m) :: Γ) (x := x) (m := m) Prf.hyp0
    exact r1_low (Prf.andE₁ d).wk (Prf.andE₁ hl) (Prf.andE₂ hl)

theorem idem0 {S : PTm k} (s0 : Γ ⊢[PRAAx] S ≐ zero) : Γ ⊢[PRAAx] S * S ≐ S := by
  ipra_lc (𝔞 S - 1) * natEq s0

theorem idem1 {S : PTm k} (s1 : Γ ⊢[PRAAx] S ≐ one) : Γ ⊢[PRAAx] S * S ≐ S := by
  ipra_lc 𝔞 S * natEq s1

/-- `s² = s`. -/
theorem sgn_idem (x m : PTm k) : Γ ⊢[PRAAx] sgn x m * sgn x m ≐ sgn x m := by
  refine .orE (lt_or_le (half m) (rem x m)) ?_ ?_
  · exact idem1 (Prf.andE₁ (res_high (x := x) (m := m) Prf.hyp0))
  · exact idem0 (Prf.andE₁ (res_low (x := x) (m := m) Prf.hyp0))

theorem par_le_one (m : PTm k) : Γ ⊢[PRAAx] le (par m) one := by
  refine .orE (par_cases m) ?_ ?_
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (zero_le one)
  · exact le_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl one)

/-- `a ≤ ⌊m/2⌋`. -/
theorem av_le {m : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (x : PTm k) :
    Γ ⊢[PRAAx] le (av x m) (half m) := by
  have d := dm hm x
  refine .orE (lt_or_le (half m) (rem x m)) ?_ ?_
  · have hlt : (lt (half m) (rem x m) :: Γ) ⊢[PRAAx] lt (half m) (rem x m) := Prf.hyp0
    have hh := res_high hlt
    have hpar := par_le_one (Γ := lt (half m) (rem x m) :: Γ) m
    have em := natEq ((eq_add_of_le (le_of_lt (Prf.andE₂ d))).wk (ψ := lt (half m) (rem x m)))
    have hpm := natEq (half_par (Γ := lt (half m) (rem x m) :: Γ) m)
    have b : (lt (half m) (rem x m) :: Γ) ⊢[PRAAx] le (monus m (rem x m)) (half m) := by
      ipra_le sl hlt + sl hpar with em - hpm
    exact le_congr (Prf.andE₂ hh).eqSymm (.eqRefl _) b
  · have hl := res_low (Γ := le (rem x m) (half m) :: Γ) (x := x) (m := m) Prf.hyp0
    exact le_congr (Prf.andE₂ hl).eqSymm (.eqRefl _) Prf.hyp0

/-- For even `m`: `a = m/2` forces `x mod m = m/2`. -/
theorem av_tie {m : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (x : PTm k)
    (pz : Γ ⊢[PRAAx] par m ≐ zero) (ha : Γ ⊢[PRAAx] av x m ≐ half m) :
    Γ ⊢[PRAAx] rem x m ≐ half m := by
  have d := dm hm x
  refine .orE (lt_or_le (half m) (rem x m)) ?_ ?_
  · have hlt : (lt (half m) (rem x m) :: Γ) ⊢[PRAAx] lt (half m) (rem x m) := Prf.hyp0
    have hh := res_high hlt
    have emr := natEq ((Prf.andE₂ hh).eqSymm.eqTrans ha.wk)
    have em := natEq ((eq_add_of_le (le_of_lt (Prf.andE₂ d))).wk (ψ := lt (half m) (rem x m)))
    have hpm := natEq (half_par (Γ := lt (half m) (rem x m) :: Γ) m)
    have pzn := natEq (pz.wk (ψ := lt (half m) (rem x m)))
    have bad : (lt (half m) (rem x m) :: Γ) ⊢[PRAAx] le one zero := by
      ipra_le sl hlt with emr - pzn - hpm + em
    exact lt_zero_absurd _ bad
  · have hl := res_low (Γ := le (rem x m) (half m) :: Γ) (x := x) (m := m) Prf.hyp0
    exact (Prf.andE₂ hl).eqSymm.eqTrans ha.wk

/-! ## Divisibility helpers -/

theorem dvd_of_eq_mul {m p K : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (e : Γ ⊢[PRAAx] p ≐ m * K) :
    Γ ⊢[PRAAx] dvd m p :=
  (congrAp2 remF (e.eqTrans (add_zero _).eqSymm) (.eqRefl _)).eqTrans
    ((rem_add_mul hm K zero).eqTrans (rem_zero m))

theorem dvd_of_add_mul {m A P Q : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (h : Γ ⊢[PRAAx] A + m * P ≐ m * Q) : Γ ⊢[PRAAx] dvd m A := by
  have e : Γ ⊢[PRAAx] m * P + A ≐ m * Q + zero := by ipra_lc natEq h
  exact (rem_add_mul hm P A).eqSymm.eqTrans
    ((congrAp2 remF e (.eqRefl _)).eqTrans ((rem_add_mul hm Q zero).eqTrans (rem_zero m)))

/-- A prime has no divisor `m` with `2 ≤ m < p`. -/
theorem no_dvd {p m : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hm2 : Γ ⊢[PRAAx] le two m)
    (hmp : Γ ⊢[PRAAx] lt m p) (h : Γ ⊢[PRAAx] dvd m p) : Γ ⊢[PRAAx] Fm.bot :=
  le_lt_absurd _ (le_congr (lpf_of_prime hp) (.eqRefl _) (lpf_min (p_pos (prime_two hp)) hm2 h)) hmp

/-! ## The polynomial identities of the step -/

section Step

variable (x A s U q : Fin 4 → PTm k) (m mp p h : PTm k)

/-- `N(a) + m (2⟨U, a⟩ + m N(U)) = m (p + 4 ∑ U_i s_i a_i)`. -/
theorem presum (he : ∀ i, Γ ⊢[PRAAx] resEq x A s U m i) (ht : ∀ i, Γ ⊢[PRAAx] s i * s i ≐ s i)
    (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] N4 (A 0) (A 1) (A 2) (A 3) + m * (two * dotUA A U + m * N4 (U 0) (U 1) (U 2) (U 3)) ≐
      m * (p + (two * two) * dotUSA A s U) := by
  ipra_lc natEq n1 - (𝔞 (x 0) + 𝔞 (A 0) * (1 - 2 * 𝔞 (s 0)) + 𝔞 m * 𝔞 (U 0)) * natEq (he 0) -
    (𝔞 (x 1) + 𝔞 (A 1) * (1 - 2 * 𝔞 (s 1)) + 𝔞 m * 𝔞 (U 1)) * natEq (he 1) -
    (𝔞 (x 2) + 𝔞 (A 2) * (1 - 2 * 𝔞 (s 2)) + 𝔞 m * 𝔞 (U 2)) * natEq (he 2) -
    (𝔞 (x 3) + 𝔞 (A 3) * (1 - 2 * 𝔞 (s 3)) + 𝔞 m * 𝔞 (U 3)) * natEq (he 3) -
    4 * (𝔞 (A 0) * 𝔞 (A 0) * natEq (ht 0) + 𝔞 (A 1) * 𝔞 (A 1) * natEq (ht 1) + 𝔞 (A 2) * 𝔞 (A 2) * natEq (ht 2) + 𝔞 (A 3) * 𝔞 (A 3) * natEq (ht 3))

/-- With every `a_i = 0`: `m p = m (m N(U))`. -/
theorem zero_norm (hx : ∀ i, Γ ⊢[PRAAx] x i ≐ m * U i)
    (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] m * p ≐ m * (m * N4 (U 0) (U 1) (U 2) (U 3)) := by
  ipra_lc -natEq n1 + (𝔞 (x 0) + 𝔞 m * 𝔞 (U 0)) * natEq (hx 0) + (𝔞 (x 1) + 𝔞 m * 𝔞 (U 1)) * natEq (hx 1) +
    (𝔞 (x 2) + 𝔞 m * 𝔞 (U 2)) * natEq (hx 2) + (𝔞 (x 3) + 𝔞 m * 𝔞 (U 3)) * natEq (hx 3)

/-- With every `x_i ≡ h (mod m)` and `m = 2h`: `m p = m (m K)`. -/
theorem tie_norm (hx : ∀ i, Γ ⊢[PRAAx] x i ≐ m * q i + h) (em : Γ ⊢[PRAAx] m ≐ two * h)
    (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] m * p ≐ m * (m * (N4 (q 0) (q 1) (q 2) (q 3) + (q 0 + q 1 + (q 2 + q 3)) + one)) := by
  ipra_lc -natEq n1 + (𝔞 (x 0) + 𝔞 m * 𝔞 (q 0) + 𝔞 h) * natEq (hx 0) +
    (𝔞 (x 1) + 𝔞 m * 𝔞 (q 1) + 𝔞 h) * natEq (hx 1) + (𝔞 (x 2) + 𝔞 m * 𝔞 (q 2) + 𝔞 h) * natEq (hx 2) +
    (𝔞 (x 3) + 𝔞 m * 𝔞 (q 3) + 𝔞 h) * natEq (hx 3) -
    (𝔞 m * (𝔞 (q 0) + 𝔞 (q 1) + (𝔞 (q 2) + 𝔞 (q 3))) + 2 * 𝔞 h + 𝔞 m) * natEq em

end Step

theorem x_of_zero {x S a m U : PTm k} (e : Γ ⊢[PRAAx] x + two * (S * a) ≐ a + m * U)
    (a0 : Γ ⊢[PRAAx] a ≐ zero) : Γ ⊢[PRAAx] x ≐ m * U := by
  ipra_lc natEq e - (2 * 𝔞 S - 1) * natEq a0

theorem zero_of_le_zero {a : PTm k} (h : Γ ⊢[PRAAx] le a zero) : Γ ⊢[PRAAx] a ≐ zero :=
  (monus_zero a).eqSymm.eqTrans h

/-! ## The tie -/

/-- `N = m m'` with `m ≤ m'`, `m = 2h + 1` and all entries `≤ h` is impossible. -/
theorem tie_odd {a b c d h m mq : PTm k} (ha : Γ ⊢[PRAAx] le a h) (hb : Γ ⊢[PRAAx] le b h)
    (hc : Γ ⊢[PRAAx] le c h) (hd : Γ ⊢[PRAAx] le d h) (hle : Γ ⊢[PRAAx] le m mq)
    (n2 : Γ ⊢[PRAAx] N4 a b c d ≐ m * mq) (em : Γ ⊢[PRAAx] m ≐ two * h + one) : Γ ⊢[PRAAx] Fm.bot := by
  have e := natEq n2; have f := natEq em
  have bad : Γ ⊢[PRAAx] le one zero := by
    ipra_le sl ha * (𝔞 h + 𝔞 a) + sl hb * (𝔞 h + 𝔞 b) + sl hc * (𝔞 h + 𝔞 c) + sl hd * (𝔞 h + 𝔞 d) +
      𝔞 m * sl hle + 4 * 𝔞 h with e + (𝔞 m + 2 * 𝔞 h + 1) * f
  exact lt_zero_absurd _ bad

/-- `a² + R = m m'` with `m ≤ m'`, `m = 2h`, `h ≥ 1`, `a < h` and `R ≤ 3h²` is impossible. -/
theorem tie_one {a b c d h m mq : PTm k} (ha : Γ ⊢[PRAAx] lt a h) (hb : Γ ⊢[PRAAx] le b h)
    (hc : Γ ⊢[PRAAx] le c h) (hd : Γ ⊢[PRAAx] le d h) (h1 : Γ ⊢[PRAAx] le one h)
    (hle : Γ ⊢[PRAAx] le m mq) (n2 : Γ ⊢[PRAAx] a * a + (b * b + (c * c + d * d)) ≐ m * mq)
    (em : Γ ⊢[PRAAx] m ≐ two * h) : Γ ⊢[PRAAx] Fm.bot := by
  have e := natEq n2; have f := natEq em
  have bad : Γ ⊢[PRAAx] le one zero := by
    ipra_le sl ha * (𝔞 h + 𝔞 a) + sl hb * (𝔞 h + 𝔞 b) + sl hc * (𝔞 h + 𝔞 c) + sl hd * (𝔞 h + 𝔞 d) +
      sl h1 + 𝔞 a + 𝔞 m * sl hle with e + (𝔞 m + 2 * 𝔞 h) * f
  exact lt_zero_absurd _ bad

/-! ## The step -/

section Descent

variable (x : Fin 4 → PTm k) (m : PTm k)

/-- The absolute residues, the signs and the quotients of the four coordinates. -/
abbrev Af : Fin 4 → PTm k := fun i => av (x i) m
abbrev sf : Fin 4 → PTm k := fun i => sgn (x i) m
abbrev Uf : Fin 4 → PTm k := fun i => uv (x i) m

/-- The new multiplier `m' = N(a)/m`. -/
abbrev mq : PTm k := quo (N4 (Af x m 0) (Af x m 1) (Af x m 2) (Af x m 3)) m

variable {x m}

theorem norm_eq {p : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] N4 (Af x m 0) (Af x m 1) (Af x m 2) (Af x m 3) ≐ m * mq x m := by
  have hdv := dvd_of_add_mul hm (presum x (Af x m) (sf x m) (Uf x m) m p
    (fun i => res_eq hm (x i)) (fun i => sgn_idem (x i) m) n1)
  exact (Prf.andE₁ (dm hm _)).eqTrans ((congrAdd (.eqRefl _) hdv).eqTrans (add_zero _))

/-- `m' ≥ 1`. -/
theorem mq_pos {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hm2 : Γ ⊢[PRAAx] le two m)
    (hmp : Γ ⊢[PRAAx] lt m p) (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] le one (mq x m) := by
  have hm := p_pos hm2
  have n2 := norm_eq hm n1
  refine .orE (zero_or_succ (mq x m)) ?_ (one_le_pos Prf.hyp0)
  have z : ((mq x m ≐ zero) :: Γ) ⊢[PRAAx] N4 (Af x m 0) (Af x m 1) (Af x m 2) (Af x m 3) ≐ zero := by
    ipra_lc natEq (n2.wk (ψ := mq x m ≐ zero)) + 𝔞 m * natEq (Prf.hyp0 (φ := mq x m ≐ zero))
  have a0 : ∀ i : Fin 4, ((mq x m ≐ zero) :: Γ) ⊢[PRAAx] Af x m i ≐ zero := fun i => by
    fin_cases i
    · exact zero_of_le_zero (le_N4_1 z)
    · exact zero_of_le_zero (le_N4_2 z)
    · exact zero_of_le_zero (le_N4_3 z)
    · exact zero_of_le_zero (le_N4_4 z)
  have zn := zero_norm x (Uf x m) m p (fun i => x_of_zero (res_eq hm.wk (x i)) (a0 i)) n1.wk
  exact .botE _ (no_dvd hp.wk hm2.wk hmp.wk (dvd_of_eq_mul hm.wk (mul_cancel hm.wk zn)))

/-- `m' < m`. -/
theorem mq_lt {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hm2 : Γ ⊢[PRAAx] le two m)
    (hmp : Γ ⊢[PRAAx] lt m p) (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] lt (mq x m) m := by
  have hm := p_pos hm2
  refine .orE (lt_or_le (mq x m) m) Prf.hyp0 ?_
  refine .botE _ ?_
  have hle : (le m (mq x m) :: Γ) ⊢[PRAAx] le m (mq x m) := Prf.hyp0
  have hm' := hm.wk (ψ := le m (mq x m))
  have n2 := norm_eq hm' (n1.wk (ψ := le m (mq x m)))
  have hA : ∀ i : Fin 4, (le m (mq x m) :: Γ) ⊢[PRAAx] le (Af x m i) (half m) := fun i => av_le hm' (x i)
  refine .orE (par_cases m) ?_ ?_
  · -- `m` even
    have pz : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] par m ≐ zero := Prf.hyp0
    have em : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] m ≐ two * half m :=
      (half_par m).eqTrans ((congrAdd (.eqRefl _) pz).eqTrans (add_zero _))
    have h1 : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] le one (half m) := by
      refine .orE (lt_or_le (half m) one) ?_ Prf.hyp0
      have hlt : (lt (half m) one :: (par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] lt (half m) one := Prf.hyp0
      have hm2' : (lt (half m) one :: (par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] le two m := hm2.wk.wk.wk
      have emn' := natEq (em.wk (ψ := lt (half m) one))
      have bad : (lt (half m) one :: (par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] le two zero := by
        ipra_le sl hm2' + 2 * sl hlt with emn'
      exact lt_zero_absurd _ bad
    have n2' := n2.wk (ψ := par m ≐ zero)
    have hA' : ∀ i : Fin 4, ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] le (Af x m i) (half m) :=
      fun i => (hA i).wk
    have t0 : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] Af x m 0 ≐ half m := by
      refine .orE (lt_or_eq_of_le (hA' 0)) ?_ Prf.hyp0
      have n2n := natEq (n2'.wk (ψ := lt (Af x m 0) (half m)))
      exact .botE _ (tie_one Prf.hyp0 (hA' 1).wk (hA' 2).wk (hA' 3).wk h1.wk hle.wk.wk
        (by ipra_lc n2n) em.wk)
    have t1 : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] Af x m 1 ≐ half m := by
      refine .orE (lt_or_eq_of_le (hA' 1)) ?_ Prf.hyp0
      have n2n := natEq (n2'.wk (ψ := lt (Af x m 1) (half m)))
      exact .botE _ (tie_one Prf.hyp0 (hA' 0).wk (hA' 2).wk (hA' 3).wk h1.wk hle.wk.wk
        (by ipra_lc n2n) em.wk)
    have t2 : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] Af x m 2 ≐ half m := by
      refine .orE (lt_or_eq_of_le (hA' 2)) ?_ Prf.hyp0
      have n2n := natEq (n2'.wk (ψ := lt (Af x m 2) (half m)))
      exact .botE _ (tie_one Prf.hyp0 (hA' 0).wk (hA' 1).wk (hA' 3).wk h1.wk hle.wk.wk
        (by ipra_lc n2n) em.wk)
    have t3 : ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] Af x m 3 ≐ half m := by
      refine .orE (lt_or_eq_of_le (hA' 3)) ?_ Prf.hyp0
      have n2n := natEq (n2'.wk (ψ := lt (Af x m 3) (half m)))
      exact .botE _ (tie_one Prf.hyp0 (hA' 0).wk (hA' 1).wk (hA' 2).wk h1.wk hle.wk.wk
        (by ipra_lc n2n) em.wk)
    have tA : ∀ i : Fin 4, ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx] Af x m i ≐ half m := fun i => by
      fin_cases i
      exacts [t0, t1, t2, t3]
    have hm'' := hm'.wk (ψ := par m ≐ zero)
    have hx : ∀ i : Fin 4, ((par m ≐ zero) :: le m (mq x m) :: Γ) ⊢[PRAAx]
        x i ≐ m * quo (x i) m + half m := fun i =>
      (Prf.andE₁ (dm hm'' (x i))).eqTrans (congrAdd (.eqRefl _) (av_tie hm'' (x i) pz (tA i)))
    have tn := tie_norm x (fun i => quo (x i) m) m p (half m) hx em n1.wk.wk
    exact no_dvd hp.wk.wk hm2.wk.wk hmp.wk.wk (dvd_of_eq_mul hm'' (mul_cancel hm'' tn))
  · -- `m` odd
    have po : ((par m ≐ one) :: le m (mq x m) :: Γ) ⊢[PRAAx] par m ≐ one := Prf.hyp0
    have em : ((par m ≐ one) :: le m (mq x m) :: Γ) ⊢[PRAAx] m ≐ two * half m + one :=
      (half_par m).eqTrans (congrAdd (.eqRefl _) po)
    exact tie_odd (hA 0).wk (hA 1).wk (hA 2).wk (hA 3).wk hle.wk n2.wk em

/-- One step of the descent: for a prime `p`, `2 ≤ m < p` and `N(x) = m p`, the explicit tuple `w` and
multiplier `m'` satisfy `N(w) = m' p` and `1 ≤ m' < m`. -/
theorem descent {p : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hm2 : Γ ⊢[PRAAx] le two m)
    (hmp : Γ ⊢[PRAAx] lt m p) (n1 : Γ ⊢[PRAAx] N4 (x 0) (x 1) (x 2) (x 3) ≐ m * p) :
    Γ ⊢[PRAAx] (N4 (w1 (Af x m) (sf x m) (Uf x m) (mq x m)) (w2 (Af x m) (sf x m) (Uf x m))
        (w3 (Af x m) (sf x m) (Uf x m)) (w4 (Af x m) (sf x m) (Uf x m)) ≐ mq x m * p) ⋏
      (le one (mq x m) ⋏ lt (mq x m) m) := by
  have hm := p_pos hm2
  have n2 := norm_eq hm n1
  have ht : ∀ i : Fin 4, Γ ⊢[PRAAx] sf x m i * sf x m i ≐ sf x m i := fun i => sgn_idem (x i) m
  have hs := star x (Af x m) (sf x m) (Uf x m) m (mq x m) p hm (fun i => res_eq hm (x i)) ht n1 n2
  exact .andI (descent_alg (Af x m) (sf x m) (Uf x m) m (mq x m) p ht n2 hs)
    (.andI (mq_pos hp hm2 hmp n1) (mq_lt hp hm2 hmp n1))

end Descent

end LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresDescent
