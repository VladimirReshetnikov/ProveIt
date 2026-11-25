import IPRADerivations.DiophantineNumberTheory.QuarticStep
import IPRADerivations.Core.EuclidLemma
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.CertificateTactics

/-!
# The gcd tools and the primitive Pythagorean parametrization

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Lemmas `lem:descent-gcd` and
`lem:pythagorean-descent`.

* `gcd_tools` (`lem:descent-gcd` (1)): for `a ≥ 1`, `g = gcd(a, b) ≥ 1` divides `a` and `b`, and the
  Bezout coefficients `u, v` of `Core/Bezout` give `g + v b = u a` or `g + u a = v b`, i.e. a signed
  identity `u a + v b = g`;
* `gauss_tool` ((2)): `gcd(a, b) = 1`, `a ∣ b c ⇒ a ∣ c`;
* `sq_dvd_tool` ((3)): `d ≥ 1`, `d² ∣ c² ⇒ d ∣ c` (also for `c = 0`);
* `square_split` ((4)): `a, b, c ≥ 1`, `gcd(a, b) = 1`, `a b = c²` give `r = gcd(a, c)`,
  `s = gcd(b, c)` with `a = r²`, `b = s²`, `c = r s`;
* `leg_parity` (`lem:pythagorean-descent`, the leg exchange): for a primitive triple
  `A² + B² = C²` with `A, B ≥ 1`, exactly one leg is even;
* `pyth_param`: with the odd leg `B` and the even leg `2H`, `m = pm`, `n = pn` (`Pythagoras`) satisfy
  `2H = 2mn`, `B = m² − n²` (`B + n² = m²`), `C = m² + n²`, `gcd(m, n) = 1`, `m > n ≥ 1`, and `m, n`
  have opposite parity;
* `pyth_unique`: any `m', n'` with `B + n'² = m'²`, `C = m'² + n'²` equal `m, n`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.DescentTools

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (pm pn pyth_at two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (odd_sq_sum not_both_even)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The gcd tools -/

/-- `lem:descent-gcd` (1): `gcd(a, b)` is a positive common divisor with a signed Bezout identity. -/
theorem gcd_tools {a : PTm n} (b : PTm n) (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) :
    Γ ⊢[PRAAx] (gcd a b ≐ succ (pred (gcd a b))) ⋏ ((dvd (gcd a b) a ⋏ dvd (gcd a b) b) ⋏
      ((gcd a b + Bezout.cur zero one (succ b) a b * b ≐ Bezout.cur one zero (succ b) a b * a) ⋎
        (gcd a b + Bezout.cur one zero (succ b) a b * a ≐ Bezout.cur zero one (succ b) a b * b))) :=
  .andI (gcd_pos ha) (.andI (gcd_dvd' ha) (bezout_at a b))

/-- (2): `gcd(a, b) = 1` and `a ∣ b c` give `a ∣ c`. -/
theorem gauss_tool {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hg : Γ ⊢[PRAAx] gcd a b ≐ one)
    (h : Γ ⊢[PRAAx] dvd a (b * c)) : Γ ⊢[PRAAx] dvd a c :=
  gauss ha hg h

/-- (3): `d² ∣ c²` with `d ≥ 1` gives `d ∣ c`. -/
theorem sq_dvd_tool {d c : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] dvd (d * d) (c * c)) :
    Γ ⊢[PRAAx] dvd d c := by
  refine .orE (zero_or_succ c) ?_ ?_
  · exact (congrAp2 remF Prf.hyp0 (.eqRefl _)).eqTrans (rem_zero _)
  · exact dvd_of_sq_dvd_sq hd.wk Prf.hyp0 h.wk

/-- (4): coprime factors of a square are squares, with computed roots `r = gcd(a, c)`, `s = gcd(b, c)`. -/
theorem square_split {a b c : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (hg : Γ ⊢[PRAAx] gcd a b ≐ one) (h : Γ ⊢[PRAAx] a * b ≐ c * c) :
    Γ ⊢[PRAAx] (a ≐ gcd a c * gcd a c) ⋏ ((b ≐ gcd b c * gcd b c) ⋏ (c ≐ gcd a c * gcd b c)) := by
  have ea := square_of_coprime ha hg h
  have eb := square_of_coprime hb (gcd_comm_one hb hg) ((mul_comm _ _).eqTrans h)
  refine .andI ea (.andI eb (sq_inj ?_))
  ipra_lc -natEq h + 𝔞 b * natEq ea + (𝔞 (gcd a c) * 𝔞 (gcd a c)) * natEq eb

/-! ## Primitive Pythagorean triples -/

/-- The leg exchange: of two coprime legs of a right triangle, one is even and the other odd. -/
theorem leg_parity {A B C : PTm n} (hg : Γ ⊢[PRAAx] gcd A B ≐ one) (hE : Γ ⊢[PRAAx] A * A + B * B ≐ C * C) :
    Γ ⊢[PRAAx] ((A ≐ two * half A) ⋏ (B ≐ two * half B + one)) ⋎
      ((A ≐ two * half A + one) ⋏ (B ≐ two * half B)) := by
  refine .orE (even_or_odd A) ?_ ?_
  · refine .orE (even_or_odd B) ?_ ?_
    · exact not_both_even _ hg.wk.wk Prf.hyp1 Prf.hyp0
    · exact .orI₁ (.andI Prf.hyp1 Prf.hyp0)
  · refine .orE (even_or_odd B) ?_ ?_
    · exact .orI₂ (.andI Prf.hyp1 Prf.hyp0)
    · exact odd_sq_sum _ Prf.hyp1 Prf.hyp0 hE.wk.wk

/-- `m > n`, from `B + n² = m²` and `B ≥ 1`. -/
theorem lt_of_sq_gap {B m n' : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (h : Γ ⊢[PRAAx] B + n' * n' ≐ m * m) :
    Γ ⊢[PRAAx] lt n' m := by
  refine .orE (lt_or_le n' m) Prf.hyp0 ?_
  have sq : (le m n' :: Γ) ⊢[PRAAx] le (m * m) (n' * n') := le_mul_mono Prf.hyp0 Prf.hyp0
  have big : (le m n' :: Γ) ⊢[PRAAx] le (succ (n' * n')) (m * m) := by
    refine le_of_eq_add (d := pred B) ?_
    ipra_lc -natEq (h.wk : (le m n' :: Γ) ⊢[PRAAx] _) + natEq (hB.wk : (le m n' :: Γ) ⊢[PRAAx] _)
  exact not_succ_le_self _ _ (le_trans big sq)

/-- `lem:pythagorean-descent`: the parametrization of a primitive triple with odd leg `B` and even leg `2H`. -/
theorem pyth_param {B H C : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hH : Γ ⊢[PRAAx] H ≐ succ (pred H))
    (hE : Γ ⊢[PRAAx] B * B + (two * H) * (two * H) ≐ C * C) (hg : Γ ⊢[PRAAx] gcd B (two * H) ≐ one) :
    Γ ⊢[PRAAx] (two * H ≐ two * (pm B H C * pn B H C)) ⋏
      ((B + pn B H C * pn B H C ≐ pm B H C * pm B H C) ⋏
      ((C ≐ pm B H C * pm B H C + pn B H C * pn B H C) ⋏
      ((gcd (pm B H C) (pn B H C) ≐ one) ⋏
      ((pn B H C ≐ succ (pred (pn B H C))) ⋏ (lt (pn B H C) (pm B H C) ⋏
      (((pm B H C ≐ two * half (pm B H C)) ⋏ (pn B H C ≐ two * half (pn B H C) + one)) ⋎
        ((pm B H C ≐ two * half (pm B H C) + one) ⋏ (pn B H C ≐ two * half (pn B H C))))))))) := by
  have p := pyth_at hB hH hE hg
  have e₁ := Prf.andE₁ p
  have e₂ := Prf.andE₁ (Prf.andE₂ p)
  have e₃ := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ p))
  have e₄ := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p)))
  have e₅ := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ p)))
  -- `B` is odd, so `m` and `n` have opposite parity.
  have hBo : Γ ⊢[PRAAx] B ≐ two * half B + one := by
    refine .orE (even_or_odd B) ?_ Prf.hyp0
    exact not_both_even _ hg.wk Prf.hyp0 (.eqRefl _)
  have par : Γ ⊢[PRAAx] ((pm B H C ≐ two * half (pm B H C)) ⋏ (pn B H C ≐ two * half (pn B H C) + one)) ⋎
      ((pm B H C ≐ two * half (pm B H C) + one) ⋏ (pn B H C ≐ two * half (pn B H C))) := by
    refine .orE (even_or_odd (pm B H C)) ?_ ?_
    · refine .orE (even_or_odd (pn B H C)) ?_ (.orI₁ (.andI Prf.hyp1 Prf.hyp0))
      let C₂ := (pn B H C ≐ two * half (pn B H C)) :: (pm B H C ≐ two * half (pm B H C)) :: Γ
      have x := natEq (e₁.wk.wk : C₂ ⊢[PRAAx] _); have o := natEq (hBo.wk.wk : C₂ ⊢[PRAAx] _)
      have u := natEq (Prf.hyp1 : C₂ ⊢[PRAAx] _); have v := natEq (Prf.hyp0 : C₂ ⊢[PRAAx] _)
      refine even_ne_odd _ (k := two * (half (pm B H C) * half (pm B H C)))
        (m := half B + two * (half (pn B H C) * half (pn B H C))) ?_
      ipra_lc -x - (𝔞 (pm B H C) + 2 * 𝔞 (half (pm B H C))) * u + (𝔞 (pn B H C) + 2 * 𝔞 (half (pn B H C))) * v + o
    · refine .orE (even_or_odd (pn B H C)) (.orI₂ (.andI Prf.hyp1 Prf.hyp0)) ?_
      let C₂ := (pn B H C ≐ two * half (pn B H C) + one) :: (pm B H C ≐ two * half (pm B H C) + one) :: Γ
      have x := natEq (e₁.wk.wk : C₂ ⊢[PRAAx] _); have o := natEq (hBo.wk.wk : C₂ ⊢[PRAAx] _)
      have u := natEq (Prf.hyp1 : C₂ ⊢[PRAAx] _); have v := natEq (Prf.hyp0 : C₂ ⊢[PRAAx] _)
      refine even_ne_odd _ (k := two * (half (pm B H C) * half (pm B H C)) + two * half (pm B H C))
        (m := half B + two * (half (pn B H C) * half (pn B H C)) + two * half (pn B H C)) ?_
      ipra_lc -x + o - (𝔞 (pm B H C) + 2 * 𝔞 (half (pm B H C)) + 1) * u +
        (𝔞 (pn B H C) + 2 * 𝔞 (half (pn B H C)) + 1) * v
  exact .andI (congrMul (.eqRefl _) e₂) (.andI e₁ (.andI e₃ (.andI e₄ (.andI e₅
    (.andI (lt_of_sq_gap hB e₁) par)))))

/-- Uniqueness: `B + n'² = m'²` and `C = m'² + n'²` determine `m' = m`, `n' = n`. -/
theorem pyth_unique {B C m n' m₁ n₁ : PTm n}
    (h₁ : Γ ⊢[PRAAx] B + n' * n' ≐ m * m) (h₂ : Γ ⊢[PRAAx] C ≐ m * m + n' * n')
    (k₁ : Γ ⊢[PRAAx] B + n₁ * n₁ ≐ m₁ * m₁) (k₂ : Γ ⊢[PRAAx] C ≐ m₁ * m₁ + n₁ * n₁) :
    Γ ⊢[PRAAx] (m₁ ≐ m) ⋏ (n₁ ≐ n') := by
  have a := natEq h₁; have b := natEq h₂; have c := natEq k₁; have d := natEq k₂
  have nn : Γ ⊢[PRAAx] n₁ * n₁ ≐ n' * n' := by
    refine mul_cancel two_pos ?_
    ipra_lc c - d - a + b
  have mm : Γ ⊢[PRAAx] m₁ * m₁ ≐ m * m := by
    ipra_lc -c + a + natEq nn
  exact .andI (sq_inj mm) (sq_inj nn)

end LeanProofs.IPRA.DiophantineNumberTheory.DescentTools
