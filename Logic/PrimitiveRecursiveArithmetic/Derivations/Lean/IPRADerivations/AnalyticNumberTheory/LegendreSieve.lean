import IPRADerivations.AnalyticNumberTheory.GcdPhiSum
import IPRADerivations.AnalyticNumberTheory.MobiusInversionReverse
import IPRADerivations.AnalyticNumberTheory.MertensTotient

/-!
# Legendre's sieve formula

Packets: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, Theorem `an:sieve`
(the identity `S(X, z) = ∑_{d ∣ P(z)} μ(d) ⌊X/d⌋`), and `analytic-number-theory/prime-counting-ipra`,
`sections/sieve.tex` (Legendre's formula).

For every modulus `P` and every `x`, the number of `1 ≤ m ≤ x` with `gcd(m, P) = 1` is
`∑_{d ≤ x, d ∣ P} μ(d) ⌊x/d⌋`. With `μ = μ⁺ − μ⁻` (`SymmetrySum.aPB`, `aNB`) and the negative part on the other
side:

    ∑_{d ≤ x} [d ∣ P] μ⁺(d) ⌊x/d⌋ = #{1 ≤ m ≤ x : gcd(m, P) = 1} + ∑_{d ≤ x} [d ∣ P] μ⁻(d) ⌊x/d⌋
                                                                                (**`legendre_sieve`**).

The packet expands the product `∏_{p ∣ P} (1 − [p ∣ m])` for each `m`. Here the same indicator is the divisor
sum `∑_{d ∣ gcd(m, P)} μ(d) = [gcd(m, P) = 1]`:

* `wB f`: the weight `f(d) [d ∣ P]`;
* `term_pt`, `conv_gcd`: `((f · [· ∣ P]) * 𝟏)(m) = (f * 𝟏)(gcd(m, P))` for `m ≥ 1` (`GcdPhiSum.div_gcd`:
  `[d ∣ m][d ∣ P] = [d ∣ gcd(m, P)]`, and the terms above `gcd(m, P)` vanish);
* `legendre_pt`: `((μ⁺ · [· ∣ P]) * 𝟏)(m) = [m ≥ 1][gcd(m, P) = 1] + ((μ⁻ · [· ∣ P]) * 𝟏)(m)` for every `m`
  (`MobiusInversionReverse.unit_pt` at `gcd(m, P)`);
* `legendre_sum`: the same summed over `m ≤ x`;
* **`legendre_sieve`**: the floor form, by `MertensTotient.floor_summatory`; `sieve_term` displays its terms
  `[d ≥ 1] f(d) [d ∣ P] ⌊x/d⌋`.

The error estimate `|S(X, z) − X ∏_{p ≤ z} (1 − 1/p)| ≤ 2^{π(z)}` of `an:sieve` is not derived.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.LegendreSieve

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB)
open LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap (conv_congr_m)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionReverse (unit_pt)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdPhiSum (div_gcd)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorFactor (shift_gcd)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The restricted weight -/

/-- `f(d) [d ∣ P]`, over `0 = d`, `1 = P`. -/
abbrev wB (f : PTm 2) : PTm 2 := f * eqb (rem (var 1) (var 0)) zero

theorem inst2_wB (f : PTm 2) (d P : PTm n) : inst2 (wB f) d P = inst2 f d P * eqb (rem P d) zero := by
  ipra_ind_simp [inst2, subst_eqb, subst_ap2, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem pt_alg {s bn bP bg F : PTm n} (h : Γ ⊢[PRAAx] bg ≐ bn * bP) :
    Γ ⊢[PRAAx] (s * bn) * ((F * bP) * one) ≐ (s * bg) * (F * one) := by
  ipra_lc -𝔞 s * 𝔞 F * natEq h

theorem z_alg {s X Y X' Y' : PTm n} (h : Γ ⊢[PRAAx] s ≐ zero) :
    Γ ⊢[PRAAx] (s * X) * Y ≐ (s * X') * Y' := by
  ipra_lc (𝔞 X * 𝔞 Y - 𝔞 X' * 𝔞 Y') * natEq h

/-- The term of `(f · [· ∣ P]) * 𝟏` at `m` is the term of `f * 𝟏` at `gcd(m, P)`. -/
theorem term_pt (f : PTm 2) (d m P : PTm n) :
    Γ ⊢[PRAAx] inst2 (cvB (wB f) one) d (pairT m P) ≐ inst2 (cvB f one) d (pairT (gcd m P) P) := by
  refine (cv_at (wB f) one d m P).eqTrans (.eqTrans ?_ (cv_at f one d (gcd m P) P).eqSymm)
  rw [inst2_wB, inst2_oneB, inst2_oneB]
  refine .orE (zero_or_succ d) ?_ ?_
  · exact z_alg ((congrSg Prf.hyp0).eqTrans sg_zero)
  · exact pt_alg (div_gcd Prf.hyp0)

/-- `((f · [· ∣ P]) * 𝟏)(m) = (f * 𝟏)(gcd(m, P))` for `m ≥ 1`. -/
theorem conv_gcd (f : PTm 2) {m P : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] conv (wB f) one m P ≐ conv f one (gcd m P) P := by
  have hg : Γ ⊢[PRAAx] gcd m P ≐ succ (pred (gcd m P)) := gcd_pos hm
  have hgm : Γ ⊢[PRAAx] le (gcd m P) m := dvd_le' hg (Prf.andE₁ (gcd_dvd' hm)) hm
  have hgZ : Γ ⊢[PRAAx] le (succ (gcd m P)) (succ m) := (succ_monus_succ _ _).eqTrans hgm
  have hg' := shift_pos hg
  have s1 : Γ ⊢[PRAAx] ap2 (sumF (cvB (wB f) one)) (succ m) (pairT m P) ≐
      ap2 (sumF (cvB f one)) (succ m) (pairT (gcd m P) P) := by
    refine sum_congr_bounded (cvB (wB f) one) (cvB f one) (pairT m P) (pairT (gcd m P) P) (succ m)
      (.allI (.impI ?_))
    rw [shift_pairT, shift_pairT, shift_gcd]
    exact term_pt f _ _ _
  have s2 : Γ ⊢[PRAAx] ap2 (sumF (cvB f one)) (succ m) (pairT (gcd m P) P) ≐
      ap2 (sumF (cvB f one)) (succ (gcd m P)) (pairT (gcd m P) P) := by
    refine sum_ext (cvB f one) (fun Δ a hs hl => ?_) hgZ
    rw [shift_pairT]
    exact (cv_at f one a _ _).eqTrans
      (zero_mul_l ((congrMul (.eqRefl _) (eqb_rem_big (hg'.weaken hs) hl)).eqTrans (mul_zero _)) _)
  exact s1.eqTrans s2

/-! ## The indicator of coprimality -/

theorem z3 {X s e Y : PTm n} (hX : Γ ⊢[PRAAx] X ≐ zero) (hs : Γ ⊢[PRAAx] s ≐ zero)
    (hY : Γ ⊢[PRAAx] Y ≐ zero) : Γ ⊢[PRAAx] X ≐ s * e + Y := by
  ipra_lc natEq hX - 𝔞 e * natEq hs - natEq hY

/-- `((μ⁺ · [· ∣ P]) * 𝟏)(m) = [m ≥ 1][gcd(m, P) = 1] + ((μ⁻ · [· ∣ P]) * 𝟏)(m)` for every `m`. -/
theorem legendre_pt (m P : PTm n) :
    Γ ⊢[PRAAx] conv (wB aPB) one m P ≐ sg m * eqb (gcd m P) one + conv (wB aNB) one m P := by
  refine .orE (zero_or_succ m) ?_ ?_
  · have h0 : ((m ≐ zero) :: Γ) ⊢[PRAAx] m ≐ zero := Prf.hyp0
    exact z3 ((conv_congr_m (wB aPB) one P h0).eqTrans (conv_zero _ _ _)) ((congrSg h0).eqTrans sg_zero)
      ((conv_congr_m (wB aNB) one P h0).eqTrans (conv_zero _ _ _))
  · have hm : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    have s1 : ((m ≐ succ (pred m)) :: Γ) ⊢[PRAAx] sg m ≐ one := (congrSg hm).eqTrans (sg_succ _)
    have e := (conv_gcd aPB (P := P) hm).eqTrans
      ((unit_pt (gcd m P) P).eqTrans (congrAdd (.eqRefl _) (conv_gcd aNB (P := P) hm).eqSymm))
    exact e.eqTrans (congrAdd ((one_mul _).eqSymm.eqTrans (congrMul s1.eqSymm (.eqRefl _))) (.eqRefl _))

/-- `[m ≥ 1][gcd(m, P) = 1]`, over `0 = m`, `1 = P`. -/
abbrev coB : PTm 2 := sg (var 0) * eqb (gcd (var 0) (var 1)) one

theorem inst2_coB (m P : PTm n) : inst2 coB m P = sg m * eqb (gcd m P) one := by
  ipra_ind_simp [inst2, subst_eqb, subst_ex2, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The summed identity: `∑_{m ≤ x} ((μ⁺ · [· ∣ P]) * 𝟏)(m) = #{1 ≤ m ≤ x : gcd(m, P) = 1} + ∑_{m ≤ x} (…⁻…)(m)`. -/
theorem legendre_sum (x P : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cvF (wB aPB) one)) (succ x) P ≐
      ap2 (sumF coB) (succ x) P + ap2 (sumF (cvF (wB aNB) one)) (succ x) P := by
  refine sum_add2 coB (cvF (wB aNB) one) (cvF (wB aPB) one) (.allI (.impI ?_))
  rw [inst2_cvF, inst2_cvF, inst2_coB]
  exact legendre_pt _ _

/-! ## The floor form -/

/-- **Legendre's sieve formula**: `∑_{d ≤ x} [d ∣ P] μ⁺(d) ⌊x/d⌋ = #{1 ≤ m ≤ x : gcd(m, P) = 1} +
∑_{d ≤ x} [d ∣ P] μ⁻(d) ⌊x/d⌋`, with the terms of `sieve_term`. -/
theorem legendre_sieve (x P : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB (wB aPB) one)) (succ x) (pairT x P) ≐
      ap2 (sumF coB) (succ x) P + ap2 (sumF (RB (wB aNB) one)) (succ x) (pairT x P) :=
  (floor_summatory (wB aPB) x P).eqSymm.eqTrans
    ((legendre_sum x P).eqTrans (congrAdd (.eqRefl _) (floor_summatory (wB aNB) x P)))

/-- The terms of the two floor sums: `[d ≥ 1] f(d) [d ∣ P] ⌊x/d⌋`. -/
theorem sieve_term (f : PTm 2) (d x P : PTm n) :
    Γ ⊢[PRAAx] inst2 (RB (wB f) one) d (pairT x P) ≐ (sg d * (inst2 f d P * eqb (rem P d) zero)) * quo x d := by
  have h := floor_term (Γ := Γ) (wB f) d x P
  rw [inst2_wB] at h
  exact h

end LeanProofs.IPRA.AnalyticNumberTheory.LegendreSieve

export_ipra AnalyticNumberTheory.LegendreSieve (coB inst2_coB)
