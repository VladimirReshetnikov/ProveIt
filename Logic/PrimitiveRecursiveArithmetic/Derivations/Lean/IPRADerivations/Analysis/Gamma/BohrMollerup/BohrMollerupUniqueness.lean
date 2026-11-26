import IPRADerivations.Analysis.Inequalities.PowerGap
import IPRADerivations.Probability.Variance
import IPRADerivations.Foundations.MixedRadix

/-!
# The finite uniqueness argument of the Bohr–Mollerup theorem

Packet: `analysis/bohr_mollerup_ipra_2026-11-15`, `paper/bohr_mollerup_ipra.tex`, Section `sec:uniqueness`
and the proof of the theorem "constructive Bohr–Mollerup theorem on positive rationals". The squeeze lemmas,
the bracket width and the power-gap bound are `Analysis/EulerSqueeze` and `Analysis/PowerGap`; this file
derives the remaining finite steps, with all values numerators over a common denominator:

* `iterated_recurrence` (`eq:recurrence-iterated`): if `b F_{j+1} = (a + b j) F_j` for `j < m` (the
  recurrence `F(q + j + 1) = (q + j) F(q + j)` at `q = a/b`), then `b^m F_m = ∏_{j<m} (a + b j) · F_0`,
  i.e. `F(q + m) = P_m(q) F(q)`;
* `bernoulli`: `u^{e+1} + (e + 1) d u^e ≤ (u + d)^{e+1}`;
* `pow_inj` ("positive integer powers are injective on strongly positive names", with the explicit
  modulus): for `u, v ≥ m`, `(e + 1) m^e |u − v| ≤ |u^{e+1} − v^{e+1}|`;
* `squeeze_close`: two numbers in the same interval `[A, B]` differ by at most `B − A`;
* `uniqueness_core`: if `F(q)^b` and `Γ₀(q)^b` both lie between `A_n^b` and `B_n^b` (`b = e + 1`), with
  `B_n = A_n + d ≤ U` and both values at least `m`, then `b m^e |F(q) − Γ₀(q)| ≤ d b U^e`;
* `uniqueness_rate`: with the bracket width `n d ≤ S` (`eq:width`, cleared), for every `n`,
  `n · b m^e |F(q) − Γ₀(q)| ≤ S · b U^e`, the explicit rate `|F(q) − Γ₀(q)| ≤ S U^{b−1} / (n m^{b−1})` from
  which the theorem's choice of `n` at precision `2^{−k}` is read.

The reading of `F` and `Γ₀` as regular names, and the real-domain corollary, are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BohrMollerupUniqueness

open_ipra
open LeanProofs.IPRA.Analysis.PowerGap (power_gap shift_le' shift_eq')
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Foundations.MixedRadix (prod_succ')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bernoulli's inequality -/

section Bernoulli

variable {u d : PTm n}

theorem bern_base :
    Γ ⊢[PRAAx] le (pw u (succ zero) + succ zero * d * pw u zero) (pw (u + d) (succ zero)) := by
  have p₁ := natEq (pw_succ (Γ := Γ) u zero); have p₂ := natEq (pw_succ (Γ := Γ) (u + d) zero)
  have z₁ := natEq (pw_zero (Γ := Γ) u); have z₂ := natEq (pw_zero (Γ := Γ) (u + d))
  ipra_le 0 using rw [p₁, p₂, z₁, z₂]; ring

theorem bern_step {e : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw u (succ e) + succ e * d * pw u e) (pw (u + d) (succ e))) :
    Γ ⊢[PRAAx] le (pw u (succ (succ e)) + succ (succ e) * d * pw u (succ e)) (pw (u + d) (succ (succ e))) := by
  have p₁ := natEq (pw_succ (Γ := Γ) u (succ e))
  have p₂ := natEq (pw_succ (Γ := Γ) u e)
  have p₃ := natEq (pw_succ (Γ := Γ) (u + d) (succ e))
  ipra_le sl ih * (𝔟 u + 𝔟 d) + (𝔟 e + 1) * 𝔟 d * 𝔟 d * 𝔟 (pw u e) using
    rw [p₁, p₃]
    linear_combination (-(𝔟 e + 1) * 𝔟 d) * p₂

theorem bern_all (u d : PTm n) :
    Γ ⊢[PRAAx] Fm.all (le (pw (Syn.shift u) (succ (var 0)) + succ (var 0) * Syn.shift d * pw (Syn.shift u) (var 0))
      (pw (Syn.shift u + Syn.shift d) (succ (var 0)))) := by
  ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
  · exact bern_base
  · exact bern_step Prf.hyp0

/-- Bernoulli's inequality `u^{e+1} + (e + 1) d u^e ≤ (u + d)^{e+1}`. -/
theorem bernoulli (u d e : PTm n) :
    Γ ⊢[PRAAx] le (pw u (succ e) + succ e * d * pw u e) (pw (u + d) (succ e)) := by
  have a := Prf.allE e (bern_all (Γ := Γ) u d)
  simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at a
  exact a

end Bernoulli

/-! ## Injectivity of powers with a modulus -/

theorem pow_inj_le {m u v : PTm n} (hu : Γ ⊢[PRAAx] le m u) (h : Γ ⊢[PRAAx] le u v) (e : PTm n) :
    Γ ⊢[PRAAx] le (succ e * pw m e * ad u v) (ad (pw u (succ e)) (pw v (succ e))) := by
  have hp := pw_le_pw (succ e) h
  have m₁ := natEq h
  have m₃ := natEq hp
  have m₄ := natEq (eq_add_of_le hp)
  have bern := le_congr (.eqRefl _)
    (Combinatorics.BinomialTheorem.congrPw (eq_add_of_le h).eqSymm (.eqRefl (succ e)))
    (bernoulli (Γ := Γ) u (monus v u) e)
  have hmu := pw_le_pw e hu
  ipra_le sl bern + (𝔟 e + 1) * 𝔟 (monus v u) * sl hmu using
    rw [m₁, m₃]
    linear_combination -m₄

/-- `(e + 1) m^e |u − v| ≤ |u^{e+1} − v^{e+1}|` for `u, v ≥ m`. -/
theorem pow_inj {m u v : PTm n} (hu : Γ ⊢[PRAAx] le m u) (hv : Γ ⊢[PRAAx] le m v) (e : PTm n) :
    Γ ⊢[PRAAx] le (succ e * pw m e * ad u v) (ad (pw u (succ e)) (pw v (succ e))) := by
  refine .orE (le_total u v) (pow_inj_le hu.wk Prf.hyp0 e) ?_
  have h := pow_inj_le (Γ := le v u :: Γ) hv.wk Prf.hyp0 e
  exact le_congr (congrMul (.eqRefl _) (add_comm _ _)) (add_comm _ _) h

/-! ## Two values in one bracket -/

theorem squeeze_close_le {A B f g : PTm n} (hf : Γ ⊢[PRAAx] le A f) (hg : Γ ⊢[PRAAx] le g B)
    (h : Γ ⊢[PRAAx] le f g) : Γ ⊢[PRAAx] le (ad f g + A) B := by
  have m₁ := natEq h
  have e := natEq (eq_add_of_le h)
  ipra_le sl hf + sl hg using
    rw [m₁]
    linear_combination e

/-- Two numbers in `[A, B]` differ by at most `B − A`: `|f − g| + A ≤ B`. -/
theorem squeeze_close {A B f g : PTm n} (hf₁ : Γ ⊢[PRAAx] le A f) (hf₂ : Γ ⊢[PRAAx] le f B)
    (hg₁ : Γ ⊢[PRAAx] le A g) (hg₂ : Γ ⊢[PRAAx] le g B) : Γ ⊢[PRAAx] le (ad f g + A) B := by
  refine .orE (le_total f g) (squeeze_close_le hf₁.wk hg₂.wk Prf.hyp0) ?_
  have h := squeeze_close_le (Γ := le g f :: Γ) hg₁.wk hf₂.wk Prf.hyp0
  exact le_congr (congrAdd (add_comm _ _) (.eqRefl _)) (.eqRefl _) h

/-! ## The uniqueness estimate -/

section Unique

variable {A B d U m f g e : PTm n}

/-- Both `b`-th powers in `[A_n^b, B_n^b]` give `b m^e |f − g| ≤ d b U^e` (`b = e + 1`). -/
theorem uniqueness_core (hd : Γ ⊢[PRAAx] B ≐ A + d) (hBU : Γ ⊢[PRAAx] le B U)
    (hmf : Γ ⊢[PRAAx] le m f) (hmg : Γ ⊢[PRAAx] le m g)
    (hf₁ : Γ ⊢[PRAAx] le (pw A (succ e)) (pw f (succ e))) (hf₂ : Γ ⊢[PRAAx] le (pw f (succ e)) (pw B (succ e)))
    (hg₁ : Γ ⊢[PRAAx] le (pw A (succ e)) (pw g (succ e))) (hg₂ : Γ ⊢[PRAAx] le (pw g (succ e)) (pw B (succ e))) :
    Γ ⊢[PRAAx] le (succ e * pw m e * ad f g) (d * (succ e * pw U e)) := by
  have pi := pow_inj hmf hmg e
  have sq := squeeze_close hf₁ hf₂ hg₁ hg₂
  have pg := power_gap hd hBU e
  ipra_le sl pi + sl sq + sl pg

/-- The explicit rate: with `n d ≤ S`, `n · b m^e |f − g| ≤ S · b U^e` for every `n`. -/
theorem uniqueness_rate {N S : PTm n} (hd : Γ ⊢[PRAAx] B ≐ A + d) (hBU : Γ ⊢[PRAAx] le B U)
    (hw : Γ ⊢[PRAAx] le (N * d) S)
    (hmf : Γ ⊢[PRAAx] le m f) (hmg : Γ ⊢[PRAAx] le m g)
    (hf₁ : Γ ⊢[PRAAx] le (pw A (succ e)) (pw f (succ e))) (hf₂ : Γ ⊢[PRAAx] le (pw f (succ e)) (pw B (succ e)))
    (hg₁ : Γ ⊢[PRAAx] le (pw A (succ e)) (pw g (succ e))) (hg₂ : Γ ⊢[PRAAx] le (pw g (succ e)) (pw B (succ e))) :
    Γ ⊢[PRAAx] le (N * (succ e * pw m e * ad f g)) (S * (succ e * pw U e)) := by
  have c := uniqueness_core hd hBU hmf hmg hf₁ hf₂ hg₁ hg₂
  ipra_le 𝔟 N * sl c + sl hw * (𝔟 e + 1) * 𝔟 (pw U e)

end Unique

/-! ## The iterated recurrence -/

/-- The factor `a + b j`, over `(j, ⟨a, ⟨b, x⟩⟩)`. -/
abbrev rB : PTm 2 := fstT (var 1) + fstT (sndT (var 1)) * var 0

theorem rB_at (j a b x : PTm n) : Γ ⊢[PRAAx] inst2 rB j (pairT a (pairT b x)) ≐ a + b * j := by
  have e : inst2 rB j (pairT a (pairT b x)) =
      fstT (pairT a (pairT b x)) + fstT (sndT (pairT a (pairT b x))) * j := by simp [inst2]
  rw [e]
  exact congrAdd (fst_pair _ _) (congrMul (snd_pair _ _).fstE (.eqRefl _))

section Recurrence

variable (F : PTm 2)

/-- `P_K = ∏_{j<K} (a + b j)`. -/
abbrev Pq (K a b x : PTm n) : PTm n := ap2 (prodF rB) K (pairT a (pairT b x))

theorem rec_step {a b x K : PTm n}
    (hr : Γ ⊢[PRAAx] b * inst2 F (succ K) x ≐ (a + b * K) * inst2 F K x)
    (ih : Γ ⊢[PRAAx] pw b K * inst2 F K x ≐ Pq K a b x * inst2 F zero x) :
    Γ ⊢[PRAAx] pw b (succ K) * inst2 F (succ K) x ≐ Pq (succ K) a b x * inst2 F zero x := by
  have p := natEq (pw_succ (Γ := Γ) b K)
  have q' := prod_succ' (Γ := Γ) rB K (pairT a (pairT b x))
  have q := natEq (q'.eqTrans (congrMul (.eqRefl _) (rB_at K a b x)))
  have r := natEq hr
  have i := natEq ih
  apply deriveNat; ipra_simps
  rw [p, q]
  linear_combination 𝔟 (pw b K) * r + (𝔟 a + 𝔟 b * 𝔟 K) * i

/-- `eq:recurrence-iterated`: if `b F_{j+1} = (a + b j) F_j` for `j < M`, then
`b^M F_M = ∏_{j<M} (a + b j) · F_0`, i.e. `F(q + M) = P_M(q) F(q)` for `q = a/b`. -/
theorem iterated_recurrence (a b x M : PTm n)
    (hrec : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (Syn.shift b * inst2 F (succ (var 0)) (Syn.shift x) ≐
        (Syn.shift a + Syn.shift b * var 0) * inst2 F (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] pw b M * inst2 F M x ≐ Pq M a b x * inst2 F zero x := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift M) ⟶
      (pw (Syn.shift b) (var 0) * inst2 F (var 0) (Syn.shift x) ≐
        Pq (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift x) * inst2 F zero (Syn.shift x))) := by
    ipra_qfind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2, subst_pairT, subst_inst2]
    · refine .impI ?_
      apply deriveNat; ipra_simps
      rw [natEq (pw_zero (Γ := le zero M :: Γ) b), natEq (prod_zero (Γ := le zero M :: Γ) rB (pairT a (pairT b x)))]
    · refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift M) ::
          (le (var 0) (Syn.shift M) ⟶
            (pw (Syn.shift b) (var 0) * inst2 F (var 0) (Syn.shift x) ≐
              Pq (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift x) * inst2 F zero (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift M) := Prf.hyp0
      exact rec_step F (Prf.impE hrec.allOpen.wk.wk hk) (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk))
  have h2 := Prf.allE M hall
  simp only [Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_mul, subst_inst2,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl M)

end Recurrence

end LeanProofs.IPRA.Analysis.BohrMollerupUniqueness
