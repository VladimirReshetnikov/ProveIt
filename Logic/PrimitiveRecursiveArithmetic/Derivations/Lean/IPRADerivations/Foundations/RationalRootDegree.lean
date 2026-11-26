import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Rational roots in every degree (`ipra_presentations_to_witnesses`, `lem:norm-rational-roots`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-rational-roots`, the
divisibility step of its proof: from the cleared equation

`c_0 q^d + c_1 p q^{d-1} + ⋯ + c_d p^d = 0`   (RR2)

"reduction modulo `q` shows `q ∣ c_d p^d`. Euclid's lemma, applied to the coprime pair
`(q, p^d)`, gives `q ∣ c_d`", where coprimality is carried by Bezout coefficients and
"multiplying the Bezout relation finitely many times gives the required coprimality of powers".

`Foundations/WitnessAlgebra` has degrees `2` and `3` as polynomial certificates. Here the
degree `d` is a variable.

* `Bez m' r u v`: a Bezout relation between `m = m' + 1` and `r`, in either orientation,
  `u m = v r + 1` or `u m + 1 = v r` (natural numbers, so the sign is a case);
* `euclid`: `m ∣ c r` gives `m ∣ c`;
* `pow_cancel`: `m ∣ c r^d` gives `m ∣ c`, by quantifier-free induction on the number of factors
  already removed (`pow_step`);
* `low_dvd`: `q` divides `∑_{i<N} a_i p^i q^{d ∸ i}` for `N ≤ d`;
* `leading_dvd`: signs are split into two coefficient lists `a`, `b` (terms `a(i, x)`,
  `b(i, x)`); from `∑_{i≤d} a_i p^i q^{d∸i} = ∑_{i≤d} b_i p^i q^{d∸i}` and a Bezout relation
  between `q` and `p`, `q` divides `(a_d ∸ b_d) + (b_d ∸ a_d)`, the absolute value of the
  leading coefficient `c_d = a_d - b_d`.

The statement `p ∣ c_0` is `leading_dvd` for the reversed coefficient list with `p` and `q`
exchanged; the reversal identity of the two sums is not derived. The scan over candidate pairs
and the completeness of the root list are not derived either.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RationalRootDegree

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem inst_five {n : ℕ} (t : PTm (n + 5)) : Syn.inst t 5 = (var 4 : PTm (n + 5)) :=
  inst_succ t 4
theorem inst_six {n : ℕ} (t : PTm (n + 6)) : Syn.inst t 6 = (var 5 : PTm (n + 6)) :=
  inst_succ t 5
theorem repl_five {n : ℕ} (s : PTm (n + 6)) : repl s 5 = (var 5 : PTm (n + 6)) :=
  repl_succ s 4
theorem repl_six {n : ℕ} (s : PTm (n + 7)) : repl s 6 = (var 6 : PTm (n + 7)) :=
  repl_succ s 5

/-! ## Euclid's lemma from a Bezout relation -/

/-- A Bezout relation between `m' + 1` and `r`, in either orientation. -/
abbrev Bez (m' r u v : PTm k) : Fm PTm k :=
  (u * succ m' ≐ v * r + one) ⋎ (u * succ m' + one ≐ v * r)

theorem euclid_pos {m' r u v c : PTm k} (hB : Γ ⊢[PRAAx] u * succ m' ≐ v * r + one)
    (h : Γ ⊢[PRAAx] dvd (succ m') (c * r)) : Γ ⊢[PRAAx] dvd (succ m') c := by
  have b := natEq hB
  have h₁ : Γ ⊢[PRAAx] dvd (succ m') (c + c * r * v) :=
    dvd_of_eq (w := u * c) (by apply deriveNat; ipra_simps; linear_combination (-𝔞 c) * b)
  exact dvd_sub h₁ (dvd_mul v h)

theorem euclid_neg {m' r u v c : PTm k} (hB : Γ ⊢[PRAAx] u * succ m' + one ≐ v * r)
    (h : Γ ⊢[PRAAx] dvd (succ m') (c * r)) : Γ ⊢[PRAAx] dvd (succ m') c := by
  have e : Γ ⊢[PRAAx] c * r * v ≐ c + succ m' * (u * c) := by
    ipra_lc (-𝔞 c) * natEq hB
  exact dvd_sub (dvd_congr e (dvd_mul v h)) (dvd_of_eq (w := u * c) (.eqRefl _))

/-- Euclid's lemma: `m ∣ c r` with `m`, `r` coprime gives `m ∣ c`. -/
theorem euclid {m' r u v c : PTm k} (hB : Γ ⊢[PRAAx] Bez m' r u v)
    (h : Γ ⊢[PRAAx] dvd (succ m') (c * r)) : Γ ⊢[PRAAx] dvd (succ m') c :=
  .orE hB (euclid_pos Prf.hyp0 h.wk) (euclid_neg Prf.hyp0 h.wk)

/-! ## Cancelling a power -/

/-- `d ∸ N = (d ∸ (N + 1)) + 1` when `d ∸ N` is positive. -/
theorem monus_peel {d N : PTm k} (h : Γ ⊢[PRAAx] monus d N ≐ succ (pred (monus d N))) :
    Γ ⊢[PRAAx] monus d N ≐ succ (monus d (succ N)) :=
  h.eqTrans (congrSucc (monus_succ d N).eqSymm)

/-- Removing one more factor `r`. -/
theorem pow_step {m' r u v c d e : PTm k} (hB : Γ ⊢[PRAAx] Bez m' r u v)
    (ih : Γ ⊢[PRAAx] dvd (succ m') (c * pw r (monus d e))) :
    Γ ⊢[PRAAx] dvd (succ m') (c * pw r (monus d (succ e))) := by
  refine .orE (zero_or_succ (monus d e)) ?_ ?_
  · have z : ((monus d e ≐ zero) :: Γ) ⊢[PRAAx] monus d e ≐ zero := Prf.hyp0
    have e₁ : ((monus d e ≐ zero) :: Γ) ⊢[PRAAx] monus d (succ e) ≐ monus d e :=
      (monus_succ d e).eqTrans ((congrPred z).eqTrans (pred_zero.eqTrans z.eqSymm))
    exact dvd_congr (congrMul (.eqRefl _) (congrPw (.eqRefl _) e₁.eqSymm)) ih.wk
  · have s : ((monus d e ≐ succ (pred (monus d e))) :: Γ) ⊢[PRAAx]
        monus d e ≐ succ (pred (monus d e)) := Prf.hyp0
    have p := natEq ((congrPw (.eqRefl r) (monus_peel s)).eqTrans
      (pw_succ r (monus d (succ e))))
    have e₂ : ((monus d e ≐ succ (pred (monus d e))) :: Γ) ⊢[PRAAx]
        c * pw r (monus d e) ≐ c * pw r (monus d (succ e)) * r := by
      ipra_lc 𝔞 c * p
    exact euclid hB.wk (dvd_congr e₂ ih.wk)

/-- Variables: `0 = e`, `1 = m'`, `2 = r`, `3 = u`, `4 = v`, `5 = c`, `6 = d`. -/
private abbrev powF : Fm PTm 7 :=
  Bez (var 1) (var 2) (var 3) (var 4) ⟶
    dvd (succ (var 1)) (var 5 * pw (var 2) (var 6)) ⟶
      dvd (succ (var 1)) (var 5 * pw (var 2) (monus (var 6) (var 0)))

private theorem pow₀ : ([] : List (Fm PTm 7)) ⊢[PRAAx] powF := by
  ipra_ind (⟨⟨trivial, trivial⟩, trivial, trivial⟩) [subst_ap2, inst_five, inst_six, repl_five, repl_six]
  · exact .impI (.impI (dvd_congr
      (congrMul (.eqRefl _) (congrPw (.eqRefl _) (monus_zero _).eqSymm)) Prf.hyp0))
  · exact .impI (.impI (pow_step Prf.hyp1 (.impE (.impE hyp2 Prf.hyp1) Prf.hyp0)))

/-- `m ∣ c r^d` with `m`, `r` coprime gives `m ∣ c`. -/
theorem pow_cancel {m' r u v c d : PTm k} (hB : Γ ⊢[PRAAx] Bez m' r u v)
    (h : Γ ⊢[PRAAx] dvd (succ m') (c * pw r d)) : Γ ⊢[PRAAx] dvd (succ m') c := by
  have i := inst (Γ := Γ) pow₀ (![d, m', r, u, v, c, d] : Fin 7 → PTm k)
  simp at i
  have r₁ := Prf.impE (Prf.impE i hB) h
  have e : Γ ⊢[PRAAx] c * pw r (monus d d) ≐ c := by
    ipra_lc 𝔞 c * natEq ((congrPw (.eqRefl r) (le_refl (Γ := Γ) d)).eqTrans (pw_zero r))
  exact dvd_congr e r₁

/-! ## The homogeneous polynomial -/

variable (a : PTm 2)

/-- The term `a(i, x) p^i q^{d ∸ i}` in `0 = i`, `1 = p`, `2 = q`, `3 = d`, `4 = x`. -/
def tG : PTm 5 :=
  inst2 a (var 0) (var 4) * pw (var 1) (var 0) * pw (var 2) (monus (var 3) (var 0))

/-- The summand; variables `0 = i`, `1 = ⟨p, ⟨q, ⟨d, x⟩⟩⟩`. -/
def tB : PTm 2 :=
  Syn.subst ![var 0, fstT (var 1), fstT (sndT (var 1)), fstT (sndT (sndT (var 1))),
    sndT (sndT (sndT (var 1)))] (tG a)

theorem tB_at (i p q d x : PTm k) :
    Γ ⊢[PRAAx] inst2 (tB a) i (pairT p (pairT q (pairT d x))) ≐
      inst2 a i x * pw p i * pw q (monus d i) := by
  have e₁ : inst2 (tB a) i (pairT p (pairT q (pairT d x))) =
      Syn.subst ![i, fstT (pairT p (pairT q (pairT d x))),
          fstT (sndT (pairT p (pairT q (pairT d x)))),
          fstT (sndT (sndT (pairT p (pairT q (pairT d x))))),
          sndT (sndT (sndT (pairT p (pairT q (pairT d x)))))] (tG a) := by
    simp only [inst2, tB, Syn.subst_subst]
    congr 1; funext j; fin_cases j <;> simp
  have e₂ : inst2 a i x * pw p i * pw q (monus d i) = Syn.subst ![i, p, q, d, x] (tG a) := by
    simp [tG]
  rw [e₁, e₂]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT p (pairT q (pairT d x))) ≐ pairT q (pairT d x) :=
    snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT (pairT p (pairT q (pairT d x)))) ≐ pairT d x :=
    (congrSnd s₁).eqTrans (snd_pair _ _)
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrFst s₂).eqTrans (fst_pair _ _)
    · exact (congrSnd s₂).eqTrans (snd_pair _ _)

/-- The partial sum `∑_{i<N} a(i, x) p^i q^{d ∸ i}`. -/
abbrev P (N p q d x : PTm k) : PTm k := ap2 (sumF (tB a)) N (pairT p (pairT q (pairT d x)))

/-- The top term: `a(d, x) p^d q^0 = a(d, x) p^d`. -/
theorem top_at (p q d x : PTm k) :
    Γ ⊢[PRAAx] inst2 (tB a) d (pairT p (pairT q (pairT d x))) ≐ inst2 a d x * pw p d := by
  ipra_lc natEq (tB_at (Γ := Γ) a d p q d x) +
    𝔞 (inst2 a d x) * 𝔞 (pw p d) * natEq ((congrPw (.eqRefl q) (le_refl (Γ := Γ) d)).eqTrans (pw_zero q))

theorem low_step {N p q' d x : PTm k} (hN : Γ ⊢[PRAAx] lt N d)
    (ih : Γ ⊢[PRAAx] dvd (succ q') (P a N p (succ q') d x)) :
    Γ ⊢[PRAAx] dvd (succ q') (P a (succ N) p (succ q') d x) := by
  -- `d ∸ N` is positive
  have hpos : Γ ⊢[PRAAx] monus d N ≐ succ (pred (monus d N)) := by
    refine .orE (zero_or_succ (monus d N)) ?_ Prf.hyp0
    exact le_lt_absurd _ (Prf.hyp0 (Γ := Γ) (φ := monus d N ≐ zero)) hN.wk
  have pk := natEq ((congrPw (.eqRefl (succ q')) (monus_peel hpos)).eqTrans
    (pw_succ (succ q') (monus d (succ N))))
  have hterm : Γ ⊢[PRAAx] dvd (succ q')
      (inst2 (tB a) N (pairT p (pairT (succ q') (pairT d x)))) :=
    dvd_of_eq (w := inst2 a N x * pw p N * pw (succ q') (monus d (succ N))) (by
      ipra_lc natEq (tB_at (Γ := Γ) a N p (succ q') d x) + 𝔞 (inst2 a N x) * 𝔞 (pw p N) * pk)
  exact dvd_congr (sum_succ' (tB a) N _).eqSymm (dvd_add ih hterm)

/-- Variables: `0 = N`, `1 = p`, `2 = q'`, `3 = d`, `4 = x`. -/
private abbrev lowF : Fm PTm 5 :=
  le (var 0) (var 3) ⟶ dvd (succ (var 2)) (P a (var 0) (var 1) (succ (var 2)) (var 3) (var 4))

private theorem low₀ : ([] : List (Fm PTm 5)) ⊢[PRAAx] lowF a := by
  ipra_ind (⟨trivial, trivial⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (dvd_congr (sum_zero (tB a) _).eqSymm (dvd_zero _))
  · exact .impI (low_step a Prf.hyp0
      (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

/-- The terms below the top one are all divisible by `q`. -/
theorem low_dvd {N p q' d x : PTm k} (h : Γ ⊢[PRAAx] le N d) :
    Γ ⊢[PRAAx] dvd (succ q') (P a N p (succ q') d x) := by
  have i := inst (Γ := Γ) (low₀ a) (![N, p, q', d, x] : Fin 5 → PTm k)
  simp at i
  exact .impE i h

/-! ## The leading coefficient -/

/-- From `S + A r^d = T + B r^d` with `m ∣ S`, `m ∣ T`, `A ≤ B` and `m`, `r` coprime:
`m ∣ B ∸ A`. -/
theorem diff_dvd {m' r u v S T A B d : PTm k} (hB : Γ ⊢[PRAAx] Bez m' r u v)
    (hS : Γ ⊢[PRAAx] dvd (succ m') S) (hT : Γ ⊢[PRAAx] dvd (succ m') T)
    (hAB : Γ ⊢[PRAAx] le A B) (hE : Γ ⊢[PRAAx] S + A * pw r d ≐ T + B * pw r d) :
    Γ ⊢[PRAAx] dvd (succ m') (monus B A) := by
  have c₁ : Γ ⊢[PRAAx] S + A * pw r d ≐ (monus B A * pw r d + T) + A * pw r d := by
    ipra_lc natEq hE + 𝔞 (pw r d) * natEq (eq_add_of_le hAB)
  exact pow_cancel hB (dvd_sub (dvd_congr (add_right_cancel c₁) hS) hT)

variable (b : PTm 2)

/-- `lem:norm-rational-roots`, the denominator: if
`∑_{i≤d} a_i p^i q^{d∸i} = ∑_{i≤d} b_i p^i q^{d∸i}` and `q`, `p` are coprime, then `q` divides
`(a_d ∸ b_d) + (b_d ∸ a_d)`. -/
theorem leading_dvd {p q' u v d x : PTm k} (hB : Γ ⊢[PRAAx] Bez q' p u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) p (succ q') d x ≐ P b (succ d) p (succ q') d x) :
    Γ ⊢[PRAAx] dvd (succ q')
      (monus (inst2 a d x) (inst2 b d x) + monus (inst2 b d x) (inst2 a d x)) := by
  have hSa := low_dvd a (N := d) (p := p) (q' := q') (x := x) (le_refl (Γ := Γ) d)
  have hSb := low_dvd b (N := d) (p := p) (q' := q') (x := x) (le_refl (Γ := Γ) d)
  -- the equation with the top terms split off
  have hE' : Γ ⊢[PRAAx] P a d p (succ q') d x + inst2 a d x * pw p d ≐
      P b d p (succ q') d x + inst2 b d x * pw p d :=
    ((congrAdd (.eqRefl _) (top_at a p (succ q') d x)).eqSymm.eqTrans
      (sum_succ' (tB a) d _).eqSymm).eqTrans
      (hE.eqTrans ((sum_succ' (tB b) d _).eqTrans
        (congrAdd (.eqRefl _) (top_at b p (succ q') d x))))
  refine .orE (lt_or_le (inst2 b d x) (inst2 a d x)) ?_ ?_
  · -- `b_d < a_d`
    have hle : (lt (inst2 b d x) (inst2 a d x) :: Γ) ⊢[PRAAx] le (inst2 b d x) (inst2 a d x) :=
      le_of_lt Prf.hyp0
    have d₂ := diff_dvd hB.wk hSb.wk hSa.wk hle hE'.wk.eqSymm
    have z := natEq hle
    refine dvd_congr ?_ d₂
    ipra_lc -z
  · -- `a_d ≤ b_d`
    have hle : (le (inst2 a d x) (inst2 b d x) :: Γ) ⊢[PRAAx] le (inst2 a d x) (inst2 b d x) :=
      Prf.hyp0
    have d₁ := diff_dvd hB.wk hSa.wk hSb.wk hle hE'.wk
    have z := natEq hle
    refine dvd_congr ?_ d₁
    ipra_lc -z

end LeanProofs.IPRA.Foundations.RationalRootDegree
