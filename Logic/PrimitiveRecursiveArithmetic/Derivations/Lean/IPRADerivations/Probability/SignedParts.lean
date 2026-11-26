import IPRADerivations.Probability.TailSum
import IPRADerivations.Probability.Variance

/-!
# Signed observables, parts, and finite linear combinations

Packet: `probability/expected_value_ipra_2026-11-16` (Section 5). A signed observable is a pair of
natural bodies `(P, N)` standing for `X = P − N`; its parts are `X⁺ = P ∸ N`, `X⁻ = N ∸ P` and
`|X| = X⁺ + X⁻`. Expectations are the weighted numerators `Ew(·) = ∑_{i<M} w_i (·)_i`.

* `part_identities` (`lem:part-identities`): `X⁺ + N = X⁻ + P` (i.e. `X = X⁺ − X⁻`), `X⁺ X⁻ = 0`,
  `|X| = X⁺ + X⁻`;
* `expect_parts`, `abs_expect_le` (`thm:expect-parts`): `Ew(X⁺) + Ew(N) = Ew(X⁻) + Ew(P)`,
  `Ew|X| = Ew(X⁺) + Ew(X⁻)`, and `|Ew(P) − Ew(N)| ≤ Ew|X|`;
* `signed_nonneg` (`thm:nonneg`) and `signed_mono` (`thm:monotone`): `N ≤ P` pointwise gives
  `Ew N ≤ Ew P`; `P + N' ≤ P' + N` pointwise (i.e. `X ≤ Y`) gives `Ew P + Ew N' ≤ Ew P' + Ew N`;
* `neg_tail_pt`, `signed_tail` (`thm:signed-tail`): `[X⁻ > k] = [P + k + 1 ≤ N]` (that is,
  `[X ≤ −k−1]`), and for `X⁺ ≤ B`, `X⁻ ≤ A`:
  `Ew P + ∑_{k<A} ∑_i w_i [X⁻_i > k] = ∑_{k<B} ∑_i w_i [X⁺_i > k] + Ew N`;
* `finite_linearity` (`cor:finite-linearity`): `Ew(∑_{j<r} a_j X_j) = ∑_{j<r} a_j Ew(X_j)`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.SignedParts

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew inst2_mul' inst2_add' geI geI_true geI_false exp_add exp_mono)
open LeanProofs.IPRA.Probability.Independence (shift_inst2 row_pt col_pt sum_scale dsum dsum_rows)
open LeanProofs.IPRA.Probability.TailSum (tlA tail_sum)
open LeanProofs.IPRA.Probability.Variance (ad)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem inst2_monus' (f g : PTm 2) (i x : PTm n) :
    inst2 (monus f g) i x = monus (inst2 f i x) (inst2 g i x) := by simp [inst2]

/-! ## Pointwise parts -/

/-- `lem:part-identities`, for `x = a − b`: `x⁺ + b = x⁻ + a`, `x⁺ x⁻ = 0`, `|x| = x⁺ + x⁻`. -/
theorem part_identities (a b : PTm n) :
    Γ ⊢[PRAAx] (monus a b + b ≐ monus b a + a) ⋏ ((monus a b * monus b a ≐ zero) ⋏
      (ad a b ≐ monus a b + monus b a)) :=
  .andI (monus_max a b) (.andI (monus_mul a b) (.eqRefl _))

/-- `[x⁻ > k] = [x ≤ −k−1]`: for `x = a − b`, `[b ∸ a ≥ k+1] = [b ≥ a + k + 1]`. -/
theorem neg_tail_pt (a b k : PTm n) : Γ ⊢[PRAAx] geI (succ k) (monus b a) ≐ geI (a + succ k) b := by
  refine .orE (lt_or_le b a) ?_ ?_
  · let C := lt b a :: Γ
    have h : C ⊢[PRAAx] lt b a := Prf.hyp0
    have e := eq_add_of_le h
    have hz : C ⊢[PRAAx] le b a := le_of_eq_add (d := succ (monus a (succ b)))
      (e.eqTrans (by ipra_ring))
    have hl : C ⊢[PRAAx] lt b (a + succ k) := le_of_eq_add (d := monus a (succ b) + succ k)
      (by have e' := natEq e; apply deriveNat; ipra_simps; linear_combination e')
    refine .eqTrans ?_ (geI_false hl).eqSymm
    refine (congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) (show C ⊢[PRAAx] monus b a ≐ zero from hz)).eqTrans
      (monus_zero _))).eqTrans ?_
    exact (succ_monus_succ _ _).eqTrans (zero_monus _)
  · have h : (le a b :: Γ) ⊢[PRAAx] le a b := Prf.hyp0
    have e := eq_add_of_le h
    refine congrMonus (.eqRefl _) ?_
    refine .eqSymm ((congrMonus (.eqRefl _) e).eqTrans ?_)
    exact (congrMonus (add_comm _ _) (add_comm _ _)).eqTrans (monus_add_add _ _ _)

/-! ## Expectation of the parts -/

section Parts

variable (w P N : PTm 2)

/-- `thm:expect-parts`: `Ew(X⁺) + Ew(N) = Ew(X⁻) + Ew(P)` (i.e. `E X = E X⁺ − E X⁻`) and
`Ew|X| = Ew(X⁺) + Ew(X⁻)`. -/
theorem expect_parts (M x : PTm n) :
    Γ ⊢[PRAAx] (Ew w (monus P N) M x + Ew w N M x ≐ Ew w (monus N P) M x + Ew w P M x) ⋏
      (Ew w (monus P N + monus N P) M x ≐ Ew w (monus P N) M x + Ew w (monus N P) M x) := by
  refine .andI ?_ (exp_add _ _ _ _ _)
  refine (exp_add w (monus P N) N M x).eqSymm.eqTrans (.eqTrans ?_ (exp_add w (monus N P) P M x))
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_mul', inst2_mul', inst2_add', inst2_add', inst2_monus', inst2_monus']
  exact congrMul (.eqRefl _) (monus_max _ _)

/-- `thm:expect-parts`: `|E X| ≤ E|X|`, cleared: `|Ew P − Ew N| ≤ Ew(X⁺) + Ew(X⁻)`. -/
theorem abs_expect_le (M x : PTm n) :
    Γ ⊢[PRAAx] le (ad (Ew w P M x) (Ew w N M x)) (Ew w (monus P N + monus N P) M x) := by
  refine .orE (le_total (Ew w P M x) (Ew w N M x)) ?_ ?_
  · let C := le (Ew w P M x) (Ew w N M x) :: Γ
    have h2 := natEq (Prf.andE₂ (expect_parts (Γ := C) w P N M x))
    have hz := natEq (show C ⊢[PRAAx] monus (Ew w P M x) (Ew w N M x) ≐ zero from Prf.hyp0)
    have e := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le (Ew w P M x) (Ew w N M x)))
    refine le_of_eq_add (d := Ew w (monus P N) M x + Ew w (monus P N) M x) ?_
    ipra_lc h2 - natEq (Prf.andE₁ (expect_parts (Γ := C) w P N M x)) + e - hz
  · let C := le (Ew w N M x) (Ew w P M x) :: Γ
    have h2 := natEq (Prf.andE₂ (expect_parts (Γ := C) w P N M x))
    have hz := natEq (show C ⊢[PRAAx] monus (Ew w N M x) (Ew w P M x) ≐ zero from Prf.hyp0)
    have e := natEq (eq_add_of_le (Prf.hyp0 : C ⊢[PRAAx] le (Ew w N M x) (Ew w P M x)))
    refine le_of_eq_add (d := Ew w (monus N P) M x + Ew w (monus N P) M x) ?_
    ipra_lc h2 + natEq (Prf.andE₁ (expect_parts (Γ := C) w P N M x)) + e - hz

/-- `thm:nonneg`: `X = P − N ≥ 0` at every outcome gives `E X ≥ 0`, i.e. `Ew N ≤ Ew P`. -/
theorem signed_nonneg {M x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 N (var 0) (Syn.shift x)) (inst2 P (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (Ew w N M x) (Ew w P M x) :=
  exp_mono w N P M x h

/-- `thm:monotone`: `X = P − N ≤ Y = P' − N'` at every outcome (`P + N' ≤ P' + N`) gives `E X ≤ E Y`,
i.e. `Ew P + Ew N' ≤ Ew P' + Ew N`. -/
theorem signed_mono (P' N' : PTm 2) {M x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (inst2 P (var 0) (Syn.shift x) + inst2 N' (var 0) (Syn.shift x))
        (inst2 P' (var 0) (Syn.shift x) + inst2 N (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (Ew w P M x + Ew w N' M x) (Ew w P' M x + Ew w N M x) := by
  refine le_congr (exp_add _ _ _ _ _) (exp_add _ _ _ _ _) (exp_mono w (P + N') (P' + N) M x (.allI (.impI ?_)))
  rw [inst2_add', inst2_add']
  exact Prf.impE h.allOpen.wk Prf.hyp0

/-- `thm:signed-tail`: for `−A ≤ X ≤ B` (`X⁺ ≤ B`, `X⁻ ≤ A`),
`E X = ∑_{k<B} P(X > k) − ∑_{k<A} P(X⁻ > k)`, cleared:
`Ew P + ∑_{k<A} ∑_i w_i [X⁻_i > k] = ∑_{k<B} ∑_i w_i [X⁺_i > k] + Ew N`
(and `[X⁻ > k] = [X ≤ −k−1]` by `neg_tail_pt`). -/
theorem signed_tail {M A B x : PTm n}
    (hB : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 (monus P N) (var 0) (Syn.shift x)) (Syn.shift B)))
    (hA : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ le (inst2 (monus N P) (var 0) (Syn.shift x)) (Syn.shift A))) :
    Γ ⊢[PRAAx] Ew w P M x + ap2 (sumF (pB (tlA w (monus N P)))) A (pairT M x) ≐
      ap2 (sumF (pB (tlA w (monus P N)))) B (pairT M x) + Ew w N M x := by
  ipra_lc -natEq (Prf.andE₁ (expect_parts (Γ := Γ) w P N M x)) + natEq (tail_sum w (monus P N) hB) -
    natEq (tail_sum w (monus N P) hA)

end Parts

/-! ## Finite linear combinations -/

section Lin

variable (w a : PTm 2) (X : PTm 3)

/-- A body read at `snd` of the parameter. -/
abbrev sbq (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_sbq (f : PTm 2) (v z : PTm n) : inst2 (sbq f) v z = inst2 f v (sndT z) := by
  simp only [inst2, sbq, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- `a(j, x) X(i, j, x)`, over `0 = i`, `1 = j`, `2 = x`. -/
def lcB : PTm 3 := Syn.subst ![var 1, var 2] a * X
/-- `w(i, x) X(i, j, x)`. -/
def wXB : PTm 3 := Syn.subst ![var 0, var 2] w * X
/-- `w(i, x) a(j, x) X(i, j, x)`. -/
def eB : PTm 3 := Syn.subst ![var 0, var 2] w * lcB a X

theorem inst3_lcB (i j x : PTm n) : inst3 (lcB a X) i j x = inst2 a j x * inst3 X i j x := by
  simp only [inst3, inst2, lcB, PTm.subst_mul, Syn.subst_subst]
  congr 1; congr 1; funext k; fin_cases k <;> rfl

theorem inst3_wXB (i j x : PTm n) : inst3 (wXB w X) i j x = inst2 w i x * inst3 X i j x := by
  simp only [inst3, inst2, wXB, PTm.subst_mul, Syn.subst_subst]
  congr 1; congr 1; funext k; fin_cases k <;> rfl

theorem inst3_eB (i j x : PTm n) : inst3 (eB w a X) i j x = inst2 w i x * inst3 (lcB a X) i j x := by
  simp only [inst3, inst2, eB, PTm.subst_mul, Syn.subst_subst]
  congr 1; congr 1; funext k; fin_cases k <;> rfl

/-- `cor:finite-linearity`: `∑_{i<M} w_i ∑_{j<r} a_j X_j(i) = ∑_{j<r} a_j ∑_{i<M} w_i X_j(i)`,
i.e. `E[∑_j a_j X_j] = ∑_j a_j E[X_j]` after clearing `W`. -/
theorem finite_linearity (M r x : PTm n) :
    Γ ⊢[PRAAx] Ew (sbq w) (oB (lcB a X)) M (pairT r x) ≐ ap2 (sumF (sbq a * pB (wXB w X))) r (pairT M x) := by
  have r1 : Γ ⊢[PRAAx] dsum (eB w a X) M r x ≐ Ew (sbq w) (oB (lcB a X)) M (pairT r x) := by
    refine dsum_rows (eB w a X) (sbq w * oB (lcB a X)) M r x (pairT r x) (.allI (.impI ?_))
    simp only [shift_pairT, inst2_mul', inst2_sbq, inst2_oB]
    refine (sum_scale (rowB (eB w a X)) (rowB (lcB a X)) (Syn.shift r) (inst2 w (var 0) (Syn.shift x))
      (pairT (var 0) (Syn.shift x)) (pairT (var 0) (Syn.shift x)) (.allI (.impI ?_))).eqTrans ?_
    · simp only [shift_pairT, shift_inst2]
      refine (row_pt _ _ _ _).eqTrans ?_
      rw [inst3_eB]
      exact congrMul (.eqRefl _) (row_pt _ _ _ _).eqSymm
    · exact congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _).eqSymm)
        (congrAp2 (sumF _) (fst_pair _ _).eqSymm (congrPairT (.eqRefl _) (snd_pair _ _).eqSymm))
  have r2 := fubini (Γ := Γ) (eB w a X) M r x
  have r3 : Γ ⊢[PRAAx] ap2 (sumF (pB (eB w a X))) r (pairT M x) ≐
      ap2 (sumF (sbq a * pB (wXB w X))) r (pairT M x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, inst2_mul', inst2_sbq, inst2_pB]
    refine sum_scale (colB (eB w a X)) (colB (wXB w X)) _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pairT, shift_inst2]
    refine (col_pt _ _ _ _).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (col_pt _ _ _ _).eqSymm))
    rw [inst3_eB, inst3_lcB, inst3_wXB]
    ipra_ring
  exact r1.eqSymm.eqTrans (r2.eqTrans r3)

end Lin

end LeanProofs.IPRA.Probability.SignedParts
