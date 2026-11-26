import IPRADerivations.AnalyticNumberTheory.FloorTelescope
import IPRADerivations.AnalyticNumberTheory.DivisorHyperbola
import IPRADerivations.Foundations.LatticeCount
import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.SumSplit
import IPRADerivations.DiophantineNumberTheory.KhinchinBlock
import IPRADerivations.Core.Header

/-!
# The fourth-root layer-cake sum (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
the error `80 Σ_{d≤x} √(x/d)(log(x/d) + 1)` is bounded by `1280x` through `log z + 1 ≤ 4z^{1/4}` and
`Σ_{d≤x} d^{−3/4} ≤ 4x^{1/4}`. The integer counterpart, with the fourth root `qr(z) = ⌊√⌊√z⌋⌋`, is

  `Σ_{d<x} (qr(⌊x/(d+1)⌋) + 1)³ ≤ 15x`                                  (`fourth_root_sum`),

since `√z (log z + 1) ≲ (qr(z) + 1)³`. The proof is a layer-cake count:

* `(r + 1)³ = Σ_{j≤r} (3j² + 3j + 1)` (`FloorTelescope.cube_sum`), so the sum is
  `Σ_d Σ_{j≤x} [j ≤ r_d](3j² + 3j + 1)` (`row_bound`);
* exchanging the two finite sums (`Core/Fubini`), the column `j = J ≥ 1` counts the `d` with
  `J ≤ qr(⌊x/(d+1)⌋)`, which forces `J⁴(d + 1) ≤ x`, i.e. `d < ⌊x/J⁴⌋` (`ind_cnt`, `LatticeCount.exact_count`);
* `(3J² + 3J + 1)⌊x/J⁴⌋ ≤ 7⌊x/J²⌋` (`col_tail`), the column `j = 0` is at most `x` (`col_zero`), and
  `Σ_J ⌊x/J²⌋ ≤ 2x` (`FloorTelescope.floor_square_sum`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.FloorTelescope (cB inst2_cB cube_sum qB inst2_qB floor_square_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop (quo_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola (quo_le_self sg_one)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (pos_of_lt_zero)
open LeanProofs.IPRA.Foundations.LatticeCount (icB icS exact_count)
open LeanProofs.IPRA.Foundations.IntervalCover (cnt)
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin1)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The integer fourth root `⌊√⌊√z⌋⌋`. -/
abbrev qr (z : PTm n) : PTm n := isqrt (isqrt z)
/-- `[j ≤ r]`. -/
abbrev ind (j r : PTm n) : PTm n := monus one (monus j r)
/-- `3j² + 3j + 1`. -/
abbrev cT (j : PTm n) : PTm n := succ (succ two * (j * j + j))
/-- `J⁴` for `J = i + 1`. -/
abbrev Q4 (i : PTm n) : PTm n := (succ i * succ i) * (succ i * succ i)

/-! ## Indicators -/

theorem ind_one {j r : PTm n} (h : Γ ⊢[PRAAx] le j r) : Γ ⊢[PRAAx] ind j r ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem ind_zero {j r : PTm n} (h : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx] ind j r ≐ zero := by
  have e := eq_add_of_le h
  have q : Γ ⊢[PRAAx] succ r + monus j (succ r) ≐ succ (monus j (succ r)) + r := by
    ipra_ring
  have m : Γ ⊢[PRAAx] monus j r ≐ succ (monus j (succ r)) :=
    (congrMonus (e.eqTrans q) (.eqRefl r)).eqTrans (add_monus _ r)
  exact (congrMonus (.eqRefl _) m).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

theorem ind_le_one (j r : PTm n) : Γ ⊢[PRAAx] le (ind j r) one := by
  refine .orE (lt_or_le r j) ?_ ?_
  · exact le_congr (ind_zero Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · exact le_congr (ind_one Prf.hyp0).eqSymm (.eqRefl _) (le_refl _)

theorem cnt_one {q d : PTm n} (h : Γ ⊢[PRAAx] lt d q) : Γ ⊢[PRAAx] cnt zero q d ≐ one := by
  have e := eq_add_of_le h
  have m : Γ ⊢[PRAAx] le one (monus q d) := by
    refine le_of_eq_add (d := monus q (succ d)) ?_
    have q' : Γ ⊢[PRAAx] succ d + monus q (succ d) ≐ (one + monus q (succ d)) + d := by
      ipra_ring
    exact (congrMonus (e.eqTrans q') (.eqRefl d)).eqTrans (add_monus _ d)
  have a : Γ ⊢[PRAAx] monus one (monus zero d) ≐ one :=
    (congrMonus (.eqRefl _) (zero_monus d)).eqTrans (monus_zero _)
  exact (congrMul a (sg_one m)).eqTrans (by ipra_ring)

/-- `J ≤ ⌊√⌊√z⌋⌋ → J⁴ ≤ z`. -/
theorem qr_pow {J z : PTm n} (h : Γ ⊢[PRAAx] le J (qr z)) : Γ ⊢[PRAAx] le ((J * J) * (J * J)) z :=
  le_trans (sq_le_sq (le_trans (sq_le_sq h) (isqrt_le (isqrt z)))) (isqrt_le z)

/-- `⌊√w⌋ ≤ w`. -/
theorem isqrt_le_self (w : PTm n) : Γ ⊢[PRAAx] le (isqrt w) w := by
  refine .orE (lt_or_le zero (isqrt w)) ?_ ?_
  · have t := le_scale (isqrt w) (Prf.hyp0 : (lt zero (isqrt w) :: Γ) ⊢[PRAAx] le one (isqrt w))
    exact le_trans (by ipra_le sl t) (isqrt_le w)
  · exact le_trans Prf.hyp0 (zero_le _)

theorem Q4_pos (i : PTm n) : Γ ⊢[PRAAx] Q4 i ≐ succ (pred (Q4 i)) :=
  pos_of_lt_zero (le_of_eq_add
    (d := i * (i * (i * i)) + two * two * (i * (i * i)) + (two * two + two) * (i * i) + two * two * i)
    (by ipra_ring))

/-- `[J ≤ qr(⌊x/(d+1)⌋)] ≤ [d < ⌊x/J⁴⌋]` for `J = i + 1`. -/
theorem ind_cnt (i d x : PTm n) :
    Γ ⊢[PRAAx] le (ind (succ i) (qr (quo x (succ d)))) (cnt zero (quo x (Q4 i)) d) := by
  refine .orE (lt_or_le (qr (quo x (succ d))) (succ i)) ?_ ?_
  · exact le_congr (ind_zero Prf.hyp0).eqSymm (.eqRefl _) (zero_le _)
  · let Δ := le (succ i) (qr (quo x (succ d))) :: Γ
    have h4 : Δ ⊢[PRAAx] le (Q4 i) (quo x (succ d)) := qr_pow Prf.hyp0
    have t1 : Δ ⊢[PRAAx] le (Q4 i * succ d) x :=
      le_trans (mul_le_mul_right (succ d) h4) (quo_mul_le (x := x) (congrSucc (pred_succ d).eqSymm))
    have t2 : Δ ⊢[PRAAx] le (succ d) (quo x (Q4 i)) := le_quo_of_mul_le (Q4_pos i) t1
    exact le_congr (ind_one Prf.hyp0).eqSymm (cnt_one t2).eqSymm (le_refl _)

/-! ## The layer-cake body and the rows -/

/-- `a(d, j, x) = [j ≤ qr(⌊x/(d+1)⌋)] (3j² + 3j + 1)`. -/
def a3 : PTm 3 :=
  monus one (monus (var 1) (isqrt (isqrt (quo (var 2) (succ (var 0)))))) * succ (succ two * (var 1 * var 1 + var 1))

theorem inst3_a3 (d j x : PTm n) : inst3 a3 d j x = ind j (qr (quo x (succ d))) * cT j := by simp [inst3, a3]

theorem a3_at (d j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB a3) j (pairT d x) ≐ ind j (qr (quo x (succ d))) * cT j := by
  rw [inst2_rowB, inst3_a3]
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _)
    (congrAp1 isqrtF (congrAp1 isqrtF (congrAp2 quoF (snd_pair _ _) (congrSucc (fst_pair _ _))))))) (.eqRefl _)

/-- One row: `(r + 1)³ ≤ Σ_{j≤x} [j ≤ r](3j² + 3j + 1)` for `r = qr(⌊x/(d+1)⌋)`. -/
theorem row_bound (d x : PTm n) :
    Γ ⊢[PRAAx] le (succ (qr (quo x (succ d))) * succ (qr (quo x (succ d))) * succ (qr (quo x (succ d))))
      (ap2 (sumF (rowB a3)) (succ x) (pairT d x)) := by
  have hr : Γ ⊢[PRAAx] le (qr (quo x (succ d))) x :=
    le_trans (isqrt_le_self _) (le_trans (isqrt_le_self _) (quo_le_self d x))
  have c := cube_sum (Γ := Γ) (succ (qr (quo x (succ d)))) x
  have p1 : Γ ⊢[PRAAx] le (ap2 (sumF cB) (succ (qr (quo x (succ d)))) x)
      (ap2 (sumF (rowB a3)) (succ (qr (quo x (succ d)))) (pairT d x)) := by
    refine sum_le_params cB (rowB a3) x (pairT d x) _ (.allI ?_)
    rw [show Syn.shift (succ (qr (quo x (succ d)))) = succ (qr (quo (Syn.shift x) (succ (Syn.shift d)))) by
      simp [Syn.shift]]
    refine .impI ?_
    rw [inst2_cB, shift_pairT]
    have hj : (lt (var 0) (succ (qr (quo (Syn.shift x) (succ (Syn.shift d))))) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (var 0) (qr (quo (Syn.shift x) (succ (Syn.shift d)))) :=
      (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact le_congr (by ipra_ring) ((a3_at _ _ _).eqTrans
      (congrMul (ind_one hj) (.eqRefl _))).eqSymm (le_refl (one * cT (var 0)))
  have hRx : Γ ⊢[PRAAx] le (succ (qr (quo x (succ d)))) (succ x) := (succ_monus_succ _ _).eqTrans hr
  have sp := sum_split (Γ := Γ) (rowB a3) (succ (qr (quo x (succ d))))
    (monus (succ x) (succ (qr (quo x (succ d))))) (pairT d x)
  have er := congrAp2 (Γ := Γ) (sumF (rowB a3)) (eq_add_of_le hRx) (.eqRefl (pairT d x))
  exact le_congr c (er.eqTrans sp).eqSymm (le_trans p1 (le_add_right _ _))

/-! ## The columns -/

theorem cT_succ_le (i : PTm n) : Γ ⊢[PRAAx] le (cT (succ i)) (succ (two * two + two) * (succ i * succ i)) :=
  le_of_eq_add (d := two * two * (i * i) + succ (two * two) * i) (by ipra_ring)

theorem inst2_icB' (d z : PTm n) : inst2 icB d z = cnt (fstT z) (sndT z) d := by simp [inst2]

theorem congrCnt {lo lo' hi hi' c : PTm n} (h₁ : Γ ⊢[PRAAx] lo ≐ lo') (h₂ : Γ ⊢[PRAAx] hi ≐ hi') :
    Γ ⊢[PRAAx] cnt lo hi c ≐ cnt lo' hi' c :=
  congrMul (congrMonus (.eqRefl _) (congrMonus h₁ (.eqRefl _)))
    (LeanProofs.IPRA.AnalyticNumberTheory.Mobius.congrSg (congrMonus h₂ (.eqRefl _)))

theorem congrCT {j j' : PTm n} (h : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] cT j ≐ cT j' :=
  congrSucc (congrMul (.eqRefl _) (congrAdd (congrMul h h) h))

/-- The column point: `1 · a(d, I + 1, X) ≤ (3J² + 3J + 1) [d < ⌊X/J⁴⌋]`. -/
theorem col_pt (d I X : PTm n) :
    Γ ⊢[PRAAx] le (one * inst2 (colB a3) d (pairT (succ I) X))
      (cT (succ I) * inst2 icB d (pairT zero (quo X (Q4 I)))) := by
  rw [inst2_colB, inst3_a3, inst2_icB']
  have e1 := fst_pair (Γ := Γ) (succ I) X
  have e2 := snd_pair (Γ := Γ) (succ I) X
  have L : Γ ⊢[PRAAx] one * (ind (fstT (pairT (succ I) X)) (qr (quo (sndT (pairT (succ I) X)) (succ d))) *
      cT (fstT (pairT (succ I) X))) ≐ ind (succ I) (qr (quo X (succ d))) * cT (succ I) :=
    (one_mul _).eqTrans (congrMul (congrMonus (.eqRefl _) (congrMonus e1
      (congrAp1 isqrtF (congrAp1 isqrtF (congrAp2 quoF e2 (.eqRefl _)))))) (congrCT e1))
  have R : Γ ⊢[PRAAx] cT (succ I) * cnt (fstT (pairT zero (quo X (Q4 I)))) (sndT (pairT zero (quo X (Q4 I)))) d ≐
      cT (succ I) * cnt zero (quo X (Q4 I)) d :=
    congrMul (.eqRefl _) (congrCnt (fst_pair _ _) (snd_pair _ _))
  exact le_congr L.eqSymm R.eqSymm (le_congr (.eqRefl _) (mul_comm _ _)
    (mul_le_mul_right (cT (succ I)) (ind_cnt I d X)))

theorem shift_one' : Syn.shift (one : PTm n) = one := by simp [Syn.shift]
theorem shift_zero' : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
theorem shift_cT (I : PTm n) : Syn.shift (cT (succ I)) = cT (succ (Syn.shift I)) := by simp [Syn.shift]
theorem shift_q4 (I X : PTm n) : Syn.shift (quo X (Q4 I)) = quo (Syn.shift X) (Q4 (Syn.shift I)) := by
  simp [Syn.shift]

/-- The column `J = I + 1`: `Σ_{d<X} a(d, J, X) ≤ 7⌊X/J²⌋`. -/
theorem col_tail (I X : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF (colB a3)) X (pairT (succ I) X)) (succ (two * two + two) * quo X (succ I * succ I)) := by
  have s := sum_le_lin1 (Γ := Γ) (colB a3) icB one (cT (succ I)) (pairT (succ I) X) (pairT zero (quo X (Q4 I))) X
    (.allI (.impI (by
      rw [shift_pairT, shift_pairT, shift_one', shift_cT, shift_zero', shift_q4, shift_succ'']
      exact col_pt _ _ _)))
  have hq : Γ ⊢[PRAAx] le (quo X (Q4 I)) X :=
    le_congr (congrAp2 quoF (.eqRefl _) (Q4_pos I)).eqSymm (.eqRefl _) (quo_le_self _ X)
  have eic := natEq ((exact_count (Γ := Γ) X zero (quo X (Q4 I)) hq).eqTrans (monus_zero _))
  have c1 := le_scale (quo X (Q4 I)) (cT_succ_le (Γ := Γ) I)
  have qm := quo_mul_le (Γ := Γ) (x := X) (Q4_pos I)
  have qq : Γ ⊢[PRAAx] le (succ I * succ I * quo X (Q4 I)) (quo X (succ I * succ I)) := by
    refine le_quo_of_mul_le (FloorTelescope.sq_pos I) ?_
    exact le_congr (by ipra_ring) (.eqRefl _) qm
  ipra_le sl s + sl c1 + 7 * sl qq with (3 * 𝔞 I * 𝔞 I + 9 * 𝔞 I + 7) * eic

/-- The column `j = 0`: `Σ_{d<X} a(d, 0, X) ≤ X`. -/
theorem col_zero (X : PTm n) : Γ ⊢[PRAAx] le (ap2 (sumF (colB a3)) X (pairT zero X)) X := by
  have s := sum_le_const (Γ := Γ) (colB a3) (N := X) (L := one) (x := pairT zero X) (.allI (.impI (by
    rw [shift_pairT, shift_zero', shift_one', inst2_colB, inst3_a3]
    have e := fst_pair (Γ := lt (var 0) (Syn.shift X) :: Γ.map Fm.shift) zero (Syn.shift X)
    have i1 := ind_le_one (Γ := lt (var 0) (Syn.shift X) :: Γ.map Fm.shift) (fstT (pairT zero (Syn.shift X)))
      (qr (quo (sndT (pairT zero (Syn.shift X))) (succ (var 0))))
    have ec := natEq ((congrCT e).eqTrans (by ipra_ring :
      (lt (var 0) (Syn.shift X) :: Γ.map Fm.shift) ⊢[PRAAx] cT zero ≐ one))
    ipra_le sl i1 with 𝔞 (ind (fstT (pairT zero (Syn.shift X)))
      (qr (quo (sndT (pairT zero (Syn.shift X))) (succ (var 0))))) * ec)))
  exact le_congr (.eqRefl _) (by ipra_ring) s

/-! ## The sum -/

/-- `(qr(⌊x/(d+1)⌋) + 1)³`. -/
abbrev WB : PTm 2 :=
  succ (isqrt (isqrt (quo (var 1) (succ (var 0))))) * succ (isqrt (isqrt (quo (var 1) (succ (var 0))))) *
    succ (isqrt (isqrt (quo (var 1) (succ (var 0)))))

theorem inst2_WB (d x : PTm n) : inst2 WB d x =
    succ (qr (quo x (succ d))) * succ (qr (quo x (succ d))) * succ (qr (quo x (succ d))) := by simp [inst2]

/-- `7 ⌊x/(j+1)²⌋`. -/
abbrev TB : PTm 2 := succ (two * two + two) * quo (var 1) (succ (var 0) * succ (var 0))

theorem inst2_TB (j x : PTm n) : inst2 TB j x = succ (two * two + two) * quo x (succ j * succ j) := by simp [inst2]

theorem shift_seven : Syn.shift (succ (two * two + two) : PTm n) = succ (two * two + two) := by simp [Syn.shift]

/-- `Σ_{d<x} (qr(⌊x/(d+1)⌋) + 1)³ ≤ 15x`. -/
theorem fourth_root_sum (x : PTm n) :
    Γ ⊢[PRAAx] le (ap2 (sumF WB) x x) (x + succ (two * two + two) * (two * x)) := by
  have s1 := sum_le_params (Γ := Γ) WB (oB a3) x (pairT (succ x) x) x (.allI (.impI (by
    rw [inst2_WB, shift_pairT, shift_succ'']
    exact le_congr (.eqRefl _) (oB_at a3 _ _ _).eqSymm (row_bound _ _))))
  have e2 := natEq (fubini (Γ := Γ) a3 x (succ x) x)
  have e3 := natEq (congrAp2 (Γ := Γ) (sumF (pB a3)) (by ipra_ring : Γ ⊢[PRAAx] succ x ≐ one + x)
    (.eqRefl (pairT x x)))
  have e4 := natEq (sum_split (Γ := Γ) (pB a3) one x (pairT x x))
  have e5 := natEq (sum_succ' (Γ := Γ) (pB a3) zero (pairT x x))
  have e6 := natEq (sum_zero (Γ := Γ) (pB a3) (pairT x x))
  have e7 := natEq ((by rw [inst2_pB]; exact congrAp2 (sumF (colB a3)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _)) :
    Γ ⊢[PRAAx] inst2 (pB a3) zero (pairT x x) ≐ ap2 (sumF (colB a3)) x (pairT zero x)))
  have hz := col_zero (Γ := Γ) x
  have ht := sum_le_params (Γ := Γ) (offB (pB a3)) TB (pairT one (pairT x x)) x x (.allI (.impI (by
    rw [inst2_offB, inst2_pB, inst2_TB, shift_pairT, shift_pairT, shift_one']
    have E : (lt (var 0) (Syn.shift x) :: Γ.map Fm.shift) ⊢[PRAAx]
        ap2 (sumF (colB a3)) (fstT (sndT (pairT one (pairT (Syn.shift x) (Syn.shift x)))))
          (pairT (fstT (pairT one (pairT (Syn.shift x) (Syn.shift x))) + var 0)
            (sndT (sndT (pairT one (pairT (Syn.shift x) (Syn.shift x)))))) ≐
        ap2 (sumF (colB a3)) (Syn.shift x) (pairT (succ (var 0)) (Syn.shift x)) :=
      congrAp2 (sumF (colB a3)) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
        (congrPairT ((congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans (by ipra_ring))
          ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))
    exact le_congr E.eqSymm (.eqRefl _) (col_tail _ _))))
  have e8 := natEq (sum_scale (Γ := Γ) TB qB x (succ (two * two + two)) x x (.allI (.impI (by
    rw [inst2_TB, inst2_qB, shift_seven]; exact .eqRefl _))))
  have e9 := natEq (sum_succ' (Γ := Γ) qB x x)
  have hfs := floor_square_sum (Γ := Γ) x x
  ipra_le sl s1 + sl hz + sl ht + 7 * sl hfs + 7 * 𝔞 (inst2 qB x x) with
    e2 + e3 + e4 + e5 + e6 + e7 + e8 - 7 * e9

end LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum
