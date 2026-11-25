import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Combinatorics.LegendreFact
import IPRADerivations.Core.LinearCombination

/-!
# The middle-interval theorem for sorted data, and the odd and even median formulas

Packet: `probability/median_ipra_constructive_proofs`, Theorem `thm:middle-interval` (both
directions, for sorted data) and Corollary `cor:odd-even`.

The data `y(i, p)` (`i < N`) is sorted: `y_i ≤ y_{i+1}` whenever `i + 1 < N` (`Sorted`), which gives
`y_i ≤ y_j` for `i ≤ j < N` (`mono`, by quantifier-free induction on `j − i`). The counts
`B(t) = #{i < N : y_i < t}`, `A(t) = #{i < N : t < y_i}` are those of `MedianCounts`.

* `count_ge`: `#{i < N : c ≤ i} + c = N` for `c ≤ N` (with `LegendreFact.count_lt`,
  `#{i < N : i < c} = c`);
* the four count bounds: `t ≤ y_u ⟹ B(t) ≤ u` (`below_le`), `y_ℓ ≤ t ⟹ A(t) + ℓ + 1 ≤ N` (`above_le`),
  `t < y_ℓ ⟹ N ≤ A(t) + ℓ` (`above_ge`) and `y_u < t ⟹ u + 1 ≤ B(t)` (`below_ge`);
* `between_med`, `med_between` (`thm:middle-interval`): for indices `ℓ, u < N` with
  `2u ≤ N ≤ 2ℓ + 2` resp. `2ℓ < N < 2u + 2`, `y_ℓ ≤ t ≤ y_u` iff `t` is a balance median
  (`2B(t) ≤ N`, `2A(t) ≤ N`); both parity patterns below satisfy all four inequalities;
* `odd_med`, `odd_unique` (`cor:odd-even`, odd case): for `N = 2q + 1`, `ℓ = u = q` and the median is
  exactly `y_q`;
* `even_med`, `even_between`, `doubled_median` (`cor:odd-even`, even case): for `N = 2q`, `q ≥ 1`,
  `ℓ = q − 1`, `u = q`, the medians are exactly `[y_{q−1}, y_q]`, and the doubled conventional
  median `M = y_{q−1} + y_q` satisfies `2 y_{q−1} ≤ M ≤ 2 y_q`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.MedianSorted

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sg_lt sg_le)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (sg_le_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Expectation (le_zero_of)
open LeanProofs.IPRA.Probability.Variance (sum_one)
open LeanProofs.IPRA.Probability.MedianCounts (belowB aboveB Bc Ac below_pt above_pt isMed)
open LeanProofs.IPRA.Combinatorics.LegendreFact (ltB inst2_ltB inst2_one2 count_lt)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Counting `c ≤ j` -/

/-- `[c ≤ j]`, over `0 = j`, `1 = c`. -/
abbrev geB : PTm 2 := sg (monus (succ (var 0)) (var 1))

theorem inst2_geB {m : ℕ} (i y : PTm m) : inst2 geB i y = sg (monus (succ i) y) := by
  simp only [inst2, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var]
  rfl

/-- `[c ≤ i] + [i < c] = 1`. -/
theorem ge_lt_bits (i c : PTm n) : Γ ⊢[PRAAx] sg (monus (succ i) c) + sg (monus c i) ≐ one := by
  refine .orE (lt_or_le i c) ?_ ?_
  · exact (congrAdd (sg_le Prf.hyp0) (sg_lt Prf.hyp0)).eqTrans (by ipra_ring)
  · have h : (le c i :: Γ) ⊢[PRAAx] lt c (succ i) := (succ_monus_succ _ _).eqTrans Prf.hyp0
    exact (congrAdd (sg_lt h) (sg_le Prf.hyp0)).eqTrans (by ipra_ring)

/-- `#{j < N : c ≤ j} + c = N` for `c ≤ N`. -/
theorem count_ge {c N : PTm n} (h : Γ ⊢[PRAAx] le c N) : Γ ⊢[PRAAx] ap2 (sumF geB) N c + c ≐ N := by
  have e : Γ ⊢[PRAAx] ap2 (sumF (addBody geB ltB)) N c ≐ ap2 (sumF (one : PTm 2)) N c := by
    refine sum_congr_bounded _ (one : PTm 2) c c N (.allI (.impI ?_))
    rw [inst2_addBody, inst2_one2, inst2_geB, inst2_ltB]
    exact ge_lt_bits _ _
  exact (congrAdd (.eqRefl _) (count_lt h).eqSymm).eqTrans
    ((sum_add geB ltB N c).eqSymm.eqTrans (e.eqTrans (sum_one N c)))

/-! ## Sorted data -/

section Sorted

variable (X : PTm 2)

/-- `y_i ≤ y_{i+1}` whenever `i + 1 < N`. -/
abbrev Sorted (N p : PTm n) : Fm PTm n :=
  Fm.all (lt (succ (var 0)) (Syn.shift N) ⟶ le (inst2 X (var 0) (Syn.shift p)) (inst2 X (succ (var 0)) (Syn.shift p)))

theorem sorted_step {N p k : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hk : Γ ⊢[PRAAx] lt (succ k) N) :
    Γ ⊢[PRAAx] le (inst2 X k p) (inst2 X (succ k) p) := by
  have h := Prf.allE k hS
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h
  exact Prf.impE h hk

theorem sorted_shift {N p : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) :
    Γ.map Fm.shift ⊢[PRAAx] Sorted X (Syn.shift N) (Syn.shift p) := by
  simpa [Sorted, Fm.shift, Syn.shift, Syn.subst_subst] using hS.shift

theorem le_shift {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e

theorem shift_inst2 (a b : PTm n) : Syn.shift (inst2 X a b) = inst2 X (Syn.shift a) (Syn.shift b) := by
  simp only [inst2, Syn.shift, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> simp

/-- `y_i ≤ y_{i+d}` for `i + d < N`. -/
theorem mono_add {N p : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (i d : PTm n) (h : Γ ⊢[PRAAx] lt (i + d) N) :
    Γ ⊢[PRAAx] le (inst2 X i p) (inst2 X (i + d) p) := by
  have hS' := sorted_shift X hS
  have hall : Γ ⊢[PRAAx] Fm.all (lt (Syn.shift i + var 0) (Syn.shift N) ⟶
      le (inst2 X (Syn.shift i) (Syn.shift p)) (inst2 X (Syn.shift i + var 0) (Syn.shift p))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_lt, PTm.subst_add, subst_inst2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (le_congr (.eqRefl _) (congrInst2 X (add_zero _).eqSymm (.eqRefl _)) (le_refl _))
    · simp only [Fm.subst_imp, subst_le, subst_lt, PTm.subst_add, subst_inst2, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      let C := lt (Syn.shift i + succ (var 0)) (Syn.shift N) ::
        (lt (Syn.shift i + var 0) (Syn.shift N) ⟶
          le (inst2 X (Syn.shift i) (Syn.shift p)) (inst2 X (Syn.shift i + var 0) (Syn.shift p))) :: Γ.map Fm.shift
      have hl : C ⊢[PRAAx] lt (Syn.shift i + succ (var 0)) (Syn.shift N) := Prf.hyp0
      have e : C ⊢[PRAAx] Syn.shift i + succ (var 0) ≐ succ (Syn.shift i + var 0) := by
        ipra_ring
      have hl' : C ⊢[PRAAx] lt (succ (Syn.shift i + var 0)) (Syn.shift N) := lt_congr e (.eqRefl _) hl
      have hl0 : C ⊢[PRAAx] lt (Syn.shift i + var 0) (Syn.shift N) := le_of_lt hl'
      have ih := Prf.impE Prf.hyp1 hl0
      have st := sorted_step X hS'.wk.wk hl'
      exact le_trans ih (le_congr (.eqRefl _) (congrInst2 X e.eqSymm (.eqRefl _)) st)
  have h' := Prf.allE d hall
  simp only [Fm.subst_imp, subst_le, subst_lt, PTm.subst_add, subst_inst2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h'
  exact Prf.impE h' h

/-- Sorted data is monotone: `y_i ≤ y_j` for `i ≤ j < N`. -/
theorem mono {N p i j : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hij : Γ ⊢[PRAAx] le i j) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] le (inst2 X i p) (inst2 X j p) := by
  have e := eq_add_of_le hij
  have m := mono_add X hS i (monus j i) (lt_congr e (.eqRefl _) hj)
  exact le_congr (.eqRefl _) (congrInst2 X e.eqSymm (.eqRefl _)) m

/-! ## The four count bounds -/

theorem pt_below_le {N p t u i : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hi : Γ ⊢[PRAAx] lt i N)
    (ht : Γ ⊢[PRAAx] le t (inst2 X u p)) : Γ ⊢[PRAAx] le (sg (monus t (inst2 X i p))) (sg (monus u i)) := by
  refine .orE (lt_or_le i u) ?_ ?_
  · exact le_congr (.eqRefl _) (sg_lt Prf.hyp0).eqSymm (sg_le_one _)
  · exact le_zero_of (sg_le (le_trans ht.wk (mono X hS.wk Prf.hyp0 hi.wk)))

/-- `t ≤ y_u ⟹ B(t) ≤ u`, for `u ≤ N`. -/
theorem below_le {N p t u : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hu : Γ ⊢[PRAAx] le u N)
    (ht : Γ ⊢[PRAAx] le t (inst2 X u p)) : Γ ⊢[PRAAx] le (Bc X N t p) u := by
  refine le_congr (.eqRefl _) (count_lt hu) (sum_le_params (belowB X) ltB (pairT t p) u N (.allI (.impI ?_)))
  have ht' := le_shift ht
  rw [shift_inst2] at ht'
  rw [shift_pairT, inst2_ltB]
  exact le_congr (below_pt X _ _ _).eqSymm (.eqRefl _) (pt_below_le X (sorted_shift X hS).wk Prf.hyp0 ht'.wk)

theorem pt_above_le {N p t l i : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hl : Γ ⊢[PRAAx] lt l N)
    (ht : Γ ⊢[PRAAx] le (inst2 X l p) t) :
    Γ ⊢[PRAAx] le (sg (monus (inst2 X i p) t)) (sg (monus (succ i) (succ l))) := by
  refine .orE (lt_or_le l i) ?_ ?_
  · have h : (lt l i :: Γ) ⊢[PRAAx] lt (succ l) (succ i) := (succ_monus_succ _ _).eqTrans Prf.hyp0
    exact le_congr (.eqRefl _) (sg_lt h).eqSymm (sg_le_one _)
  · exact le_zero_of (sg_le (le_trans (mono X hS.wk Prf.hyp0 hl.wk) ht.wk))

/-- `y_ℓ ≤ t ⟹ A(t) + ℓ + 1 ≤ N`, for `ℓ < N`. -/
theorem above_le {N p t l : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hl : Γ ⊢[PRAAx] lt l N)
    (ht : Γ ⊢[PRAAx] le (inst2 X l p) t) : Γ ⊢[PRAAx] le (Ac X N t p + succ l) N := by
  have s : Γ ⊢[PRAAx] le (Ac X N t p) (ap2 (sumF geB) N (succ l)) := by
    refine sum_le_params (aboveB X) geB (pairT t p) (succ l) N (.allI (.impI ?_))
    have ht' := le_shift ht
    rw [shift_inst2] at ht'
    have hs : Syn.shift (succ l) = succ (Syn.shift l) := by simp [Syn.shift]
    have hl' := le_shift hl
    rw [hs] at hl'
    rw [shift_pairT, inst2_geB, hs]
    exact le_congr (above_pt X _ _ _).eqSymm (.eqRefl _)
      (pt_above_le (i := var 0) X (sorted_shift X hS).wk hl'.wk ht'.wk)
  exact le_congr (.eqRefl _) (count_ge hl) (add_le_add_right _ s)

theorem pt_above_ge {N p t l i : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hi : Γ ⊢[PRAAx] lt i N)
    (ht : Γ ⊢[PRAAx] lt t (inst2 X l p)) :
    Γ ⊢[PRAAx] le (sg (monus (succ i) l)) (sg (monus (inst2 X i p) t)) := by
  refine .orE (lt_or_le i l) ?_ ?_
  · exact le_zero_of (sg_le Prf.hyp0)
  · exact le_congr (.eqRefl _) (sg_lt (lt_of_lt_of_le ht.wk (mono X hS.wk Prf.hyp0 hi.wk))).eqSymm (sg_le_one _)

/-- `t < y_ℓ ⟹ N ≤ A(t) + ℓ`, for `ℓ ≤ N`. -/
theorem above_ge {N p t l : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hl : Γ ⊢[PRAAx] le l N)
    (ht : Γ ⊢[PRAAx] lt t (inst2 X l p)) : Γ ⊢[PRAAx] le N (Ac X N t p + l) := by
  have s : Γ ⊢[PRAAx] le (ap2 (sumF geB) N l) (Ac X N t p) := by
    refine sum_le_params geB (aboveB X) l (pairT t p) N (.allI (.impI ?_))
    have ht' := le_shift ht
    have hs : Syn.shift (succ t) = succ (Syn.shift t) := by simp [Syn.shift]
    rw [hs, shift_inst2] at ht'
    rw [shift_pairT, inst2_geB]
    exact le_congr (.eqRefl _) (above_pt X _ _ _).eqSymm (pt_above_ge X (sorted_shift X hS).wk Prf.hyp0 ht'.wk)
  exact le_congr (count_ge hl) (.eqRefl _) (add_le_add_right _ s)

theorem pt_below_ge {N p t u i : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hu : Γ ⊢[PRAAx] lt u N)
    (ht : Γ ⊢[PRAAx] lt (inst2 X u p) t) :
    Γ ⊢[PRAAx] le (sg (monus (succ u) i)) (sg (monus t (inst2 X i p))) := by
  refine .orE (lt_or_le i (succ u)) ?_ ?_
  · have hiu : (lt i (succ u) :: Γ) ⊢[PRAAx] le i u := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact le_congr (.eqRefl _) (sg_lt (lt_of_le_of_lt (mono X hS.wk hiu hu.wk) ht.wk)).eqSymm (sg_le_one _)
  · exact le_zero_of (sg_le Prf.hyp0)

/-- `y_u < t ⟹ u + 1 ≤ B(t)`, for `u < N`. -/
theorem below_ge {N p t u : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hu : Γ ⊢[PRAAx] lt u N)
    (ht : Γ ⊢[PRAAx] lt (inst2 X u p) t) : Γ ⊢[PRAAx] le (succ u) (Bc X N t p) := by
  refine le_congr (count_lt hu) (.eqRefl _) (sum_le_params ltB (belowB X) (succ u) (pairT t p) N (.allI (.impI ?_)))
  have hu' := le_shift hu
  have ht' := le_shift ht
  have hs : Syn.shift (succ u) = succ (Syn.shift u) := by simp [Syn.shift]
  have hs' : Syn.shift (succ (inst2 X u p)) = succ (inst2 X (Syn.shift u) (Syn.shift p)) := by
    simp [Syn.shift, shift_inst2]
  rw [hs] at hu'
  rw [hs'] at ht'
  rw [shift_pairT, inst2_ltB, hs]
  exact le_congr (.eqRefl _) (below_pt X _ _ _).eqSymm
    (pt_below_ge (i := var 0) X (sorted_shift X hS).wk hu'.wk ht'.wk)

/-! ## The middle-interval theorem -/

/-- `thm:middle-interval`, sufficiency: if `2u ≤ N ≤ 2ℓ + 2`, every `t ∈ [y_ℓ, y_u]` is a balance median. -/
theorem between_med {N p t l u : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hl : Γ ⊢[PRAAx] lt l N)
    (hu : Γ ⊢[PRAAx] lt u N) (F1 : Γ ⊢[PRAAx] le (two * u) N) (F2 : Γ ⊢[PRAAx] le N (two * l + two))
    (h₁ : Γ ⊢[PRAAx] le (inst2 X l p) t) (h₂ : Γ ⊢[PRAAx] le t (inst2 X u p)) : Γ ⊢[PRAAx] isMed X N t p := by
  refine .andI (le_trans (le_mul_mono (le_refl two) (below_le X hS (le_of_lt hu) h₂)) F1) ?_
  refine le_of_eq_add (d := monus (two * l + two) N + two * monus N (Ac X N t p + succ l)) ?_
  ipra_lc 2 * natEq (eq_add_of_le (above_le X hS hl h₁)) + natEq (eq_add_of_le F2)

/-- `thm:middle-interval`, necessity: if `2ℓ < N < 2u + 2`, every balance median lies in `[y_ℓ, y_u]`. -/
theorem med_between {N p t l u : PTm n} (hS : Γ ⊢[PRAAx] Sorted X N p) (hl : Γ ⊢[PRAAx] lt l N)
    (hu : Γ ⊢[PRAAx] lt u N) (F3 : Γ ⊢[PRAAx] lt (two * l) N) (F4 : Γ ⊢[PRAAx] lt N (two * u + two))
    (hm : Γ ⊢[PRAAx] isMed X N t p) : Γ ⊢[PRAAx] le (inst2 X l p) t ⋏ le t (inst2 X u p) := by
  refine .andI ?_ ?_
  · refine .orE (lt_or_le t (inst2 X l p)) ?_ Prf.hyp0
    let C := lt t (inst2 X l p) :: Γ
    have g := above_ge X hS.wk (le_of_lt hl.wk) (Prf.hyp0 : C ⊢[PRAAx] _)
    refine not_succ_le_self N _ (le_of_eq_add (d := monus N (two * Ac X N t p) +
      two * monus (Ac X N t p + l) N + monus N (succ (two * l))) ?_)
    ipra_lc 2 * natEq (eq_add_of_le g) + natEq (eq_add_of_le (Prf.andE₂ hm.wk : C ⊢[PRAAx] _)) +
      natEq (eq_add_of_le (F3.wk : C ⊢[PRAAx] _))
  · refine .orE (lt_or_le (inst2 X u p) t) ?_ Prf.hyp0
    let C := lt (inst2 X u p) t :: Γ
    have g := below_ge X hS.wk hu.wk (Prf.hyp0 : C ⊢[PRAAx] _)
    refine not_succ_le_self N _ (le_of_eq_add (d := monus (two * u + two) (succ N) +
      two * monus (Bc X N t p) (succ u) + monus N (two * Bc X N t p)) ?_)
    ipra_lc 2 * natEq (eq_add_of_le g) + natEq (eq_add_of_le (Prf.andE₁ hm.wk : C ⊢[PRAAx] _)) +
      natEq (eq_add_of_le (F4.wk : C ⊢[PRAAx] _))

/-! ## The odd and even formulas -/

/-- `cor:odd-even`, odd case: for `N = 2q + 1`, `y_q` is a balance median. -/
theorem odd_med {q p : PTm n} (hS : Γ ⊢[PRAAx] Sorted X (succ (two * q)) p) :
    Γ ⊢[PRAAx] isMed X (succ (two * q)) (inst2 X q p) p :=
  between_med X hS (le_of_eq_add (d := q) (by ipra_ring))
    (le_of_eq_add (d := q) (by ipra_ring))
    (le_of_eq_add (d := one) (by ipra_ring))
    (le_of_eq_add (d := one) (by ipra_ring)) (le_refl _) (le_refl _)

/-- `cor:odd-even`, odd case: for `N = 2q + 1` the balance median is unique, `t = y_q`. -/
theorem odd_unique {q p t : PTm n} (hS : Γ ⊢[PRAAx] Sorted X (succ (two * q)) p)
    (hm : Γ ⊢[PRAAx] isMed X (succ (two * q)) t p) : Γ ⊢[PRAAx] t ≐ inst2 X q p := by
  have h := med_between X hS (le_of_eq_add (d := q) (by ipra_ring))
    (le_of_eq_add (d := q) (by ipra_ring)) (le_refl _)
    (le_of_eq_add (d := zero) (by ipra_ring)) hm
  exact le_antisymm (Prf.andE₂ h) (Prf.andE₁ h)

/-- `cor:odd-even`, even case: for `N = 2q` (`q ≥ 1`), every `t ∈ [y_{q−1}, y_q]` is a balance median. -/
theorem even_med {q p t : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hS : Γ ⊢[PRAAx] Sorted X (two * q) p)
    (h₁ : Γ ⊢[PRAAx] le (inst2 X (pred q) p) t) (h₂ : Γ ⊢[PRAAx] le t (inst2 X q p)) :
    Γ ⊢[PRAAx] isMed X (two * q) t p := by
  have e := natEq hq
  exact between_med X hS (le_of_eq_add (d := q) (by apply deriveNat; ipra_simps; linear_combination e))
    (le_of_eq_add (d := pred q) (by apply deriveNat; ipra_simps; linear_combination e))
    (le_refl _) (le_of_eq_add (d := zero) (by apply deriveNat; ipra_simps; linear_combination -2 * e)) h₁ h₂

/-- `cor:odd-even`, even case: for `N = 2q` (`q ≥ 1`), every balance median lies in `[y_{q−1}, y_q]`. -/
theorem even_between {q p t : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hS : Γ ⊢[PRAAx] Sorted X (two * q) p)
    (hm : Γ ⊢[PRAAx] isMed X (two * q) t p) : Γ ⊢[PRAAx] le (inst2 X (pred q) p) t ⋏ le t (inst2 X q p) := by
  have e := natEq hq
  exact med_between X hS (le_of_eq_add (d := q) (by apply deriveNat; ipra_simps; linear_combination e))
    (le_of_eq_add (d := pred q) (by apply deriveNat; ipra_simps; linear_combination e))
    (le_of_eq_add (d := one) (by apply deriveNat; ipra_simps; linear_combination 2 * e))
    (le_of_eq_add (d := one) (by ipra_ring)) hm

/-- The doubled conventional median `M = y_{q−1} + y_q` of an even sample lies in the doubled median
interval: `2 y_{q−1} ≤ M ≤ 2 y_q`. -/
theorem doubled_median {q p : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hS : Γ ⊢[PRAAx] Sorted X (two * q) p) :
    Γ ⊢[PRAAx] le (two * inst2 X (pred q) p) (inst2 X (pred q) p + inst2 X q p) ⋏
      le (inst2 X (pred q) p + inst2 X q p) (two * inst2 X q p) := by
  have e := natEq hq
  have m := mono X (i := pred q) (j := q) hS (le_of_eq_add (d := one) (by apply deriveNat; ipra_simps; linear_combination e))
    (le_of_eq_add (d := pred q) (by apply deriveNat; ipra_simps; linear_combination e))
  refine .andI (le_of_eq_add (d := monus (inst2 X q p) (inst2 X (pred q) p)) ?_)
    (le_of_eq_add (d := monus (inst2 X q p) (inst2 X (pred q) p)) ?_)
  · ipra_lc natEq (eq_add_of_le m)
  · ipra_lc natEq (eq_add_of_le m)

end Sorted

end LeanProofs.IPRA.Probability.MedianSorted
