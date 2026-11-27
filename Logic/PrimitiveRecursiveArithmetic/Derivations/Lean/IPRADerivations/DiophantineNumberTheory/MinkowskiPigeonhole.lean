import IPRADerivations.Core.Pigeonhole
import IPRADerivations.Foundations.MasterCertificate

/-!
# Bounded color collision with only a finite prefix range contract

Packet `diophantine-number-theory/minkowski_ipra`,
`paper/02_finite_proof.tex`, `lem:php`. The input hypothesis bounds only
colors at indices `i≤H`; no global range premise is required. The actual
primitive recursive totalization takes remainders modulo the runtime `H`.
The existing bounded least searches produce two indices. Their proved
bounds put them inside the original prefix, where the remainders equal
the original colors.

The fixed color program has arbitrary persistent numerical data. A second
closed endpoint specializes it to actual finite sequence entries; length
metadata need not be trusted, since its premise explicitly bounds every
one of the first `H+1` decoded entries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiPigeonhole

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Inclusive source prefix: only the first `H+1` colors must be below `H`. -/
def prefixRange (f : PR 2) (H x : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift H) ⟶ lt (ap2 f (var 0) (Syn.shift x)) (Syn.shift H))

@[simp] theorem subst_prefixRange {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (H x : PTm n) :
    (prefixRange f H x).subst σ = prefixRange f (Syn.subst σ H) (Syn.subst σ x) := by
  simp only [prefixRange, Fm.subst_all, Fm.subst_imp, subst_le, subst_lt, subst_ap2,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem prefixRange_at (f : PR 2) {H x : PTm n} (h : Γ ⊢[PRAAx] prefixRange f H x)
    (i : PTm n) (hi : Γ ⊢[PRAAx] le i H) : Γ ⊢[PRAAx] lt (ap2 f i x) H := by
  have contract : Γ ⊢[PRAAx] le i H ⟶ lt (ap2 f i x) H := by
    simpa only [prefixRange, Fm.subst_imp, subst_le, subst_lt, subst_ap2,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE i h
  exact Prf.impE contract hi

private alias positive_successor := Common.pos_of_one_le

/-- The actual globally bounded color body; its data are `(H,x)`. -/
def totalBody (f : PR 2) : PTm 2 := rem (ap2 f (var 0) (sndT (var 1))) (fstT (var 1))

theorem totalBody_at (f : PR 2) (i H x : PTm n) :
    Γ ⊢[PRAAx] inst2 (totalBody f) i (pairT H x) ≐ rem (ap2 f i x) H := by
  simp only [totalBody, inst2, subst_ap2, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp2 remF (congrAp2 f (.eqRefl _) (snd_pair _ _)) (fst_pair _ _)

/-- Global range follows from totalization itself, without a range hypothesis on `f`. -/
theorem total_range (f : PR 2) (H x : PTm n) (hH : Γ ⊢[PRAAx] le one H) :
    Γ ⊢[PRAAx] Permutation.rangeAll (totalBody f) H (pairT H x) := by
  refine .allI ?_
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift H) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hH.shift
  have ranged := rem_lt' (positive_successor positive) (ap2 f (var 0) (Syn.shift x))
  simpa only [Syn.shift, subst_pairT] using
    lt_congr (totalBody_at f (var 0) (Syn.shift H) (Syn.shift x)).eqSymm (.eqRefl _) ranged

/-- The actual bounded searches on the totalized color program. -/
def first (f : PR 2) (H x : PTm n) : PTm n := Pigeonhole.phpI (totalBody f) H (pairT H x)
def second (f : PR 2) (H x : PTm n) : PTm n := Pigeonhole.phpJ (totalBody f) H (pairT H x)
def pairSearch (f : PR 2) (H x : PTm n) : PTm n := pairT (first f H x) (second f H x)

@[simp] theorem subst_first {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (H x : PTm n) :
    Syn.subst σ (first f H x) = first f (Syn.subst σ H) (Syn.subst σ x) := by
  simp only [first, Pigeonhole.phpI, Pigeonhole.firstMatch, Pigeonhole.phpJ, Search.mu,
    subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ]

@[simp] theorem subst_second {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (H x : PTm n) :
    Syn.subst σ (second f H x) = second f (Syn.subst σ H) (Syn.subst σ x) := by
  simp only [second, Pigeonhole.phpJ, Search.mu, subst_ap2, subst_pairT, ConciseIPRA.PTm.subst_succ]

@[simp] theorem subst_pairSearch {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (H x : PTm n) :
    Syn.subst σ (pairSearch f H x) = pairSearch f (Syn.subst σ H) (Syn.subst σ x) := by
  simp only [pairSearch, subst_pairT, subst_first, subst_second]

theorem remainder_original (f : PR 2) (H x i : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hr : Γ ⊢[PRAAx] lt (ap2 f i x) H) :
    Γ ⊢[PRAAx] rem (ap2 f i x) H ≐ ap2 f i x :=
  rem_eq' (positive_successor hH)
    (((congrAdd (mul_zero H) (.eqRefl _)).eqTrans (zero_add _)).eqSymm) hr

/-- Totalization preserves every original color in the supplied finite prefix. -/
theorem prefix_preserved (f : PR 2) (H x i : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hr : Γ ⊢[PRAAx] prefixRange f H x) (hi : Γ ⊢[PRAAx] le i H) :
    Γ ⊢[PRAAx] inst2 (totalBody f) i (pairT H x) ≐ ap2 f i x :=
  (totalBody_at f i H x).eqTrans (remainder_original f H x i hH (prefixRange_at f hr i hi))

/-- Exact source conclusion, recovered for the original colors after the actual search. -/
theorem bounded_collision (f : PR 2) (H x : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hr : Γ ⊢[PRAAx] prefixRange f H x) :
    Γ ⊢[PRAAx] lt (first f H x) (second f H x) ⋏
      (le (second f H x) H ⋏ (ap2 f (first f H x) x ≐ ap2 f (second f H x) x)) := by
  have found := Pigeonhole.pigeonhole (total_range f H x hH)
  have ij : Γ ⊢[PRAAx] lt (first f H x) (second f H x) := Prf.andE₁ found
  have jH : Γ ⊢[PRAAx] le (second f H x) H := Prf.andE₁ (Prf.andE₂ found)
  have iH := le_trans (le_of_lt ij) jH
  have original := (prefix_preserved f H x (first f H x) hH hr iH).eqSymm.eqTrans
    ((Prf.andE₂ (Prf.andE₂ found)).eqTrans (prefix_preserved f H x (second f H x) hH hr jH))
  exact .andI ij (.andI jH original)

/-- Actual exported PR symbols; their definitions do not inspect any proof. -/
def firstF (f : PR 2) : PR 2 := PTm.toPR (first f (var 0) (var 1))
def secondF (f : PR 2) : PR 2 := PTm.toPR (second f (var 0) (var 1))
def searchF (f : PR 2) : PR 2 := PTm.toPR (pairSearch f (var 0) (var 1))

theorem first_at (f : PR 2) (H x : PTm n) : Γ ⊢[PRAAx] ap2 (firstF f) H x ≐ first f H x := by
  have h := toPR_eq (Γ := Γ) (first f (var 0) (var 1)) ![H,x]
  simpa only [firstF, ap2, subst_first, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem second_at (f : PR 2) (H x : PTm n) : Γ ⊢[PRAAx] ap2 (secondF f) H x ≐ second f H x := by
  have h := toPR_eq (Γ := Γ) (second f (var 0) (var 1)) ![H,x]
  simpa only [secondF, ap2, subst_second, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem search_at (f : PR 2) (H x : PTm n) : Γ ⊢[PRAAx] ap2 (searchF f) H x ≐ pairSearch f H x := by
  have h := toPR_eq (Γ := Γ) (pairSearch f (var 0) (var 1)) ![H,x]
  simpa only [searchF, ap2, subst_pairSearch, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem search_first (f : PR 2) (H x : PTm n) :
    Γ ⊢[PRAAx] fstT (ap2 (searchF f) H x) ≐ first f H x :=
  (congrFst (search_at f H x)).eqTrans (fst_pair _ _)
theorem search_second (f : PR 2) (H x : PTm n) :
    Γ ⊢[PRAAx] sndT (ap2 (searchF f) H x) ≐ second f H x :=
  (congrSnd (search_at f H x)).eqTrans (snd_pair _ _)

/-- The source's returned pair, as one actual PR code. -/
theorem search_collision (f : PR 2) (H x : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hr : Γ ⊢[PRAAx] prefixRange f H x) :
    Γ ⊢[PRAAx] lt (fstT (ap2 (searchF f) H x)) (sndT (ap2 (searchF f) H x)) ⋏
      (le (sndT (ap2 (searchF f) H x)) H ⋏
        (ap2 f (fstT (ap2 (searchF f) H x)) x ≐ ap2 f (sndT (ap2 (searchF f) H x)) x)) := by
  have found := bounded_collision f H x hH hr
  exact .andI (lt_congr (search_first f H x).eqSymm (search_second f H x).eqSymm (.andE₁ found))
    (.andI (le_congr (search_second f H x).eqSymm (.eqRefl _) (.andE₁ (.andE₂ found)))
      (((congrAp2 f (search_first f H x) (.eqRefl _)).eqTrans (.andE₂ (.andE₂ found))).eqTrans
        (congrAp2 f (search_second f H x).eqSymm (.eqRefl _))))

/-- Variables are the number of colors and all persistent numerical input data. -/
def collisionFormula (f : PR 2) : Fm PTm 2 :=
  le one (var 0) ⟶ prefixRange f (var 0) (var 1) ⟶
    (lt (fstT (ap2 (searchF f) (var 0) (var 1))) (sndT (ap2 (searchF f) (var 0) (var 1))) ⋏
    (le (sndT (ap2 (searchF f) (var 0) (var 1))) (var 0) ⋏
      (ap2 f (fstT (ap2 (searchF f) (var 0) (var 1))) (var 1) ≐
        ap2 f (sndT (ap2 (searchF f) (var 0) (var 1))) (var 1))))

theorem bounded_color_collision (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (collisionFormula f) :=
  closeUniv 2 (.impI (.impI (search_collision f (var 0) (var 1) Prf.hyp1 Prf.hyp0)))

/-- Exact actual index-program metadata at every internal horizon and input. -/
theorem search_programs_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((ap2 (searchF f) (var 0) (var 1) ≐ pairSearch f (var 0) (var 1)) ⋏
      ((ap2 (firstF f) (var 0) (var 1) ≐ fstT (ap2 (searchF f) (var 0) (var 1))) ⋏
        (ap2 (secondF f) (var 0) (var 1) ≐ sndT (ap2 (searchF f) (var 0) (var 1))))) :=
  closeUniv 2 (.andI (search_at f _ _)
    (.andI ((first_at f _ _).eqTrans (search_first f _ _).eqSymm)
      ((second_at f _ _).eqTrans (search_second f _ _).eqSymm)))

/-- The totalized color as one fixed PR3 symbol, with all data internal. -/
def totalColorF (f : PR 2) : PR 3 := PTm.toPR (rem (ap2 f (var 0) (var 2)) (var 1))

theorem totalColor_at (f : PR 2) (i H x : PTm n) :
    Γ ⊢[PRAAx] ap3 (totalColorF f) i H x ≐ rem (ap2 f i x) H := by
  have h := toPR_eq (Γ := Γ) (rem (ap2 f (var 0) (var 2)) (var 1) : PTm 3) ![i,H,x]
  simpa only [totalColorF, ap3, subst_ap2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

/-- Totalization is globally bounded, and agrees with every in-range original color. -/
theorem total_color_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 1) ⟶
        (lt (ap3 (totalColorF f) (var 0) (var 1) (var 2)) (var 1) ⋏
          (lt (ap2 f (var 0) (var 2)) (var 1) ⟶
            (ap3 (totalColorF f) (var 0) (var 1) (var 2) ≐ ap2 f (var 0) (var 2))))) := by
  refine closeUniv 3 (.impI (.andI ?_ (.impI ?_)))
  · exact lt_congr (totalColor_at f _ _ _).eqSymm (.eqRefl _)
      (rem_lt' (positive_successor Prf.hyp0) _)
  · exact (totalColor_at f _ _ _).eqTrans (remainder_original f _ _ _ Prf.hyp1 Prf.hyp0)

/-! ## Literal source specialization to an actual finite sequence code -/

/-- Actual source entry lookup, rather than an externally supplied evaluator. -/
def sequenceColorF : PR 2 := PTm.toPR (entry (var 1) (var 0))

theorem sequenceColor_at (i S : PTm n) : Γ ⊢[PRAAx] ap2 sequenceColorF i S ≐ entry S i := by
  have h := toPR_eq (Γ := Γ) (entry (var 1) (var 0) : PTm 2) ![i,S]
  simpa only [sequenceColorF, ap2, subst_entry, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

def sequenceRange (H S : PTm n) : Fm PTm n :=
  .all (le (var 0) (Syn.shift H) ⟶ lt (entry (Syn.shift S) (var 0)) (Syn.shift H))

@[simp] theorem subst_sequenceRange {m : ℕ} (σ : Fin n → PTm m) (H S : PTm n) :
    (sequenceRange H S).subst σ = sequenceRange (Syn.subst σ H) (Syn.subst σ S) := by
  simp only [sequenceRange, Fm.subst_all, Fm.subst_imp, subst_le, subst_lt, subst_entry,
    Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem sequence_range_adapter (H S : PTm n) (h : Γ ⊢[PRAAx] sequenceRange H S) :
    Γ ⊢[PRAAx] prefixRange sequenceColorF H S := by
  refine .allI (.impI ?_)
  have original : (le (var 0) (Syn.shift H) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (entry (Syn.shift S) (var 0)) (Syn.shift H) := .impE h.allOpen.wk Prf.hyp0
  exact lt_congr (sequenceColor_at _ _).eqSymm (.eqRefl _) original

/-- `lem:php`: actual bounded pair search on the first `H+1` supplied sequence entries. -/
theorem sequence_collision (H S : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hr : Γ ⊢[PRAAx] sequenceRange H S) :
    Γ ⊢[PRAAx] lt (fstT (ap2 (searchF sequenceColorF) H S)) (sndT (ap2 (searchF sequenceColorF) H S)) ⋏
      (le (sndT (ap2 (searchF sequenceColorF) H S)) H ⋏
        (entry S (fstT (ap2 (searchF sequenceColorF) H S)) ≐
          entry S (sndT (ap2 (searchF sequenceColorF) H S)))) := by
  have found := search_collision sequenceColorF H S hH (sequence_range_adapter H S hr)
  exact .andI (.andE₁ found) (.andI (.andE₁ (.andE₂ found))
    ((sequenceColor_at _ S).eqSymm.eqTrans ((Prf.andE₂ (.andE₂ found)).eqTrans (sequenceColor_at _ S))))

/-- Fully closed source lemma; horizon, list code and selected indices are numerical. -/
theorem sequence_collision_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (le one (var 0) ⟶ sequenceRange (var 0) (var 1) ⟶
        (lt (fstT (ap2 (searchF sequenceColorF) (var 0) (var 1)))
            (sndT (ap2 (searchF sequenceColorF) (var 0) (var 1))) ⋏
        (le (sndT (ap2 (searchF sequenceColorF) (var 0) (var 1))) (var 0) ⋏
          (entry (var 1) (fstT (ap2 (searchF sequenceColorF) (var 0) (var 1))) ≐
            entry (var 1) (sndT (ap2 (searchF sequenceColorF) (var 0) (var 1))))))) :=
  closeUniv 2 (.impI (.impI (sequence_collision (var 0) (var 1) Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiPigeonhole
