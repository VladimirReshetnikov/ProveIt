import IPRADerivations.DiophantineNumberTheory.SignedEuclidean
import IPRADerivations.Foundations.SequenceComposition
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.Powers

/-!
# Runtime-dimensional residue colors for the finite Minkowski mesh

The actual color is the reverse base-`m` fold
`C_0=0`, `C_(n+1)=m*C_n+r_n`, where `r_n` is the actual signed
Euclidean remainder of the decoded coordinate at index `n`.
Dimension, modulus, vector codes and coordinate positions are internal.
For every positive modulus, including one, the color is below `m^n`.
Natural division proves the exact quotient/remainder step inverses.
A pointwise QF induction then proves that equal colors force equality
of every residue at an internal coordinate `k<n`.

Vector coordinates use the total `MasterCertificate.entry` decoder and
arbitrary signed natural pairs; no canonical signs or trusted vector-shape
metadata are required. The later geometric mesh frontend must supply its
own coordinate-shape and distinct-decoded-cell conditions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiResidues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open LeanProofs.IPRA.DiophantineNumberTheory.SignedEuclidean
  (decode computedRemainder computedQuotient divmodF)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The actual signed remainder of an actual decoded vector coordinate. -/
def digit (a k m : PTm n) : PTm n := computedRemainder (entry a k) m

@[simp] theorem subst_digit {l : ℕ} (σ : Fin n → PTm l) (a k m : PTm n) :
    Syn.subst σ (digit a k m) = digit (Syn.subst σ a) (Syn.subst σ k) (Syn.subst σ m) := by
  simp only [digit, SignedEuclidean.subst_computedRemainder, subst_entry]

theorem digit_congr {a a' k k' m m' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a')
    (hk : Γ ⊢[PRAAx] k ≐ k') (hm : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] digit a k m ≐ digit a' k' m' :=
  congrSnd (congrAp2 divmodF (entry_congr ha hk) hm)

theorem digit_bound (a k m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] lt (digit a k m) m := Prf.andE₂ (SignedEuclidean.program_correct (entry a k) m hm)

theorem digit_one (a k : PTm n) : Γ ⊢[PRAAx] digit a k one ≐ zero :=
  (SignedEuclidean.computed_remainder (entry a k) one).eqTrans (SignedEuclidean.remainder_one _)

/-- Actual primitive recursion: stage, accumulated color, modulus, vector. -/
def colorStep : PTm 4 := var 2*var 1+digit (var 3) (var 0) (var 2)
def colorF : PR 3 := recDef (zero : PTm 2) colorStep
def color (N m a : PTm n) : PTm n := ap3 colorF N m a

@[simp] theorem subst_color {l : ℕ} (σ : Fin n → PTm l) (N m a : PTm n) :
    Syn.subst σ (color N m a) = color (Syn.subst σ N) (Syn.subst σ m) (Syn.subst σ a) := subst_ap3 _ _ _ _ _

theorem color_zero (m a : PTm n) : Γ ⊢[PRAAx] color zero m a ≐ zero := by
  have h := rec_zero (Γ := Γ) (zero : PTm 2) colorStep ![m,a]
  have eq : (Fin.cases zero ![m,a] : Fin 3 → PTm n) = ![zero,m,a] := by funext i; fin_cases i <;> rfl
  rw [eq] at h
  simpa only [color, colorF, ap3, ConciseIPRA.PTm.subst_zero] using h

theorem color_succ (N m a : PTm n) :
    Γ ⊢[PRAAx] color (succ N) m a ≐ m*color N m a+digit a N m := by
  have h := rec_succ (Γ := Γ) (zero : PTm 2) colorStep N ![m,a]
  have e1 : (Fin.cases (succ N) ![m,a] : Fin 3 → PTm n) = ![succ N,m,a] := by funext i; fin_cases i <;> rfl
  have e2 : (Fin.cases N (Fin.cases (app (recDef (zero : PTm 2) colorStep) (Fin.cases N ![m,a])) ![m,a]) : Fin 4 → PTm n) =
      ![N,color N m a,m,a] := by funext i; fin_cases i <;> rfl
  rw [e1,e2] at h
  simpa only [color, colorF, ap3, colorStep, PTm.subst_add, PTm.subst_mul, subst_digit,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] using h

/-- One Horner step stays strictly below the next radix power. -/
theorem range_step {m C P r : PTm n} (hC : Γ ⊢[PRAAx] lt C P) (hr : Γ ⊢[PRAAx] lt r m) :
    Γ ⊢[PRAAx] lt (m*C+r) (P*m) := by
  have first : Γ ⊢[PRAAx] le (succ (m*C+r)) (m*succ C) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (m*C) hr)
  exact le_trans first (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl m) hC))

/-- Global finite color range, with no nontrivial-modulus or vector-shape assumption. -/
theorem color_range (N m a : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] lt (color N m a) (pw m N) := by
  have all : Γ ⊢[PRAAx] .all (lt (color (var 0) (Syn.shift m) (Syn.shift a)) (pw (Syn.shift m) (var 0))) := by
    refine PRA.qfInd _ (lt_QF _ _) ?_ ?_
    · simp only [subst_lt, subst_color, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero]
      exact lt_congr (color_zero m a).eqSymm (pw_zero m).eqSymm (zero_lt_succ zero)
    · simp only [subst_lt, subst_color, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ]
      have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
        simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hm.shift
      exact lt_congr (color_succ _ _ _).eqSymm (pw_succ _ _).eqSymm
        (range_step Prf.hyp0 (digit_bound _ _ _ positive.wk))
  simpa only [subst_lt, subst_color, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE N all

/-- Exact step decoding follows from actual natural division uniqueness. -/
theorem color_peel (N m a : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] (quo (color (succ N) m a) m ≐ color N m a) ⋏
      (rem (color (succ N) m a) m ≐ digit a N m) := by
  have pos := SignedEuclidean.positive_form m hm
  have eq := div_mod_unique ((color_succ N m a).eqTrans (congrAdd (congrMul pos (.eqRefl _)) (.eqRefl _)))
    (lt_congr (.eqRefl _) pos (digit_bound a N m hm))
  exact .andI ((congrAp2 quoF (.eqRefl _) pos).eqTrans (Prf.andE₁ eq))
    ((congrAp2 remF (.eqRefl _) pos).eqTrans (Prf.andE₂ eq))

/-- A collision at the next dimension exposes both previous colors and the last residues. -/
theorem peel_collision (N m a b : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] color (succ N) m a ≐ color (succ N) m b) :
    Γ ⊢[PRAAx] (color N m a ≐ color N m b) ⋏ (digit a N m ≐ digit b N m) :=
  .andI ((Prf.andE₁ (color_peel N m a hm)).eqSymm.eqTrans
    ((congrAp2 quoF h (.eqRefl _)).eqTrans (Prf.andE₁ (color_peel N m b hm))))
    ((Prf.andE₂ (color_peel N m a hm)).eqSymm.eqTrans
      ((congrAp2 remF h (.eqRefl _)).eqTrans (Prf.andE₂ (color_peel N m b hm))))

/-- Pointwise induction step; no quantified injectivity invariant is used. -/
theorem coordinate_step (N m a b k : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (previous : Γ ⊢[PRAAx] (lt k N ⟶ (color N m a ≐ color N m b) ⟶ (digit a k m ≐ digit b k m))) :
    Γ ⊢[PRAAx] lt k (succ N) ⟶ (color (succ N) m a ≐ color (succ N) m b) ⟶ (digit a k m ≐ digit b k m) := by
  refine .impI (.impI ?_)
  have leN : ((color (succ N) m a ≐ color (succ N) m b) :: lt k (succ N) :: Γ) ⊢[PRAAx] le k N :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp1
  refine .orE (lt_or_eq_of_le leN) ?_ ?_
  · exact .impE (.impE previous.wk.wk.wk Prf.hyp0)
      (Prf.andE₁ (peel_collision N m a b hm.wk.wk.wk Prf.hyp1))
  · exact (digit_congr (.eqRefl a) (Prf.hyp0 : _ ⊢[PRAAx] k ≐ N) (.eqRefl m)).eqTrans
      ((Prf.andE₂ (peel_collision N m a b hm.wk.wk.wk Prf.hyp1)).eqTrans
        (digit_congr (.eqRefl b) (Prf.hyp0 : _ ⊢[PRAAx] k ≐ N) (.eqRefl m)).eqSymm)

/-- Equal colors imply equality of every arbitrary internal in-range residue. -/
theorem coordinate_injective (N m a b k : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hk : Γ ⊢[PRAAx] lt k N) (h : Γ ⊢[PRAAx] color N m a ≐ color N m b) :
    Γ ⊢[PRAAx] digit a k m ≐ digit b k m := by
  have all : Γ ⊢[PRAAx] .all (lt (Syn.shift k) (var 0) ⟶
      (color (var 0) (Syn.shift m) (Syn.shift a) ≐ color (var 0) (Syn.shift m) (Syn.shift b)) ⟶
        (digit (Syn.shift a) (Syn.shift k) (Syn.shift m) ≐ digit (Syn.shift b) (Syn.shift k) (Syn.shift m))) := by
    refine PRA.qfInd _ ⟨lt_QF _ _, ⟨trivial,trivial⟩⟩ ?_ ?_
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_color, subst_digit, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_color, subst_digit, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
        simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hm.shift
      exact coordinate_step _ _ _ _ _ positive.wk Prf.hyp0
  have contract : Γ ⊢[PRAAx] lt k N ⟶ (color N m a ≐ color N m b) ⟶ (digit a k m ≐ digit b k m) := by
    simpa only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_color, subst_digit, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE N all
  exact Prf.impE (Prf.impE contract hk) h

/-- Quantify coordinates only after the pointwise QF proof is complete. -/
def sameResidues (N m a b : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ (digit (Syn.shift a) (var 0) (Syn.shift m) ≐ digit (Syn.shift b) (var 0) (Syn.shift m)))

theorem collision_residues (N m a b : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] color N m a ≐ color N m b) : Γ ⊢[PRAAx] sameResidues N m a b := by
  refine .allI (.impI ?_)
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hm.shift
  have eq : Γ.map Fm.shift ⊢[PRAAx] color (Syn.shift N) (Syn.shift m) (Syn.shift a) ≐ color (Syn.shift N) (Syn.shift m) (Syn.shift b) := by
    simpa only [Fm.shift, Fm.subst_eq, subst_color, Syn.shift] using h.shift
  exact coordinate_injective _ _ _ _ _ positive.wk Prf.hyp0 eq.wk

/-- A color collision therefore gives exact coordinatewise signed lattice differences. -/
theorem collision_coordinate_difference (N m a b k : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hk : Γ ⊢[PRAAx] lt k N) (h : Γ ⊢[PRAAx] color N m a ≐ color N m b) :
    Γ ⊢[PRAAx] ZT.eq (decode (entry a k)-decode (entry b k))
      (ZT.ofNat m*(computedQuotient (entry a k) m-computedQuotient (entry b k) m)) :=
  SignedEuclidean.computed_collision (entry a k) (entry b k) m hm (coordinate_injective N m a b k hm hk h)

/-- The degenerate modulus is handled by the same actual fold. -/
theorem color_one (N a : PTm n) : Γ ⊢[PRAAx] color N one a ≐ zero := by
  have all : Γ ⊢[PRAAx] .all (color (var 0) one (Syn.shift a) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_color, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact color_zero _ _
    · simp only [Fm.subst_eq, subst_color, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact (color_succ _ _ _).eqTrans ((congrAdd ((one_mul _).eqTrans Prf.hyp0) (digit_one _ _)).eqTrans (add_zero zero))
  simpa only [Fm.subst_eq, subst_color, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] using Prf.allE N all

/-- Global range at every runtime dimension, modulus and vector. -/
theorem color_range_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ lt (ap3 colorF (var 0) (var 1) (var 2)) (pw (var 1) (var 0))) :=
  closeUniv 3 (.impI (color_range (var 0) (var 1) (var 2) Prf.hyp0))

/-- Exact unconditional recursion equations for the exported color symbol. -/
theorem color_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 colorF zero (var 1) (var 2) ≐ zero) ⋏
      (ap3 colorF (succ (var 0)) (var 1) (var 2) ≐
        var 1*ap3 colorF (var 0) (var 1) (var 2)+digit (var 2) (var 0) (var 1))) :=
  closeUniv 3 (.andI (color_zero (var 1) (var 2)) (color_succ (var 0) (var 1) (var 2)))

theorem color_peel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      ((quo (ap3 colorF (succ (var 0)) (var 1) (var 2)) (var 1) ≐ ap3 colorF (var 0) (var 1) (var 2)) ⋏
        (rem (ap3 colorF (succ (var 0)) (var 1) (var 2)) (var 1) ≐ digit (var 2) (var 0) (var 1)))) :=
  closeUniv 3 (.impI (color_peel (var 0) (var 1) (var 2) Prf.hyp0))

theorem coordinate_injective_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ lt (var 4) (var 0) ⟶
      (ap3 colorF (var 0) (var 1) (var 2) ≐ ap3 colorF (var 0) (var 1) (var 3)) ⟶
        (computedRemainder (entry (var 2) (var 4)) (var 1) ≐ computedRemainder (entry (var 3) (var 4)) (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (coordinate_injective
    (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem collision_residues_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶
      (ap3 colorF (var 0) (var 1) (var 2) ≐ ap3 colorF (var 0) (var 1) (var 3)) ⟶
        sameResidues (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (collision_residues (var 0) (var 1) (var 2) (var 3) Prf.hyp1 Prf.hyp0)))

/-- A collision already supplies the exact coordinatewise signed lattice equation. -/
theorem collision_coordinate_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ lt (var 4) (var 0) ⟶
      (ap3 colorF (var 0) (var 1) (var 2) ≐ ap3 colorF (var 0) (var 1) (var 3)) ⟶
        ZT.eq (decode (entry (var 2) (var 4))-decode (entry (var 3) (var 4)))
          (ZT.ofNat (var 1)*(computedQuotient (entry (var 2) (var 4)) (var 1)-
            computedQuotient (entry (var 3) (var 4)) (var 1)))) :=
  closeUniv 5 (.impI (.impI (.impI (collision_coordinate_difference
    (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem modulus_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 colorF (var 0) one (var 1) ≐ zero) ⋏ (digit (var 1) (var 2) one ≐ zero)) :=
  closeUniv 3 (.andI (color_one (var 0) (var 1)) (digit_one (var 1) (var 2)))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiResidues
