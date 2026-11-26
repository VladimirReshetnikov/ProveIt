import IPRADerivations.Analysis.Inequalities.RationalNonnegativePowers

/-!
# Actual rational square-root brackets from integer square root

For A >= 0, B >= 1 and H >= 1, the actual numerator is
isqrt(A*B*H*H) and the common denominator is B*H. The two adjacent
fractions bracket the square root without a square-root oracle or a
supplied endpoint condition. Every coefficient and precision is numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalSquareRootBounds

open_ipra
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def three : PTm n := two+one
def radicand (A B H : PTm n) : PTm n := A*B*H*H
def root (A B H : PTm n) : PTm n := isqrt (radicand A B H)
def denominator (B H : PTm n) : PTm n := B*H
def lower (A B H : PTm n) : PTm n := fraction (root A B H) (denominator B H)
def upper (A B H : PTm n) : PTm n := fraction (succ (root A B H)) (denominator B H)
def deficit (A B H : PTm n) : PTm n := monus (radicand A B H) (root A B H*root A B H)
def square (q : PTm n) : PTm n := RationalArithmetic.multiply q q
def squareGap (A B H : PTm n) : PTm n :=
  RationalArithmetic.add (fraction A B) (RationalArithmetic.negative (square (lower A B H)))

ipra_subst three
ipra_subst radicand
ipra_subst root
ipra_subst denominator
ipra_subst lower
ipra_subst upper
ipra_subst deficit
ipra_subst square
ipra_subst squareGap

theorem denominator_positive (B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    le one (denominator B H) := positive_product B H hB hH

theorem root_lower (A B H : PTm n) : Γ ⊢[PRAAx] le (root A B H*root A B H) (radicand A B H) := isqrt_le _

theorem root_strict (A B H : PTm n) : Γ ⊢[PRAAx] lt (radicand A B H) (succ (root A B H)*succ (root A B H)) :=
  lt_congr (.eqRefl _) (congrMul (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm) (lt_isqrt_succ_sq _)

theorem deficit_identity (A B H : PTm n) : Γ ⊢[PRAAx]
    radicand A B H ≐ root A B H*root A B H+deficit A B H := eq_add_of_le (root_lower A B H)

theorem root_deficit (A B H : PTm n) : Γ ⊢[PRAAx]
    root A B H*root A B H+deficit A B H ≐ radicand A B H := (deficit_identity A B H).eqSymm

theorem root_unit_bound (A B H : PTm n) (hAB : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx]
    le (root A B H) (denominator B H) :=
  nat_sqrt_mono (le_trans (root_lower A B H)
    (le_congr (by unfold radicand; ipra_ring) (by unfold denominator; ipra_ring) (mul_le_mul_right (B*H*H) hAB)))

/-- This local arithmetic helper is used only after deriving the square
comparison from the original A/B guard. -/
theorem root_ge (A B H x : PTm n) (h : Γ ⊢[PRAAx] le (x*x) (radicand A B H)) : Γ ⊢[PRAAx]
    le x (root A B H) := by
  refine .orE (lt_or_le (root A B H) x) ?_ Prf.hyp0
  exact le_lt_absurd _ (le_trans (sq_le_sq Prf.hyp0) h.wk) (root_strict A B H).wk

theorem root_unit_lower (A B H : PTm n) (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    le (denominator B H) (root A B H) :=
  root_ge A B H _ (le_congr (by unfold denominator; ipra_ring) (by unfold radicand; ipra_ring)
    (mul_le_mul_right (B*H*H) hBA))

theorem root_scaled_lower (A B H : PTm n) (hAB : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx]
    le (A*H) (root A B H) :=
  root_ge A B H _ (le_congr (by ipra_ring) (by unfold radicand; ipra_ring)
    (mul_le_mul_right (A*H*H) hAB))

theorem deficit_local_bound (A B H : PTm n) : Γ ⊢[PRAAx] le (deficit A B H) (two*root A B H+one) := by
  apply le_of_add_le_add_right (c := root A B H*root A B H)
  exact le_congr ((deficit_identity A B H).eqTrans (add_comm _ _)) (by ipra_ring) (le_of_lt (root_strict A B H))

theorem deficit_bound (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (hAB : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx] le (deficit A B H) (three*denominator B H) :=
  le_trans (deficit_local_bound A B H) (le_congr (.eqRefl _) (by unfold three; ipra_ring)
    (add_le_add₂ (le_mul_mono (le_refl two) (root_unit_bound A B H hAB)) (denominator_positive B H hB hH)))

theorem root_zero (B H : PTm n) : Γ ⊢[PRAAx] root zero B H ≐ zero :=
  (congrAp1 isqrtF (by unfold radicand; ipra_ring)).eqTrans isqrt_zero

theorem diagonal_root (B H : PTm n) : Γ ⊢[PRAAx] root B B H ≐ denominator B H :=
  le_antisymm (root_unit_bound B B H (le_refl B)) (root_unit_lower B B H (le_refl B))

theorem lower_represents (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (lower A B H) (ZT.ofNat (root A B H)) (denominator B H) :=
  fraction_represents _ _ (denominator_positive B H hB hH)

theorem upper_represents (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (upper A B H) (ZT.ofNat (succ (root A B H))) (denominator B H) :=
  fraction_represents _ _ (denominator_positive B H hB hH)

theorem fraction_square (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    square (fraction A B) ≐ fraction (A*A) (B*B) := RationalNonnegativePowers.fraction_multiply A B A B hB hB

theorem lower_square_fraction (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    square (lower A B H) ≐ fraction (root A B H*root A B H) (denominator B H*denominator B H) :=
  fraction_square _ _ (denominator_positive B H hB hH)

theorem upper_square_fraction (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    square (upper A B H) ≐ fraction (succ (root A B H)*succ (root A B H)) (denominator B H*denominator B H) :=
  fraction_square _ _ (denominator_positive B H hB hH)

theorem lower_square_bound (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (square (lower A B H)) (fraction A B) := by
  have hp := denominator_positive (Γ := Γ) B H hB hH
  have raw : Γ ⊢[PRAAx] le (B*(root A B H*root A B H)) (A*(denominator B H*denominator B H)) :=
    le_congr (by ipra_ring) (by simp only [denominator,radicand]; ipra_ring) (mul_le_mul_right B (root_lower A B H))
  exact RationalArgmin.rationalLE_congr (lower_square_fraction A B H hB hH).eqSymm (.eqRefl _)
    (fraction_order _ _ _ _ (positive_product _ _ hp hp) hB raw)

/-- The upper endpoint is strictly above the actual square root, even
when the radicand is a perfect square or A=0. -/
theorem upper_square_strict (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (square (upper A B H)) (fraction A B)) := by
  refine .impI ?_
  let Δ := RationalArgmin.rationalLE (square (upper A B H)) (fraction A B)::Γ
  have hp := denominator_positive (Γ := Γ) B H hB hH
  have cmp : Δ ⊢[PRAAx] RationalArgmin.rationalLE
      (fraction (succ (root A B H)*succ (root A B H)) (denominator B H*denominator B H)) (fraction A B) :=
    RationalArgmin.rationalLE_congr (upper_square_fraction A B H hB hH).wk (.eqRefl _) Prf.hyp0
  have raw : Δ ⊢[PRAAx] le (B*(succ (root A B H)*succ (root A B H))) (A*(denominator B H*denominator B H)) :=
    GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents _ _ (positive_product _ _ hp hp)).wk (fraction_represents A B hB).wk cmp
  have small : Δ ⊢[PRAAx] le (succ (root A B H)*succ (root A B H)) (radicand A B H) :=
    RationalValueBounds.positive_cancel hB.wk
      (le_congr (.eqRefl _) (by simp only [denominator,radicand]; ipra_ring) raw)
  exact le_lt_absurd _ small (root_strict A B H).wk

theorem bracket_width (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.add (upper A B H) (RationalArithmetic.negative (lower A B H)) ≐ fraction one (denominator B H) := by
  have hp := denominator_positive (Γ := Γ) B H hB hH
  have value := GaussianRationalHorner.scalar_add_same _ _ _ _ _ hp
    (upper_represents A B H hB hH)
    (RationalRepresentations.represents_negative _ _ _ (lower_represents A B H hB hH))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hp) value (fraction_represents _ _ hp) hp hp
  ipra_lc

theorem square_gap_represents (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (squareGap A B H) (ZT.ofNat (deficit A B H)) (denominator B H*denominator B H) := by
  have hp := denominator_positive (Γ := Γ) B H hB hH
  have hp2 := positive_product _ _ hp hp
  have target : Γ ⊢[PRAAx] RationalArithmetic.represents (fraction A B) (ZT.ofNat (radicand A B H))
      (denominator B H*denominator B H) := by
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := by unfold denominator; ipra_ring)
      (h := GaussianRationalHorner.scalar_rescale _ _ B (B*H*H) (fraction_represents A B hB))
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    unfold radicand
    ipra_simps
    ring
  have sq : Γ ⊢[PRAAx] RationalArithmetic.represents (square (lower A B H))
      (ZT.ofNat (root A B H*root A B H)) (denominator B H*denominator B H) :=
    GaussianRationalHorner.scalar_congr (lower_square_fraction A B H hB hH).eqSymm
      (by apply ZT.derive; rfl) (.eqRefl _) (fraction_represents _ _ hp2)
  have value := GaussianRationalHorner.scalar_add_same _ _ _ _ _ hp2 target
    (RationalRepresentations.represents_negative _ _ _ sq)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := value)
  ipra_lc natEq (deficit_identity (Γ := Γ) A B H)

theorem square_gap_fraction (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    squareGap A B H ≐ fraction (deficit A B H) (denominator B H*denominator B H) := by
  have hp := denominator_positive (Γ := Γ) B H hB hH
  have hp2 := positive_product _ _ hp hp
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hp2) (square_gap_represents A B H hB hH)
    (fraction_represents _ _ hp2) hp2 hp2 (by apply ZT.derive; rfl)

theorem square_gap_bound (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (hAB : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (squareGap A B H) (fraction three H) := by
  have hp := denominator_positive (Γ := Γ) B H hB hH
  have Hle : Γ ⊢[PRAAx] le H (denominator B H) :=
    le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H hB)
  have first : Γ ⊢[PRAAx] le (H*deficit A B H) (three*denominator B H*H) :=
    le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right H (deficit_bound A B H hB hH hAB))
  have second : Γ ⊢[PRAAx] le (three*denominator B H*H) (three*(denominator B H*denominator B H)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (three*denominator B H) Hle)
  have raw := le_trans first second
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (positive_product _ _ hp hp) hH
    (square_gap_represents A B H hB hH) (fraction_represents three H hH) raw

theorem root_successor_relative (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    le (H*succ (root A B H)) (succ H*root A B H) := by
  have Hle : Γ ⊢[PRAAx] le H (root A B H) :=
    le_trans (le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H hB)) (root_unit_lower A B H hBA)
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (H*root A B H) Hle)

theorem relative_integer_bound (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    le (H*H*(succ (root A B H)*succ (root A B H))) (succ H*succ H*radicand A B H) :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring) (sq_le_sq (root_successor_relative A B H hB hBA)))
    (le_mul_mono (le_refl _) (root_lower A B H))

def relativeBound (A B H : PTm n) : PTm n :=
  RationalArithmetic.multiply (square (fraction (succ H) H)) (fraction A B)

ipra_subst relativeBound

theorem relative_fraction (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    relativeBound A B H ≐ fraction (succ H*succ H*A) (H*H*B) :=
  (RationalAlgebra.multiply_congr (fraction_square (succ H) H hH) (.eqRefl _)).eqTrans
    (RationalNonnegativePowers.fraction_multiply _ _ _ _ (positive_product _ _ hH hH) hB)

/-- Initialization's relative upper bound is derived from the actual
integer bracket and B<=A, without a relative-error oracle. -/
theorem upper_relative_bound (A B H : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (hBA : Γ ⊢[PRAAx] le B A) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (square (upper A B H)) (relativeBound A B H) := by
  have hp := denominator_positive (Γ := Γ) B H hB hH
  exact RationalArgmin.rationalLE_congr (upper_square_fraction A B H hB hH).eqSymm (relative_fraction A B H hB hH).eqSymm
    (fraction_order _ _ _ _ (positive_product _ _ hp hp) (positive_product _ _ (positive_product _ _ hH hH) hB)
      (le_congr (by ipra_ring) (by simp only [denominator,radicand]; ipra_ring)
        (mul_le_mul_right B (relative_integer_bound A B H hB hBA))))

/-! Literal PR3 output: integer root, positive denominator, lower and
upper rational brackets, and the actual natural squared deficit. -/
def output (A B H : PTm n) : PTm n := pairT (root A B H) (pairT (denominator B H)
  (pairT (lower A B H) (pairT (upper A B H) (deficit A B H))))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (A B H : PTm n) : PTm n := ap3 outputF A B H

ipra_subst output
ipra_subst run

theorem program_at (A B H : PTm n) : Γ ⊢[PRAAx] run A B H ≐ output A B H := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![A,B,H]
theorem returned_root (A B H : PTm n) : Γ ⊢[PRAAx] fstT (run A B H) ≐ root A B H :=
  (program_at A B H).fstE
theorem returned_denominator (A B H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A B H)) ≐ denominator B H :=
  (program_at A B H).sndE.fstE
theorem returned_lower (A B H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run A B H))) ≐ lower A B H :=
  (program_at A B H).sndE.sndE.fstE
theorem returned_upper (A B H : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run A B H)))) ≐ upper A B H :=
  (program_at A B H).sndE.sndE.sndE.fstE
theorem returned_deficit (A B H : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run A B H)))) ≐ deficit A B H :=
  (program_at A B H).sndE.sndE.sndE.sndE

theorem actual_square_root_bracket_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶
      (RationalArgmin.rationalLE (square (lower (var 0) (var 1) (var 2))) (fraction (var 0) (var 1)) ⋏
        (neg (RationalArgmin.rationalLE (square (upper (var 0) (var 1) (var 2))) (fraction (var 0) (var 1))) ⋏
          RationalArithmetic.add (upper (var 0) (var 1) (var 2)) (RationalArithmetic.negative (lower (var 0) (var 1) (var 2))) ≐
            fraction one (denominator (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.impI (.andI (lower_square_bound _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (upper_square_strict _ _ _ Prf.hyp1 Prf.hyp0) (bracket_width _ _ _ Prf.hyp1 Prf.hyp0)))))

theorem actual_half_angle_bounds_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ le (var 0) (var 1) ⟶
      (le (root (var 0) (var 1) (var 2)) (denominator (var 1) (var 2)) ⋏
        (le (var 0*var 2) (root (var 0) (var 1) (var 2)) ⋏
          ((root (var 0) (var 1) (var 2)*root (var 0) (var 1) (var 2)+deficit (var 0) (var 1) (var 2) ≐ radicand (var 0) (var 1) (var 2)) ⋏
            le (deficit (var 0) (var 1) (var 2)) (three*denominator (var 1) (var 2)))))) :=
  closeUniv 3 (.impI (.impI (.impI (.andI (root_unit_bound _ _ _ Prf.hyp0)
    (.andI (root_scaled_lower _ _ _ Prf.hyp0) (.andI (root_deficit _ _ _) (deficit_bound _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))))

theorem actual_square_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ le (var 0) (var 1) ⟶
      RationalArgmin.rationalLE (squareGap (var 0) (var 1) (var 2)) (fraction three (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (square_gap_bound _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_relative_initialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (var 2) ⟶ le (var 1) (var 0) ⟶
      RationalArgmin.rationalLE (square (upper (var 0) (var 1) (var 2))) (relativeBound (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (upper_relative_bound _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_zero_and_unit_roots_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (root zero (var 0) (var 1) ≐ zero ⋏ root (var 0) (var 0) (var 1) ≐ denominator (var 0) (var 1)) :=
  closeUniv 2 (.andI (root_zero _ _) (diagonal_root _ _))

theorem actual_square_root_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) ⋏
      ((fstT (run (var 0) (var 1) (var 2)) ≐ root (var 0) (var 1) (var 2)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2))) ≐ denominator (var 1) (var 2)) ⋏
          ((fstT (sndT (sndT (run (var 0) (var 1) (var 2)))) ≐ lower (var 0) (var 1) (var 2)) ⋏
            ((fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐ upper (var 0) (var 1) (var 2)) ⋏
              sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2))))) ≐ deficit (var 0) (var 1) (var 2)))))) :=
  closeUniv 3 (.andI (program_at _ _ _) (.andI (returned_root _ _ _) (.andI (returned_denominator _ _ _)
    (.andI (returned_lower _ _ _) (.andI (returned_upper _ _ _) (returned_deficit _ _ _))))))

end LeanProofs.IPRA.Analysis.RationalSquareRootBounds
