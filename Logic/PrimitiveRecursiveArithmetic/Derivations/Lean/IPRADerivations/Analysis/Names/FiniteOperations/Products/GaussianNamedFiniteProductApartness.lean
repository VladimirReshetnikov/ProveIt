import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductName
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# Apartness of a finite named Gaussian product

Uniform separation of each used row by 1/D gives the actual
ascending product separation by 1/D^N. A computed binary clock
provides the margin required by the named reciprocal constructor.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductApartness

open_ipra
open ComplexLogarithmRemainder (oneCode normSq normSq_one)
open GaussianCoefficientNameBounds (unit)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianNamedFiniteProductName (nameF data name_at clock)
open GaussianNameReciprocal (lower apart anchor lower_congr)
open GaussianRationalHorner (ofGaussian_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalLowerBounds (lower_from_representation lower_to_cleared product_lower)
open GaussianRationalReciprocal (qone)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (D N : PTm n) : PTm n := pw D N
def apartClock (N D : PTm n) : PTm n := GaussianRootSchedule.binaryLength (denominator D N)

def rowLowerAt (f : PR 3) (p N D x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ lower (ap3 f (Syn.shift p) (var 0) (Syn.shift x)) (Syn.shift D))
def rowLower (f : PR 3) (N D x : PTm n) : Fm PTm n :=
  .all (rowLowerAt f (var 0) (Syn.shift N) (Syn.shift D) (Syn.shift x))

ipra_subst denominator

ipra_subst apartClock

ipra_subst rowLowerAt [Syn.subst_shift, Syn.shift_subst]

ipra_subst rowLower [Syn.subst_shift, Syn.shift_subst]

theorem rows_at (f : PR 3) (p N D x : PTm n) (h : Γ ⊢[PRAAx] rowLower f N D x) :
    Γ ⊢[PRAAx] rowLowerAt f p N D x := by simpa [rowLower] using h.allE p

theorem row_at (f : PR 3) (p N D x i : PTm n) (h : Γ ⊢[PRAAx] rowLowerAt f p N D x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] lower (ap3 f p i x) D := by
  have test : Γ ⊢[PRAAx] lt i N ⟶ lower (ap3 f p i x) D := by simpa [rowLowerAt] using h.allE i
  exact .impE test hi

theorem denominator_positive (D N : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (denominator D N) :=
  GaussianFactorBudget.power_positive D N hD

theorem weaken_margin (q D E : PTm n) (hd : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] le D E)
    (h : Γ ⊢[PRAAx] lower q D) : Γ ⊢[PRAAx] lower q E := by
  let a := rawGaussian q
  let K := rawDen q
  have hp := raw_den_positive (Γ := Γ) q
  have rep := raw_represents (Γ := Γ) q
  have r := lower_to_cleared q a K one D hp hd rep h
  exact lower_from_representation q a K one E hp (le_trans hd he) rep
    (le_trans r (le_mul_mono (le_mul_mono he he) (le_refl (normSq a))))

private theorem unit_margin : Γ ⊢[PRAAx] lower (qone : PTm n) one :=
  lower_from_representation _ oneCode one one one (le_refl _) (le_refl _) (ofGaussian_represents _ _ (le_refl _))
    (le_congr (by ipra_ring) (congrMul (.eqRefl _) normSq_one).eqSymm (le_refl _))

def prefixLaw (f : PR 3) (p N D x i : PTm n) : Fm PTm n :=
  le i N ⟶ lower (sample f p i x) (denominator D i)

ipra_subst prefixLaw

private theorem prefix_zero (f : PR 3) (p N D x : PTm n) :
    Γ ⊢[PRAAx] prefixLaw f p N D x zero :=
  .impI (lower_congr (sample_zero f p x).eqSymm (pw_zero D).eqSymm unit_margin).wk

private theorem prefix_succ (f : PR 3) (p N D x i : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] rowLowerAt f p N D x) (previous : Γ ⊢[PRAAx] prefixLaw f p N D x i) :
    Γ ⊢[PRAAx] prefixLaw f p N D x (succ i) := by
  refine .impI ?_
  let Δ := le (succ i) N :: Γ
  have hi : Δ ⊢[PRAAx] lt i N := Prf.hyp0
  have prev := Prf.impE previous.wk (le_of_lt hi)
  have last := row_at f p N D x i hr.wk hi
  have both := product_lower (sample f p i x) (ap3 f p i x) one (denominator D i) one D
    (denominator_positive D i hD.wk) hD.wk prev last
  exact GaussianRationalLowerBounds.lower_congr (sample_succ f p i x).eqSymm (one_mul one) (pw_succ D i).eqSymm both

theorem prefix_lower (f : PR 3) (p N D x i : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] rowLowerAt f p N D x) :
    Γ ⊢[PRAAx] prefixLaw f p N D x i := by
  have hD' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift,one] using hD.shift
  have hr' : Γ.map Fm.shift ⊢[PRAAx] rowLowerAt f (Syn.shift p) (Syn.shift N) (Syn.shift D) (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using hr.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw f (Syn.shift p) (Syn.shift N) (Syn.shift D) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero (Γ := Γ) f p N D x
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ f _ _ _ _ (var 0) hD'.wk hr'.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i

theorem sample_lower (f : PR 3) (p N D x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] rowLowerAt f p N D x) :
    Γ ⊢[PRAAx] lower (sample f p N x) (denominator D N) :=
  .impE (prefix_lower f p N D x N hD hr) (le_refl _)

theorem name_lower (f : PR 3) (p N R L D x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] rowLower f N D x) :
    Γ ⊢[PRAAx] lower (ap2 (nameF f) p (data N R L x)) (denominator D N) :=
  lower_congr (name_at f p N R L x).eqSymm (.eqRefl _)
    (sample_lower f (clock N R L p) N D x hD (rows_at f (clock N R L p) N D x hr))

theorem clock_budget (N D : PTm n) : Γ ⊢[PRAAx] le (denominator D N) (unit (apartClock N D)) :=
  (GaussianRootSchedule.binary_length_correct (denominator D N)).andE₁

theorem name_apart (f : PR 3) (N R L D x : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] rowLower f N D x) : Γ ⊢[PRAAx] apart (nameF f) (apartClock N D) (data N R L x) :=
  weaken_margin _ (denominator D N) (unit (apartClock N D)) (denominator_positive D N hD) (clock_budget N D)
    (name_lower f (anchor (apartClock N D)) N R L D x hD hr)

theorem name_empty_at (f : PR 3) (p R L x : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data zero R L x) ≐ qone :=
  (name_at f p zero R L x).eqTrans (sample_zero f (clock zero R L p) x)

theorem name_empty_apart (f : PR 3) (R L x : PTm n) :
    Γ ⊢[PRAAx] apart (nameF f) zero (data zero R L x) :=
  lower_congr (name_empty_at f (anchor zero) R L x).eqSymm (pw_zero two).eqSymm unit_margin

theorem actual_internal_product_apart_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 3) ⋏ rowLower f (var 0) (var 3) (var 4)) ⟶
      apart (nameF f) (apartClock (var 0) (var 3)) (data (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (name_apart f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_empty_product_name_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (nameF f) (var 0) (data zero (var 1) (var 2) (var 3)) ≐ qone) :=
  closeUniv 4 (name_empty_at f _ _ _ _)

theorem actual_empty_product_apart_closed (f : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (apart (nameF f) zero (data zero (var 0) (var 1) (var 2))) :=
  closeUniv 3 (name_empty_apart f _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductApartness
