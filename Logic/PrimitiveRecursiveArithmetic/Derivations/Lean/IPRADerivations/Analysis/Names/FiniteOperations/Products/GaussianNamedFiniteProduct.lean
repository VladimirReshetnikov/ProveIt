import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalRectangularProduct
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic

/-!
# Finite products of simultaneous Gaussian observations

Each row program takes precision, row index, and data. The product
uses the actual ascending rational fold. Uniform row bounds and a
common pairwise error give a finite product estimate for any internal
row count, including an empty range.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProduct

open_ipra
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianNameArithmetic (product_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono_same)
open GaussianRationalFiniteProduct (product_zero product_canonical)
open GaussianRationalHorner (canonical qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (qone qone_bounded bounded_product bound_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body (f : PR 3) : PTm 3 := ap3 f (var 0) (var 1) (var 2)
def sample (f : PR 3) (p N x : PTm n) : PTm n := GaussianRationalRectangularProduct.row (body f) p N x

def rowBoundsAt (f : PR 3) (p N R x : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ bounded (ap3 f (Syn.shift p) (var 0) (Syn.shift x)) (Syn.shift R) one)

def rowDistance (f g : PR 3) (p q N E K x y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ distanceBounded
    (ap3 f (Syn.shift p) (var 0) (Syn.shift x)) (ap3 g (Syn.shift q) (var 0) (Syn.shift y))
    (Syn.shift E) (Syn.shift K))

def radius (R i : PTm n) : PTm n := pw (R+one) i
def amplification (R i : PTm n) : PTm n := i*radius R i

ipra_subst sample

ipra_subst rowBoundsAt [one, Syn.subst_shift, Syn.shift_subst]

ipra_subst rowDistance [Syn.subst_shift, Syn.shift_subst]

ipra_subst radius [one]

ipra_subst amplification

theorem sample_zero (f : PR 3) (p x : PTm n) : Γ ⊢[PRAAx] sample f p zero x ≐ qone :=
  product_zero _ _

theorem sample_succ (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] sample f p (succ i) x ≐ qmul (sample f p i x) (ap3 f p i x) := by
  simpa [sample,body,inst3] using GaussianRationalRectangularProduct.row_succ (Γ := Γ) (body f) p i x

theorem sample_canonical (f : PR 3) (p N x : PTm n) : Γ ⊢[PRAAx] canonical (sample f p N x) :=
  product_canonical _ _ _

theorem row_bound_at (f : PR 3) (p N R x i : PTm n) (hb : Γ ⊢[PRAAx] rowBoundsAt f p N R x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] bounded (ap3 f p i x) R one := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ bounded (ap3 f p i x) R one := by
    simpa [rowBoundsAt,one] using hb.allE i
  exact .impE rule hi

theorem row_distance_at (f g : PR 3) (p q N E K x y i : PTm n)
    (hd : Γ ⊢[PRAAx] rowDistance f g p q N E K x y) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded (ap3 f p i x) (ap3 g q i y) E K := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ distanceBounded (ap3 f p i x) (ap3 g q i y) E K := by
    simpa [rowDistance] using hd.allE i
  exact .impE rule hi

private theorem radius_succ (R i : PTm n) : Γ ⊢[PRAAx] radius R (succ i) ≐ radius R i*(R+one) := pw_succ _ _

private theorem pref_radius (f : PR 3) (p i R x : PTm n)
    (old : Γ ⊢[PRAAx] bounded (sample f p i x) (radius R i) one)
    (last : Γ ⊢[PRAAx] bounded (ap3 f p i x) R one) :
    Γ ⊢[PRAAx] bounded (sample f p (succ i) x) (radius R (succ i)) one := by
  have h : Γ ⊢[PRAAx] le (radius R i*R) (radius R (succ i)) :=
    le_congr (.eqRefl _) (radius_succ R i).eqSymm (le_mul_mono (le_refl _) (le_add_right R one))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl _) (le_refl _)) (le_refl _)
      (le_congr (by ipra_ring) (by ipra_ring) h)
      (bound_congr (sample_succ f p i x).eqSymm (.eqRefl _) (.eqRefl _)
        (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) old last))

private theorem increment_error (R i E : PTm n) :
    Γ ⊢[PRAAx] le (amplification R i*E*R+radius R i*E) (amplification R (succ i)*E) := by
  apply le_of_eq_add (d := (R+i)*radius R i*E)
  have step : Γ ⊢[PRAAx] amplification R (succ i)*E ≐ (succ i*(radius R i*(R+one)))*E :=
    congrMul (congrMul (.eqRefl _) (radius_succ R i)) (.eqRefl _)
  exact step.eqTrans (by unfold amplification; ipra_ring)

def prefixLaw (f g : PR 3) (p q N R E K x y i : PTm n) : Fm PTm n := le i N ⟶
  ((bounded (sample f p i x) (radius R i) one ⋏ bounded (sample g q i y) (radius R i) one) ⋏
    distanceBounded (sample f p i x) (sample g q i y) (amplification R i*E) K)

ipra_subst prefixLaw [one]

private theorem prefix_zero (f g : PR 3) (p q N R E K x y : PTm n) (hk : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] prefixLaw f g p q N R E K x y zero := by
  have rz : Γ ⊢[PRAAx] one ≐ radius R zero := (pw_zero _).eqSymm
  have ez : Γ ⊢[PRAAx] zero ≐ amplification R zero*E := by unfold amplification; ipra_ring
  exact .impI (Prf.andI
    (.andI (bound_congr (sample_zero f p x).eqSymm rz (.eqRefl _) qone_bounded)
      (bound_congr (sample_zero g q y).eqSymm rz (.eqRefl _) qone_bounded))
    (distance_congr (sample_zero f p x).eqSymm (sample_zero g q y).eqSymm ez (.eqRefl _)
      (distance_refl_zero qone K hk))).wk

private theorem prefix_succ (f g : PR 3) (p q N R E K x y i : PTm n)
    (hk : Γ ⊢[PRAAx] le one K) (hf : Γ ⊢[PRAAx] rowBoundsAt f p N R x) (hg : Γ ⊢[PRAAx] rowBoundsAt g q N R y)
    (hd : Γ ⊢[PRAAx] rowDistance f g p q N E K x y) (previous : Γ ⊢[PRAAx] prefixLaw f g p q N R E K x y i) :
    Γ ⊢[PRAAx] prefixLaw f g p q N R E K x y (succ i) := by
  refine .impI ?_
  let Δ := le (succ i) N :: Γ
  have hi : Δ ⊢[PRAAx] lt i N := Prf.hyp0
  have prev := Prf.impE previous.wk (le_of_lt hi)
  have a := row_bound_at f p N R x i hf.wk hi
  have b := row_bound_at g q N R y i hg.wk hi
  have d := row_distance_at f g p q N E K x y i hd.wk hi
  have raw := product_distance (sample f p i x) (sample g q i y) (ap3 f p i x) (ap3 g q i y)
    (amplification R i*E) E K R (radius R i) hk.wk prev.andE₂ d a prev.andE₁.andE₂
  have close := distance_radius_mono_same hk.wk (increment_error R i E) raw
  exact .andI (.andI (pref_radius f p i R x prev.andE₁.andE₁ a) (pref_radius g q i R y prev.andE₁.andE₂ b))
    (distance_congr (sample_succ f p i x).eqSymm (sample_succ g q i y).eqSymm (.eqRefl _) (.eqRefl _) close)

theorem prefix_control (f g : PR 3) (p q N R E K x y i : PTm n)
    (hk : Γ ⊢[PRAAx] le one K) (hf : Γ ⊢[PRAAx] rowBoundsAt f p N R x) (hg : Γ ⊢[PRAAx] rowBoundsAt g q N R y)
    (hd : Γ ⊢[PRAAx] rowDistance f g p q N E K x y) :
    Γ ⊢[PRAAx] prefixLaw f g p q N R E K x y i := by
  have hk' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift,Syn.shift,one] using hk.shift
  have hf' : Γ.map Fm.shift ⊢[PRAAx] rowBoundsAt f (Syn.shift p) (Syn.shift N) (Syn.shift R) (Syn.shift x) :=
    by simpa [Fm.shift,Syn.shift] using hf.shift
  have hg' : Γ.map Fm.shift ⊢[PRAAx] rowBoundsAt g (Syn.shift q) (Syn.shift N) (Syn.shift R) (Syn.shift y) :=
    by simpa [Fm.shift,Syn.shift] using hg.shift
  have hd' : Γ.map Fm.shift ⊢[PRAAx] rowDistance f g (Syn.shift p) (Syn.shift q) (Syn.shift N)
      (Syn.shift E) (Syn.shift K) (Syn.shift x) (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw f g (Syn.shift p) (Syn.shift q) (Syn.shift N) (Syn.shift R) (Syn.shift E)
      (Syn.shift K) (Syn.shift x) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,⟨le_QF _ _,le_QF _ _⟩,le_QF _ _⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero f g p q N R E K x y hk
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ f g _ _ _ _ _ _ _ _ (var 0) hk'.wk hf'.wk hg'.wk hd'.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i

theorem sample_distance (f g : PR 3) (p q N R E K x y : PTm n)
    (hk : Γ ⊢[PRAAx] le one K) (hf : Γ ⊢[PRAAx] rowBoundsAt f p N R x) (hg : Γ ⊢[PRAAx] rowBoundsAt g q N R y)
    (hd : Γ ⊢[PRAAx] rowDistance f g p q N E K x y) :
    Γ ⊢[PRAAx] distanceBounded (sample f p N x) (sample g q N y) (amplification R N*E) K :=
  (Prf.impE (prefix_control f g p q N R E K x y N hk hf hg hd) (le_refl _)).andE₂

private theorem same_rows (f : PR 3) (p N x : PTm n) : Γ ⊢[PRAAx] rowDistance f f p p N zero one x x := by
  refine .allI (.impI ?_)
  simpa [rowDistance,Syn.shift,one] using
    (distance_refl_zero (ap3 f (Syn.shift p) (var 0) (Syn.shift x)) one (le_refl one))

theorem sample_bound (f : PR 3) (p N R x : PTm n) (hf : Γ ⊢[PRAAx] rowBoundsAt f p N R x) :
    Γ ⊢[PRAAx] bounded (sample f p N x) (radius R N) one :=
  (Prf.impE (prefix_control f f p p N R zero one x x N (le_refl one) hf hf (same_rows f p N x)) (le_refl _)).andE₁.andE₁

theorem actual_finite_named_row_distance_closed (f g : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 5) ⋏ (rowBoundsAt f (var 0) (var 2) (var 3) (var 6) ⋏ rowBoundsAt g (var 1) (var 2) (var 3) (var 7))) ⟶
      rowDistance f g (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (sample f (var 0) (var 2) (var 6)) (sample g (var 1) (var 2) (var 7))
        (amplification (var 3) (var 2)*var 4) (var 5)) :=
  closeUniv 8 (.impI (.impI (sample_distance f g _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProduct
