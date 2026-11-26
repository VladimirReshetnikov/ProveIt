import IPRADerivations.Analysis.Inequalities.GaussianRationalNonnegativeFractions
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# Independent dyadic square-root sampling of a named radicand

At query (p), bounded rational square-root search reads the radicand
at query (2(p+2)). A certified regular nonnegative square root proves
the accuracy of this program. That square root is never read by the
sampler.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedBoundedSquareRoot

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates (candidate)
open GaussianRationalNonnegativeFractions (numerator denominator denominator_positive fraction_at)
open GaussianRationalNonnegativeProducts (nonnegative)
open GaussianRationalHorner (canonical qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans point_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def observations (f : PR 2) (x : PTm n) : Fm PTm n := .all
  (canonical (ap2 f (var 0) (Syn.shift x)) ⋏ nonnegative (ap2 f (var 0) (Syn.shift x)))

@[simp] theorem subst_observations {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x : PTm n) :
    (observations f x).subst σ = observations f (Syn.subst σ x) := by
  simp [observations,Syn.subst_shift,Syn.shift_subst]

theorem observation_at (f : PR 2) (p x : PTm n) (h : Γ ⊢[PRAAx] observations f x) :
    Γ ⊢[PRAAx] canonical (ap2 f p x) ⋏ nonnegative (ap2 f p x) := by
  simpa [observations] using h.allE p

def rootClock (p : PTm n) : PTm n := succ (succ p)
def radicandClock (p : PTm n) : PTm n := p+p
def rootPoint (g : PR 2) (p y : PTm n) : PTm n :=
  let q := ap2 g (radicandClock p) y
  fraction (candidate (numerator q) (denominator q) p) (unit p)
def sqrtF (g : PR 2) : PR 2 := PTm.toPR (rootPoint g (rootClock (var 0)) (var 1) : PTm 2)

@[simp] theorem subst_rootClock {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (rootClock p) = rootClock (Syn.subst σ p) := by simp [rootClock]
@[simp] theorem subst_radicandClock {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (radicandClock p) = radicandClock (Syn.subst σ p) := by simp [radicandClock]
@[simp] theorem subst_rootPoint {l : ℕ} (σ : Fin n → PTm l) (g : PR 2) (p y : PTm n) :
    Syn.subst σ (rootPoint g p y) = rootPoint g (Syn.subst σ p) (Syn.subst σ y) := by
  simp [rootPoint]

theorem sample_at (g : PR 2) (p y : PTm n) : Γ ⊢[PRAAx] ap2 (sqrtF g) p y ≐ rootPoint g (rootClock p) y := by
  simpa [sqrtF,ap2] using toPR_eq (Γ := Γ) (rootPoint g (rootClock (var 0)) (var 1) : PTm 2) ![p,y]

private def cost (f : PR 2) (x : PTm n) : PTm n := multiplyModulus f f x x+one
private def sourceClock (f : PR 2) (p x : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (cost f x+one) (radicandClock p)

private theorem source_later (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le p (sourceClock f p x) :=
  le_trans (le_add_right p p) (le_add_right _ _)

private theorem scheduled_root (f g : PR 2) (p x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (nf : Γ ⊢[PRAAx] observations f x) (ng : Γ ⊢[PRAAx] observations g y)
    (sq : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) g (multiplyData f f x x) y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f (sourceClock f p x) x) (rootPoint g p y) (num 3) (unit p) := by
  let t := sourceClock f p x
  let v := radicandClock p
  let U := unit t
  let P := unit v
  let C := cost f x
  let Z := ap2 f t x
  let W := ap2 g v y
  let X := ap2 (multiplyF f f) t (multiplyData f f x x)
  let a := numerator Z
  let b := denominator Z
  have time : Γ ⊢[PRAAx] le ((C+one)*P) U := GaussianFastValueCut.query_budget _ _
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  have hP : Γ ⊢[PRAAx] le one P := unit_positive v
  have hD := positive_product (Γ := Γ) U P hU hP
  have readZ := observation_at f t x nf
  have readW := observation_at g v y ng
  have eqZ : Γ ⊢[PRAAx] Z ≐ fraction a b := fraction_at Z readZ.andE₁ readZ.andE₂
  have eqW : Γ ⊢[PRAAx] W ≐ fraction (numerator W) (denominator W) := fraction_at W readW.andE₁ readW.andE₂
  have hb := denominator_positive (Γ := Γ) Z
  have eqSquare : Γ ⊢[PRAAx] qmul Z Z ≐ fraction (a*a) (b*b) :=
    (GaussianRationalSyntheticDivision.qmul_congr eqZ eqZ).eqTrans
      (GaussianEulerDampedTimeRate.fraction_product a b a b hb hb)
  have raw : Γ ⊢[PRAAx] distanceBounded X (qmul Z Z) C U :=
    GaussianNameRingLaws.multiply_sample_error f f x x t hf hf
  have first : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) X (C*P) (U*P) :=
    distance_radius_mono _ _ _ _ _ _ hU hD (by ipra_le 0)
      (distance_symmetric _ _ _ _ hU (distance_congr (.eqRefl _) eqSquare (.eqRefl _) (.eqRefl _) raw))
  have second : Γ ⊢[PRAAx] distanceBounded X W (U+P) (U*P) :=
    cross_at _ _ _ _ t v sq
  have combined := distance_triangle_same _ _ _ _ _ _ hD first second
  have slack : Γ ⊢[PRAAx] le (C*P+(U+P)) (two*U) := by ipra_le sl time
  have rescaled : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) W (two*two) P :=
    distance_radius_mono _ _ _ _ _ _ hD hP (by ipra_le 𝔞 P * sl slack + 2 * 𝔞 U * 𝔞 P) combined
  have dyadic : Γ ⊢[PRAAx] P ≐ unit p*unit p := pw_add two p p
  have squareDistance := distance_congr (.eqRefl _) eqW (.eqRefl _) dyadic rescaled
  have roots := GaussianGammaHalfSqrtBrackets.bounded_root_close a b (numerator W) (denominator W) p two
    hb (denominator_positive W) squareDistance
  exact distance_congr eqZ.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) roots

private theorem root_clock_unit (p : PTm n) : Γ ⊢[PRAAx] unit (rootClock p) ≐ num 4*unit p := by
  unfold rootClock unit
  exact (pw_succ two (succ p)).eqTrans ((congrMul (pw_succ two p) (.eqRefl _)).eqTrans (by ipra_ring))

theorem square_root_at (f g : PR 2) (p q x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (nf : Γ ⊢[PRAAx] observations f x) (ng : Γ ⊢[PRAAx] observations g y)
    (sq : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) g (multiplyData f f x x) y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 (sqrtF g) q y) (unit p+unit q) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let r := rootClock q
  let D := unit r
  let t := sourceClock f r x
  let T := unit t
  let X := ap2 f p x
  let Y := ap2 f t x
  let Z := rootPoint g r y
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hD : Γ ⊢[PRAAx] le one D := unit_positive r
  have hT : Γ ⊢[PRAAx] le one T := unit_positive t
  have later : Γ ⊢[PRAAx] le D T :=
    GaussianExponentialReference.unit_monotone (source_later f r x)
  have pd := positive_product (Γ := Γ) P D hP hD
  have first : Γ ⊢[PRAAx] distanceBounded X Y (P+D) (P*D) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hP hT) pd (by ipra_le 𝔞 P^2*sl later)
      (point_at f x p t hf)
  have second : Γ ⊢[PRAAx] distanceBounded Y Z (num 3*P) (P*D) :=
    distance_radius_mono _ _ _ _ _ _ hD pd (by ipra_le 0) (scheduled_root f g r x y hf nf ng sq)
  have total := distance_triangle_same X Y Z (P+D) (num 3*P) (P*D) pd first second
  have e := natEq (root_clock_unit (Γ := Γ) q)
  have narrowed : Γ ⊢[PRAAx] distanceBounded X Z (P+Q) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ pd (positive_product _ _ hP hQ)
      (by ipra_le 0 with (𝔞 P)^2*e) total
  exact distance_congr (.eqRefl _) (sample_at g q y).eqSymm (.eqRefl _) (.eqRefl _) narrowed

theorem square_root_cross (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (nf : Γ ⊢[PRAAx] observations f x) (ng : Γ ⊢[PRAAx] observations g y)
    (sq : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) g (multiplyData f f x x) y) :
    Γ ⊢[PRAAx] crossEquivalent f (sqrtF g) x y := by
  refine .allI (.allI ?_)
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hf.shift.shift
  have af : Δ ⊢[PRAAx] observations f (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using nf.shift.shift
  have ag : Δ ⊢[PRAAx] observations g (sh y) := by simpa [Fm.shift,Syn.shift,sh,Δ] using ng.shift.shift
  have s : Δ ⊢[PRAAx] crossEquivalent (multiplyF f f) g (multiplyData f f (sh x) (sh x)) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using sq.shift.shift
  exact square_root_at f g (var 1) (var 0) (sh x) (sh y) h af ag s

theorem square_root_unique (f h g : PR 2) (x z y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hh : Γ ⊢[PRAAx] pointCN h z)
    (nf : Γ ⊢[PRAAx] observations f x) (nh : Γ ⊢[PRAAx] observations h z) (ng : Γ ⊢[PRAAx] observations g y)
    (sf : Γ ⊢[PRAAx] crossEquivalent (multiplyF f f) g (multiplyData f f x x) y)
    (sh : Γ ⊢[PRAAx] crossEquivalent (multiplyF h h) g (multiplyData h h z z) y) :
    Γ ⊢[PRAAx] crossEquivalent f h x z :=
  cross_trans _ _ _ _ _ _ (square_root_cross f g x y hf nf ng sf)
    (cross_symm _ _ _ _ (square_root_cross h g z y hh nh ng sh))

theorem actual_independent_named_square_root_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((pointCN f (var 1) ⋏ (observations f (var 1) ⋏ observations g (var 0))) ⟶
        crossEquivalent (multiplyF f f) g (multiplyData f f (var 1) (var 1)) (var 0) ⟶
        crossEquivalent f (sqrtF g) (var 1) (var 0)) :=
  closeUniv 2 (.impI (.impI
    (square_root_cross f g _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedBoundedSquareRoot
