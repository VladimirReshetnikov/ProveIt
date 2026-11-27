import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorDerivativeUniformInput
import IPRADerivations.Analysis.Geometry.DiskNames.GaussianNamedDiskDemandLift

/-!
# Cofinal Barnes factorial names at regular Gaussian inputs

A primitive-recursive input clock freezes one observation of the original
regular Gaussian name. The original cofinal factorial Taylor program
then evaluates that rational observation at a separate output precision.
The Taylor order and disk radius are both internal parameters.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylor

open_ipra
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalNamedDemand (source native_source)
open GaussianBarnesCanonicalTaylorDerivativeUniformInput (inputClock inputClock_monotone uniform_input)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNamedDiskDemandLift (input_budget output_budget)
open GaussianNamedInverseRate (independentRate rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data

def data (x R e : PTm n) : PTm n := pairT x (pairT R e)
def clock (p R e : PTm n) : PTm n := succ (inputClock R e (succ p))

def frozenData (f : PR 2) (k x R e : PTm n) : PTm n :=
  let q := ap2 f k x
  fd (rawGaussian q) (R+one) (rawDen q) e e

def sample (f : PR 2) (p x R e : PTm n) : PTm n :=
  ap2 F (succ p) (frozenData f (clock p R e) x R e)

def nameF (f : PR 2) : PR 2 :=
  PTm.toPR (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x R e : PTm n) :
    Syn.subst σ (data x R e) = data (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ e) := by simp [data]

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x R e : PTm n) :
    Syn.subst σ (frozenData f k x R e) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ e) := by
  simp [frozenData,GaussianBarnesCanonicalTaylorProductDerivativeName.data,
    GaussianBarnesCanonicalTaylorProductDerivativeName.coefficientData,LeanProofs.IPRA.Analysis.Products.fact,one]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x R e : PTm n) :
    Syn.subst σ (sample f p x R e) = sample f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ e) := by
  simp [sample,clock]

theorem sample_at (f : PR 2) (p x R e : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x R e) ≐ sample f p x R e := by
  simpa [nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (sample f (var 0) (var 1) (var 2) (var 3)) p ![x, R, e])

theorem retains (e : PTm n) : Γ ⊢[PRAAx] le e (previous e) := le_trans (le_succ_self e) (le_succ_self (succ e))

theorem late_rate (f g : PR 2) (s k l x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (succ (inputClock R e s)) k) (hl : Γ ⊢[PRAAx] le (succ (inputClock R e s)) l) :
    Γ ⊢[PRAAx] independentRate F F (frozenData f k x R e) (frozenData g l y R e) one (unit s) := by
  let a := inputClock R e s
  let q := ap2 f k x
  let r := ap2 g l y
  have den := positive_product _ _ (unit_positive (Γ := Γ) k) (unit_positive l)
  have recoded := GaussianFastValueCut.recode_distance_bound q r _ _ den (cross_at f g x y k l he)
  have fine := distance_radius_mono _ _ _ _ one (unit a) den (unit_positive a) (input_budget k l a hk hl) recoded
  exact uniform_input (rawGaussian q) (rawGaussian r) R (rawDen q) (rawDen r) e e s
    (native_source f k x R hf) (native_source g l y R hg) (retains e) fine

private theorem observations_of_le (f g : PR 2) (p q x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x R e) (sample g q y R e) (unit p+unit q) (unit p*unit q) := by
  have fit := Common.succ_le_succ (inputClock_monotone R e (succ p) (succ q) (Common.succ_le_succ hpq))
  have rate := late_rate f g (succ p) (clock p R e) (clock q R e) x y R e hf hg he (le_refl _) fit
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive (succ p)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (output_budget p q)
    (rate_at _ _ _ _ _ _ (succ p) (succ q) rate)

theorem observations (f g : PR 2) (p q x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x R e) (sample g q y R e) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le f g p q x y R e hf.wk hg.wk he.wk Prf.hyp0) ?_
  have rev := observations_of_le g f q p y x R e hg.wk hf.wk (cross_symm _ _ _ _ he.wk) Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem proper (f g : PR 2) (x y R e : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R e) (data y R e) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have left : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have right : Δ ⊢[PRAAx] source g (sh y) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have same : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have obs := observations f g p q (sh x) (sh y) (sh R) (sh e) left right same
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ] using
    distance_congr (sample_at f p (sh x) (sh R) (sh e)).eqSymm
      (sample_at g q (sh y) (sh R) (sh e)).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem regular (f : PR 2) (x R e : PTm n) (hf : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x R e) :=
  proper f f x x R e hf hf (cross_refl f x hf.andE₁)

theorem actual_named_Barnes_factorial_Taylor_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular f _ _ _ Prf.hyp0))

theorem actual_named_Barnes_factorial_Taylor_proper_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 2)) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2) (var 3)) (data (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (proper f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFactorialTaylor
