import IPRADerivations.Analysis.Names.GaussianNamedHalf
import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.GaussianNamedBoundedSquareRoot
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift

/-!
# The radial logarithm of a positive rational squared radius

The original logarithm of the squared radius is halved as a regular
name. Its exponential agrees with independent dyadic square-root search.
The proof uses a nonnegative representative from the squared modulus
of the exponential at a quarter of the logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalHalfLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianPositiveRationalLogarithm (source logF fraction)
open GaussianNamedBoundedSquareRoot (sqrtF observations square_root_cross)
open GaussianExponentialRealPart (doubleRealF doubleRealData squareF squareData)
open GaussianRadiusExponentialName (input)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "L" => GaussianPositiveRationalLogarithm.data

def nameF : PR 2 := GaussianNamedHalf.nameF logF
def data (a b : PTm n) : PTm n := GaussianNamedHalf.data logF (L a b)
def exponentialData (a b : PTm n) : PTm n := exponentialInputData nameF (data a b)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (data a b) = data (Syn.subst σ a) (Syn.subst σ b) := by simp [data]

theorem regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data a b) :=
  GaussianNamedHalf.regular logF (L a b) (GaussianPositiveRationalLogarithm.name_regular a b h)

theorem real (a b : PTm n) : Γ ⊢[PRAAx] realSamples nameF (data a b) := by
  apply GaussianNamedHalf.real
  refine .allI ?_
  have ed : Syn.shift (L a b) = L (Syn.shift a) (Syn.shift b) :=
    GaussianPositiveRationalLogarithm.subst_data _ _ _
  rw [ed]
  exact .andI (GaussianPositiveRationalLogarithm.sample_canonical (var 0) (Syn.shift a) (Syn.shift b))
    (GaussianPositiveRationalLogarithm.sample_axis (var 0) (Syn.shift a) (Syn.shift b))

theorem exponential_square (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (E nameF) (E nameF)) constantF
      (multiplyData (E nameF) (E nameF) (exponentialData a b) (exponentialData a b)) (fraction a b) := by
  have hx := exponential_input nameF (data a b) (regular a b h)
  have hy := GaussianPositiveRationalLogarithm.exponential_input a b h
  have sum := GaussianNamedHalf.double logF (L a b) (GaussianPositiveRationalLogarithm.name_regular a b h)
  have exp := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent nameF nameF logF
    _ _ _ (data a b) (data a b) (L a b) hx hx hy sum
  exact cross_trans _ _ _ _ _ _ exp (GaussianPositiveRationalLogarithm.exponential_fraction a b h)

def quarterData (a b : PTm n) : PTm n := GaussianNamedHalf.data nameF (data a b)
abbrev quarterF : PR 2 := GaussianNamedHalf.nameF nameF
abbrev positiveF : PR 2 := squareF (E quarterF)
def positiveData (a b : PTm n) : PTm n := squareData (E quarterF) (exponentialInputData quarterF (quarterData a b))

@[simp] theorem subst_positiveData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (positiveData a b) = positiveData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [positiveData,quarterData,exponentialInputData]

theorem positive_cross (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent positiveF (E nameF) (positiveData a b) (exponentialData a b) := by
  let f := quarterF
  let x := quarterData a b
  let y := data a b
  have hy := regular a b h
  have hx := GaussianNamedHalf.regular nameF y hy
  have hxR := exponential_input f x hx
  have halve := GaussianNamedHalf.double nameF y hy
  have conj := GaussianNamedHalf.conjugate_fixed f x hx (GaussianNamedHalf.real nameF y (real a b))
  have branch := GaussianNamedGammaHalfShift.add_cross f f (GaussianNameConjugation.nameF f) f x x x x
    hx hx (GaussianNameConjugation.regular _ _ hx) hx (cross_refl _ _ hx) conj
  have doubleEq := cross_trans _ _ _ _ _ _ branch halve
  have product := GaussianExponentialRealPart.exponential_norm_square f (U f x) x hxR
  exact cross_trans _ _ _ _ _ _ product
    (GaussianExponentialRadiusIndependence.independent_radii_proper (doubleRealF f) nameF _ _ _ _
      (GaussianExponentialRealPart.double_real_input f (U f x) x hxR) (exponential_input _ _ hy) doubleEq)

private theorem positive_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN positiveF (positiveData a b) :=
  GaussianExponentialRealPart.square_regular _ _ (GaussianRadiusExponentialName.name_regular _ _ _
    (exponential_input _ _ (GaussianNamedHalf.regular nameF _ (regular a b h))))

private theorem positive_observations (a b : PTm n) :
    Γ ⊢[PRAAx] observations positiveF (positiveData a b) := by
  refine .allI ?_
  let x := exponentialInputData quarterF (quarterData (Syn.shift a) (Syn.shift b))
  let p : PTm (n+1) := var 0
  let f := E quarterF
  have hc := GaussianNameArithmetic.multiply_canonical (Γ := Γ.map Fm.shift) f
    (GaussianNameConjugation.nameF f) x x p
  have hp := GaussianExponentialRealPart.square_sample_positive (Γ := Γ.map Fm.shift) f p x
  have ed : Syn.shift (positiveData a b) = positiveData (Syn.shift a) (Syn.shift b) :=
    subst_positiveData _ _ _
  rw [ed]
  exact .andI hc (GaussianRationalNonnegativeFractions.nonnegative_of_positive _ hc hp)

private theorem fraction_observations (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] observations constantF (fraction a b) := by
  have hb' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift,one] using hb.shift
  refine .allI ?_
  let q := fraction (Syn.shift a) (Syn.shift b)
  have e := constant_at (Γ := Γ.map Fm.shift) (var 0) q
  have hc := GaussianRationalHorner.ofGaussian_canonical
    (ComplexLogarithmRemainder.scale (Syn.shift a) ComplexLogarithmRemainder.oneCode) (Syn.shift b) hb'
  have hp := GaussianRationalNonnegativeFractions.fraction_nonnegative (Syn.shift a) (Syn.shift b) hb'
  have ed : Syn.shift (fraction a b) = q := GaussianPositiveRationalLogarithm.subst_fraction _ _ _
  rw [ed]
  exact .andI (GaussianRationalHorner.canonical_congr e hc)
    (GaussianRationalNonnegativeProducts.congr e.eqSymm hp)

theorem exponential_square_root (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) (sqrtF constantF) (exponentialData a b) (fraction a b) := by
  let x := positiveData a b
  let y := exponentialData a b
  let f := positiveF
  let g := E nameF
  have hx := positive_regular a b h
  have hy := GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (regular a b h))
  have e := positive_cross a b h
  have sq := cross_trans _ _ _ _ _ _ (multiply_cross f g f g x y x y hx hy hx hy e e) (exponential_square a b h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ e)
    (square_root_cross f constantF x (fraction a b) hx (positive_observations a b) (fraction_observations a b h.andE₂) sq)

theorem actual_exponential_positive_half_logarithm_square_root_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ crossEquivalent (E nameF) (sqrtF constantF)
        (exponentialData (var 0) (var 1)) (fraction (var 0) (var 1))) :=
  closeUniv 2 (.impI (exponential_square_root _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalHalfLogarithm
