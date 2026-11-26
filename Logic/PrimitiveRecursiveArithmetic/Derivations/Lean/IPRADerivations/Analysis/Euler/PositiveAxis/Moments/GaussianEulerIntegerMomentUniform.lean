import IPRADerivations.Analysis.Euler.PositiveAxis.Moments.GaussianEulerIntegerMomentIntegrand
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName

/-!
# Actual moment rows with one uniform compact observation clock

The numerical time-power bound T^N supplies the original uniform-clock
constant-product constructor. Its raw observations are exactly t^N
times the unchanged base Euler observations at a clock depending only
on N,T,p. This retains genuine original shifted-Euler compatibility.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegerMomentUniform

open_ipra
open GaussianEulerIntegerMomentIntegrand (source monomial shiftedData)
open GaussianEulerIntegrandName (data)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerIntegrandName.nameF

def nameF : PR 2 := GaussianBoundedConstantProductName.nameF I
def nameData (z B N a b T : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data (pw T N) (monomial N a b) (data z B a b)
def clock (p N T : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p (pw T N)
ipra_subst nameData
ipra_subst clock

theorem input (z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    GaussianBoundedConstantProductName.input I (pw T N) (monomial N a b) (data z B a b) :=
  .andI (GaussianEulerIntegrandName.name_regular _ _ _ _ (GaussianEulerIntegerMomentIntegrand.time_source z B a b E T h))
    (GaussianEulerIntegerMomentIntegrand.monomial_bound N a b E T h.andE₂)

theorem name_regular (z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    pointCN nameF (nameData z B N a b T) :=
  GaussianBoundedConstantProductName.name_regular I _ _ _ (input z B N a b E T h)

theorem original_shifted_cross (z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    crossEquivalent I nameF (shiftedData z B N a b) (nameData z B N a b T) :=
  cross_trans _ _ _ _ _ _ (GaussianEulerIntegerMomentIntegrand.original_pointwise z B N a b E T h)
    (cross_symm _ _ _ _ (GaussianBoundedConstantProductName.ordinary_product_identity I _ _ _ (input z B N a b E T h)))

theorem sample_at (p z B N a b T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (nameData z B N a b T) ≐ qmul (monomial N a b) (ap2 I (clock p N T) (data z B a b)) :=
  GaussianBoundedConstantProductName.sample_at I p _ _ _

theorem original_observations (p q z B N a b E T : PTm n) (h : Γ ⊢[PRAAx] source B a b E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I p (shiftedData z B N a b)) (ap2 nameF q (nameData z B N a b T))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_shifted_cross z B N a b E T h)

theorem actual_original_uniform_integer_moment_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (ap2 nameF (var 0) (nameData (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) ≐
      qmul (monomial (var 3) (var 4) (var 5)) (ap2 I (clock (var 0) (var 3) (var 6)) (data (var 1) (var 2) (var 4) (var 5)))) :=
  closeUniv 7 (sample_at _ _ _ _ _ _ _)
theorem actual_original_shifted_uniform_integer_moment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 3) (var 4) (var 5) (var 6) ⟶ crossEquivalent I nameF
      (shiftedData (var 0) (var 1) (var 2) (var 3) (var 4)) (nameData (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))) :=
  closeUniv 7 (.impI (original_shifted_cross _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegerMomentUniform
