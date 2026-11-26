import IPRADerivations.Analysis.GaussianBarnesCanonicalFiniteLogRows
import IPRADerivations.Analysis.GaussianNamedFiniteExponentialFold
import IPRADerivations.Analysis.GaussianNamedFiniteProductFamilyCongruence

/-!
# Exponentiating the actual finite Barnes logarithmic interval

The original synchronized finite logarithm exponentiates to the
original product of direct Barnes factors on the same interval.
The original schedules are retained on both sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLogProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHead (parameters subst_parameters)
open GaussianBarnesCanonicalLogTail (source row_source)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedFiniteExponentialFold (exponentialBody)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Row" => GaussianBarnesCanonicalLogFactor.nameF
local notation "Factor" => GaussianBarnesCanonicalFactor.nameF
local notation "Sum" => GaussianBarnesCanonicalFiniteLogRows.nameF
local notation "Finite" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "Head" => GaussianBarnesCanonicalHead.nameF
local notation "b" => GaussianBarnesCanonicalFiniteLogRows.body
local notation "h" => GaussianBarnesCanonicalHead.body
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

def expData (z R B N r : PTm n) : PTm n :=
  ed (GaussianBarnesCanonicalFiniteLog.radius R) (GaussianBarnesCanonicalFiniteLog.data z R B N r)

@[simp] theorem subst_expData {m : ℕ} (σ : Fin n → PTm m) (z R B N r : PTm n) :
    Syn.subst σ (expData z R B N r) =
      expData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by simp [expData]

theorem row_identity (z R B N i : PTm n) (hs : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent (Exp Row) Factor (inst2 (exponentialBody Row b) i (parameters z R B N))
      (inst2 h i (parameters z R B N)) := by
  let k := succ (N+i)
  let x := parameters z R B N
  let y := GaussianBarnesCanonicalLogFactor.expData z R B k
  let d := GaussianBarnesCanonicalFactor.data z R B k
  have a : Γ ⊢[PRAAx] inst2 (exponentialBody Row b) i x ≐ y := by
    rw [GaussianNamedFiniteExponentialFold.exponentialBody_at]
    ipra_congr (exponentialInputData Row (var 0) : PTm 1) with
      [GaussianBarnesCanonicalFiniteLogRows.body_at i z R B N] using [y,GaussianBarnesCanonicalLogFactor.expData,exponentialInputData]
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr (Exp Row) Factor y _ d _
    a.eqSymm (GaussianBarnesCanonicalHead.body_at i z R B N).eqSymm
    (GaussianBarnesCanonicalLogFactor.factor_cross z R B k (row_source z R B N i hs))

theorem direct_product_cross (z R B N r : PTm n) (hs : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteExponentialFold.productF Row b) Head
      (GaussianNamedFiniteExponentialFold.productData Row b r (parameters z R B N))
      (GaussianBarnesCanonicalHead.data z R B N r) := by
  let x := parameters z R B N
  have rows := GaussianBarnesCanonicalFiniteLogRows.rows_regular z R B N r hs
  refine family_product_cross (Exp Row) Factor (exponentialBody Row b) h r x x
    (GaussianNamedFiniteExponentialFold.exponential_rows Row b r x rows)
    (GaussianBarnesCanonicalHead.rows_regular z R B N r (.andI hs.andE₁ hs.andE₂.andE₂.andE₁)) ?_
  refine .allI (.impI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  have src : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hs.shift.wk
  simpa only [Syn.shift,sh,Δ,x,subst_parameters] using row_identity (sh z) (sh R) (sh B) (sh N) (var 0) src

theorem exponential_product_cross (z R B N r : PTm n) (hs : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent (Exp Finite) Head (expData z R B N r) (GaussianBarnesCanonicalHead.data z R B N r) := by
  let x := parameters z R B N
  let a := GaussianBarnesCanonicalFiniteLogRows.data z R B N r
  let d := GaussianBarnesCanonicalFiniteLog.data z R B N r
  let c := GaussianNamedFiniteExponentialFold.productData Row b r x
  have rows := GaussianBarnesCanonicalFiniteLogRows.rows_regular z R B N r hs
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper Finite Sum
    (GaussianBarnesCanonicalFiniteLog.radius R) (GaussianNameBounds.U Sum a) d a
    (GaussianBarnesCanonicalFiniteLog.exponential_input z R B N r hs)
    (exponential_input Sum a (GaussianNamedFiniteSumFamily.regular Row b r x rows))
    (cross_symm _ _ _ _ (GaussianBarnesCanonicalFiniteLogRows.finite_cross z R B N r hs))
  exact cross_trans _ _ _ _ _ _ left
    (cross_trans (Exp Sum) (GaussianNamedFiniteExponentialFold.productF Row b) Head
      (exponentialInputData Sum a) c (GaussianBarnesCanonicalHead.data z R B N r)
      (GaussianNamedFiniteExponentialFold.exponential_product_cross Row b r x rows)
      (direct_product_cross z R B N r hs))

theorem actual_exponentiated_Barnes_finite_logarithm_is_original_factor_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent (Exp Finite) Head
        (expData (var 0) (var 1) (var 2) (var 3) (var 4))
        (GaussianBarnesCanonicalHead.data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (exponential_product_cross _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLogProduct
