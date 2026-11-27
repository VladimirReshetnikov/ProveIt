import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.Observations.GaussianDiscretePeriodicGridReadback
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.DiscreteDerivatives.GaussianDiscreteThirdDerivativeEstimate
import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.Observations.GaussianSignedObservationOrder
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveExponentialOrder

/-!
# Finite derivative rates and approximate cyclic readback

Three fine derivative rates control the unwrapped coarse stencil.
Each wrapped value is compared with the corresponding original
Gaussian observation. The four comparisons cost eight times their
common rounding error in the signed stencil. Exact multiplication
by N³ gives the cyclic bound and then cancels from the displacement.
-/

set_option autoImplicit false
set_option maxHeartbeats 1550000

namespace LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicThirdDerivative

open_ipra
open GaussianDiscretePeriodicGridReadback
  (factor sample grid data wrappedStencil third_at projected_distance_of_third_lower)
open GaussianDiscreteDerivativeRounding (source latticeScale body)
open GaussianDiscreteThirdDerivativeEstimate (fourObservations comparisonBudget four_observations_lower)
open GaussianSignedObservationGrid (rounded)
open GaussianSignedObservationReadback (realProjection)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open RationalValueBounds (upper_of_radius)
open SignedDiscreteDerivativeOperators (width divisor)
open SignedDiscreteThirdDerivativeEstimate (window)
open SignedDiscreteDerivativeBounds (floorOn)
open SignedCubicTaylorGrid (combination)
open SignedGridStepBounds (neg_order)
open PeriodicThirdDifferenceConstancy (band)
open PeriodicThirdDifferenceModulo (thirdLower third)
open PolynomialBisection (zle_add zle_congr zle_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rounded_distance (a b S P : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (h : Γ ⊢[PRAAx] distanceBounded a b P S) :
    Γ ⊢[PRAAx] band (rounded a S-rounded b S) (P+two) := by
  have left := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hS
    (distance_symmetric _ _ _ _ hS h))
  have right := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hS h)
  have lo := GaussianSignedObservationOrder.lower a b S P left
  have hi := neg_order (GaussianSignedObservationOrder.lower b a S P right)
  exact .andI lo (zle_congr (by simp only [ZT.toZ_neg,ZT.toZ_sub]; ring)
    (by simp only [ZT.toZ_neg,neg_neg]) hi)

private theorem stencil_error (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : ZT n) (E : PTm n)
    (h₀ : Γ ⊢[PRAAx] band (a₀-b₀) E) (h₁ : Γ ⊢[PRAAx] band (a₁-b₁) E)
    (h₂ : Γ ⊢[PRAAx] band (a₂-b₂) E) (h₃ : Γ ⊢[PRAAx] band (a₃-b₃) E) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (num 8*E)) (combination a₀ a₁ a₂ a₃-combination b₀ b₁ b₂ b₃) := by
  have lo₀ := neg_order h₀.andE₂
  have lo₁ := zle_scale (num 3) h₁.andE₁
  have lo₂ := zle_scale (num 3) (neg_order h₂.andE₂)
  have raw := zle_add (zle_add (zle_add h₃.andE₁ lo₂) lo₁) lo₀
  apply zle_congr ?_ ?_ raw
  · simp only [ZT.toZ_add,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    ipra_simps
    ring
  · simp only [combination,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat]
    ring

def compareNode (f : PTm 2) (x N P j k : PTm n) : Fm PTm n :=
  distanceBounded (sample f x (rem j N)) (inst2 f k x) P (latticeScale x)

def wrapping (f : PTm 2) (x N i P : PTm n) : Fm PTm n :=
  let k₀ := i*width x
  let k₁ := k₀+width x
  let k₂ := k₁+width x
  let k₃ := k₂+width x
  compareNode f x N P i k₀ ⋏
    (compareNode f x N P (succ i) k₁ ⋏
      (compareNode f x N P (succ (succ i)) k₂ ⋏
        compareNode f x N P (succ (succ (succ i))) k₃))

def rowBudget (x N T E₀ E₁ E₂ P : PTm n) : PTm n :=
  comparisonBudget x N T E₀ E₁ E₂+factor N*(num 8*(P+two))

theorem wrapped_stencil_lower (f : PTm 2) (x N i E P : PTm n)
    (hS : Γ ⊢[PRAAx] le one (latticeScale x)) (hw : Γ ⊢[PRAAx] wrapping f x N i P)
    (h : Γ ⊢[PRAAx] zle (-ZT.ofNat E) (ZT.ofNat (factor N)*fourObservations f x (i*width x))) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (E+factor N*(num 8*(P+two)))) ((third (grid f)).val i (data x N)) := by
  have err :
      Γ ⊢[PRAAx] zle (-ZT.ofNat (num 8*(P+two))) (wrappedStencil f x N i-fourObservations f x (i*width x)) :=
    stencil_error _ _ _ _ _ _ _ _ (P+two) (rounded_distance _ _ _ _ hS hw.andE₁)
      (rounded_distance _ _ _ _ hS hw.andE₂.andE₁)
      (rounded_distance _ _ _ _ hS hw.andE₂.andE₂.andE₁)
      (rounded_distance _ _ _ _ hS hw.andE₂.andE₂.andE₂)
  have raw := zle_add h (zle_scale (factor N) err)
  apply zle_congr ?_ ?_ raw
  · simp only [ZT.toZ_add,ZT.toZ_ofNat,ZT.toZ_neg,ZT.toZ_mul,Q.mk_add,map_add,Q.mk_mul,map_mul]
    ring
  · rw [third_at]
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_sub]
    ring

def row (f g h j : PTm 2) (x N i T E₀ E₁ E₂ P : PTm n) : Fm PTm n :=
  let L := window x (i*width x)
  source f g x L E₀ ⋏
    (source g h x L E₁ ⋏
      (source h j x L E₂ ⋏
        (floorOn (body j) x L T ⋏ wrapping f x N i P)))

def certified (f g h j : PTm 2) (x N T E₀ E₁ E₂ P : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ row f g h j (Syn.shift x) (Syn.shift N) (var 0)
    (Syn.shift T) (Syn.shift E₀) (Syn.shift E₁) (Syn.shift E₂) (Syn.shift P))

theorem row_lower (f g h j : PTm 2) (x N i T E₀ E₁ E₂ P : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hS : Γ ⊢[PRAAx] le one (latticeScale x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hs : Γ ⊢[PRAAx] row f g h j x N i T E₀ E₁ E₂ P) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (rowBudget x N T E₀ E₁ E₂ P)) ((third (grid f)).val i (data x N)) :=
  let tail := hs.andE₂.andE₂
  wrapped_stencil_lower f x N i _ P hS tail.andE₂.andE₂
    (four_observations_lower f g h j x (i*width x) N T E₀ E₁ E₂ hM hS hD hs.andE₁
      hs.andE₂.andE₁ tail.andE₁ tail.andE₂.andE₁)

theorem cyclic_third_lower (f g h j : PTm 2) (x N T E₀ E₁ E₂ P : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hS : Γ ⊢[PRAAx] le one (latticeScale x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hs : Γ ⊢[PRAAx] certified f g h j x N T E₀ E₁ E₂ P) :
    Γ ⊢[PRAAx] thirdLower (grid f) (data x N) N (rowBudget x N T E₀ E₁ E₂ P) := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have hm : Δ ⊢[PRAAx] le one (width (sh x)) := by
    simpa only [Δ,i,sh,Fm.shift,Syn.shift,subst_le,SignedDiscreteDerivativeOperators.subst_width,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hM.shift.wk
  have ht : Δ ⊢[PRAAx] le one (latticeScale (sh x)) := by
    simpa only [Δ,i,sh,Fm.shift,Syn.shift,subst_le,GaussianDiscreteDerivativeRounding.subst_latticeScale,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hS.shift.wk
  have hd : Δ ⊢[PRAAx] divisor (sh x) ≐ sh N*width (sh x) := by
    simpa [Δ,i,sh,Fm.shift,Syn.shift] using hD.shift.wk
  have localRow : Δ ⊢[PRAAx] row f g h j (sh x) (sh N) i (sh T) (sh E₀) (sh E₁) (sh E₂) (sh P) :=
    .impE hs.allOpen.wk Prf.hyp0
  have ds : Syn.shift (data x N) = data (sh x) (sh N) := by
    simp [data,PeriodicThirdDifferenceModulo.data,factor,sh,Syn.shift]
  have es : Syn.shift (rowBudget x N T E₀ E₁ E₂ P) = rowBudget (sh x) (sh N) (sh T) (sh E₀) (sh E₁) (sh E₂) (sh P) := by
    simp [rowBudget,factor,comparisonBudget,SignedDiscreteThirdDerivativeNormalization.budget,GaussianDiscreteDerivativeRounding.allowance,
      sh,Syn.shift,two,one,num]
  rw [ds,es]
  exact row_lower f g h j (sh x) (sh N) i (sh T) (sh E₀) (sh E₁) (sh E₂) (sh P) hm ht hd localRow

theorem projected_distance (f g h j : PTm 2) (x N i T E₀ E₁ E₂ P : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hS : Γ ⊢[PRAAx] le one (latticeScale x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hs : Γ ⊢[PRAAx] certified f g h j x N T E₀ E₁ E₂ P) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (sample f x (rem i N)))
      (realProjection (sample f x (rem zero N))) (num 4*rowBudget x N T E₀ E₁ E₂ P+two) (latticeScale x) :=
  projected_distance_of_third_lower f x N i _ hN hi hS (cyclic_third_lower f g h j x N T E₀ E₁ E₂ P hM hS hD hs)

theorem actual_Gaussian_periodic_fine_derivative_distance_closed (f g h j : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let x := var 0
       let N := var 1
       let i := var 2
       let T := var 3
       let E₀ := var 4
       let E₁ := var 5
       let E₂ := var 6
       let P := var 7
       le one (width x) ⟶ le one (latticeScale x) ⟶ divisor x ≐ N*width x ⟶ le one N ⟶ le i N ⟶
         certified f g h j x N T E₀ E₁ E₂ P ⟶
           distanceBounded (realProjection (sample f x (rem i N)))
             (realProjection (sample f x (rem zero N))) (num 4*rowBudget x N T E₀ E₁ E₂ P+two) (latticeScale x)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (.impI (projected_distance f g h j _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicThirdDerivative
