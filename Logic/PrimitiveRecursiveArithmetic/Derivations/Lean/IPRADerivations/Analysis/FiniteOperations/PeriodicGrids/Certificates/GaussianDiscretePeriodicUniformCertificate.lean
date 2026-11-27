import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.Certificates.GaussianDiscretePeriodicMetricCertificate

/-!
# Use one analytic window for all periodic derivative stencils

Every local window needed at a coarse index i<N ends at or before
succ((N+2)*M). The original three derivative rates and third real
lower bound can therefore be supplied once on this common window.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicUniformCertificate

open_ipra
open GaussianDiscretePeriodicMetricCertificate (derivative wrapping row)
open GaussianDiscretePeriodicDerivativeSchedule (clock denominator)
open GaussianDiscretePeriodicGridReadback (sample)
open GaussianDiscreteDerivativeRounding (latticeScale)
open GaussianSignedObservationReadback (realProjection)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open SignedDiscreteDerivativeOperators (width divisor)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def window (x N : PTm n) : PTm n := succ ((N+two)*width x)

theorem local_window_le (x N i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (SignedDiscreteThirdDerivativeEstimate.window x (i*width x)) (window x N) := by
  let M := width x
  have moved := add_le_add_right (M+M+one) (mul_le_mul_right M hi)
  exact le_congr (by unfold SignedDiscreteThirdDerivativeEstimate.window M; ipra_ring)
    (by unfold window M; ipra_ring) moved

@[simp] theorem subst_window {m : ℕ} (σ : Fin n → PTm m) (x N : PTm n) :
    Syn.subst σ (window x N) = window (Syn.subst σ x) (Syn.subst σ N) := by
  simp [window,two,one]

@[simp] theorem subst_derivative {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (x K U : PTm n) :
    (derivative f g x K U).subst σ = derivative f g (Syn.subst σ x) (Syn.subst σ K) (Syn.subst σ U) := by
  simp [derivative,subst_inst2,one,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_third_floor {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x K U : PTm n) :
    (GaussianDiscretePeriodicThirdFloor.source f x K U).subst σ =
      GaussianDiscretePeriodicThirdFloor.source f (Syn.subst σ x) (Syn.subst σ K) (Syn.subst σ U) := by
  simp [GaussianDiscretePeriodicThirdFloor.source,subst_inst2,one,Syn.subst_shift,Syn.shift_subst]

private theorem shifted_le (K L : PTm n) (h : Γ ⊢[PRAAx] le K L) :
    lt (var 0) (Syn.shift K) :: Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift K) (Syn.shift L) := by
  simpa only [Fm.shift,Syn.shift,subst_le] using h.shift.wk

theorem derivative_restrict (f g : PTm 2) (x K L U : PTm n) (hK : Γ ⊢[PRAAx] le K L)
    (h : Γ ⊢[PRAAx] derivative f g x L U) : Γ ⊢[PRAAx] derivative f g x K U := by
  refine .allI (.impI ?_)
  exact .impE h.allOpen.wk (lt_of_lt_of_le Prf.hyp0 (shifted_le K L hK))

theorem third_floor_restrict (f : PTm 2) (x K L U : PTm n) (hK : Γ ⊢[PRAAx] le K L)
    (h : Γ ⊢[PRAAx] GaussianDiscretePeriodicThirdFloor.source f x L U) :
    Γ ⊢[PRAAx] GaussianDiscretePeriodicThirdFloor.source f x K U := by
  refine .allI (.impI ?_)
  exact .impE h.allOpen.wk (lt_of_lt_of_le Prf.hyp0 (shifted_le K L hK))

def source (f g h j : PTm 2) (x N U : PTm n) : Fm PTm n :=
  let L := window x N
  derivative f g x L U ⋏ (derivative g h x L U ⋏
    (derivative h j x L U ⋏ (GaussianDiscretePeriodicThirdFloor.source j x L U ⋏
      .all (lt (var 0) (Syn.shift N) ⟶ wrapping f (Syn.shift x) (Syn.shift N) (var 0) (Syn.shift U)))))

theorem metric_certificate (f g h j : PTm 2) (x N U : PTm n)
    (src : Γ ⊢[PRAAx] source f g h j x N U) :
    Γ ⊢[PRAAx] GaussianDiscretePeriodicMetricCertificate.source f g h j x N U := by
  refine .allI (.impI ?_)
  let sh (z : PTm n) := Syn.shift z
  let X := sh x
  let V := sh N
  let U' := sh U
  let i : PTm (n+1) := var 0
  let Δ := lt i V :: Γ.map Fm.shift
  let K := SignedDiscreteThirdDerivativeEstimate.window X (i*width X)
  let L := window X V
  have fit : Δ ⊢[PRAAx] le K L := local_window_le X V i Prf.hyp0
  have a : Δ ⊢[PRAAx] derivative f g X L U' := by
    simpa only [Δ,X,V,U',L,sh,Fm.shift,Syn.shift,subst_derivative,subst_window] using src.andE₁.shift.wk
  have b : Δ ⊢[PRAAx] derivative g h X L U' := by
    simpa only [Δ,X,V,U',L,sh,Fm.shift,Syn.shift,subst_derivative,subst_window] using src.andE₂.andE₁.shift.wk
  have c : Δ ⊢[PRAAx] derivative h j X L U' := by
    simpa only [Δ,X,V,U',L,sh,Fm.shift,Syn.shift,subst_derivative,subst_window] using src.andE₂.andE₂.andE₁.shift.wk
  have d : Δ ⊢[PRAAx] GaussianDiscretePeriodicThirdFloor.source j X L U' := by
    simpa only [Δ,X,V,U',L,sh,Fm.shift,Syn.shift,subst_third_floor,subst_window] using src.andE₂.andE₂.andE₂.andE₁.shift.wk
  have wrap : Δ ⊢[PRAAx] wrapping f X V i U' :=
    .impE src.andE₂.andE₂.andE₂.andE₂.allOpen.wk Prf.hyp0
  exact .andI (derivative_restrict f g X K L U' fit a)
    (.andI (derivative_restrict g h X K L U' fit b)
      (.andI (derivative_restrict h j X K L U' fit c)
        (.andI (third_floor_restrict j X K L U' fit d) wrap)))

theorem dyadic_distance (f g h j : PTm 2) (x N i p : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (hS : Γ ⊢[PRAAx] latticeScale x ≐ denominator x N p) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] le i N) (hr : Γ ⊢[PRAAx] source f g h j x N (unit (clock N p))) :
    Γ ⊢[PRAAx] distanceBounded (realProjection (sample f x (rem i N)))
      (realProjection (sample f x (rem zero N))) one (unit p) :=
  GaussianDiscretePeriodicMetricCertificate.dyadic_distance f g h j x N i p hM hD hS hN hi
    (metric_certificate f g h j x N _ hr)

theorem actual_Gaussian_uniform_window_periodic_distance_closed (f g h j : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0
       let N := var 1
       let i := var 2
       let p := var 3
       le one (width x) ⟶ divisor x ≐ N*width x ⟶ latticeScale x ≐ denominator x N p ⟶
       le one N ⟶ le i N ⟶ source f g h j x N (unit (clock N p)) ⟶
         distanceBounded (realProjection (sample f x (rem i N)))
           (realProjection (sample f x (rem zero N))) one (unit p)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (dyadic_distance f g h j _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianDiscretePeriodicUniformCertificate
