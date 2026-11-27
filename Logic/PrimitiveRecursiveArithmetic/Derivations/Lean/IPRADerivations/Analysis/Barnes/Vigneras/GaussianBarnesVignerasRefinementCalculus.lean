import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasRefinementNode

/-! The compact-strip modulus supplies the actual bounds on the entire fine window.
The unit-period proof then supplies the wrapped zeroth observations. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementCalculus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasCandidateCalculus (Candidate strip tagSource strip_at)
open GaussianBarnesVignerasRefinementChart (scheduled precision strip_bounds)
open GaussianBarnesVignerasRefinementJet (firstBody secondBody thirdBody radius)
open GaussianBarnesVignerasRefinementNode (derivativeAt floorAt at_node)
open GaussianBarnesVignerasRefinementWrap (body numerator translation observationClock orbits)
open GaussianCoefficientNameBounds (unit)
open GaussianDiscretePeriodicMetricCertificate (derivative wrapping)
open GaussianDiscretePeriodicUniformCertificate (window)
open GaussianRationalHorner (positive_product)
open SignedDiscreteDerivativeOperators (width divisor)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "far" => GaussianBarnesVignerasCubicForce.translation
local notation "floor" => GaussianDiscretePeriodicThirdFloor.source

def rates (c : Candidate) (x N U : PTm n) : Fm PTm n :=
  let F := body c.value c.valueData
  let G := firstBody c.first c.firstData
  let H := secondBody c.second c.secondData
  let J := thirdBody c.third c.thirdData
  let K := window x N
  derivative F G x K U ⋏ (derivative G H x K U ⋏ (derivative H J x K U ⋏ floor J x K U))

theorem global_rates (c : Candidate) (x N p M : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one (width x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) (hNeed : Γ ⊢[PRAAx] le M (divisor x))
    (h : Γ ⊢[PRAAx] scheduled x p) (hs : Γ ⊢[PRAAx] strip c (precision p) (far (precision p)) M) :
    Γ ⊢[PRAAx] rates c x N (unit p) := by
  let F := body c.value c.valueData
  let G := firstBody c.first c.firstData
  let H := secondBody c.second c.secondData
  let J := thirdBody c.third c.thirdData
  let sh (v : PTm n) := Syn.shift v
  let X := sh x
  let D := divisor X
  let P := sh p
  let R := radius X
  let i : PTm (n+1) := var 0
  let A := numerator X i
  let K := window x N
  let Δ := lt i (sh K) :: Γ.map Fm.shift
  have all : Γ ⊢[PRAAx] .all (lt i (sh K) ⟶ derivativeAt F G X i (sh (unit p)) ⋏
      (derivativeAt G H X i (sh (unit p)) ⋏ (derivativeAt H J X i (sh (unit p)) ⋏ floorAt J X i (sh (unit p))))) := by
    refine .allI (.impI ?_)
    have nn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
    have mm : Δ ⊢[PRAAx] le one (width X) := by simpa [Δ,X,sh,Fm.shift,Syn.shift,one] using hM.shift.wk
    have dd : Δ ⊢[PRAAx] divisor X ≐ sh N*width X := by simpa [Δ,X,sh,Fm.shift,Syn.shift] using hD.shift.wk
    have need : Δ ⊢[PRAAx] le (sh M) D := by simpa [Δ,D,X,sh,Fm.shift,Syn.shift] using hNeed.shift.wk
    have sched : Δ ⊢[PRAAx] scheduled X P := by simpa [Δ,X,P,sh,Fm.shift,Syn.shift] using h.shift.wk
    have stripSource : Δ ⊢[PRAAx] strip c (precision P) (far (precision P)) (sh M) := by
      simpa [Δ,P,sh,Fm.shift,Syn.shift] using hs.shift.wk
    have hi : Δ ⊢[PRAAx] lt i (window X (sh N)) := by
      simpa [Δ,K,X,sh,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh K))
    have loc := strip_bounds X (sh N) i nn mm dd hi
    have e := sched.andE₂.andE₁
    have low : Δ ⊢[PRAAx] le ((far (precision P)+one)*D) A :=
      le_congr (congrMul (congrAdd e (.eqRefl _)) (.eqRefl _)) (.eqRefl _) loc.andE₁
    have high : Δ ⊢[PRAAx] le (succ A) ((far (precision P)+num 6)*D) :=
      le_congr (.eqRefl _) (congrMul (congrAdd e (.eqRefl _)) (.eqRefl _)) loc.andE₂
    have pos : Δ ⊢[PRAAx] le one D :=
      le_congr (.eqRefl _) dd.eqSymm (positive_product _ _ nn mm)
    have row := strip_at c (precision P) (far (precision P)) (sh M) A D stripSource
      (.andI pos (.andI need (.andI low high)))
    have unitShift : sh (unit p) = unit P :=
      GaussianCoefficientNameBounds.subst_unit _ _
    rw [unitShift]
    exact at_node c X (sh N) i P nn mm dd sched hi row
  refine .andI (.allI (.impI ?_)) (.andI (.allI (.impI ?_)) (.andI (.allI (.impI ?_)) (.allI (.impI ?_))))
  · exact (Prf.impE all.allOpen.wk Prf.hyp0).andE₁
  · exact (Prf.impE all.allOpen.wk Prf.hyp0).andE₂.andE₁
  · exact (Prf.impE all.allOpen.wk Prf.hyp0).andE₂.andE₂.andE₁
  · exact (Prf.impE all.allOpen.wk Prf.hyp0).andE₂.andE₂.andE₂

theorem uniform (c : Candidate) (x N p M : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hM : Γ ⊢[PRAAx] le one (width x))
    (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x) (hNeed : Γ ⊢[PRAAx] le M (divisor x))
    (h : Γ ⊢[PRAAx] scheduled x p) (hs : Γ ⊢[PRAAx] strip c (precision p) (far (precision p)) M)
    (ho : Γ ⊢[PRAAx] orbits c.value c.valueData x N) :
    Γ ⊢[PRAAx] GaussianDiscretePeriodicUniformCertificate.source (body c.value c.valueData)
      (firstBody c.first c.firstData) (secondBody c.second c.secondData) (thirdBody c.third c.thirdData) x N (unit p) := by
  let F := body c.value c.valueData
  let sh (v : PTm n) := Syn.shift v
  let X := sh x
  let P := sh p
  let i : PTm (n+1) := var 0
  let Δ := lt i (sh N) :: Γ.map Fm.shift
  have all := global_rates c x N p M hN hM hD hNeed h hs
  have wrap : Γ ⊢[PRAAx] .all (lt i (sh N) ⟶ wrapping F X (sh N) i (unit P)) := by
    refine .allI (.impI ?_)
    have nn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
    have dd : Δ ⊢[PRAAx] divisor X ≐ sh N*width X := by simpa [Δ,X,sh,Fm.shift,Syn.shift] using hD.shift.wk
    have sched : Δ ⊢[PRAAx] scheduled X P := by simpa [Δ,X,P,sh,Fm.shift,Syn.shift] using h.shift.wk
    have orb : Δ ⊢[PRAAx] orbits c.value c.valueData X (sh N) := by
      have shifted : Δ ⊢[PRAAx] (orbits c.value c.valueData x N).subst (fun j => var j.succ) :=
        ho.shift.wk
      simp only [orbits,Fm.subst_all,Fm.subst_imp,subst_lt,Syn.subst_var,Syn.up_zero,
        PTm.subst_mul,GaussianBarnesVignerasRefinementWrap.subst_numerator,
        GaussianBarnesVignerasIntegerPeriod.subst_source,SignedDiscreteDerivativeOperators.subst_width,
        SignedDiscreteDerivativeOperators.subst_divisor,Foundations.BoundedFormulas.subst_up_shift'] at shifted
      simpa only [X,sh,orbits,Syn.shift] using shifted
    have later : Δ ⊢[PRAAx] le (succ P) (observationClock X) :=
      le_trans (le_of_eq_add (d := num 4) (by unfold precision; ipra_ring))
        (GaussianBarnesVignerasRefinementChart.observation_late X P sched)
    exact GaussianBarnesVignerasRefinementWrap.stencil c.value c.valueData X (sh N) P i nn dd later orb
  simpa only [GaussianDiscretePeriodicUniformCertificate.source,GaussianCoefficientNameBounds.subst_unit,
    Syn.shift,sh] using .andI all.andE₁ (.andI all.andE₂.andE₁
    (.andI all.andE₂.andE₂.andE₁ (.andI all.andE₂.andE₂.andE₂ wrap)))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasRefinementCalculus
