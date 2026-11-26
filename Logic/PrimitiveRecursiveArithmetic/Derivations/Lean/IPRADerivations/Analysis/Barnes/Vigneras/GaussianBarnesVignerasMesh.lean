import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasCyclicDerivative
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasIntegerPeriod

/-!
# Actual Barnes logarithmic quotient observations on a unit mesh

At residue i the primitive-recursive observation reads the quotient at
1+i/N and at a separately supplied observation precision. The requested
output precision determines the Taylor tolerance. All observations are
canonical real Gaussian rationals, so the signed-grid projection is exact.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Common (pos_of_one_le)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (rem_small)
open GaussianBarnesVignerasCyclicDerivative (LowerJet clock)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (canonical canonical_unique ofGaussian_canonical ofGaussian_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedObservationReadback (realProjection)
open RationalGaussianEmbedding (axis canonical_axis_roundtrip embed embed_canonical)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF
local notation "cd" => GaussianBarnesVignerasIntegerPeriod.data
local notation "I" => GaussianBarnesVignerasIntegerPeriod.input
local notation "M" => GaussianBarnesVignerasIntegerPeriod.margin

def body (f : PR 2) (t : PTm 2) : PTm 2 :=
  ap2 (Q f) (sndT (var 1)) (cd t (fstT (var 1)+var 0) (fstT (var 1)))

def mesh_source (f g : PR 2) (t v : PTm 2) (J : LowerJet) (N E p r y : PTm n) : Fm PTm n :=
  GaussianBarnesVignerasCyclicDerivative.source (body f t) g v J (pairT N r) y one one N (clock E p) E

theorem sample_at (f : PR 2) (t : PTm 2) (N p i : PTm n) :
    Γ ⊢[PRAAx] inst2 (body f t) i (pairT N p) ≐ ap2 (Q f) p (cd t (N+i) N) := by
  simp only [body,inst2,subst_ap2,GaussianBarnesVignerasIntegerPeriod.subst_data,PTm.subst_add,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val]
  ipra_congr (ap2 (Q f) (var 0) (cd t (var 1+var 2) (var 1)) : PTm 3) with
    [snd_pair N p,fst_pair N p,.eqRefl i]

theorem projection_fixed (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q) (hr : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] realProjection q ≐ q := by
  have hD := raw_den_positive (Γ := Γ) q
  have left := ofGaussian_represents (RationalGaussianEmbedding.native (ComplexLogarithmRemainder.re (rawGaussian q))) (rawDen q) hD
  have right := GaussianGammaRealValues.projection_represents (Γ := Γ) q (rawGaussian q) (rawDen q) (raw_represents q)
  have eq : Γ ⊢[PRAAx] realProjection q ≐ embed (fstT q) :=
    canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hD) (embed_canonical _) hD left right
  exact eq.eqTrans (canonical_axis_roundtrip q hc hr)

theorem actual_sample_real (f : PR 2) (t : PTm 2) (N p i : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] canonical (ap2 (Q f) p (cd t (N+i) N)) ⋏ axis (ap2 (Q f) p (cd t (N+i) N)) := by
  have ha := le_trans hN (le_add_right N i)
  have hs := GaussianBarnesCanonicalPositiveLogarithm.default_source (N+i) N ha hN
  exact GaussianRealNameExponentialInjectivity.difference_sample_real _ _ p _ _
    (GaussianNamedPositiveLogarithm.real_samples f (I t (N+i) N) (M t (N+i) N))
    (GaussianBarnesCanonicalPositiveLogarithmRealAxis.samples_axis _ _ _ hs)

private theorem projected_sample_at (f : PR 2) (t : PTm 2) (N p i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] realProjection (inst2 (body f t) (rem i N) (pairT N p)) ≐ ap2 (Q f) p (cd t (N+i) N) := by
  let q := ap2 (Q f) p (cd t (N+i) N)
  have read := (congrInst2 (body f t) (rem_small (pos_of_one_le hN) hi) (.eqRefl (pairT N p))).eqTrans
    (sample_at f t N p i)
  have e : Γ ⊢[PRAAx] realProjection (inst2 (body f t) (rem i N) (pairT N p)) ≐ realProjection q := by
    ipra_congr (realProjection (var 0) : PTm 1) with [read]
  have r := actual_sample_real f t N p i hN
  exact e.eqTrans (projection_fixed q r.andE₁ r.andE₂)

theorem dyadic_distance (f g : PR 2) (t v : PTm 2) (J : LowerJet) (N E p r y i : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) (h : Γ ⊢[PRAAx] mesh_source f g t v J N E p r y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (Q f) r (cd t (N+i) N)) (ap2 (Q f) r (cd t (N+zero) N)) one (unit p) :=
  distance_congr (projected_sample_at f t N r i hN hi) (projected_sample_at f t N r zero hN hN) (.eqRefl _) (.eqRefl _)
    (GaussianBarnesVignerasCyclicDerivative.dyadic_distance (body f t) g v J (pairT N r) y one one N E i p
      (le_refl one) hN (le_of_lt hi) h)

theorem actual_Barnes_quotient_mesh_observation_rate_closed (f g : PR 2) (t v : PTm 2) (J : LowerJet) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let N := var 0
       let E := var 1
       let p := var 2
       let r := var 3
       let y := var 4
       let i := var 5
       (le one N ⋏ (lt i N ⋏ mesh_source f g t v J N E p r y)) ⟶
       distanceBounded (ap2 (Q f) r (cd t (N+i) N)) (ap2 (Q f) r (cd t (N+zero) N)) one (unit p)) :=
  closeUniv 6 (.impI (dyadic_distance f g t v J _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasMesh
