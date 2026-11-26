import IPRADerivations.Analysis.Barnes.Taylor.Grids.Finite.GaussianBarnesCanonicalFiniteTaylorGridObservations
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalUniformCutoff
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceNormalization

/-!
# Original cofinal Barnes observations on the native forward grid

Both grids use the same shifted Gaussian numerators and the same
widened disk. A single uniform cutoff controls all their literal
rows. The normalized forward differences then have a dyadic bound
at sufficiently late independent cofinal and finite readback clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridObservations

open_ipra
open ComplexLogarithmRemainder (add bounded bounded_add bounded_mono scale normSq)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianPolynomialForwardDifferenceNormalization (normalized)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_decode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "literalData" => GaussianBarnesCanonicalFiniteTaylorGrid.literalData
local notation "literalGrid" => GaussianBarnesCanonicalFiniteTaylorGridObservations.literalGrid
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def cofinalData (z h R B j : PTm n) : PTm n :=
  GaussianBarnesCanonicalValue.data (add z (scale j h)) (R+one) B

private def parameters (t z h R B : PTm n) : PTm n := pairT t (pairT z (pairT h (pairT R B)))

private def cofinalBody : PTm 2 :=
  let u := var 1
  let a := sndT u
  let b := sndT a
  let c := sndT b
  ap2 G (fstT u) (cofinalData (fstT a) (fstT b) (fstT c) (sndT c) (var 0))

def cofinalGrid (t z h R B e : PTm n) : PTm n :=
  sequence cofinalBody (succ e) (parameters t z h R B)

def tailCutoff (p R : PTm n) : PTm n := GaussianBarnesCanonicalUniformCutoff.cutoff (R+one) p

def amplification (B e : PTm n) : PTm n := pw B e*pw two e
def deadline (p B e : PTm n) : PTm n := exponent (num 3*amplification B e) p

@[simp] theorem subst_cofinalData {l : ℕ} (σ : Fin n → PTm l) (z h R B j : PTm n) :
    Syn.subst σ (cofinalData z h R B j) = cofinalData (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ j) := by simp [cofinalData,one]

@[simp] theorem subst_cofinalGrid {l : ℕ} (σ : Fin n → PTm l) (t z h R B e : PTm n) :
    Syn.subst σ (cofinalGrid t z h R B e) = cofinalGrid (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ h)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ e) := by simp [cofinalGrid,parameters]

@[simp] theorem subst_tailCutoff {l : ℕ} (σ : Fin n → PTm l) (p R : PTm n) :
    Syn.subst σ (tailCutoff p R) = tailCutoff (Syn.subst σ p) (Syn.subst σ R) := by
  simp [tailCutoff,GaussianBarnesCanonicalUniformCutoff.cutoff,GaussianBarnesCanonicalUniformCutoff.gain,
    GaussianBarnesCanonicalDiskBound.prefixBound,GaussianRadiusExponentialLipschitzRate.factor,one,two]

@[simp] theorem subst_amplification {l : ℕ} (σ : Fin n → PTm l) (B e : PTm n) :
    Syn.subst σ (amplification B e) = amplification (Syn.subst σ B) (Syn.subst σ e) := by simp [amplification,two,one]

@[simp] theorem subst_deadline {l : ℕ} (σ : Fin n → PTm l) (p B e : PTm n) :
    Syn.subst σ (deadline p B e) = deadline (Syn.subst σ p) (Syn.subst σ B) (Syn.subst σ e) := by simp [deadline]

theorem cofinal_at (t z h R B e j : PTm n) (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] entry (cofinalGrid t z h R B e) j ≐ ap2 G t (cofinalData z h R B j) := by
  let a := pairT z (pairT h (pairT R B))
  let b := pairT h (pairT R B)
  let c := pairT R B
  have t₀ := snd_pair (Γ := Γ) t a
  have t₁ := (congrSnd t₀).eqTrans (snd_pair z b)
  have t₂ := (congrSnd t₁).eqTrans (snd_pair h c)
  refine (sequence_decode cofinalBody (x := parameters t z h R B) hj).eqTrans ?_
  ipra_congr (ap2 G (var 0) (cofinalData (var 1) (var 2) (var 3) (var 4) (var 5)) : PTm 6) with
    [fst_pair t a, (congrFst t₀).eqTrans (fst_pair z b), (congrFst t₁).eqTrans (fst_pair h c),
      (congrFst t₂).eqTrans (fst_pair R B), (congrSnd t₂).eqTrans (snd_pair R B), .eqRefl j]
    using [cofinalBody,parameters,inst2,a,b,c]

theorem node_source (z h R B H e j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hj : Γ ⊢[PRAAx] le j e) :
    Γ ⊢[PRAAx] source (add z (scale j h)) (R+one) B := by
  have delta := bounded_mono (GaussianBarnesCanonicalFiniteTaylorGrid.step_bound h H e j hh hj) hs
  have wide : Γ ⊢[PRAAx] le (R*B+B) ((R+one)*B) :=
    le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)
  exact .andI hz.andE₁ (bounded_mono (bounded_add hz.andE₂ delta) wide)

theorem node_rate (p z h R B H r e j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hj : Γ ⊢[PRAAx] le j e)
    (hr : Γ ⊢[PRAAx] le (tailCutoff p R) r) :
    Γ ⊢[PRAAx] independentRate G V (cofinalData z h R B j) (literalData z h R B r j) one (unit p) := by
  have node := node_source z h R B H e j hz hh hs hj
  have early := le_trans hr (le_add_left r (initial (R+one)))
  exact GaussianNamedRateComposition.symmetric _ _ _ _ _ _ (unit_positive p)
    (GaussianBarnesCanonicalUniformCutoff.uniform_rate (add z (scale j h)) (R+one) B p (initial (R+one)+r) node early)

theorem row_bound (t s p z h R B H r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hr : Γ ⊢[PRAAx] le (tailCutoff p R) r) :
    Γ ⊢[PRAAx] rowBound (cofinalGrid t z h R B e) (literalGrid s z h R B r e) (succ e)
      (rateNumerator one (unit p) t s) (rateDenominator (unit p) t s) := by
  refine .allI (.impI ?_)
  let a (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (succ (a e)) :: Γ.map Fm.shift
  let j : PTm (n+1) := var 0
  have hzs : Δ ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hz.shift.wk
  have hhs : Δ ⊢[PRAAx] bounded (a h) (a H) := by simpa [Δ,a,Fm.shift,Syn.shift] using hh.shift.wk
  have hss : Δ ⊢[PRAAx] le (a e*a H) (a B) := by simpa [Δ,a,Fm.shift,Syn.shift] using hs.shift.wk
  have hrs : Δ ⊢[PRAAx] le (tailCutoff (a p) (a R)) (a r) := by simpa [Δ,a,Fm.shift,Syn.shift] using hr.shift.wk
  have inside : Δ ⊢[PRAAx] lt j (succ (a e)) := Prf.hyp0
  have before : Δ ⊢[PRAAx] le j (a e) := (succ_monus_succ _ _).eqSymm.eqTrans inside
  have near := rate_at G V (cofinalData (a z) (a h) (a R) (a B) j) (literalData (a z) (a h) (a R) (a B) (a r) j)
    one (unit (a p)) (a t) (a s) (node_rate (a p) (a z) (a h) (a R) (a B) (a H) (a r) (a e) j hzs hhs hss before hrs)
  have actual := distance_congr (cofinal_at (a t) (a z) (a h) (a R) (a B) (a e) j inside).eqSymm
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.literal_at (a s) (a z) (a h) (a R) (a B) (a r) (a e) j inside).eqSymm
    (.eqRefl _) (.eqRefl _) near
  simpa [rowBound,Δ,a,j,Syn.shift,one] using actual

theorem normalized_bound (t s p z h R B H r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hr : Γ ⊢[PRAAx] le (tailCutoff p R) r)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) :
    Γ ⊢[PRAAx] distanceBounded
      (normalized (cofinalGrid t z h R B e) e (ofGaussian h B))
      (normalized (literalGrid s z h R B r e) e (ofGaussian h B))
      (pw B e*(pw two e*rateNumerator one (unit p) t s)) (rateDenominator (unit p) t s) :=
  GaussianPolynomialForwardDifferenceNormalization.normalized_error _ _ e _ B _ _ hz.andE₁
    (GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hz.andE₁ hn))
    (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive p))
    (row_bound t s p z h R B H r e hz hh hs hr)

theorem scheduled_bound (p t s z h R B H r e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hr : Γ ⊢[PRAAx] le (tailCutoff (deadline p B e) R) r)
    (ht : Γ ⊢[PRAAx] le (deadline p B e) t) (hu : Γ ⊢[PRAAx] le (deadline p B e) s) :
    Γ ⊢[PRAAx] distanceBounded
      (normalized (cofinalGrid t z h R B e) e (ofGaussian h B))
      (normalized (literalGrid s z h R B r e) e (ofGaussian h B)) one (unit p) := by
  let k := deadline p B e
  let Q := unit k
  let T := unit t
  let S := unit s
  let U := unit p
  let M := amplification B e
  have tq : Γ ⊢[PRAAx] le Q T := GaussianExponentialReference.unit_monotone ht
  have sq : Γ ⊢[PRAAx] le Q S := GaussianExponentialReference.unit_monotone hu
  have fit : Γ ⊢[PRAAx] le (num 3*M*U) Q := query_budget _ _
  have budget : Γ ⊢[PRAAx]
      le ((pw B e*(pw two e*rateNumerator one Q t s))*U) (one*rateDenominator Q t s) := by
    change Γ ⊢[PRAAx] le ((pw B e*(pw two e*(one*T*S+Q*(T+S))))*U) (one*(Q*T*S))
    ipra_le 𝔞 T*𝔞 S*sl fit + 𝔞 M*𝔞 U*𝔞 T*sl sq + 𝔞 M*𝔞 U*𝔞 S*sl tq using
      dsimp only [M,amplification]
      ipra_simps
      ring
  exact distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive k)) (unit_positive p)
    budget (normalized_bound t s k z h R B H r e hz hh hs hr hn)

theorem actual_Barnes_cofinal_grid_uniform_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let p := var 0
     let t := var 1
     let s := var 2
     let z := var 3
     let h := var 4
     let R := var 5
     let B := var 6
     let H := var 7
     let r := var 8
     let e := var 9
     (source z R B ⋏ (bounded h H ⋏ (le (e*H) B ⋏ le one (normSq h)))) ⟶
       (le (tailCutoff (deadline p B e) R) r ⋏ (le (deadline p B e) t ⋏ le (deadline p B e) s)) ⟶
       distanceBounded
         (normalized (cofinalGrid t z h R B e) e (ofGaussian h B))
         (normalized (literalGrid s z h R B r e) e (ofGaussian h B)) one (unit p)) :=
  closeUniv 10 (.impI (.impI (scheduled_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁
    Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridObservations
