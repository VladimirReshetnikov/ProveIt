import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripTail
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds

/-!
# Sharp decay and explicit dyadic cutoffs for the actual Binet strip

An independent observation of the original real decay supplies the
sharp real exponential term. At the physical cutoff `D*L` the original
real argument is the integer `X*L`, giving an explicit dyadic tail
bound for any later finite endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripTailEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceStrip (source nameF data)
open GaussianBinetLaplaceStripTail (envelope tailNumerator tailDenominator named_tail_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation observation_rescale subst_observation)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem envelope_from_observation (q a E P Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] bounded (observation a E q) P Q) :
    Γ ⊢[PRAAx] envelope a E (P*unit q+Q) (Q*unit q) one := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] bounded (observation (s a) (s E) (s q)) (s P) (s Q) := by
    simpa only [Fm.shift,GaussianRationalMetric.subst_bounded,subst_observation,Syn.shift,s,Δ] using h.shift
  have qs : Δ ⊢[PRAAx] le one (s Q) := by simpa [Fm.shift,Syn.shift,s,Δ,one] using hQ.shift
  have up := unit_positive (Γ := Δ) p
  have uq := unit_positive (Γ := Δ) (s q)
  have near := GaussianNameEquivalence.point_at decayF (decayData (s a) (s E)) p (s q)
    (GaussianEulerDecayQuadraturePrecision.observation_regular (Γ := Δ) (s a) (s E))
  have raw := norm_from_distance _ _ _ _ _ _ (positive_product _ _ up uq) qs near hs
  have norm : Δ ⊢[PRAAx] bounded (observation (s a) (s E) p)
      ((s P*unit (s q)+s Q)*unit p+one*(s Q*unit (s q))) ((s Q*unit (s q))*unit p) :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) raw
  simpa only [s,Δ,p,Syn.shift,PTm.subst_mul,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using norm

theorem strip_endpoint_observation_bound (p q X Y D sign R T N A C E P Q : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hb : Γ ⊢[PRAAx] bounded (observation (X*A) (D*E) q) P Q) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF .cofinal) p (data X Y D sign R T N A C E))
      (tailNumerator p X D (P*unit q+Q) (Q*unit q)) (tailDenominator p X (Q*unit q)) :=
  named_tail_bound p X Y D sign R T N A C E _ _ one h hA hC
    (positive_product _ _ hQ (unit_positive q)) (envelope_from_observation q (X*A) (D*E) P Q hQ hb)

private theorem integer_observation (X D L E p : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] observation (X*(D*L*E)) (D*E) p ≐ observation (X*L) one p := by
  have hn : Γ ⊢[PRAAx] X*(D*L*E) ≐ (X*L)*(D*E) := by ipra_ring
  have hd : Γ ⊢[PRAAx] D*E ≐ one*(D*E) := by ipra_ring
  have e : Γ ⊢[PRAAx] observation (X*(D*L*E)) (D*E) p ≐ observation ((X*L)*(D*E)) (one*(D*E)) p := by
    simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![X*(D*L*E),D*E,p]) (σ' := ![(X*L)*(D*E),one*(D*E),p])
      (fun i => by fin_cases i; exact hn; exact hd; exact .eqRefl p)
  exact e.eqTrans (observation_rescale (X*L) one (D*E) p (le_refl one) (positive_product _ _ hD hE))

theorem integer_cutoff_envelope (X D L E : PTm n)
    (hX : Γ ⊢[PRAAx] le one X) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] envelope (X*(D*L*E)) (D*E) one (unit L) two := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have dx : Δ ⊢[PRAAx] le one (s D) := by simpa [Fm.shift,Syn.shift,s,Δ,one] using hD.shift
  have ex : Δ ⊢[PRAAx] le one (s E) := by simpa [Fm.shift,Syn.shift,s,Δ,one] using hE.shift
  have xx : Δ ⊢[PRAAx] le one (s X) := by simpa [Fm.shift,Syn.shift,s,Δ,one] using hX.shift
  have hp := unit_positive (Γ := Δ) p
  have hl := unit_positive (Γ := Δ) (s L)
  have hx := unit_positive (Γ := Δ) (s X*s L)
  have grow : Δ ⊢[PRAAx] le (unit (s L)) (unit (s X*s L)) :=
    GaussianExponentialReference.unit_monotone (le_congr (by ipra_ring) (.eqRefl _)
      (mul_le_mul_right (s L) xx))
  have raw := GaussianEulerDecayFactorBounds.original_integer_decay_bound (Γ := Δ) (s X*s L) p
  have eval : Δ ⊢[PRAAx] bounded (observation (s X*s L) one p) (one*unit p+two*unit (s L)) (unit (s L)*unit p) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hx hp) (positive_product _ _ hl hp)
      (by ipra_le 𝔞(unit p)*𝔞(unit p)*sl grow) raw
  have bound := bound_congr (integer_observation (s X) (s D) (s L) (s E) p dx ex).eqSymm
    (.eqRefl _) (.eqRefl _) eval
  simpa only [s,Δ,p,Syn.shift,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,
    one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using bound

theorem integer_cutoff_bound (p X Y D sign R T N L C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T (D*L*E) C E)
    (hL : Γ ⊢[PRAAx] le one L) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF .cofinal) p (data X Y D sign R T N (D*L*E) C E))
      (tailNumerator p X D one (unit L)) (tailDenominator p X (unit L)) := by
  have hX := h.andE₁.andE₁.andE₁.andE₁
  have hD := h.andE₁.andE₁.andE₂
  have hE := h.andE₂.andE₁
  exact named_tail_bound p X Y D sign R T N (D*L*E) C E one (unit L) two h
    (positive_product _ _ (positive_product _ _ hD hL) hE) hC (unit_positive L)
    (integer_cutoff_envelope X D L E hX hD hE)

theorem actual_Binet_Laplace_integer_cutoff_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 3*var 8*var 10) (var 9) (var 10) ⟶
      le one (var 8) ⟶ le one (var 9) ⟶
        bounded (ap2 (nameF .cofinal) (var 0)
          (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 3*var 8*var 10) (var 9) (var 10)))
          (tailNumerator (var 0) (var 1) (var 3) one (unit (var 8))) (tailDenominator (var 0) (var 1) (unit (var 8)))) :=
  closeUniv 11 (.impI (.impI (.impI (integer_cutoff_bound _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripTailEnvelope
