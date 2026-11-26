import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripDomination

/-!
# Uniform tails for the actual cofinal Binet strips

The original real exponential endpoint estimate controls every positive
width. Finer observations are auxiliary and can be eliminated after
fixing the requested observation of the original Binet integral.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceStrip (Kernel evaluatorF fixedData source nameF data)
open GaussianBinetLaplaceStripDomination (quadrature_bound)
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (quadrature mesh precision)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayQuadraturePrecision (endpointDifference numerator denominator independent_quadrature_endpoint)
open GaussianEulerDecayEndpointBound (endpoint_norm)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance distance_zero_iff)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "twelve" => num 12
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "CofinalF" => evaluatorF Kernel.cofinal
local notation "DecayF" => GaussianEulerDecayQuadrature.evaluatorF

def decayAllowance (C J : PTm n) : PTm n := J+num 8+C+num 3*C*C

/-- The original scaled-axis quadrature has its stated leading endpoint
radius, plus an explicit error when both the mesh size and the sampling
clock reach the auxiliary precision `t`. -/
theorem decay_quadrature_bound (p t M a C E P Q J : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hQ : Γ ⊢[PRAAx] le one Q) (hstep : Γ ⊢[PRAAx] le C (E*M))
    (hp : Γ ⊢[PRAAx] le (unit t) (unit p)) (hm : Γ ⊢[PRAAx] le (unit t) M)
    (hb : Γ ⊢[PRAAx] bounded (observation a E p) (P*unit p+J*Q) (Q*unit p)) :
    Γ ⊢[PRAAx] bounded (quadrature DecayF p M a C E zero)
      (P*unit t+decayAllowance C J*Q) (Q*unit t) := by
  let U := unit p
  let V := unit t
  let L := E*E*M
  let Lp := L*U
  let A := P*U+J*Q
  let B := Q*U
  let Y := endpointDifference a C E p
  let W := quadrature DecayF p M a C E zero
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) t
  have hB := positive_product _ _ hQ hu
  have hL := positive_product _ _ (positive_product _ _ hE hE) hM
  have hLp := positive_product _ _ hL hu
  have hDen : Γ ⊢[PRAAx] le one (denominator p p M E) :=
    positive_product _ _ hLp hu
  have coarse := independent_quadrature_endpoint p p M a C E zero ha hM hE hC hstep
  have meshError : Γ ⊢[PRAAx] distanceBounded W Y
      (num 3*C*C*U+C*E*M+two*L) Lp :=
    distance_radius_mono _ _ _ _ _ _ hDen hLp (le_of_eq_add (d := zero) (by
      dsimp only [Lp,L,U,numerator,denominator,GaussianNameRingLaws.three]; ipra_ring)) coarse
  have endpointRaw := endpoint_norm a C E p A B hE hB hb
  have endpoint : Γ ⊢[PRAAx] bounded Y (P*U+(J+num 6)*Q) B :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hB hu) hB
      (le_of_eq_add (d := zero) (by dsimp only [A,B,U]; ipra_ring)) endpointRaw
  have raw := norm_from_distance W Y _ Lp _ B hLp hB meshError endpoint
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hLp hB) (positive_product _ _ hQ hv) ?_ raw
  change Γ ⊢[PRAAx] le
    (((num 3*C*C*U+C*E*M+two*L)*B+(P*U+(J+num 6)*Q)*Lp)*(Q*V))
    ((P*V+decayAllowance C J*Q)*(Lp*B))
  have ht : Γ ⊢[PRAAx] le V L := le_trans hm
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*M ≐ M) (.eqRefl L)
      (mul_le_mul_right M (positive_product _ _ hE hE)))
  have hy : Γ ⊢[PRAAx] le (E*M) L :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] one*(E*M) ≐ E*M)
      (by dsimp only [L]; ipra_ring : Γ ⊢[PRAAx] E*(E*M) ≐ L) (mul_le_mul_right (E*M) hE)
  have hUV : Γ ⊢[PRAAx] le V U := hp
  dsimp only [decayAllowance,Lp,B]
  ipra_le (𝔞(Q)*𝔞(Q)*𝔞(U)*
    ((𝔞(J)+8)*𝔞(L)+𝔞(C)*𝔞(E*M)))*sl hUV +
    (𝔞(Q)*𝔞(Q)*𝔞(U)*𝔞(U)*𝔞(C))*sl hy +
    (3*𝔞(Q)*𝔞(Q)*𝔞(U)*𝔞(U)*𝔞(C)*𝔞(C))*sl ht

def stripAllowance (X D C J : PTm n) : PTm n := num 10*C+D*decayAllowance (X*C) J

theorem quadrature_late_bound (p t M X Y D sign R T N A C E P Q J : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hM : Γ ⊢[PRAAx] le one M) (hm : Γ ⊢[PRAAx] le (unit t) M)
    (hp : Γ ⊢[PRAAx] le (unit t) (unit p)) (hstep : Γ ⊢[PRAAx] le (X*C) ((D*E)*M))
    (hb : Γ ⊢[PRAAx] bounded (observation (X*A) (D*E) p) (P*unit p+J*Q) (Q*unit p)) :
    Γ ⊢[PRAAx] bounded (quadrature CofinalF p M (E+A) C E (fixedData X Y D sign R T N))
      ((D*P)*unit t+stripAllowance X D C J*((twelve*X)*Q)) (((twelve*X)*Q)*unit t) := by
  let U := unit p
  let V := unit t
  let K := twelve*X
  let H := decayAllowance (X*C) J
  have hE := h.andE₂.andE₁
  have hD := h.andE₁.andE₁.andE₂
  have hX := h.andE₁.andE₁.andE₁.andE₁
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ h12 hX
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have read := decay_quadrature_bound p t M (X*A) (X*C) (D*E) P Q J
    (positive_product _ _ hX hA) hM (positive_product _ _ hX hC) (positive_product _ _ hD hE) hQ hstep hp hm hb
  have raw := quadrature_bound p M X Y D sign R T N A C E
    (P*V+H*Q) (Q*V) h hM (positive_product _ _ hQ hV) read
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hE hU)
    (positive_product _ _ hK (positive_product _ _ hQ hV)))
    (positive_product _ _ (positive_product _ _ hK hQ) hV) ?_ raw
  change Γ ⊢[PRAAx] le (((C*num 10)*(K*(Q*V))+(D*(P*V+H*Q))*(E*U))*((K*Q)*V))
    (((D*P)*V+(num 10*C+D*H)*(K*Q))*((E*U)*(K*(Q*V))))
  have hEU : Γ ⊢[PRAAx] le V (E*U) := le_trans hp
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*U ≐ U) (.eqRefl _) (mul_le_mul_right U hE))
  ipra_le (10*𝔞(C)*𝔞(K)*𝔞(K)*𝔞(Q)*𝔞(Q)*𝔞(V))*sl hEU +
    (𝔞(D)*𝔞(H)*𝔞(E)*𝔞(U)*𝔞(K)*𝔞(Q)*𝔞(Q)*𝔞(V))*sl hK

def envelope (a E P Q J : PTm n) : Fm PTm n := .all
  (bounded (observation (Syn.shift a) (Syn.shift E) (var 0))
    (Syn.shift P*unit (var 0)+Syn.shift J*Syn.shift Q) (Syn.shift Q*unit (var 0)))

theorem envelope_at (a E P Q J p : PTm n) (h : Γ ⊢[PRAAx] envelope a E P Q J) :
    Γ ⊢[PRAAx] bounded (observation a E p) (P*unit p+J*Q) (Q*unit p) := by
  simpa only [envelope,GaussianRationalMetric.subst_bounded,GaussianEulerDecayMesh.subst_observation,
    PTm.subst_mul,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit,Syn.inst_zero,
    Syn.subst_inst_shift,Syn.subst_var] using h.allE p

def tailNumerator (p X D P Q : PTm n) : PTm n := D*P*unit p+twelve*X*Q
def tailDenominator (p X Q : PTm n) : PTm n := twelve*X*Q*unit p

private theorem late_strip_bound (p t X Y D sign R T N A C E P Q J : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hb : Γ ⊢[PRAAx] envelope (X*A) (D*E) P Q J) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (qsub (ap2 (nameF .cofinal) p (data X Y D sign R T N A C E)) qzero)
      (tailNumerator p X D P Q) (tailDenominator p X Q) (one+stripAllowance X D C J) t := by
  let F := nameF .cofinal
  let x := data X Y D sign R T N A C E
  let S := X*C
  let s := t+GaussianFastValueCut.normalizer S
  let k := precision s T
  let m := mesh s (meshGain R T) T
  let K := twelve*X
  let V := unit t
  let W := unit p
  let U := unit s
  let H := stripAllowance X D C J
  have hu := unit_positive (Γ := Γ) s
  have hv := unit_positive (Γ := Γ) t
  have hw := unit_positive (Γ := Γ) p
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hK := positive_product _ _ h12 h.andE₁.andE₁.andE₁.andE₁
  have hE := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have hs : Γ ⊢[PRAAx] le t s := le_add_right t (GaussianFastValueCut.normalizer S)
  have hg : Γ ⊢[PRAAx] le V U := GaussianExponentialReference.unit_monotone hs
  have hk : Γ ⊢[PRAAx] le V (unit k) := GaussianExponentialReference.unit_monotone
    (le_trans hs (le_of_eq_add (d := T+num 6) (by dsimp only [k,precision]; ipra_ring)))
  have hm : Γ ⊢[PRAAx] le V m := by
    have hz : Γ ⊢[PRAAx] le t (s+num 6) := le_trans hs (le_add_right s (num 6))
    exact le_trans (GaussianExponentialReference.unit_monotone hz)
      (le_of_eq_add (d := unit (s+num 6)*meshGain R T*T*T) (by dsimp only [m,mesh]; ipra_ring))
  have hM : Γ ⊢[PRAAx] le one m := le_trans hv hm
  have step : Γ ⊢[PRAAx] le S ((D*E)*m) := by
    let l := GaussianFastValueCut.normalizer S
    have inClock : Γ ⊢[PRAAx] le l (s+num 6) :=
      le_trans (le_congr (.eqRefl _) (by dsimp only [s,l]; ipra_ring) (le_add_right l t)) (le_add_right s (num 6))
    have mUpper : Γ ⊢[PRAAx] le (unit (s+num 6)) m :=
      le_of_eq_add (d := unit (s+num 6)*meshGain R T*T*T) (by dsimp only [m,mesh]; ipra_ring)
    have has := le_trans (GaussianFastValueCut.normalizer_budget S)
      (le_trans (GaussianExponentialReference.unit_monotone inClock) mUpper)
    exact le_trans has (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*m ≐ m) (.eqRefl _) (mul_le_mul_right m hE))
  have eval := quadrature_late_bound k t m X Y D sign R T N A C E P Q J h hA hC hQ hM hm hk step
    (envelope_at (X*A) (D*E) P Q J k hb)
  have read : Γ ⊢[PRAAx] ap2 F s x ≐ quadrature CofinalF k m (E+A) C E (fixedData X Y D sign R T N) :=
    GaussianCompactRiemannName.name_at CofinalF s (E+A) C E (meshGain R T) T (fixedData X Y D sign R T N)
  have sample := bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) eval
  have regular := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N A C E h
  have near := GaussianNameEquivalence.point_at F x p s regular
  let Z := ((K*Q)*W)*V
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _
    (positive_product _ _ hK hQ) hw) hv
  have known := norm_from_distance _ _ _ _ _ _ (positive_product _ _ hw hu)
    (positive_product _ _ (positive_product _ _ hK hQ) hv) near sample
  apply (distance_zero_iff _ _ _ hZ).iffMpr
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hw hu)
    (positive_product _ _ (positive_product _ _ hK hQ) hv)) hZ ?_ known
  change Γ ⊢[PRAAx] le (((W+U)*((K*Q)*V)+((D*P)*V+H*(K*Q))*(W*U))*(((K*Q)*W)*V))
    (((D*P*W+K*Q)*V+(one+H)*((K*Q)*W))*((W*U)*((K*Q)*V)))
  ipra_le 𝔞(K)*𝔞(K)*𝔞(Q)*𝔞(Q)*𝔞(W)*𝔞(W)*𝔞(V)*sl hg

/-- The exact leading envelope is uniform in the strip width and horizon.
The requested integral observation contributes only its normal (2^{-p})
error. -/
theorem named_tail_bound (p X Y D sign R T N A C E P Q J : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hb : Γ ⊢[PRAAx] envelope (X*A) (D*E) P Q J) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF .cofinal) p (data X Y D sign R T N A C E))
      (tailNumerator p X D P Q) (tailDenominator p X Q) := by
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hD : Γ ⊢[PRAAx] le one (tailDenominator p X Q) :=
    positive_product _ _ (positive_product _ _
      (positive_product _ _ h12 h.andE₁.andE₁.andE₁.andE₁) hQ) (unit_positive p)
  apply (distance_zero_iff _ _ _ hD).iffMp
  apply GaussianRationalSlackRemoval.slack_removal_at _ _ _ (one+stripAllowance X D C J) hD
  exact late_strip_bound p _ X Y D sign R T N A C E P Q J h hA hC hQ hb

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripTail
