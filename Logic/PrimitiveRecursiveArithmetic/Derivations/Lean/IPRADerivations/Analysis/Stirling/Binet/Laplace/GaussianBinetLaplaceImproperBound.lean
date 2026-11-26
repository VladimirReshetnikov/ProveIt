import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceImproperName
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripTail
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayQuadratureAtZero

/-!
# The sharp norm bound for the actual improper Binet integral

The real decay quadrature starts at zero, with initial exponential
sample exactly one. The finite estimate is transferred to the original
complex Binet quadrature by the already proved scalar majorant. The
result holds on every compact prefix and at the actual improper sampler.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceImproperBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianBinetLaplaceStrip (Kernel evaluatorF fixedData)
open GaussianBinetLaplaceStripTail (tailNumerator tailDenominator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (quadrature mesh precision)
open GaussianEulerDecayMesh (observation stepError errorDen)
open GaussianEulerDecayQuadratureAtZero (zero_observation actual_decay_quadrature)
open GaussianEulerDecayQuadraturePrecision (endpointDifference same_mesh_precision)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (distance_zero_iff norm_from_distance)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "CofinalF" => evaluatorF Kernel.cofinal
local notation "DecayF" => GaussianEulerDecayQuadrature.evaluatorF
local notation "twelve" => num 12
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def realAllowance (C : PTm n) : PTm n := num 3*C*C+two*C+num 7

theorem late_real_quadrature_bound (p t M C E : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hstep : Γ ⊢[PRAAx] le C (E*M)) (hp : Γ ⊢[PRAAx] le (unit t) (unit p))
    (hm : Γ ⊢[PRAAx] le (unit t) M) :
    Γ ⊢[PRAAx] bounded (quadrature DecayF p M zero C E zero) (unit t+realAllowance C) (unit t) := by
  let U := unit t
  let V := unit p
  let j := GaussianFastValueCut.exponent (num 20*M) t
  let W := unit j
  let B := E*M
  let Z := B*B*W
  let P := quadrature DecayF p M zero C E zero
  let Q := quadrature DecayF j M zero C E zero
  let Y := endpointDifference zero C E j
  let A := num 3*C*C+one
  have hu := unit_positive (Γ := Γ) t
  have hv := unit_positive (Γ := Γ) p
  have hw := unit_positive (Γ := Γ) j
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ hE hM
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ hB hB) hw
  have hUV : Γ ⊢[PRAAx] le U V := hp
  have hUW : Γ ⊢[PRAAx] le U W :=
    GaussianExponentialReference.unit_monotone (le_add_right t (GaussianFastValueCut.normalizer (num 20*M)))
  have budget : Γ ⊢[PRAAx] le (num 20*M*U) W := GaussianFastValueCut.query_budget (num 20*M) t
  have hMB : Γ ⊢[PRAAx] le M B :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] one*M ≐ M) (.eqRefl B) (mul_le_mul_right M hE)
  have hBB : Γ ⊢[PRAAx] le (M*U) (B*B) := le_mul_mono hMB (le_trans hm hMB)
  have first : Γ ⊢[PRAAx] distanceBounded Q Y A U := by
    apply distance_radius_mono _ _ _ _ _ _ hZ hu ?_
      (actual_decay_quadrature j M zero C E zero hM hE hC hstep)
    change Γ ⊢[PRAAx] le ((M*(GaussianNameRingLaws.three*C*C*W+num 20*(B*B)))*U) (A*(B*B*W))
    dsimp only [A,GaussianNameRingLaws.three]
    ipra_le 3*𝔞(C)*𝔞(C)*𝔞(W)*sl hBB + 𝔞(B)*𝔞(B)*sl budget
  have same := same_mesh_precision p j M zero C E zero hM hE
  have second : Γ ⊢[PRAAx] distanceBounded P Q (two*C) U := by
    apply distance_radius_mono _ _ _ _ _ _
      (positive_product _ _ hE (positive_product _ _ hv hw)) hu ?_ same
    change Γ ⊢[PRAAx] le (C*(V+W)*U) (two*C*(E*(V*W)))
    ipra_le 2*𝔞(C)*𝔞(V)*𝔞(W)*sl hE + 𝔞(C)*𝔞(W)*sl hUV + 𝔞(C)*𝔞(V)*sl hUW
  have start : Γ ⊢[PRAAx] bounded (observation zero E j) one one :=
    bound_congr (zero_observation E j hE).eqSymm (.eqRefl _) (.eqRefl _) GaussianRationalReciprocal.qone_bounded
  have endpoint : Γ ⊢[PRAAx] bounded Y (U+num 6) U := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) hw) hu ?_
      (GaussianEulerDecayEndpointBound.endpoint_norm zero C E j one one hE (le_refl one) start)
    change Γ ⊢[PRAAx] le ((one*W+num 6*one)*U) ((U+num 6)*(one*W))
    ipra_le 6*sl hUW
  have joined := distance_triangle_same _ _ _ _ _ _ hu second first
  have raw := distance_triangle_same _ _ _ _ _ _ hu joined ((distance_zero_iff _ _ _ hu).iffMpr endpoint)
  exact (distance_zero_iff _ _ _ hu).iffMp
    (distance_radius_mono _ _ _ _ _ _ hu hu (le_of_eq_add (d := zero) (by dsimp only [A,realAllowance]; ipra_ring)) raw)

def stripAllowance (X D C : PTm n) : PTm n := num 10*C+D*realAllowance (X*C)

private theorem late_strip_quadrature_bound (p t M X Y D sign R T N C E : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R T zero C E)
    (hC : Γ ⊢[PRAAx] le one C) (hM : Γ ⊢[PRAAx] le one M)
    (hm : Γ ⊢[PRAAx] le (unit t) M) (hp : Γ ⊢[PRAAx] le (unit t) (unit p))
    (hstep : Γ ⊢[PRAAx] le (X*C) ((D*E)*M)) :
    Γ ⊢[PRAAx] bounded (quadrature CofinalF p M (E+zero) C E (fixedData X Y D sign R T N))
      (D*unit t+stripAllowance X D C*(twelve*X)) ((twelve*X)*unit t) := by
  let U := unit p
  let V := unit t
  let K := twelve*X
  let H := realAllowance (X*C)
  have hE := h.andE₂.andE₁
  have hD := h.andE₁.andE₁.andE₂
  have hX := h.andE₁.andE₁.andE₁.andE₁
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ h12 hX
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have bound := late_real_quadrature_bound p t M (X*C) (D*E) hM (positive_product _ _ hX hC)
    (positive_product _ _ hD hE) hstep hp hm
  have rew : Γ ⊢[PRAAx] quadrature DecayF p M zero (X*C) (D*E) zero ≐
      quadrature DecayF p M (X*zero) (X*C) (D*E) zero := by
    simpa only [GaussianCompactRiemannName.subst_quadrature,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
      ConciseIPRA.PTm.subst_zero] using
      Prf.eqCongr1 (quadrature DecayF (Syn.shift p) (Syn.shift M) (var 0) (Syn.shift (X*C)) (Syn.shift (D*E)) zero)
        (by ipra_ring : Γ ⊢[PRAAx] zero ≐ X*zero)
  have realBound := bound_congr rew (.eqRefl _) (.eqRefl _) bound
  have raw := GaussianBinetLaplaceStripDomination.quadrature_bound p M X Y D sign R T N zero C E
    (V+H) V h hM hV realBound
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hE hU) (positive_product _ _ hK hV))
    (positive_product _ _ hK hV) ?_ raw
  change Γ ⊢[PRAAx] le (((C*num 10)*(K*V)+(D*(V+H))*(E*U))*(K*V))
    ((D*V+(num 10*C+D*H)*K)*((E*U)*(K*V)))
  have hEU : Γ ⊢[PRAAx] le V (E*U) := le_trans hp
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*U ≐ U) (.eqRefl _) (mul_le_mul_right U hE))
  ipra_le (10*𝔞(C)*𝔞(K)*𝔞(K)*𝔞(V))*sl hEU +
    (𝔞(D)*𝔞(H)*𝔞(E)*𝔞(U)*𝔞(K)*𝔞(V))*sl hK

private theorem strip_slack (p t X Y D sign R T N C E : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R T zero C E)
    (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (qsub (ap2 (GaussianBinetLaplaceStrip.nameF .cofinal) p
        (GaussianBinetLaplaceStrip.data X Y D sign R T N zero C E)) qzero)
      (tailNumerator p X D one one) (tailDenominator p X one) (one+stripAllowance X D C) t := by
  let F := GaussianBinetLaplaceStrip.nameF .cofinal
  let x := GaussianBinetLaplaceStrip.data X Y D sign R T N zero C E
  let S := X*C
  let l := GaussianFastValueCut.normalizer S
  let s := t+l
  let k := precision s T
  let m := mesh s (meshGain R T) T
  let K := twelve*X
  let V := unit t
  let W := unit p
  let U := unit s
  let H := stripAllowance X D C
  have hu := unit_positive (Γ := Γ) s
  have hv := unit_positive (Γ := Γ) t
  have hw := unit_positive (Γ := Γ) p
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ h12 h.andE₁.andE₁.andE₁.andE₁
  have hE := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have hs : Γ ⊢[PRAAx] le t s := le_add_right t l
  have hg : Γ ⊢[PRAAx] le V U := GaussianExponentialReference.unit_monotone hs
  have hk : Γ ⊢[PRAAx] le V (unit k) := GaussianExponentialReference.unit_monotone
    (le_trans hs (le_of_eq_add (d := T+num 6) (by dsimp only [k,precision]; ipra_ring)))
  have hmesh : Γ ⊢[PRAAx] le (unit (s+num 6)) m :=
    le_of_eq_add (d := unit (s+num 6)*meshGain R T*T*T) (by dsimp only [m,mesh]; ipra_ring)
  have hm : Γ ⊢[PRAAx] le V m := le_trans
    (GaussianExponentialReference.unit_monotone (le_trans hs (le_add_right s (num 6)))) hmesh
  have hM := le_trans hv hm
  have step : Γ ⊢[PRAAx] le S ((D*E)*m) := by
    have inClock : Γ ⊢[PRAAx] le l (s+num 6) :=
      le_trans (le_congr (.eqRefl _) (by dsimp only [s]; ipra_ring) (le_add_right l t)) (le_add_right s (num 6))
    have has := le_trans (GaussianFastValueCut.normalizer_budget S)
      (le_trans (GaussianExponentialReference.unit_monotone inClock) hmesh)
    exact le_trans has (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*m ≐ m) (.eqRefl _) (mul_le_mul_right m hE))
  have eval := late_strip_quadrature_bound k t m X Y D sign R T N C E h hC hM hm hk step
  have read : Γ ⊢[PRAAx] ap2 F s x ≐ quadrature CofinalF k m (E+zero) C E (fixedData X Y D sign R T N) :=
    GaussianCompactRiemannName.name_at CofinalF s (E+zero) C E (meshGain R T) T (fixedData X Y D sign R T N)
  have sample := bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) eval
  have reg := GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N zero C E h
  have near := GaussianNameEquivalence.point_at F x p s reg
  have den : Γ ⊢[PRAAx] le one (K*V) := positive_product _ _ hK hv
  have known := norm_from_distance _ _ _ _ _ _ (positive_product _ _ hw hu) den near sample
  let Z := (K*W)*V
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ hK hw) hv
  have target : Γ ⊢[PRAAx] bounded (ap2 F p x) ((D*W+K)*V+(one+H)*(K*W)) Z := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hw hu) den) hZ ?_ known
    change Γ ⊢[PRAAx] le (((W+U)*(K*V)+(D*V+H*K)*(W*U))*((K*W)*V))
      (((D*W+K)*V+(one+H)*(K*W))*((W*U)*(K*V)))
    ipra_le 𝔞(K)*𝔞(K)*𝔞(W)*𝔞(W)*𝔞(V)*sl hg
  apply (distance_zero_iff _ _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ hK (le_refl one)) hw) hv)).iffMpr
  exact bound_congr (.eqRefl _) (by
    change Γ ⊢[PRAAx] (D*W+K)*V+(one+H)*(K*W) ≐ (D*one*W+K*one)*V+(one+H)*(K*one*W)
    ipra_ring) (by
    change Γ ⊢[PRAAx] (K*W)*V ≐ (K*one*W)*V
    ipra_ring) target

/-- This is the fixed-prefix norm bound, with leading (D/(12X))
and no dependence on the horizon or width. -/
theorem strip_bound (p X Y D sign R T N C E : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R T zero C E)
    (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] bounded (ap2 (GaussianBinetLaplaceStrip.nameF .cofinal) p
      (GaussianBinetLaplaceStrip.data X Y D sign R T N zero C E))
      (tailNumerator p X D one one) (tailDenominator p X one) := by
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hK := positive_product _ _ h12 h.andE₁.andE₁.andE₁.andE₁
  have hp : Γ ⊢[PRAAx] le one (tailDenominator p X one) :=
    positive_product _ _ (positive_product _ _ hK (le_refl one)) (unit_positive p)
  apply (distance_zero_iff _ _ _ hp).iffMp
  exact GaussianRationalSlackRemoval.slack_removal_at _ _ _ (one+stripAllowance X D C) hp
    (strip_slack p _ X Y D sign R T N C E h hC)

theorem prefix_bound (p X Y D sign R L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source X Y D sign R) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] bounded (ap2 (GaussianBinetLaplaceStrip.nameF .cofinal) p
      (GaussianBinetLaplaceOrderedPrefixes.prefixData X Y D sign R L))
      (tailNumerator p X D one one) (tailDenominator p X one) := by
  let T := GaussianBinetLaplaceOrderedPrefixes.width D L
  have hD := h.andE₁.andE₂
  have ht : Γ ⊢[PRAAx] le one T := positive_product _ _ (positive_product _ _ hD hL) (le_refl one)
  have panel : Γ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R T zero T one :=
    .andI h (.andI (le_refl one) (le_congr (by ipra_ring) (by ipra_ring) (le_refl T)))
  exact strip_bound p X Y D sign R T zero T one panel ht

theorem improper_bound (p X Y D sign R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianLogGammaEulerResidualDomain.source X Y D sign R) :
    Γ ⊢[PRAAx] bounded (ap2 GaussianBinetLaplaceImproperName.nameF p (GaussianBinetLaplaceImproperName.data X Y D sign R))
      (tailNumerator (succ p) X D one one) (tailDenominator (succ p) X one) :=
  bound_congr (GaussianBinetLaplaceImproperName.sample_at p X Y D sign R).eqSymm (.eqRefl _) (.eqRefl _)
    (prefix_bound (succ p) X Y D sign R (GaussianBinetLaplaceImproperName.cutoff p D) h
      (GaussianBinetLaplaceImproperName.cutoff_positive p D))

theorem actual_Binet_Laplace_improper_norm_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianLogGammaEulerResidualDomain.source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      bounded (ap2 GaussianBinetLaplaceImproperName.nameF (var 0)
        (GaussianBinetLaplaceImproperName.data (var 1) (var 2) (var 3) (var 4) (var 5)))
        (tailNumerator (succ (var 0)) (var 1) (var 3) one one) (tailDenominator (succ (var 0)) (var 1) one)) :=
  closeUniv 6 (.impI (improper_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceImproperBound
