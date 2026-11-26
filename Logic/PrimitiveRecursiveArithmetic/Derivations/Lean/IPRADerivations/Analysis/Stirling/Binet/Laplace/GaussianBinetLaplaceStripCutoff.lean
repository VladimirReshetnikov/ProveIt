import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceStrip

/-!
# Uniform-mesh Binet strip comparison

The common regular partition compares the finite and cofinal Binet
integrands at the same physical tags. Multiplication by the mesh
width cancels the grid count in the sum of the cutoff errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripCutoff

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianBinetLaplaceStrip (Kernel evaluatorF evaluator_at fixedData tagNumerator tag_inside source subst_source)
open GaussianCompactRiemannName
  (grid grid_inside quadrature sampleBody sampleData sample_body_at precision mesh)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "CofinalF" => evaluatorF Kernel.cofinal
local notation "FiniteF" => evaluatorF Kernel.finite

theorem grid_tag (i M A C E : PTm n) :
    Γ ⊢[PRAAx] (tagNumerator (grid i M (E+A) C E) ≐ A*M+C*i) ⋏
      (sndT (grid i M (E+A) C E) ≐ E*M) := by
  have hd : Γ ⊢[PRAAx] sndT (grid i M (E+A) C E) ≐ E*M := snd_pair _ _
  have ha : Γ ⊢[PRAAx] fstT (grid i M (E+A) C E) ≐ (A*M+C*i)+E*M :=
    (fst_pair _ _).eqTrans (by ipra_ring)
  exact .andI ((congrMonus ha hd).eqTrans (add_monus _ _)) hd

theorem quadrature_refinement (K : Kernel) (p q M r X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le one r) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature (evaluatorF K) p (r*M) (E+A) C E (fixedData X Y D sign R T N))
      (quadrature (evaluatorF K) q M (E+A) C E (fixedData X Y D sign R T N))
      (C*rateNumerator (meshGain R T*C) (E*M) p q) (E*rateDenominator (E*M) p q) :=
  GaussianCompactRiemannName.quadrature_refinement _ _ _ _ _ _ _ _ _ _
    (le_trans h.andE₂.andE₁ (le_add_right E A)) h.andE₂.andE₁ hM hr
    (GaussianBinetLaplaceStrip.sampled_modulus K X Y D sign R T N A C E h)

private theorem cutoff_term (i p q M X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody CofinalF) i (sampleData p M (E+A) C E (fixedData X Y D sign R T N)))
      (inst2 (sampleBody FiniteF) i (sampleData q M (E+A) C E (fixedData X Y D sign R T N)))
      (rateNumerator one (num 8*N) p q) (rateDenominator (num 8*N) p q) := by
  let x := fixedData X Y D sign R T N
  let t := grid i M (E+A) C E
  let a := tagNumerator t
  let b := sndT t
  have hE := h.andE₂.andE₁
  have ht := grid_inside i M (E+A) C E (le_trans hE (le_add_right E A)) hE hM (le_of_lt hi)
  have hp := tag_inside t A C E T hE h.andE₂.andE₂ ht
  have hi' : Γ ⊢[PRAAx] GaussianBinetLaplaceIntegrand.input X Y D sign R T a b :=
    .andI h.andE₁ (.andI ht.andE₂.andE₁ hp.andE₂)
  have first := (sample_body_at (Γ := Γ) CofinalF i p M (E+A) C E x).eqTrans
    (evaluator_at .cofinal p t X Y D sign R T N)
  have second := (sample_body_at (Γ := Γ) FiniteF i q M (E+A) C E x).eqTrans
    (evaluator_at .finite q t X Y D sign R T N)
  exact distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (GaussianBinetLaplaceIntegrand.cutoff_rate X Y D sign R T N a b hi' hN))

private theorem common_weight (f g : PTm 2) (M x y C E A D : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] termsDistance f g M x y A D) :
    Γ ⊢[PRAAx] distanceBounded (GaussianRationalRiemannRefinement.leftSum f M x C E)
      (GaussianRationalRiemannRefinement.leftSum g M y C E) (C*A) (E*D) := by
  let u := GaussianRationalFiniteSum.sum f M x
  let v := GaussianRationalFiniteSum.sum g M y
  let w := weight C E M
  have d := positive_product _ _ hE hM
  have raw := GaussianRationalReciprocal.bounded_product w _ C (E*M) (M*A) D d hD (weight_bound C E M hE hM)
    (sum_distance f g M x y A D hD h)
  have scaled := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ d hD) (positive_product _ _ hE hD)
    (le_of_eq_add (d := zero) (by ipra_ring)) scaled

theorem quadrature_cutoff (p q M X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature CofinalF p M (E+A) C E (fixedData X Y D sign R T N))
      (quadrature FiniteF q M (E+A) C E (fixedData X Y D sign R T N))
      (C*rateNumerator one (num 8*N) p q) (E*rateDenominator (num 8*N) p q) := by
  let x := fixedData X Y D sign R T N
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h.shift
  have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,Fm.shift,Syn.shift,s,one] using hM.shift
  have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,Fm.shift,Syn.shift,s,one] using hN.shift
  have rows : Γ ⊢[PRAAx] termsDistance (sampleBody CofinalF) (sampleBody FiniteF) M
      (sampleData p M (E+A) C E x) (sampleData q M (E+A) C E x)
      (rateNumerator one (num 8*N) p q) (rateDenominator (num 8*N) p q) := by
    refine .allI (.impI ?_)
    simpa only [termsDistance,Syn.shift,s,Δ,x,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      PTm.subst_add,PTm.subst_mul,PTm.subst_num,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,
      GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator] using
      cutoff_term (var 0) (s p) (s q) (s M) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s C) (s E)
        hs.wk ms.wk ns.wk Prf.hyp0
  have hk := positive_product _ _ (GaussianBinetKernelTailMajorant.eight_positive (Γ := Γ)) hN
  exact common_weight _ _ M _ _ C E _ _ hM h.andE₂.andE₁ (denominator_positive _ p q hk) rows

private theorem cutoff_diagonal (p X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianBinetLaplaceStrip.nameF .cofinal) p (GaussianBinetLaplaceStrip.data X Y D sign R T N A C E))
      (ap2 (GaussianBinetLaplaceStrip.nameF .finite) p (GaussianBinetLaplaceStrip.data X Y D sign R T N A C E))
      (diagonalNumerator C (E*(num 8*N)) (two*C) p) (diagonalDenominator (E*(num 8*N)) p) := by
  let x := fixedData X Y D sign R T N
  let q := precision p T
  let M := mesh p (meshGain R T) T
  let K := num 8*N
  let U := unit p
  let V := unit q
  have he := h.andE₂.andE₁
  have hk : Γ ⊢[PRAAx] le one K := positive_product _ _ GaussianBinetKernelTailMajorant.eight_positive hN
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) q
  have g : Γ ⊢[PRAAx] le U V :=
    GaussianCompactRiemannName.dyadic_monotone p q (le_of_eq_add (d := T+num 6) (by dsimp only [q,precision]; ipra_ring))
  have orig := quadrature_cutoff q q M X Y D sign R T N A C E h
    (GaussianCompactRiemannName.mesh_positive p (meshGain R T) T) hN
  have raw := distance_radius_mono _ _ _ _ (diagonalNumerator C (E*K) (two*C) p) (diagonalDenominator (E*K) p)
    (positive_product _ _ he (denominator_positive K q q hk)) (positive_product _ _ (positive_product _ _ he hk) hu) ?_ orig
  · exact distance_congr (GaussianCompactRiemannName.name_at CofinalF p (E+A) C E (meshGain R T) T x).eqSymm
      (GaussianCompactRiemannName.name_at FiniteF p (E+A) C E (meshGain R T) T x).eqSymm
      (.eqRefl _) (.eqRefl _) raw
  · change Γ ⊢[PRAAx] le ((C*(one*V*V+K*(V+V)))*((E*K)*U))
      ((C*U+(two*C)*(E*K))*(E*(K*V*V)))
    ipra_le 2*𝔞(C)*𝔞(E)*𝔞(K*K)*𝔞(V)*sl g + 2*𝔞(C)*𝔞(E)*𝔞(K*K)*𝔞(V*V)*sl he

theorem cutoff_rate (X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate (GaussianBinetLaplaceStrip.nameF .cofinal) (GaussianBinetLaplaceStrip.nameF .finite)
      (GaussianBinetLaplaceStrip.data X Y D sign R T N A C E) (GaussianBinetLaplaceStrip.data X Y D sign R T N A C E)
      C (E*(num 8*N)) := by
  let s (v : PTm n) := Syn.shift v
  have hd := positive_product _ _ h.andE₂.andE₁
    (positive_product _ _ (GaussianBinetKernelTailMajorant.eight_positive (Γ := Γ)) hN)
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (two*C) hd
    (GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R T N A C E h)
    (GaussianBinetLaplaceStrip.regular .finite X Y D sign R T N A C E h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Fm.shift,Syn.shift,s,subst_source] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (s N) := by simpa [Fm.shift,Syn.shift,s,one] using hN.shift
  simpa only [diagonalEnvelope,GaussianBinetLaplaceStrip.subst_data,Syn.shift,s,PTm.subst_mul,PTm.subst_num,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,two] using
    cutoff_diagonal (var 0) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s C) (s E) hs ns

theorem actual_Binet_compact_strip_cutoff_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) (var 9) ⟶ le one (var 6) ⟶
        independentRate (GaussianBinetLaplaceStrip.nameF .cofinal) (GaussianBinetLaplaceStrip.nameF .finite)
          (GaussianBinetLaplaceStrip.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
          (GaussianBinetLaplaceStrip.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
          (var 8) (var 9*(num 8*var 6))) :=
  closeUniv 10 (.impI (.impI (cutoff_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripCutoff
