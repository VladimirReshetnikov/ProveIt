import IPRADerivations.Analysis.Stirling.Binet.Bose.LiteralTails.GaussianBinetBoseLiteralLate
import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseCompact
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Quadrature of the original Bose integrand by a shared literal prefix

The lower time margin permits one positive-index cutoff for all tags
in a finite time panel. The weighted comparison keeps the original
left mesh, its exact integration weight and the original arctangent
observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixQuadrature

open_ipra
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBoseCompact (source arctangent_bound arctangent_samples tag_lower)
open GaussianBinetBoseDenominator (reciprocalF reciprocalData reciprocal_regular)
open GaussianBinetLaplaceStrip (tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid inside quadrature sampleBody sampleData sample_body_at precision mesh)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance)
open GaussianRationalRoundedPower (multiplication_difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Atan" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "Actual" => GaussianBinetBoseIntegrandBound.nameF
local notation "actualData" => GaussianBinetBoseIntegrandBound.data
local notation "Literal" => GaussianBinetBoseLiteralPrefix.value
local notation "clock" => GaussianBinetBoseLiteralUniform.clock

def cost (D T E : PTm n) : PTm n := two*(T*D+E)+(T*D)*num 4

def point (p N X Y D sign A B : PTm n) : PTm n :=
  qmul (ap2 Atan p (atanData X Y D sign A B)) (Literal (clock p N A B) N A B)

ipra_subst cost [two]

ipra_subst point [GaussianBinetBoseLiteralUniform.clock]

/-- Compare one literal prefix at a read clock at least as large as the cutoff clock. -/
theorem point_error_late (s p N X Y D sign A B T E : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (lower : Γ ⊢[PRAAx] le B (E*A)) (upper : Γ ⊢[PRAAx] le A (T*B))
    (hs : Γ ⊢[PRAAx] le s p) (hN : Γ ⊢[PRAAx] le (E*E*unit s) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Actual p (actualData X Y D sign A B)) (point p N X Y D sign A B)
      (cost D T E) (unit s) := by
  let x := atanData X Y D sign A B
  let y := reciprocalData A B
  let u := ap2 Atan p x
  let v := ap2 reciprocalF p y
  let w := Literal (clock p N A B) N A B
  have hp := unit_positive (Γ := Γ) s
  have norm := arctangent_bound p X Y D sign A B T hz hB upper
  have read := GaussianNamedProductObservationBound.sample_error Atan reciprocalF x y p (T*D) E
    (GaussianBinetArctangentQuadrature.regular X Y D sign A B hz hB)
    (reciprocal_regular A B hA hB) (arctangent_samples X Y D sign A B T hz hB upper)
    (GaussianBinetBoseReciprocalTimeRate.inverse_samples_bound A B E hA hB lower)
  have sub := distance_symmetric w v (num 4) (unit s) hp
    (GaussianBinetBoseLiteralLate.finite_uniform_late s p N A B E hA hB hE lower hs hN)
  have product := GaussianRationalReciprocal.bound_congr (multiplication_difference u v w).eqSymm
    (.eqRefl _) (one_mul _) (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hp norm sub)
  exact distance_triangle_same _ _ _ _ _ _ hp
    (GaussianExponentialReference.dyadic_weaken _ _ _ s p hs read) product

theorem point_error (p N X Y D sign A B T E : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (lower : Γ ⊢[PRAAx] le B (E*A)) (upper : Γ ⊢[PRAAx] le A (T*B))
    (hN : Γ ⊢[PRAAx] le (E*E*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Actual p (actualData X Y D sign A B)) (point p N X Y D sign A B)
      (cost D T E) (unit p) :=
  point_error_late p p N X Y D sign A B T E hz hA hB hE lower upper (le_refl p) hN

def evaluatorTerm (p t z : PTm n) : PTm n :=
  let x := sndT z
  point p (fstT z) (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
    (tagNumerator t) (sndT t)

def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))

ipra_subst evaluatorTerm

theorem evaluator_at (p N t X Y D sign : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (pairT N (fixedData X Y D sign)) ≐
      point p N X Y D sign (tagNumerator t) (sndT t) := by
  let x := fixedData X Y D sign
  let z := pairT N x
  have read : Γ ⊢[PRAAx] ap3 evaluatorF p t z ≐ evaluatorTerm p t z := by
    simpa only [evaluatorF,ap3,subst_evaluatorTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,z]
  have x₁ : Γ ⊢[PRAAx] sndT (sndT z) ≐ pairT Y (pairT D sign) :=
    (congrSnd (snd_pair N x)).eqTrans (snd_pair _ _)
  have x₂ := (congrSnd x₁).eqTrans (snd_pair Y (pairT D sign))
  have decode := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (tagNumerator (var 6)) (sndT (var 6)) : PTm 7)
    (σ := ![p,fstT z,fstT (sndT z),fstT (sndT (sndT z)),fstT (sndT (sndT (sndT z))),sndT (sndT (sndT (sndT z))),t])
    (σ' := ![p,N,X,Y,D,sign,t]) (fun j => by
      fin_cases j
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst (snd_pair N x)).eqTrans (fst_pair _ _)
      · exact (congrFst x₁).eqTrans (fst_pair _ _)
      · exact (congrFst x₂).eqTrans (fst_pair _ _)
      · exact (congrSnd x₂).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  exact read.eqTrans (by simpa [evaluatorTerm] using decode)

private theorem cell_error (s p M N X Y D sign T A C E i : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hs : Γ ⊢[PRAAx] le s p) (hN : Γ ⊢[PRAAx] le (E*E*unit s) N) (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody GaussianBinetBoseCompact.evaluatorF) i (sampleData p M (E+A) C E (fixedData X Y D sign)))
      (inst2 (sampleBody evaluatorF) i (sampleData p M (E+A) C E (pairT N (fixedData X Y D sign))))
      (cost D T E) (unit s) := by
  let t := grid i M (E+A) C E
  let x := fixedData X Y D sign
  have hE := h.andE₂.andE₂.andE₁
  have hEA : Γ ⊢[PRAAx] le one (E+A) := le_trans hE (le_add_right E A)
  have ht : Γ ⊢[PRAAx] inside (E+A) C E t :=
    GaussianCompactRiemannName.grid_inside i M (E+A) C E hEA hE hM (le_of_lt hi)
  have lo := tag_lower A C E t h.andE₂.andE₁ hE ht
  have up := tag_inside t A C E T hE h.andE₂.andE₂.andE₂ ht
  have old := (sample_body_at (Γ := Γ) GaussianBinetBoseCompact.evaluatorF i p M (E+A) C E x).eqTrans
    (GaussianBinetBoseCompact.evaluator_at p t X Y D sign)
  have literal := (sample_body_at (Γ := Γ) evaluatorF i p M (E+A) C E (pairT N x)).eqTrans
    (evaluator_at p N t X Y D sign)
  exact distance_congr old.eqSymm literal.eqSymm (.eqRefl _) (.eqRefl _)
    (point_error_late s p N X Y D sign (tagNumerator t) (sndT t) T E h.andE₁ lo.andE₁ ht.andE₂.andE₁ hE lo.andE₂ up.andE₂ hs hN)

/-- Compare the actual common quadrature at independent cutoff and read clocks. -/
theorem quadrature_error_late (s p M N X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hs : Γ ⊢[PRAAx] le s p) (hN : Γ ⊢[PRAAx] le (E*E*unit s) N) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature GaussianBinetBoseCompact.evaluatorF p M (E+A) C E (fixedData X Y D sign))
      (quadrature evaluatorF p M (E+A) C E (pairT N (fixedData X Y D sign)))
      (C*cost D T E) (E*unit s) := by
  let x := fixedData X Y D sign
  let v := sampleData p M (E+A) C E x
  let w := sampleData p M (E+A) C E (pairT N x)
  let f := sampleBody GaussianBinetBoseCompact.evaluatorF
  let g := sampleBody evaluatorF
  have hE := h.andE₂.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) s
  have terms : Γ ⊢[PRAAx] termsDistance f g M v w (cost D T E) (unit s) := by
    refine .allI (.impI ?_)
    let sh (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
    have h' : Δ ⊢[PRAAx] source (sh X) (sh D) (sh sign) (sh T) (sh A) (sh C) (sh E) := by
      simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
    have hm' : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hM.shift.wk
    have hn' : Δ ⊢[PRAAx] le (sh E*sh E*unit (sh s)) (sh N) := by
      simpa [Δ,sh,Fm.shift,Syn.shift] using hN.shift.wk
    have sl : Δ ⊢[PRAAx] le (sh s) (sh p) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.wk
    have vv : sh v = sampleData (sh p) (sh M) (sh E+sh A) (sh C) (sh E) (fixedData (sh X) (sh Y) (sh D) (sh sign)) := by
      simp only [sh,v,x,Syn.shift,GaussianCompactRiemannName.subst_sampleData,PTm.subst_add,
        GaussianBinetArctangentQuadrature.subst_fixedData]
    have ww : sh w = sampleData (sh p) (sh M) (sh E+sh A) (sh C) (sh E) (pairT (sh N) (fixedData (sh X) (sh Y) (sh D) (sh sign))) := by
      simp only [sh,w,x,Syn.shift,GaussianCompactRiemannName.subst_sampleData,PTm.subst_add,subst_pairT,
        GaussianBinetArctangentQuadrature.subst_fixedData]
    have aa : sh (cost D T E) = cost (sh D) (sh T) (sh E) := subst_cost _ _ _ _
    have dd : sh (unit s) = unit (sh s) := GaussianCoefficientNameBounds.subst_unit _ _
    change Δ ⊢[PRAAx] distanceBounded (inst2 f (var 0) (sh v)) (inst2 g (var 0) (sh w)) (sh (cost D T E)) (sh (unit s))
    rw [vv,ww,aa,dd]
    exact cell_error (Γ := Δ) (sh s) (sh p) (sh M) (sh N) (sh X) (sh Y) (sh D) (sh sign) (sh T) (sh A) (sh C) (sh E) (var 0)
      h' hm' sl hn' Prf.hyp0
  change Γ ⊢[PRAAx] distanceBounded (leftSum f M v C E) (leftSum g M w C E) (C*cost D T E) (E*unit s)
  exact GaussianCompactScalarMajorant.common_mesh_distance f g M v w C E (cost D T E) (unit s)
    hM hE hp terms

theorem quadrature_error (p M N X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hN : Γ ⊢[PRAAx] le (E*E*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature GaussianBinetBoseCompact.evaluatorF p M (E+A) C E (fixedData X Y D sign))
      (quadrature evaluatorF p M (E+A) C E (pairT N (fixedData X Y D sign)))
      (C*cost D T E) (E*unit p) :=
  quadrature_error_late p p M N X Y D sign T A C E h hM (le_refl p) hN

theorem compact_name_error (p N X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E)
    (hN : Γ ⊢[PRAAx] le (E*E*unit (precision p T)) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetBoseCompact.nameF p (GaussianBinetBoseCompact.data X Y D sign T A C E))
      (quadrature evaluatorF (precision p T) (mesh p (GaussianBinetBoseCompact.gain D E T) T)
        (E+A) C E (pairT N (fixedData X Y D sign)))
      (C*cost D T E) (E*unit (precision p T)) := by
  let L := GaussianBinetBoseCompact.gain D E T
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) GaussianBinetBoseCompact.evaluatorF p
    (E+A) C E L T (fixedData X Y D sign)
  exact distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (quadrature_error (precision p T) (mesh p L T) N X Y D sign T A C E h
      (GaussianCompactRiemannName.mesh_positive p L T) hN)

end LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixQuadrature
