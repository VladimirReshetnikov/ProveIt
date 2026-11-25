import IPRADerivations.Analysis.GaussianBinetLaplaceScalarMajorant
import IPRADerivations.Analysis.GaussianBinetLaplaceStripCutoff
import IPRADerivations.Analysis.GaussianEulerDecayEndpointBound

/-!
# Domination on the actual uniform Binet strip

The scalar majorant uses the original exponential evaluated at the
rescaled real time `(X/D)t`. An exact change of weight identifies its
comparison sum with `D/(12X)` times the original real decay quadrature.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripDomination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceScalarMajorant (scalar subst_scalar twelfth)
open GaussianBinetLaplaceStrip (Kernel evaluatorF fixedData evaluator_at source subst_source tagNumerator tag_inside)
open GaussianBinetLaplaceStripCutoff (grid_tag)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (grid grid_inside sampleBody sampleData sample_body_at quadrature field0 field1 field2 field3 field4
    field0_at field1_at field2_at field3_at field4_at subst_sampleData)
open GaussianCompactScalarMajorant (scalarLeft weighted_majorant scalar_left_embedding common_mesh_distance)
open GaussianEulerDecayMesh (observation)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (leftSum weight termsDistance)
open GaussianRationalSumMajorant (majorized majorized_congr termsMajorized majorant_bound)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalGaussianRealPart (embedBody embed_congr)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "twelve" => num 12
local notation "CofinalF" => evaluatorF Kernel.cofinal
local notation "DecayF" => GaussianEulerDecayQuadrature.evaluatorF

def scalarCell (i x : PTm n) : PTm n :=
  scalar (field0 x) (field2 x*field1 x+field3 x*i) (field4 x*field1 x)
def scalarBody : PTm 2 := scalarCell (var 0) (var 1)

@[simp] theorem subst_scalarCell {m : ℕ} (σ : Fin n → PTm m) (i x : PTm n) :
    Syn.subst σ (scalarCell i x) = scalarCell (Syn.subst σ i) (Syn.subst σ x) := by simp [scalarCell]

theorem scalar_congr {p q a b c d : PTm n} (hp : Γ ⊢[PRAAx] p ≐ q)
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) : Γ ⊢[PRAAx] scalar p a b ≐ scalar q c d := by
  simpa only [subst_scalar,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (scalar (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,a,b]) (σ' := ![q,c,d]) (fun i => by fin_cases i; exact hp; exact ha; exact hb)

private theorem scalar_cell_at (i p M a C E : PTm n) : Γ ⊢[PRAAx]
    inst2 scalarBody i (sampleData p M a C E zero) ≐ scalar p (a*M+C*i) (E*M) := by
  simp only [scalarBody,inst2,subst_scalarCell,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold scalarCell
  exact scalar_congr (field0_at _ _ _ _ _ _)
    (congrAdd (congrMul (field2_at _ _ _ _ _ _) (field1_at _ _ _ _ _ _)) (congrMul (field3_at _ _ _ _ _ _) (.eqRefl _)))
    (congrMul (field4_at _ _ _ _ _ _) (field1_at _ _ _ _ _ _))

private theorem strip_cell_majorized (i p M X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hi : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] majorized
      (inst2 (sampleBody CofinalF) i (sampleData p M (E+A) C E (fixedData X Y D sign R T N)))
      (inst2 scalarBody i (sampleData p M (X*A) (X*C) (D*E) zero)) := by
  let x := fixedData X Y D sign R T N
  let t := grid i M (E+A) C E
  let a := tagNumerator t
  let b := sndT t
  have hE := h.andE₂.andE₁
  have ht := grid_inside i M (E+A) C E (le_trans hE (le_add_right E A)) hE hM (le_of_lt hi)
  have hp := tag_inside t A C E T hE h.andE₂.andE₂ ht
  have valid : Γ ⊢[PRAAx] GaussianBinetLaplaceIntegrand.input X Y D sign R T a b :=
    .andI h.andE₁ (.andI ht.andE₂.andE₁ hp.andE₂)
  have left := (sample_body_at (Γ := Γ) CofinalF i p M (E+A) C E x).eqTrans
    (evaluator_at .cofinal p t X Y D sign R T N)
  have tag := grid_tag (Γ := Γ) i M A C E
  have numerator := (congrMul (.eqRefl X) tag.andE₁).eqTrans (by ipra_ring : Γ ⊢[PRAAx] X*(A*M+C*i) ≐ (X*A)*M+(X*C)*i)
  have denominator := (congrMul (.eqRefl D) tag.andE₂).eqTrans (by ipra_ring : Γ ⊢[PRAAx] D*(E*M) ≐ (D*E)*M)
  have right := (scalar_cell_at (Γ := Γ) i p M (X*A) (X*C) (D*E)).eqTrans
    (scalar_congr (.eqRefl p) numerator.eqSymm denominator.eqSymm)
  exact majorized_congr left.eqSymm right.eqSymm
    (GaussianBinetLaplaceScalarMajorant.cofinal_majorized p X Y D sign R T a b valid)

private theorem strip_rows_majorized (p M X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] termsMajorized (sampleBody CofinalF) scalarBody M
      (sampleData p M (E+A) C E (fixedData X Y D sign R T N))
      (sampleData p M (X*A) (X*C) (D*E) zero) := by
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h.shift
  have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,Fm.shift,Syn.shift,s,one] using hM.shift
  simpa only [termsMajorized,Syn.shift,s,Δ,subst_sampleData,subst_pairT,PTm.subst_add,PTm.subst_mul,
    ConciseIPRA.PTm.subst_zero] using
    strip_cell_majorized (var 0) (s p) (s M) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s C)
      (s E) hs.wk ms.wk Prf.hyp0

private theorem scaled_cell_error (i p M a C E : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] distanceBounded
      (inst2 (embedBody scalarBody) i (sampleData p M a C E zero))
      (inst2 (multiplyBody (sampleBody DecayF)) i (pairT twelfth (sampleData p M a C E zero))) (num 10) (unit p) := by
  let data := sampleData p M a C E zero
  have l : Γ ⊢[PRAAx] inst2 (embedBody scalarBody) i data ≐ embed (scalar p (a*M+C*i) (E*M)) := by
    simpa only [data, inst2, embedBody, RationalGaussianEmbedding.subst_embed] using
      embed_congr (scalar_cell_at (Γ := Γ) i p M a C E)
  have r := (multiply_body_at (Γ := Γ) (sampleBody DecayF) twelfth i data).eqTrans
    (qmul_congr (.eqRefl _) (GaussianEulerDecayQuadrature.cell_at i p M a C E zero))
  exact distance_congr l.eqSymm r.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianBinetLaplaceScalarMajorant.scalar_observation_distance p (a*M+C*i) (E*M) (positive_product _ _ hE hM))

private theorem scaled_rows_error (p M a C E : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] termsDistance (embedBody scalarBody)
      (multiplyBody (sampleBody DecayF)) M (sampleData p M a C E zero)
      (pairT twelfth (sampleData p M a C E zero)) (num 10) (unit p) := by
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (s M) := by simpa [Fm.shift,Syn.shift,s,one] using hM.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (s E) := by simpa [Fm.shift,Syn.shift,s,one] using hE.shift
  simpa only [termsDistance,Syn.shift,s,subst_sampleData,subst_pairT,ConciseIPRA.PTm.subst_zero,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_num,twelfth,GaussianPositiveRationalLogarithm.subst_fraction,
    one,ConciseIPRA.PTm.subst_succ] using
    scaled_cell_error (var 0) (s p) (s M) (s a) (s C) (s E) ms.wk es.wk

def panelScale (X D : PTm n) : PTm n := GaussianPositiveRationalLogarithm.fraction D (twelve*X)

private theorem multiply_fraction (A B C E : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    qmul (GaussianPositiveRationalLogarithm.fraction A B) (GaussianPositiveRationalLogarithm.fraction C E) ≐
      GaussianPositiveRationalLogarithm.fraction (A*C) (B*E) := by
  let f := GaussianEuclideanDistanceName.fraction A B
  let g := GaussianEuclideanDistanceName.fraction C E
  exact (qmul_congr (GaussianEulerDecayOrder.fraction_embedding A B hB).eqSymm
    (GaussianEulerDecayOrder.fraction_embedding C E hE).eqSymm).eqTrans
    ((RationalGaussianEmbedding.embed_multiply f g).eqSymm.eqTrans
      ((embed_congr (RationalNonnegativePowers.fraction_multiply A B C E hB hE)).eqTrans
        (GaussianEulerDecayOrder.fraction_embedding (A*C) (B*E) (positive_product _ _ hB hE))))

private theorem weight_rescale (M X D C E : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hX : Γ ⊢[PRAAx] le one X) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] qmul (weight C E M) twelfth ≐ qmul (panelScale X D) (weight (X*C) (D*E) M) := by
  let f : PTm n → PTm n → PTm n := GaussianPositiveRationalLogarithm.fraction
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hB := positive_product _ _ hE hM
  have h12X := positive_product _ _ h12 hX
  have hDEM := positive_product _ _ (positive_product _ _ hD hE) hM
  have hxD := positive_product _ _ hX hD
  have hDen := positive_product _ _ hB h12
  have left := multiply_fraction C (E*M) one twelve hB h12
  have right := multiply_fraction D (twelve*X) (X*C) ((D*E)*M) h12X hDEM
  have rescale := GaussianGammaEncodingRescaling.fraction_rescale
    (ComplexLogarithmRemainder.scale (C*one) ComplexLogarithmRemainder.oneCode) ((E*M)*twelve) (X*D) hDen hxD
  have target : Γ ⊢[PRAAx] f (D*(X*C)) ((twelve*X)*((D*E)*M)) ≐
      f ((X*D)*(C*one)) ((X*D)*((E*M)*twelve)) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.scale ((X*D)*(C*one)) ComplexLogarithmRemainder.oneCode)
      (ComplexLogarithmRemainder.scale (X*D) (ComplexLogarithmRemainder.scale (C*one) ComplexLogarithmRemainder.oneCode)) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring
  have merge := GaussianGammaFiniteValueProperness.fraction_equal _ _ _ (positive_product _ _ hxD hDen) native
  exact left.eqTrans (right.eqTrans (target.eqTrans (merge.eqTrans rescale))).eqSymm

private theorem scaled_left_sum (p M X D A C E : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hX : Γ ⊢[PRAAx] le one X) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] leftSum (multiplyBody (sampleBody DecayF)) M
      (pairT twelfth (sampleData p M (X*A) (X*C) (D*E) zero)) C E ≐
      qmul (panelScale X D) (quadrature DecayF p M (X*A) (X*C) (D*E) zero) := by
  let f := sampleBody DecayF
  let w := weight C E M
  let v := weight (X*C) (D*E) M
  let z := GaussianRationalFiniteSum.sum f M (sampleData p M (X*A) (X*C) (D*E) zero)
  exact (qmul_congr (.eqRefl w) (sum_multiply f twelfth M _)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative w twelfth z).eqSymm.eqTrans
      ((qmul_congr (weight_rescale M X D C E hM hX hD hE) (.eqRefl z)).eqTrans
        (GaussianReciprocalHorner.qmul_associative (panelScale X D) v z)))

theorem scalar_strip_distance (p M X D A C E : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hX : Γ ⊢[PRAAx] le one X) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded
      (embed (scalarLeft scalarBody M (sampleData p M (X*A) (X*C) (D*E) zero) C E))
      (qmul (panelScale X D) (quadrature DecayF p M (X*A) (X*C) (D*E) zero)) (C*num 10) (E*unit p) := by
  let x := sampleData p M (X*A) (X*C) (D*E) zero
  have raw := common_mesh_distance (embedBody scalarBody) (multiplyBody (sampleBody DecayF)) M x
    (pairT twelfth x) C E (num 10) (unit p) hM hE (unit_positive p)
    (scaled_rows_error p M (X*A) (X*C) (D*E) hM (positive_product _ _ hD hE))
  exact distance_congr (scalar_left_embedding scalarBody M x C E hE hM).eqSymm
    (scaled_left_sum p M X D A C E hM hX hD hE) (.eqRefl _) (.eqRefl _) raw

/-- A checked radius of the rescaled original decay quadrature gives a
radius for the actual Binet quadrature, with only the explicit grid
observation allowance (10C/(E2^p)). -/
theorem quadrature_bound (p M X Y D sign R T N A C E P Q : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hQ : Γ ⊢[PRAAx] le one Q)
    (hb : Γ ⊢[PRAAx] bounded (quadrature DecayF p M (X*A) (X*C) (D*E) zero) P Q) :
    Γ ⊢[PRAAx] bounded (quadrature CofinalF p M (E+A) C E (fixedData X Y D sign R T N))
      ((C*num 10)*((twelve*X)*Q)+(D*P)*(E*unit p)) ((E*unit p)*((twelve*X)*Q)) := by
  let x := sampleData p M (X*A) (X*C) (D*E) zero
  have hE := h.andE₂.andE₁
  have hX := h.andE₁.andE₁.andE₁.andE₁
  have hD := h.andE₁.andE₁.andE₂
  have d := positive_product _ _ hE (unit_positive p)
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hSc := positive_product _ _ h12 hX
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hSc hQ
    (GaussianBinetLaplaceScalarMajorant.fraction_norm D (twelve*X) hSc) hb
  have near := scalar_strip_distance p M X D A C E hM hX hD hE
  have bd := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ d (positive_product _ _ hSc hQ) near product
  exact majorant_bound _ _ _ _ (positive_product _ _ d (positive_product _ _ hSc hQ))
    (weighted_majorant _ _ M _ x C E hM hE (strip_rows_majorized p M X Y D sign R T N A C E h hM)) bd

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripDomination
