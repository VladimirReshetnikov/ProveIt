import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenTimeRescale
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenOrigin

/-!
# Align the positive Bose strip with a suffix of the zero-origin mesh

The width is `(1+C)/E = T`. The complete mesh has `(T*E)*B` cells.
Its first `B` cells end at `1/E`; the remaining `C*B` cells have the
same physical tags and mesh weights as the positive strip.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenSuffix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseFrozenMatrix (matrix matrix_at cell_at subst_frozenPiNumerator subst_piDenominator)
open GaussianBinetBosePrefixTranspose (data)
open GaussianBinetBoseFrozenTimeRescale (coordinates rescale_error)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianBinetSecondDecayPointwise (row frozenPiNumerator)
open GaussianCompactRiemannName (grid fraction_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (sum termsEqual sum_index_congr)
open GaussianRationalFubini (column columnBody column_entry columnSumBody column_sum_at columnFirst)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianStirlingConstant (piDenominator)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def geometry (T E B C : PTm n) : Fm PTm n :=
  (le one T ⋏ le one E) ⋏ ((le one B ⋏ le one C) ⋏ (one+C ≐ T*E))

def fullMesh (T E B : PTm n) : PTm n := (T*E)*B

def fullData (q k T E B X Y D sign : PTm n) : PTm n :=
  data q (fullMesh T E B) k X Y D sign zero T one

def columnSegment (j L S d : PTm n) : PTm n := sum (offB (columnBody matrix)) L (pairT S (pairT j d))
def segmentData (L S d : PTm n) : PTm n := pairT L (pairT S d)
def segmentBody : PTm 2 := columnSegment (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))

def suffixValue (q k N T E B C X Y D sign : PTm n) : PTm n :=
  qmul (weight one E B) (sum segmentBody N (segmentData (C*B) B (fullData q k T E B X Y D sign)))

def prefixValue (q k N T E B X Y D sign : PTm n) : PTm n :=
  qmul (weight one E B) (columnFirst matrix B N (fullData q k T E B X Y D sign))

@[simp] theorem subst_geometry {m : ℕ} (σ : Fin n → PTm m) (T E B C : PTm n) :
    (geometry T E B C).subst σ = geometry (Syn.subst σ T) (Syn.subst σ E) (Syn.subst σ B) (Syn.subst σ C) := by
  simp [geometry,one]
@[simp] theorem subst_fullMesh {m : ℕ} (σ : Fin n → PTm m) (T E B : PTm n) :
    Syn.subst σ (fullMesh T E B) = fullMesh (Syn.subst σ T) (Syn.subst σ E) (Syn.subst σ B) := by simp [fullMesh]
@[simp] theorem subst_fullData {m : ℕ} (σ : Fin n → PTm m) (q k T E B X Y D sign : PTm n) :
    Syn.subst σ (fullData q k T E B X Y D sign) = fullData (Syn.subst σ q) (Syn.subst σ k) (Syn.subst σ T)
      (Syn.subst σ E) (Syn.subst σ B) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [fullData,one]
@[simp] theorem subst_segmentData {m : ℕ} (σ : Fin n → PTm m) (L S d : PTm n) :
    Syn.subst σ (segmentData L S d) = segmentData (Syn.subst σ L) (Syn.subst σ S) (Syn.subst σ d) := by simp [segmentData]
@[simp] theorem subst_columnSegment {m : ℕ} (σ : Fin n → PTm m) (j L S d : PTm n) :
    Syn.subst σ (columnSegment j L S d) = columnSegment (Syn.subst σ j) (Syn.subst σ L) (Syn.subst σ S) (Syn.subst σ d) :=
  by simp [columnSegment]

theorem strip_source (T E B C X D sign : PTm n) (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign) :
    Γ ⊢[PRAAx] GaussianBinetBoseCompact.source X D sign T one C E :=
  .andI hz (.andI (le_refl one) (.andI h.andE₁.andE₂ (le_congr (.eqRefl _) (h.andE₂.andE₂.eqTrans (mul_comm T E)) (le_refl _))))

theorem mesh_split (T E B C : PTm n) (h : Γ ⊢[PRAAx] geometry T E B C) : Γ ⊢[PRAAx] fullMesh T E B ≐ B+C*B :=
  (congrMul h.andE₂.andE₂.eqSymm (.eqRefl B)).eqTrans (by ipra_ring)

theorem full_weight (T E B : PTm n) (hT : Γ ⊢[PRAAx] le one T) (hE : Γ ⊢[PRAAx] le one E)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] weight T one (fullMesh T E B) ≐ weight one E B :=
  (fraction_congr _ _ _ _ (by ipra_ring) (by unfold fullMesh; ipra_ring)).eqTrans
    (GaussianCompactRiemannSplit.fraction_cancel T one (E*B) hT (positive_product _ _ hE hB))

theorem segment_at (j L S d : PTm n) : Γ ⊢[PRAAx] inst2 segmentBody j (segmentData L S d) ≐ columnSegment j L S d := by
  let x := segmentData L S d
  have start : Γ ⊢[PRAAx] sndT x ≐ pairT S d := snd_pair _ _
  simpa only [segmentBody,inst2,subst_columnSegment,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (columnSegment (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![j,fstT x,fstT (sndT x),sndT (sndT x)]) (σ' := ![j,L,S,d]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact fst_pair _ _
        exact (congrFst start).eqTrans (fst_pair _ _)
        exact (congrSnd start).eqTrans (snd_pair _ _))

theorem cell_error (i j q k T E B C X Y D sign : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign) (hi : Γ ⊢[PRAAx] lt i (C*B)) :
    Γ ⊢[PRAAx] distanceBounded (inst3 matrix i j (data q (C*B) k X Y D sign one C E))
      (inst3 matrix (B+i) j (fullData q k T E B X Y D sign)) (num 4) (unit q) := by
  let a := B+i
  let b := E*B
  let H := frozenPiNumerator (succ j) k
  let J := piDenominator k
  let t := grid i (C*B) (E+one) C E
  let u := grid (B+i) (fullMesh T E B) (one+zero) T one
  have ht := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) i (C*B) one C E
  have hu := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) (B+i) (fullMesh T E B) zero T one
  have e₁ := coordinates q X Y D sign (tagNumerator t) (C*a) (sndT t) (C*b) H J
    (ht.andE₁.eqTrans (by dsimp only [a]; ipra_ring)) (ht.andE₂.eqTrans (by dsimp only [b]; ipra_ring))
  have e₂ := coordinates q X Y D sign (tagNumerator u) (T*a) (sndT u) (T*b) H J
    (hu.andE₁.eqTrans (by dsimp only [a]; ipra_ring)) (hu.andE₂.eqTrans (by dsimp only [b,fullMesh]; ipra_ring))
  have within : Γ ⊢[PRAAx] le a (T*b) := by
    have cmp := add_le_add_right B (le_of_lt hi)
    exact le_congr (add_comm i B) ((add_comm (C*B) B).eqTrans
      ((mesh_split T E B C h).eqSymm.eqTrans (by dsimp only [b,fullMesh]; ipra_ring))) cmp
  have hbase := positive_product _ _ h.andE₁.andE₂ h.andE₂.andE₁.andE₁
  rw [matrix_at, matrix_at]
  exact distance_congr ((cell_at i j q k (C*B) X Y D sign one C E).eqTrans e₁).eqSymm
    ((cell_at (B+i) j q k (fullMesh T E B) X Y D sign zero T one).eqTrans e₂).eqSymm (.eqRefl _) (.eqRefl _)
    (rescale_error q X Y D sign a b C T H J T hz hbase h.andE₂.andE₁.andE₂ h.andE₁.andE₁
      (GaussianBinetKernelPi.denominator_positive k) within)

theorem column_error (j q k T E B C X Y D sign : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign) :
    Γ ⊢[PRAAx] distanceBounded (column matrix j (C*B) (data q (C*B) k X Y D sign one C E))
      (columnSegment j (C*B) B (fullData q k T E B X Y D sign)) ((C*B)*num 4) (unit q) := by
  let x := data q (C*B) k X Y D sign one C E
  let y := fullData q k T E B X Y D sign
  have rows : Γ ⊢[PRAAx] termsDistance (columnBody matrix) (offB (columnBody matrix)) (C*B)
      (pairT j x) (pairT B (pairT j y)) (num 4) (unit q) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] geometry (s T) (s E) (s B) (s C) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_geometry] using h.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift
    let d := data (s q) (s C*s B) (s k) (s X) (s Y) (s D) (s sign) one (s C) (s E)
    let e := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    have cmp := cell_error (var 0) (s j) (s q) (s k) (s T) (s E) (s B) (s C) (s X) (s Y) (s D) (s sign) hs.wk zs.wk Prf.hyp0
    have first := column_entry (Γ := lt (var 0) (s C*s B)::Δ) matrix (var 0) (s j) d
    have second := (GaussianRationalFiniteProduct.offset_at (Γ := lt (var 0) (s C*s B)::Δ) (columnBody matrix) (s B) (var 0) (pairT (s j) e)).eqTrans
      (column_entry matrix (s B+var 0) (s j) e)
    simpa only [termsDistance,x,y,d,e,Δ,s,Syn.shift,subst_pairT,GaussianBinetBosePrefixTranspose.subst_data,subst_fullData,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_num,one,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ] using distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _) cmp
  exact sum_distance _ _ _ _ _ _ _ (unit_positive q) rows

theorem suffix_error (q k N T E B C X Y D sign : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign) :
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetBoseFrozenMatrix.value q k N (C*B) X Y D sign one C E)
      (suffixValue q k N T E B C X Y D sign) (C*(N*num 4)) (E*unit q) := by
  let x := data q (C*B) k X Y D sign one C E
  let y := fullData q k T E B X Y D sign
  let u := columnFirst matrix (C*B) N x
  let v := sum segmentBody N (segmentData (C*B) B y)
  let w := weight one E B
  have cols : Γ ⊢[PRAAx] termsDistance (columnSumBody matrix) segmentBody N (pairT (C*B) x) (segmentData (C*B) B y)
      ((C*B)*num 4) (unit q) := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] geometry (s T) (s E) (s B) (s C) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_geometry] using h.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift
    let d := data (s q) (s C*s B) (s k) (s X) (s Y) (s D) (s sign) one (s C) (s E)
    let e := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    have cmp := column_error (Γ := lt (var 0) (s N)::Δ) (var 0) (s q) (s k) (s T) (s E) (s B) (s C) (s X) (s Y) (s D) (s sign) hs.wk zs.wk
    have first := column_sum_at (Γ := lt (var 0) (s N)::Δ) matrix (var 0) (s C*s B) d
    have second := segment_at (Γ := lt (var 0) (s N)::Δ) (var 0) (s C*s B) (s B) e
    simpa only [termsDistance,x,y,d,e,Δ,s,Syn.shift,subst_pairT,GaussianBinetBosePrefixTranspose.subst_data,subst_fullData,
      subst_segmentData,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_num,one,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ] using distance_congr first.eqSymm second.eqSymm (.eqRefl _) (.eqRefl _) cmp
  have hE := h.andE₁.andE₂
  have hB := h.andE₂.andE₁.andE₁
  have hC := h.andE₂.andE₁.andE₂
  have hu := unit_positive (Γ := Γ) q
  have hb := positive_product _ _ hE hB
  have err := sum_distance _ _ _ _ _ _ _ hu cols
  have prod := GaussianRationalReciprocal.bounded_product w _ one (E*B) (N*((C*B)*num 4)) (unit q) hb hu
    (weight_bound one E B hE hB) err
  have near := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference w u v).eqSymm (.eqRefl _) (.eqRefl _) prod
  exact distance_congr (qmul_congr (GaussianCompactRiemannSplit.weight_shared C E B hC hE hB).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hb hu) (positive_product _ _ hE hu)
      (le_of_eq_add (d := zero) (by ipra_ring)) near)

/-- Split the original full-grid sum at the first `B` genuine cells. -/
theorem full_split (q k N T E B C X Y D sign : PTm n) (h : Γ ⊢[PRAAx] geometry T E B C) : Γ ⊢[PRAAx]
    GaussianBinetBoseFrozenMatrix.value q k N (fullMesh T E B) X Y D sign zero T one ≐
      qadd (prefixValue q k N T E B X Y D sign) (suffixValue q k N T E B C X Y D sign) := by
  let F := columnSumBody matrix
  let x := fullData q k T E B X Y D sign
  let M := fullMesh T E B
  let L := C*B
  let y := segmentData L B x
  let w := weight one E B
  let g := GaussianInverseBinomialRows.pairAddBody F segmentBody
  have cols : Γ ⊢[PRAAx] termsEqual F g N (pairT M x) (pairT (pairT B x) y) := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := Γ.map Fm.shift
    let j : PTm (n+1) := var 0
    let d := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    let m := fullMesh (s T) (s E) (s B)
    let l := s C*s B
    let z := segmentData l (s B) d
    have hs : Δ ⊢[PRAAx] geometry (s T) (s E) (s B) (s C) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_geometry] using h.shift
    have count := mesh_split (Γ := lt j (s N)::Δ) (s T) (s E) (s B) (s C) hs.wk
    have split := (sum_index_congr (columnBody matrix) count (.eqRefl (pairT j d))).eqTrans
      (GaussianRationalMatrixFiniteSums.sum_split (columnBody matrix) (s B) l (pairT j d))
    have read := (column_sum_at (Γ := lt j (s N)::Δ) matrix j m d).eqTrans split
    have collected := (GaussianInverseBinomialRows.pair_add_at (Γ := lt j (s N)::Δ) F segmentBody j (pairT (s B) d) z).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (column_sum_at matrix j (s B) d) (segment_at j l (s B) d))
    simpa only [termsEqual,F,g,x,y,M,L,s,Δ,j,d,m,l,z,Syn.shift,subst_pairT,subst_fullMesh,subst_fullData,
      subst_segmentData,PTm.subst_mul] using read.eqTrans collected.eqSymm
  have sums := (GaussianRationalFiniteSum.sum_congr_bounded F g N (pairT M x) (pairT (pairT B x) y) cols).eqTrans
    (GaussianInverseBinomialRows.pair_sum_add F segmentBody N (pairT B x) y)
  exact (qmul_congr (full_weight T E B h.andE₁.andE₁ h.andE₁.andE₂ h.andE₂.andE₁.andE₁) sums).eqTrans
    (GaussianRationalCoefficientScaling.qmul_add w _ _)


end LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenSuffix
