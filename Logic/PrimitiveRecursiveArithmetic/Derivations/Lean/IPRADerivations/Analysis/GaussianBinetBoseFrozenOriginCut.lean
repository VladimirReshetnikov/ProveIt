import IPRADerivations.Analysis.GaussianBinetBoseFrozenSuffixCut

/-!
# Restore the lower time strip after the geometric cutoff

The first B cells have time at most `1/E`. At a fixed retained count
I, their contribution is at most `2*K*I/E²`. The reciprocal-square
suffix bound permits choosing I before E and before the larger Bose
prefix count.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenOriginCut

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseFrozenSuffix (geometry fullMesh fullData prefixValue suffixValue full_split subst_geometry)
open GaussianBinetBoseFrozenMatrix (matrix matrix_at cell_at)
open GaussianBinetBoseFrozenTimeRescale (coordinates)
open GaussianBinetSecondDecayPointwise (angle row fullDecay frozenPiNumerator)
open GaussianBinetSecondDecayFrozenTail (mesh)
open GaussianBinetSecondDecaySharedTail (clockFloor)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (grid)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalFiniteSum (sum sum_canonical)
open GaussianRationalFubini (column columnBody column_entry columnSumBody column_sum_at columnFirst)
open GaussianRationalHorner (positive_product qadd qmul qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (constantBody constant_entry constant_sum termsDistance sum_distance weight weight_bound)
open GaussianRationalSyntheticDivision (qsub_congr qadd_sub_cancel)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianStirlingConstant (piDenominator)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

private theorem norm_of_terms (f : PTm 2) (N x P E : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] termsDistance f constantBody N x qzero P E) : Γ ⊢[PRAAx] bounded (sum f N x) (N*P) E := by
  have zeroSum : Γ ⊢[PRAAx] sum constantBody N qzero ≐ qzero :=
    (constant_sum qzero N).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value N)
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hE).iffMp
    (distance_congr (.eqRefl _) zeroSum (.eqRefl _) (.eqRefl _) (sum_distance _ _ _ _ _ _ _ hE h))

private theorem cell_bound (i j q k T E B C X Y D sign K : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign)
    (hi : Γ ⊢[PRAAx] le i B) (hK : Γ ⊢[PRAAx] le D (K*X)) : Γ ⊢[PRAAx]
    bounded (inst3 matrix i j (fullData q k T E B X Y D sign)) (two*K) E := by
  let M := fullMesh T E B
  let H := frozenPiNumerator (succ j) k
  let J := piDenominator k
  let a := T*i
  let v := angle q X Y D sign a M
  let w := fullDecay q a M H J
  let t := grid i M (one+zero) T one
  have hE := h.andE₁.andE₂
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ (positive_product _ _ h.andE₁.andE₁ hE) h.andE₂.andE₁.andE₁
  have hJ := GaussianBinetKernelPi.denominator_positive (Γ := Γ) k
  have raw := GaussianBinetArctangentQuadratureBound.name_bound q X Y D sign a M hz hM
  have boundAngle : Γ ⊢[PRAAx] bounded v K E :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hM hz.andE₁.andE₁) hE
      (by dsimp only [a,M,fullMesh]; ipra_le 𝔞(T)*𝔞(D)*𝔞(E)*sl hi + 𝔞(T)*𝔞(E)*𝔞(B)*sl hK) raw
  have hq := unit_positive (Γ := Γ) q
  have boundDecay : Γ ⊢[PRAAx] bounded w two one :=
    bounded_radius_mono _ _ _ _ _ hq (le_refl one) (by ipra_le sl hq)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound q (two*(a*H)) (M*J) (positive_product _ _ hM hJ))
  have prod := bounded_product v w K E two one hE (le_refl one) boundAngle boundDecay
  have loc := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) i M zero T one
  have eq := coordinates q X Y D sign (tagNumerator t) a (sndT t) M H J
    (loc.andE₁.eqTrans (by dsimp only [a]; ipra_ring)) (loc.andE₂.eqTrans (one_mul _))
  rw [matrix_at]
  exact bound_congr ((cell_at i j q k M X Y D sign zero T one).eqTrans eq).eqSymm
    (mul_comm _ _) (mul_comm E one |>.eqTrans (one_mul E)) prod

private theorem column_bound (j q k T E B C X Y D sign K : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign) (hK : Γ ⊢[PRAAx] le D (K*X)) : Γ ⊢[PRAAx]
    bounded (column matrix j B (fullData q k T E B X Y D sign)) (B*(two*K)) E := by
  let x := fullData q k T E B X Y D sign
  have rows : Γ ⊢[PRAAx] termsDistance (columnBody matrix) constantBody B (pairT j x) qzero (two*K) E := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let i : PTm (n+1) := var 0
    let Δ := lt i (s B)::Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] geometry (s T) (s E) (s B) (s C) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_geometry] using h.shift.wk
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    let d := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    have raw := cell_bound i (s j) (s q) (s k) (s T) (s E) (s B) (s C) (s X) (s Y) (s D) (s sign) (s K)
      hs zs (le_of_lt Prf.hyp0) ks
    have carried := bound_congr (column_entry matrix i (s j) d).eqSymm (.eqRefl _) (.eqRefl _) raw
    have eq := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hs.andE₁.andE₂).iffMpr carried
    simpa only [termsDistance,s,i,Δ,x,d,Syn.shift,subst_pairT,GaussianBinetBoseFrozenSuffix.subst_fullData,
      GaussianRationalHorner.subst_qzero,constant_entry,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ] using eq
  exact norm_of_terms _ _ _ _ _ h.andE₁.andE₂ rows

theorem prefix_bound (q k I T E B C K X Y D sign : PTm n) (h : Γ ⊢[PRAAx] geometry T E B C)
    (hz : Γ ⊢[PRAAx] source X D sign) (hK : Γ ⊢[PRAAx] le D (K*X)) : Γ ⊢[PRAAx]
    bounded (prefixValue q k I T E B X Y D sign) (I*(two*K)) (E*E) := by
  let f := columnSumBody matrix
  let x := fullData q k T E B X Y D sign
  let w := weight one E B
  have cols : Γ ⊢[PRAAx] termsDistance f constantBody I (pairT B x) qzero (B*(two*K)) E := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let j : PTm (n+1) := var 0
    let Δ := lt j (s I)::Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] geometry (s T) (s E) (s B) (s C) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_geometry] using h.shift.wk
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    let d := fullData (s q) (s k) (s T) (s E) (s B) (s X) (s Y) (s D) (s sign)
    have raw := column_bound j (s q) (s k) (s T) (s E) (s B) (s C) (s X) (s Y) (s D) (s sign) (s K) hs zs ks
    have carried := bound_congr (column_sum_at matrix j (s B) d).eqSymm (.eqRefl _) (.eqRefl _) raw
    have eq := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hs.andE₁.andE₂).iffMpr carried
    simpa only [termsDistance,f,s,j,Δ,x,d,Syn.shift,subst_pairT,GaussianBinetBoseFrozenSuffix.subst_fullData,
      GaussianRationalHorner.subst_qzero,constant_entry,PTm.subst_mul,two,one,ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ] using eq
  have he := h.andE₁.andE₂
  have hb := h.andE₂.andE₁.andE₁
  have hd := positive_product _ _ he hb
  have raw := bounded_product w _ one (E*B) (I*(B*(two*K))) E hd he (weight_bound one E B he hb)
    (norm_of_terms _ _ _ _ _ he cols)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd he) (positive_product _ _ he he)
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem prefix_gap (q k I T E B C K X Y D sign : PTm n) (h : Γ ⊢[PRAAx] geometry T E B C)
    (hz : Γ ⊢[PRAAx] source X D sign) (hK : Γ ⊢[PRAAx] le D (K*X)) : Γ ⊢[PRAAx]
    distanceBounded (GaussianBinetBoseFrozenMatrix.value q k I (fullMesh T E B) X Y D sign zero T one)
      (suffixValue q k I T E B C X Y D sign) (I*(two*K)) (E*E) := by
  let a := prefixValue q k I T E B X Y D sign
  let b := suffixValue q k I T E B C X Y D sign
  have e := (full_split q k I T E B C X Y D sign h).eqTrans (GaussianReciprocalHorner.qadd_commutative a b)
  have can : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a := GaussianRationalHorner.qmul_canonical _ _
  exact bound_congr ((qsub_congr e (.eqRefl b)).eqTrans (qadd_sub_cancel b a can)).eqSymm (.eqRefl _) (.eqRefl _)
    (prefix_bound q k I T E B C K X Y D sign h hz hK)

theorem cut_and_restore (q k I r T E B C K X Y D sign : PTm n)
    (h : Γ ⊢[PRAAx] geometry T E B C) (hz : Γ ⊢[PRAAx] source X D sign)
    (hI : Γ ⊢[PRAAx] le one I) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hm : Γ ⊢[PRAAx] le (mesh T (succ (I+r)) k) (fullMesh T E B))
    (hq : Γ ⊢[PRAAx] le (clockFloor (fullMesh T E B) T (succ (I+r)) k) (unit q)) : Γ ⊢[PRAAx]
    distanceBounded (suffixValue q k (I+r) T E B C X Y D sign)
      (GaussianBinetBoseFrozenMatrix.value q k I (fullMesh T E B) X Y D sign zero T one)
      ((num 11*K)*(E*E)+(I*(two*K))*I) (I*(E*E)) := by
  have he := positive_product _ _ h.andE₁.andE₂ h.andE₁.andE₂
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hI he
    (GaussianBinetBoseFrozenSuffixCut.tail_gap q k I r T E B C K X Y D sign h hz hI hK hm hq)
    (distance_symmetric _ _ _ _ he (prefix_gap q k I T E B C K X Y D sign h hz hK))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseFrozenOriginCut
