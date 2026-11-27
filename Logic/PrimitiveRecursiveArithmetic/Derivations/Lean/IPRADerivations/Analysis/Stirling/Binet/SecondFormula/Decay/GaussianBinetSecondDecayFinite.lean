import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayGrid
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayQuadrature

/-!
# A summable bound on each actual finite second Binet row

The original angular row is dominated by a positive envelope on the
same grid. The envelope is a scaled half-decay quadrature plus its
explicit dyadic allowance. This proves a uniform inverse-square bound
in the positive summation index at every integer horizon.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayFinite

open_ipra
open GaussianBinetSecondDecayEnvelope (envelope envelope_distance)
open GaussianBinetSecondDecayGrid (value rowData rowBody envelopeData envelopeBody row_at envelope_at)
open GaussianBinetSecondDecayPointwise (rowEnvelope halfDecay row_majorized)
open GaussianBinetSecondDecayQuadrature (physicalValue physical_at physical_bound)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianCompactScalarMajorant (scalarLeft scalar_left_embedding weighted_majorant common_mesh_distance)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayQuadrature (evaluatorF)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (sum multiplyBody multiply_body_at sum_multiply)
open GaussianRationalHorner (positive_product qmul qadd qzero qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (leftSum termsDistance weight)
open GaussianRationalSumMajorant (majorized_congr termsMajorized majorant_bound)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianReciprocalHorner (qmul_associative qadd_zero_right)
open GaussianRightHalfPlaneLogarithm (source)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "RF" => GaussianEuclideanDistanceName.fraction

def allowance (K T : PTm n) : PTm n := K*(num 8+num 10*T)

ipra_subst allowance

theorem row_envelope_distance (p m K T a b H J : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hbJ : Γ ⊢[PRAAx] le one (b*J)) :
    Γ ⊢[PRAAx] distanceBounded (embed (rowEnvelope p m K T a b H J))
      (qmul (fraction (two*K) m) (halfDecay p a b H J)) (allowance K T) (unit p) := by
  let c := fraction (two*K) m
  let v := envelope p (a*H) (b*J)
  let w := halfDecay p a b H J
  let U := unit p
  let delta := fraction (num 10*K*T) U
  have hp := unit_positive (Γ := Γ) p
  have cBound : Γ ⊢[PRAAx] bounded c (two*K) one :=
    GaussianEulerExponentCompactBounds.fraction_bound _ _ _ hm
      (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (two*K) hm))
  have near := GaussianApproximateInverseDistance.multiply_distance c (embed v) w (two*K) (num 4) U hp cBound
    (envelope_distance p (a*H) (b*J) hbJ)
  have small : Γ ⊢[PRAAx] distanceBounded delta qzero (num 10*K*T) U :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hp).iffMpr
      (GaussianBinetLaplaceScalarMajorant.fraction_norm _ _ hp)
  have exactModel : Γ ⊢[PRAAx] embed (rowEnvelope p m K T a b H J) ≐ qadd (qmul c (embed v)) delta :=
    (RationalGaussianEmbedding.embed_add _ _).eqTrans
      (qadd_congr
        ((RationalGaussianEmbedding.embed_multiply _ _).eqTrans
          (qmul_congr (GaussianEulerDecayOrder.fraction_embedding (two*K) m hm) (.eqRefl _)))
        (GaussianEulerDecayOrder.fraction_embedding (num 10*K*T) U hp))
  exact distance_congr exactModel.eqSymm (qadd_zero_right _ (qmul_canonical _ _))
    (by unfold allowance; ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ U hp near small)

private theorem observation_congr (p a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] observation a b p ≐ observation c d p := by
  simpa only [GaussianEulerDecayMesh.subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![a,b,p]) (σ' := ![c,d,p]) (fun i => by fin_cases i; exact ha; exact hb; exact .eqRefl _)

theorem terms_majorized (p N T H J m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le one J)
    (hm : Γ ⊢[PRAAx] le one m) (hr : Γ ⊢[PRAAx] le (m*J) H) (hK : Γ ⊢[PRAAx] le D (K*X))
    (hc : Γ ⊢[PRAAx] le (two*(T*N*H)) (unit p)) :
    Γ ⊢[PRAAx] termsMajorized rowBody envelopeBody N (rowData p N T H J X Y D sign) (envelopeData p N T H J m K) := by
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let i : PTm (n+1) := var 0
  let Δ := lt i (s N) :: Γ.map Fm.shift
  have sz : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
    simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
  have sn : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
  have sj : Δ ⊢[PRAAx] le one (s J) := (Order.shift_one_le hJ).wk
  have sm : Δ ⊢[PRAAx] le one (s m) := (Order.shift_one_le hm).wk
  have sr : Δ ⊢[PRAAx] le (s m*s J) (s H) := by simpa [Δ,s,Fm.shift,Syn.shift] using hr.shift.wk
  have sk : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
  have sc : Δ ⊢[PRAAx] le (two*(s T*s N*s H)) (unit (s p)) := by
    simpa [Δ,s,Fm.shift,Syn.shift,one,two] using hc.shift.wk
  have ht : Δ ⊢[PRAAx] le (s T*i) (s T*s N) :=
    le_congr (mul_comm i (s T)) (mul_comm (s N) (s T)) (mul_le_mul_right (s T) (le_of_lt Prf.hyp0))
  have clock : Δ ⊢[PRAAx] le (two*(s T*i*s H)) (unit (s p)) := le_trans
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*s H) ht)) sc
  have result := majorized_congr (row_at i (s p) (s N) (s T) (s H) (s J) (s X) (s Y) (s D) (s sign)).eqSymm
    (envelope_at i (s p) (s N) (s T) (s H) (s J) (s m) (s K)).eqSymm
    (row_majorized (s p) (s X) (s Y) (s D) (s sign) (s T*i) (s N) (s H) (s J) (s m) (s K) (s T)
      sz sn sj sm sr sk ht clock)
  simpa only [termsMajorized,Δ,i,s,Syn.shift,GaussianBinetSecondDecayGrid.subst_rowData,
    GaussianBinetSecondDecayGrid.subst_envelopeData] using result

private theorem envelope_grid_distance (p N T H J m K : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hH : Γ ⊢[PRAAx] le one H)
    (hJ : Γ ⊢[PRAAx] le one J) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded
      (embed (scalarLeft envelopeBody N (envelopeData p N T H J m K) T one))
      (qmul (fraction (two*K) m) (physicalValue p N T H J))
      (T*allowance K T) (unit p) := by
  let c := fraction (two*K) m
  let f := sampleBody evaluatorF
  let x := envelopeData p N T H J m K
  let y := sampleData p N zero (H*T) J zero
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have rows : Γ ⊢[PRAAx] termsDistance (embedBody envelopeBody) (multiplyBody f) N x (pairT c y) (allowance K T) U := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let i : PTm (n+1) := var 0
    let Δ := lt i (s N) :: Γ.map Fm.shift
    have sn : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
    have sj : Δ ⊢[PRAAx] le one (s J) := (Order.shift_one_le hJ).wk
    have sm : Δ ⊢[PRAAx] le one (s m) := (Order.shift_one_le hm).wk
    let xs := envelopeData (s p) (s N) (s T) (s H) (s J) (s m) (s K)
    let ys := sampleData (s p) (s N) zero (s H*s T) (s J) zero
    let cs := fraction (two*s K) (s m)
    have l : Δ ⊢[PRAAx] inst2 (embedBody envelopeBody) i xs ≐ embed (rowEnvelope (s p) (s m) (s K) (s T) (s T*i) (s N) (s H) (s J)) := by
      simpa only [inst2,embedBody,RationalGaussianEmbedding.subst_embed] using
        embed_congr (envelope_at (Γ := Δ) i (s p) (s N) (s T) (s H) (s J) (s m) (s K))
    have bind : Δ ⊢[PRAAx] observation (zero*s N+(s H*s T)*i) (s J*s N) (s p) ≐
        halfDecay (s p) (s T*i) (s N) (s H) (s J) :=
      observation_congr _ _ _ _ _ (by ipra_ring) (mul_comm _ _)
    have right := (GaussianRationalFiniteSum.multiply_body_at (Γ := Δ) f cs i ys).eqTrans
      (qmul_congr (.eqRefl cs)
        ((GaussianEulerDecayQuadrature.cell_at i (s p) (s N) zero (s H*s T) (s J) zero).eqTrans bind))
    have read : Δ ⊢[PRAAx] distanceBounded (inst2 (embedBody envelopeBody) i xs)
        (inst2 (multiplyBody f) i (pairT cs ys)) (allowance (s K) (s T)) (unit (s p)) :=
      distance_congr l.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
        (row_envelope_distance (s p) (s m) (s K) (s T) (s T*i) (s N) (s H) (s J) sm (positive_product _ _ sn sj))
    simpa only [termsDistance,Δ,i,s,Syn.shift,x,y,c,U,xs,ys,cs,
      GaussianBinetSecondDecayGrid.subst_envelopeData,GaussianCompactRiemannName.subst_sampleData,
      subst_pairT,GaussianPositiveRationalLogarithm.subst_fraction,subst_allowance,
      GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,two,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using read
  have d := common_mesh_distance (embedBody envelopeBody) (multiplyBody f) N x (pairT c y)
    T one (allowance K T) U hN (le_refl one) hu rows
  have ew : Γ ⊢[PRAAx] weight T one N ≐ fraction T N :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul N)
  let z := sum f N y
  have e : Γ ⊢[PRAAx] leftSum (multiplyBody f) N (pairT c y) T one ≐ qmul c (physicalValue p N T H J) :=
    (qmul_congr (.eqRefl _) (sum_multiply f c N y)).eqTrans
      ((GaussianRationalPowerAlgebra.commute_nested (weight T one N) c z).eqTrans
         (qmul_congr (.eqRefl _) ((qmul_congr ew (.eqRefl _)).eqTrans (physical_at p N T H J hN hH hJ).eqSymm)))
  exact distance_congr (scalar_left_embedding envelopeBody N x T one (le_refl one) hN).eqSymm
    e (.eqRefl _) (one_mul U) d

/-- The full scalar envelope bounds any Gaussian grid dominated by its rows. -/
theorem dominated_bound (f : PTm 2) (x p N T H J m K : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le one T)
    (hJ : Γ ⊢[PRAAx] le one J) (hm : Γ ⊢[PRAAx] le one m) (hRate : Γ ⊢[PRAAx] le (m*J) H)
    (hstep : Γ ⊢[PRAAx] le (H*T) (J*N))
    (hmesh : Γ ⊢[PRAAx] le (num 3*((H*T)*(H*T))) N) (hclock : Γ ⊢[PRAAx] le (num 20*N) (unit p))
    (hslack : Γ ⊢[PRAAx] le ((m*m)*T*(num 8+num 10*T)) (unit p))
    (rows : Γ ⊢[PRAAx] termsMajorized f envelopeBody N x (envelopeData p N T H J m K)) :
    Γ ⊢[PRAAx] bounded (leftSum f N x T one) (num 11*K) (m*m) := by
  let U := unit p
  let b := m*m
  let z := physicalValue p N T H J
  let c := fraction (two*K) m
  let y := envelopeData p N T H J m K
  let w := scalarLeft envelopeBody N y T one
  have hH := le_trans (positive_product _ _ hm hJ) hRate
  have hU := unit_positive (Γ := Γ) p
  have hb := positive_product _ _ hm hm
  have base := physical_bound p N T H J m hN hT hJ hm hRate hstep hmesh hclock
  have product : Γ ⊢[PRAAx] bounded (qmul c z) ((two*K)*num 5) b :=
    bounded_product _ _ _ _ _ _ hm hm (GaussianBinetLaplaceScalarMajorant.fraction_norm _ _ hm) base
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ (T*allowance K T) U _ b hU hb
    (envelope_grid_distance p N T H J m K hN hH hJ hm) product
  have upper : Γ ⊢[PRAAx] bounded (embed w) (num 11*K) (m*m) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU hb) hb
      (by dsimp only [U,b,allowance]; ipra_le 𝔞(K)*𝔞(m)*𝔞(m)*sl hslack) raw
  have major := weighted_majorant f envelopeBody N x y T one hN (le_refl one) rows
  exact majorant_bound _ _ _ _ hb major upper

theorem finite_bound (p N T H J m K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le one T)
    (hJ : Γ ⊢[PRAAx] le one J) (hm : Γ ⊢[PRAAx] le one m) (hRate : Γ ⊢[PRAAx] le (m*J) H)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hstep : Γ ⊢[PRAAx] le (H*T) (J*N))
    (hmesh : Γ ⊢[PRAAx] le (num 3*((H*T)*(H*T))) N) (hclock : Γ ⊢[PRAAx] le (num 20*N) (unit p))
    (hrow : Γ ⊢[PRAAx] le (two*(T*N*H)) (unit p))
    (hslack : Γ ⊢[PRAAx] le ((m*m)*T*(num 8+num 10*T)) (unit p)) :
    Γ ⊢[PRAAx] bounded (value p N T H J X Y D sign) (num 11*K) (m*m) :=
  dominated_bound rowBody (rowData p N T H J X Y D sign) p N T H J m K hN hT hJ hm hRate hstep hmesh hclock hslack
    (terms_majorized p N T H J m K X Y D sign hz hN hJ hm hRate hK hrow)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayFinite
