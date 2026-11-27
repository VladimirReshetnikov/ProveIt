import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogarithmRealTail
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.RelativeLogarithms.GaussianBarnesCanonicalHeadRelativeLog
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayRealSamples

/-! The original relative logarithm of the kept Barnes product is real at a real step. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeRealAxis

open_ipra
open ComplexLogarithmRemainder (im)
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct power_at)
open GaussianBarnesCanonicalHeadRelativeLog (data nameF numerator radius denominator relative)
open GaussianBarnesCanonicalLogarithmRealPrefix (fraction_axis)
open GaussianBarnesCanonicalLogarithmRealTail (local_real)
open GaussianRationalConjugation (point_congr point_embed)
open GaussianRationalFiniteProduct (qprod subst_qprod)
open GaussianRationalFiniteSumAxis (rowAxes row_axis)
open GaussianRationalHorner (canonical positive_product qmul_canonical)
open GaussianRationalL1 (rawGaussian)
open GaussianRationalReciprocal (power reciprocal subst_power)
open GaussianRootAlgebra (im_add im_scale)
open GaussianSignedNameExponentialOrder (realSamples)
open RationalGaussianEmbedding (axis subst_axis axis_add axis_negative axis_multiply axis_congr axis_one canonical_axis_roundtrip)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem power_axis (q k : PTm n) (hq : Γ ⊢[PRAAx] axis q) : Γ ⊢[PRAAx] axis (power q k) := by
  let x := Syn.shift q
  let Δ := Γ.map Fm.shift
  let motive : Fm PTm (n+1) := axis (power x (var 0))
  have hx : Δ ⊢[PRAAx] axis x := by simpa [Fm.shift,Syn.shift,x,Δ] using hq.shift
  have all : Γ ⊢[PRAAx] .all motive := by
    refine PRA.qfInd _ (by simp [motive,axis,RationalArgmin.rationalEq,Fm.QF]) ?_ ?_
    · simp only [motive,x,subst_axis,subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact axis_congr (GaussianRationalReciprocal.power_zero q).eqSymm axis_one
    · simp only [motive,x,subst_axis,subst_power,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact axis_congr (GaussianRationalReciprocal.power_succ x (var 0)).eqSymm (axis_multiply _ _ Prf.hyp0 hx.wk)
  simpa only [motive,x,subst_axis,subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

private theorem product_axis (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] rowAxes t x) :
    Γ ⊢[PRAAx] axis (GaussianRationalFiniteProduct.qprod t N x) := by
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  let motive : Fm PTm (n+1) := axis (qprod t (var 0) y)
  have rows : Δ ⊢[PRAAx] rowAxes t y := by simpa [Δ,y,Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all motive := by
    refine PRA.qfInd _ (by simp [motive,axis,RationalArgmin.rationalEq,Fm.QF]) ?_ ?_
    · simp only [motive,y,subst_axis,subst_qprod,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact axis_congr (GaussianRationalFiniteProduct.product_zero t x).eqSymm axis_one
    · simp only [motive,y,subst_axis,subst_qprod,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact axis_congr (GaussianRationalFiniteProduct.product_succ t (var 0) y).eqSymm
        (axis_multiply _ _ Prf.hyp0 (row_axis t y (var 0) rows.wk))
  simpa only [motive,y,subst_axis,subst_qprod,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

private theorem raw_real (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] ZT.eq (im (rawGaussian q)) (ZT.ofNat zero) :=
  let e := canonical_axis_roundtrip q hc hq
  GaussianEulerDecayRealSamples.fixed_raw_imaginary_zero q ((point_congr e.eqSymm).eqTrans ((point_embed _).eqTrans e))

private theorem reciprocal_axis (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q) (hq : Γ ⊢[PRAAx] axis q) :
    Γ ⊢[PRAAx] axis (reciprocal q) := by
  have hi := ZT.toZ_eq (raw_real q hc hq)
  apply fraction_axis _ _ (zero_lt_succ _)
  apply ZT.derive
  rw [GaussianRationalReciprocal.inverseNumerator,im_scale,GaussianRationalReciprocal.im_conjugate,hi]
  simp

theorem head_axis (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx] axis (powerProduct z B N) := by
  apply product_axis _ _ _ (.allI ?_)
  let Δ := Γ.map Fm.shift
  let Z := Syn.shift z
  let D := Syn.shift B
  let i : PTm (n+1) := var 0
  let k := succ i
  have d : Δ ⊢[PRAAx] le one D := by simpa [Fm.shift,Syn.shift,D,Δ,one] using hB.shift
  have r : Δ ⊢[PRAAx] ZT.eq (im Z) (ZT.ofNat zero) := by simpa [Fm.shift,Syn.shift,Z,Δ] using hz.shift
  have row := power_axis (GaussianBarnesCanonicalFactor.base Z D k) k
    (axis_add _ _ axis_one (fraction_axis Z (D*k) (positive_product _ _ d (zero_lt_succ i)) r))
  simpa only [Z,D,i,Syn.shift,GaussianBarnesCanonicalPolynomialShift.subst_data] using
    axis_congr (power_at (Γ := Δ) i Z D).eqSymm row

theorem relative_real (z h B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) (hh : Γ ⊢[PRAAx] ZT.eq (im h) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] realSamples nameF (data z h B N) := by
  let w := ComplexLogarithmRemainder.add z h
  let a := powerProduct z B N
  let b := powerProduct w B N
  have hw : Γ ⊢[PRAAx] ZT.eq (im w) (ZT.ofNat zero) := by
    apply ZT.derive
    dsimp only [w]
    rw [im_add,ZT.toZ_eq hz,ZT.toZ_eq hh]
    simp
  have aa := head_axis z B N hB hz
  have bb := head_axis w B N hB hw
  have ia := reciprocal_axis a (GaussianRationalFiniteProduct.product_canonical _ _ _) aa
  have r : Γ ⊢[PRAAx] axis (relative z h B N) := axis_multiply _ _ ia (axis_add _ _ bb (axis_negative _ aa))
  exact local_real (numerator z h B N) (radius z h B N) (denominator z h B N)
    (raw_real _ (qmul_canonical _ _) r)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeRealAxis
