import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesCanonicalLogarithmRealPrefix

/-!
# Real observations of the original cofinal Barnes logarithm tail

The actual finite cubic series at a real center has zero imaginary
numerator. Its signed dyadic rounding preserves zero in that coordinate.
The original retained sum therefore has real observations at every clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogarithmRealTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (im mul power series)
open LogarithmRemainder (three)
open ComplexLogarithmCauchy (eval_im_congr)
open GaussianBarnesCanonicalLogarithmRealPrefix (fraction_axis)
open GaussianRationalFiniteSumAxis (rowAxes sum_axis)
open GaussianRootAlgebra (im_add im_neg im_scale im_mul im_zero im_one)
open GaussianSignedNameExponentialOrder (realSamples)
open RationalGaussianEmbedding (axis axis_congr axis_multiply)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def realCode (z : PTm n) : Fm PTm n := ZT.eq (im z) (ZT.ofNat zero)

@[simp] private theorem subst_realCode {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    (realCode z).subst σ = realCode (Syn.subst σ z) := by simp [realCode]

private theorem real_congr {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) (h : Γ ⊢[PRAAx] realCode b) :
    Γ ⊢[PRAAx] realCode a := ZT.derive ((eval_im_congr e).trans (ZT.toZ_eq h))

private theorem real_power (z k : PTm n) (hz : Γ ⊢[PRAAx] realCode z) : Γ ⊢[PRAAx] realCode (power z k) := by
  let Z := Syn.shift z
  let Δ := Γ.map Fm.shift
  let motive : Fm PTm (n+1) := realCode (power Z (var 0))
  have hs : Δ ⊢[PRAAx] realCode Z := by simpa [Fm.shift,Syn.shift,Z,Δ] using hz.shift
  have p : Γ ⊢[PRAAx] .all motive := by
    refine PRA.qfInd _ (by simp [motive,realCode,ZT.eq,Fm.QF]) ?_ ?_
    · simp only [motive,Z,subst_realCode,ComplexLogarithmRemainder.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact real_congr (ComplexLogarithmRemainder.power_zero z) (ZT.derive (by simp [im_one,ZT.toZ_ofNat]))
    · simp only [motive,Z,subst_realCode,ComplexLogarithmRemainder.subst_power,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      apply real_congr (ComplexLogarithmRemainder.power_succ Z (var 0))
      apply ZT.derive
      change ZT.toZ (motive :: Δ) (im (mul (power Z (var 0)) Z)) = ZT.toZ (motive :: Δ) (ZT.ofNat zero)
      have hi := ZT.toZ_eq (Prf.hyp0 : motive :: Δ ⊢[PRAAx] realCode (power Z (var 0)))
      have hx := ZT.toZ_eq (hs.wk : motive :: Δ ⊢[PRAAx] realCode Z)
      rw [im_mul,hi,hx]
      simp
  simpa only [motive,Z,subst_realCode,ComplexLogarithmRemainder.subst_power,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using p.allE k

private theorem real_series (z D k : PTm n) (hz : Γ ⊢[PRAAx] realCode z) : Γ ⊢[PRAAx] realCode (series z D k) := by
  let Z := Syn.shift z
  let E := Syn.shift D
  let Δ := Γ.map Fm.shift
  let motive : Fm PTm (n+1) := realCode (series Z E (var 0))
  have hs : Δ ⊢[PRAAx] realCode Z := by simpa [Fm.shift,Syn.shift,Z,Δ] using hz.shift
  have p : Γ ⊢[PRAAx] .all motive := by
    refine PRA.qfInd _ (by simp [motive,realCode,ZT.eq,Fm.QF]) ?_ ?_
    · simp only [motive,Z,E,subst_realCode,ComplexLogarithmRemainder.subst_series,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact real_congr (ComplexLogarithmRemainder.series_zero z D) (ZT.derive (by simp [im_zero,ZT.toZ_ofNat]))
    · simp only [motive,Z,E,subst_realCode,ComplexLogarithmRemainder.subst_series,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      apply real_congr (ComplexLogarithmRemainder.series_succ Z E (var 0))
      have hx := ZT.toZ_eq (hs.wk : motive :: Δ ⊢[PRAAx] realCode Z)
      let w := ComplexLogarithmRemainder.neg Z
      have hneg : motive :: Δ ⊢[PRAAx] realCode w := ZT.derive (by dsimp only [w]; rw [im_neg,hx]; simp)
      have hr := ZT.toZ_eq (real_power w (var 0+three) hneg)
      have hi := ZT.toZ_eq (Prf.hyp0 : motive :: Δ ⊢[PRAAx] realCode (series Z E (var 0)))
      apply ZT.derive
      change ZT.toZ (motive :: Δ) (im (ComplexLogarithmRemainder.add
        (ComplexLogarithmRemainder.scale ((var 0+three)*E) (series Z E (var 0)))
        (ComplexLogarithmRemainder.neg (ComplexLogarithmRemainder.scale (Products.fact (var 0+two)) (power w (var 0+three)))))) = _
      rw [im_add,im_neg,im_scale,im_scale,hi,hr]
      simp
  simpa only [motive,Z,E,subst_realCode,ComplexLogarithmRemainder.subst_series,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using p.allE k

private theorem rounded_real (z D U : PTm n) (hz : Γ ⊢[PRAAx] realCode z) :
    Γ ⊢[PRAAx] realCode (DyadicComplexLogarithm.rounded z D U) := by
  have parts : Γ ⊢[PRAAx] (im z).pos ≐ (im z).neg :=
    (add_zero _).eqSymm.eqTrans (hz.eqTrans (zero_add _))
  have q : Γ ⊢[PRAAx] quo (U*(im z).pos) D ≐ quo (U*(im z).neg) D := by
    ipra_congr (quo (var 0*var 1) (var 2) : PTm 3) with [.eqRefl U,parts,.eqRefl D]
  apply ZT.derive
  rw [DyadicComplexLogarithm.rounded,ComplexLogarithmRemainder.eval_im_code]
  simp [DyadicComplexLogarithm.roundedCoordinate,ZT.toZ,ZT.ofNat,natEq q]

private theorem cubic_observation_real (p z R N : PTm n) (hz : Γ ⊢[PRAAx] realCode z) :
    Γ ⊢[PRAAx] realCode (DyadicComplexLogarithm.observation p z R N) :=
  real_congr (DyadicComplexLogarithm.observation_compute p z R N)
    (rounded_real _ _ _ (real_series z N (DyadicComplexLogarithm.precision p) hz))

theorem local_value_axis (p z R N : PTm n) (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] axis (GaussianLocalLogarithmName.value p z R N) := by
  have hx := ZT.toZ_eq hz
  have hn : Γ ⊢[PRAAx] realCode (ComplexLogarithmName.baseNumerator z N) := by
    apply ZT.derive
    rw [ComplexLogarithmName.baseNumerator,im_add,im_scale,im_neg,im_mul,hx]
    simp
  have base := ZT.toZ_eq (rounded_real (ComplexLogarithmName.baseNumerator z N)
    (ComplexLogarithmName.baseDenominator N) (DyadicComplexLogarithm.unit p) hn)
  have tail := ZT.toZ_eq (cubic_observation_real p z R N hz)
  have ro : Γ ⊢[PRAAx] realCode (ComplexLogarithmName.observation p z R N) := by
    apply real_congr (ComplexLogarithmName.observation_compute p z R N)
    apply ZT.derive
    rw [ComplexLogarithmName.observationTerm,im_add,base,tail]
    simp
  exact fraction_axis (ComplexLogarithmName.observation p z R N) _ (GaussianLocalLogarithmName.unit_positive p) ro

theorem local_real (z R N : PTm n) (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx]
    realSamples GaussianLocalLogarithmName.pointF (GaussianLocalLogarithmName.data z R N) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (x : PTm n) := Syn.shift x
  have zr : Δ ⊢[PRAAx] ZT.eq (im (sh z)) (ZT.ofNat zero) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
  have p := GaussianLocalLogarithmName.point_canonical (Γ := Δ) (var 0) (sh z) (sh R) (sh N)
  have eq := GaussianLocalLogarithmName.point_at (Γ := Δ) (var 0) (sh z) (sh R) (sh N)
  simpa only [sh,Syn.shift,GaussianLocalLogarithmName.subst_data,GaussianLocalLogarithmName.point] using
    (Prf.andI p (axis_congr eq.eqSymm (local_value_axis _ _ _ _ zr)))

theorem row_axis (p z R B k : PTm n) (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] axis (GaussianBarnesCanonicalLogRow.roundedValue p z R B k) := by
  let D := B*k
  have real := cubic_observation_real p z (R*B) D hz
  have number := axis_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point k one (le_refl one))
    (GaussianStirlingNames.fraction_axis (Γ := Γ) k one (le_refl one))
  exact axis_multiply _ _ number (fraction_axis _ _ (GaussianLocalLogarithmName.unit_positive p) real)

theorem interval_axis (p z R B N r : PTm n) (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] axis (GaussianBarnesCanonicalLogRoundedTail.value p z R B N r) := by
  apply sum_axis _ _ _ (.allI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  have zr : Δ ⊢[PRAAx] ZT.eq (im (sh z)) (ZT.ofNat zero) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
  have e := GaussianBarnesCanonicalLogRoundedTail.body_at (Γ := Δ) (sh p) (sh z) (sh R) (sh B) (sh N) (var 0)
  simpa only [sh,Syn.shift,GaussianBarnesCanonicalLogRoundedTail.subst_data] using
    axis_congr e.eqSymm (row_axis _ _ _ _ _ zr)

theorem cofinal_real (z R B : PTm n) (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx]
    realSamples GaussianBarnesCanonicalLogCofinal.nameF (GaussianBarnesCanonicalLogCofinal.data z R B) := by
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have zr : Δ ⊢[PRAAx] ZT.eq (im (sh z)) (ZT.ofNat zero) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
  have e := GaussianBarnesCanonicalLogCofinal.sample_at (Γ := Δ) p (sh z) (sh R) (sh B)
  have canon := GaussianRationalFiniteSum.sum_canonical (Γ := Δ) GaussianBarnesCanonicalLogRoundedTail.body
    (GaussianBarnesCanonicalLogSchedule.length p (sh R))
    (GaussianBarnesCanonicalLogRoundedTail.data (GaussianBarnesCanonicalLogSchedule.clock p (sh R))
      (sh z) (sh R) (sh B) (GaussianBarnesCanonicalLogSchedule.initial (sh R)))
  simpa only [sh,Syn.shift,GaussianBarnesCanonicalLogCofinal.subst_data] using
    (Prf.andI (GaussianRationalHorner.canonical_congr e canon) (axis_congr e.eqSymm (interval_axis _ _ _ _ _ _ zr)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogarithmRealTail
