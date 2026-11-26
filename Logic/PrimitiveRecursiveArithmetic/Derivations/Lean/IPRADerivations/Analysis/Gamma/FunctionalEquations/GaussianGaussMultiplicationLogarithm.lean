import IPRADerivations.Analysis.Names.Rates.GaussianNamedInverseRate
import IPRADerivations.Analysis.Logarithm.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Series.RationalHarmonicIntervalVariation

/-!
# Gauss multiplication logarithm comparison

The positive integer logarithm observations are the unchanged Gamma mesh
observations. The finite harmonic rectangle comparison proves their full
relative-time bound at each common mesh.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaFiniteApproximantName (logF)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr)
open Products (fact)
open RationalGaussianEmbedding (embed scalarZero)
open RationalHarmonicInterval (interval horizon numerator)
open RationalValueBounds (radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem harmonic_bound (a b Q F A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b)
    (hQ : Γ ⊢[PRAAx] le one Q)
    (hgap : Γ ⊢[PRAAx] le (D*monus b a) (A*a)) : Γ ⊢[PRAAx]
    le (D*S (Q*b) F) (D*S (Q*a) F+A*F) := by
  let u := Q*b
  let v := Q*a
  have hv : Γ ⊢[PRAAx] le one v := RationalAlgebra.positive_product hQ ha
  have huv : Γ ⊢[PRAAx] le v u := le_mul_mono (le_refl Q) hab
  have delta : Γ ⊢[PRAAx] monus u v ≐ Q*monus b a := by
    have split : Γ ⊢[PRAAx] u ≐ v+Q*monus b a :=
      (congrMul (.eqRefl Q) (eq_add_of_le hab)).eqTrans (by dsimp [u,v]; ipra_ring)
    exact (congrMonus split (.eqRefl v)).eqTrans (add_monus' _ _)
  have distance : Γ ⊢[PRAAx] le (D*monus u v) (A*v) :=
    le_congr (by
      have e := natEq delta
      apply deriveNat
      ipra_simps
      rw [e]
      ring) (by dsimp [v]; ipra_ring) (mul_le_mul_right Q hgap)
  have step := mul_le_mul_right D (RationalHarmonicIntervalVariation.harmonic_increment u v F huv)
  have budget := mul_le_mul_right F distance
  apply RationalValueBounds.positive_cancel hv
  change Γ ⊢[PRAAx] le (v*(D*S u F)) (v*(D*S v F+A*F))
  ipra_le sl step+sl budget

private theorem interval_radius (a b Q A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b)
    (hQ : Γ ⊢[PRAAx] le one Q)
    (hgap : Γ ⊢[PRAAx] le (D*monus b a) (A*a)) : Γ ⊢[PRAAx]
    radius (interval b a Q) scalarZero A D := by
  let L := horizon b a Q
  let F := fact L
  let z := numerator b a Q L
  have hF : Γ ⊢[PRAAx] le one F := GammaEulerMesh.factorial_positive L
  have hz : Γ ⊢[PRAAx] RationalArithmetic.represents (interval b a Q) z F :=
    RationalHarmonicInterval.common_value b a Q L
  have hzero := RationalGaussianEmbedding.scalar_zero_represents (Γ := Γ) one
  have hs : Γ ⊢[PRAAx] le (S (Q*a) F) (S (Q*b) F) := S_mono F (le_mul_mono (le_refl Q) hab)
  have hd := harmonic_bound a b Q F A D ha hab hQ hgap
  apply RationalValueBounds.radius_of_upper
  · apply RationalCubeInfimumIntervals.upper_of_representations _ _ z (ZT.ofNat zero) F one A D
      hF (le_refl one) hz hzero
    apply zle_of_toZ (monus (D*S (Q*a) F+A*F) (D*S (Q*b) F))
    have e := natEq (eq_add_of_le hd)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    simp only [z,numerator,ZT.toZ]
    ipra_simps
    linear_combination -e
  · apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat zero) z one F A D
      (le_refl one) hF hzero hz
    apply zle_of_toZ (D*monus (S (Q*b) F) (S (Q*a) F)+A*F)
    have e := natEq (eq_add_of_le hs)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    simp only [z,numerator,ZT.toZ]
    ipra_simps
    linear_combination -𝔞 D*e

/-- The exact relative-time bound for any two positive integer
logarithm arguments at a shared finite mesh. -/
theorem integer_log_distance_at (a b p A D : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hab : Γ ⊢[PRAAx] le a b) (hD : Γ ⊢[PRAAx] le one D)
    (hgap : Γ ⊢[PRAAx] le (D*monus b a) (A*a)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logF p b) (ap2 logF p a) A D := by
  let Q := GammaEulerConstantName.mesh p
  let g := embed (interval b a Q)
  have finite := RationalGaussianNameEmbedding.distance_from_radius (interval b a Q) scalarZero A D hD
    (interval_radius a b Q A D ha hab (GammaEulerConstantName.mesh_positive p) hgap)
  have boundedG : Γ ⊢[PRAAx] bounded g A D := by
    have e : Γ ⊢[PRAAx] qsub g (embed scalarZero) ≐ g :=
      (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl _) RationalGaussianEmbedding.embed_zero).eqTrans
        (GaussianRationalReconstruction.qsub_zero_right _ (RationalGaussianEmbedding.embed_canonical _))
    exact GaussianRationalReciprocal.bound_congr e (.eqRefl _) (.eqRefl _) finite
  have original : Γ ⊢[PRAAx] qsub (ap2 logF p b) (ap2 logF p a) ≐ g :=
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianGammaFiniteApproximantName.log_sample_at p b)
      (GaussianGammaFiniteApproximantName.log_sample_at p a)).eqTrans
      (GaussianPositiveRationalLogarithmProperness.original_finite_difference b a Q (le_trans ha hab) ha)
  exact GaussianRationalReciprocal.bound_congr original.eqSymm (.eqRefl _) (.eqRefl _) boundedG

/-- The upper endpoint (m(N+1)-1) in the grouped Euler product. -/
def top (m N : PTm n) : PTm n := monus (m*(N+one)) one

@[simp] theorem subst_top {l : ℕ} (σ : Fin n → PTm l) (m N : PTm n) :
    Syn.subst σ (top m N) = top (Syn.subst σ m) (Syn.subst σ N) := by simp [top]

theorem top_split (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] top m N ≐ m*N+monus m one := by
  have split : Γ ⊢[PRAAx] m*(N+one) ≐ (m*N+monus m one)+one := by
    have e := natEq (eq_add_of_le hm)
    apply deriveNat
    ipra_simps
    linear_combination e
  exact (congrMonus split (.eqRefl one)).eqTrans (add_monus _ _)

theorem top_lower (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (m*N) (top m N) :=
  le_of_eq_add (d := monus m one) (top_split m N hm)

theorem top_positive (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (top m N) :=
  le_trans (RationalAlgebra.positive_product hm hN) (top_lower m N hm)

/-- The literal Gamma logarithm samples obey
(lvertlog(m(N+1)-1)-log(mN)vertle 1/N) at every shared clock. -/
theorem log_distance_at (m N p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logF p (top m N)) (ap2 logF p (m*N)) one N := by
  apply integer_log_distance_at (m*N) (top m N) p one N (RationalAlgebra.positive_product hm hN)
    (top_lower m N hm) hN
  have e : Γ ⊢[PRAAx] monus (top m N) (m*N) ≐ monus m one :=
    (congrMonus (top_split m N hm) (.eqRefl _)).eqTrans (add_monus' _ _)
  have gap : Γ ⊢[PRAAx] le (monus m one) m :=
    le_of_eq_add (d := one) ((eq_add_of_le hm).eqTrans (add_comm _ _))
  exact le_congr ((mul_comm _ _).eqTrans (congrMul (.eqRefl N) e).eqSymm)
    (one_mul _).eqSymm (mul_le_mul_right N gap)

open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

theorem log_independent_distance_at (m N p q : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logF p (top m N)) (ap2 logF q (m*N))
      (rateNumerator one N p q) (rateDenominator N p q) := by
  have regular := GaussianNameEquivalence.point_at logF (m*N) p q
    (GaussianGammaFiniteApproximantName.log_regular _ (RationalAlgebra.positive_product hm hN))
  have both := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    hN (RationalAlgebra.positive_product (unit_positive p) (unit_positive q))
    (log_distance_at m N p hm hN) regular
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) both

theorem log_independent_rate (m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    independentRate logF logF (top m N) (m*N) one N := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift m)) := by
    simpa [Fm.shift,Syn.shift] using hm.shift.shift
  have ht : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using hN.shift.shift
  simpa [independentRate,Syn.shift] using
    log_independent_distance_at (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift N)) (var 1) (var 0) hs ht

theorem actual_gauss_multiplication_logarithm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 2) ⋏ le one (var 1)) ⟶
      distanceBounded (ap2 logF (var 0) (top (var 2) (var 1))) (ap2 logF (var 0) (var 2*var 1)) one (var 1)) :=
  closeUniv 3 (.impI (log_distance_at _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_gauss_multiplication_logarithm_independent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le one (var 1) ⋏ le one (var 0)) ⟶
      independentRate logF logF (top (var 1) (var 0)) (var 1*var 0) one (var 0)) :=
  closeUniv 2 (.impI (log_independent_rate _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationLogarithm
