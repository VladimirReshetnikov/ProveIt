import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.Algebra.GaussianHarmonicLogarithmProduct

/-!
# The actual logarithm of a factorial is the sum of its logs

An induction in iPRA compares the literal harmonic-log samples at a
fixed clock. Each factorial multiplication contributes at most two
dyadic units to the error. Amplifying the common row clock by the
internal count yields an exact identity for the original logarithm
and the original finite named sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaFactorialLogSum

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm point_at)
open GaussianNameRingLaws (equivalent_of_envelope)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamily (body finite data nameF sample_at term_at regular)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "L" => GaussianHarmonicLogarithmName.data
local notation "S" => GaussianHarmonicLogarithmName.sample
local notation "O" => GaussianPositiveRationalLogarithm.data

def harmonicBody : PTm 2 := L (succ (var 0)) one
def logarithmBody : PTm 2 := O (succ (var 0)) one

@[simp] theorem harmonic_row (i x : PTm n) : inst2 harmonicBody i x = L (succ i) one := by
  simp [inst2,harmonicBody,one]

@[simp] theorem logarithm_row (i x : PTm n) : inst2 logarithmBody i x = O (succ i) one := by
  simp [inst2,logarithmBody,one]

private theorem sample_one (p : PTm n) : Γ ⊢[PRAAx] S p one one ≐ qzero := by
  let Q := GaussianHarmonicLogarithmProduct.mesh p
  let K := RationalHarmonicInterval.horizon one one Q
  let a := RationalHarmonicInterval.numerator one one Q K
  let b := RationalHarmonicInterval.interval one one Q
  let c : PTm n := RationalGaussianEmbedding.scalarZero
  have hc := RationalNormalForm.normalize_well_formed (Γ := Γ) (ZT.ofNat zero) one (le_refl one)
  have eq : Γ ⊢[PRAAx] b ≐ c := by
    apply RationalFiniteSum.canonical_equal b c a (ZT.ofNat zero) (fact K) one
      (RationalHarmonicInterval.common_canonical one one Q K) hc
      (RationalHarmonicInterval.common_value one one Q K) (RationalGaussianEmbedding.scalar_zero_represents one)
      (GammaEulerMesh.factorial_positive K) (le_refl one)
    apply ZT.derive (u := a*ZT.ofNat one) (v := ZT.ofNat zero*ZT.ofNat (fact K))
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    simp [a,RationalHarmonicInterval.numerator,ZT.toZ,IPRA.Q.mk_zero,map_zero]
  have embed := (RationalGaussianEmbedding.embed_at (Γ := Γ) b).eqSymm.eqTrans
    ((congrAp1 RationalGaussianEmbedding.embedF eq).eqTrans (RationalGaussianEmbedding.embed_at c))
  exact (GaussianHarmonicLogarithmName.sample_at p one one).eqTrans (embed.eqTrans RationalGaussianEmbedding.embed_zero)

def finiteEnvelope (p N x : PTm n) : Fm PTm n :=
  distanceBounded (S p (fact N) one) (finite H harmonicBody p N x) (N*two) (unit p)

ipra_subst finiteEnvelope [finite, fact, one, two]

private theorem finite_zero (p x : PTm n) : Γ ⊢[PRAAx] finiteEnvelope p zero x := by
  have old : Γ ⊢[PRAAx] S p (fact zero) one ≐ S p one one :=
    congrAp2 H (.eqRefl _) (congrPairT (fact_zero zero) (.eqRefl _))
  have sum := GaussianRationalFiniteSum.sum_zero (Γ := Γ) (body H harmonicBody) (pairT p x)
  exact distance_congr (old.eqTrans (sample_one p)).eqSymm sum.eqSymm (zero_mul two).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qzero (unit p) (unit_positive p))

private theorem finite_succ (p N x : PTm n) (h : Γ ⊢[PRAAx] finiteEnvelope p N x) :
    Γ ⊢[PRAAx] finiteEnvelope p (succ N) x := by
  let Y := S p (succ N) one
  have Fpos := GammaEulerMesh.factorial_positive (Γ := Γ) N
  have Npos := zero_lt_succ (Γ := Γ) N
  have raw := GaussianHarmonicLogarithmProduct.finite_samples p (fact N) one (succ N) one
    (.andI (.andI Fpos (le_refl one)) (.andI Npos (le_refl one)))
  have factEq : Γ ⊢[PRAAx] S p (fact (succ N)) one ≐ S p (fact N*succ N) (one*one) :=
    congrAp2 H (.eqRefl _) (congrPairT (fact_succ N zero) (one_mul one).eqSymm)
  have prev := distance_congr factEq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  have row := (GaussianRationalFiniteSum.sum_succ (Γ := Γ) (body H harmonicBody) N (pairT p x)).eqTrans
    (qadd_congr (.eqRefl _) (term_at H harmonicBody N p x))
  rw [harmonic_row] at row
  have summed := GaussianNameArithmetic.sum_distance _ _ Y Y _ _ (unit p) (unit_positive p) h
    (GaussianRationalPowerDifference.distance_refl_zero Y (unit p) (unit_positive p))
  have tail := distance_congr (.eqRefl _) row.eqSymm (add_zero _ : Γ ⊢[PRAAx] _) (.eqRefl _) summed
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) prev tail)

/-- At one original row clock the accumulation has the exact linear budget. -/
theorem finite_factorial_distance (p N x : PTm n) : Γ ⊢[PRAAx] finiteEnvelope p N x := by
  have all : Γ ⊢[PRAAx] .all (finiteEnvelope (Syn.shift p) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_finiteEnvelope,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using finite_zero (Γ := Γ) p x
    · simpa only [subst_finiteEnvelope,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        finite_succ (Γ := finiteEnvelope (Syn.shift p) (var 0) (Syn.shift x) :: Γ.map Fm.shift)
          (Syn.shift p) (var 0) (Syn.shift x) Prf.hyp0
  simpa only [subst_finiteEnvelope,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem harmonic_rows (N x : PTm n) : Γ ⊢[PRAAx] regularRows H harmonicBody N x := by
  refine .allI (.impI ?_)
  rw [harmonic_row]
  exact GaussianHarmonicLogarithmName.name_regular _ _ (.andI (zero_lt_succ _) (le_refl _))

theorem logarithm_rows (N x : PTm n) : Γ ⊢[PRAAx] regularRows logF logarithmBody N x := by
  refine .allI (.impI ?_)
  rw [logarithm_row]
  exact GaussianPositiveRationalLogarithm.name_regular _ _ (.andI (zero_lt_succ _) (le_refl _))

theorem matching_rows (N x : PTm n) : Γ ⊢[PRAAx] equalRows logF H logarithmBody harmonicBody N x x := by
  refine .allI (.impI ?_)
  rw [harmonic_row,logarithm_row]
  exact GaussianHarmonicLogarithmName.cross_original _ _ (.andI (zero_lt_succ _) (le_refl _))

theorem harmonic_factorial_diagonal (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (S p (fact N) one) (ap2 (nameF H harmonicBody) p (data N x)) (num 4) (unit p) := by
  let k := exponent N p
  have hp := unit_positive (Γ := Γ) p
  have hk := unit_positive (Γ := Γ) k
  have hfactor := GaussianHarmonicLogarithmName.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have grow : Γ ⊢[PRAAx] le (unit p) (unit k) :=
    unit_monotone (le_add_right p (GaussianFastValueCut.normalizer N))
  have first := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hk) hp
    (by ipra_le Groth.ι (IPRA.Q.mk Γ (unit p))*sl grow) (point_at H (L (fact N) one) p k hfactor)
  have budget := query_budget (Γ := Γ) N p
  have a : Γ ⊢[PRAAx] le ((N*two)*unit p) (two*unit k) := by
    ipra_le 2*sl budget
  have raw : Γ ⊢[PRAAx] distanceBounded (S k (fact N) one) (finite H harmonicBody k N x) (N*two) (unit k) :=
    finite_factorial_distance k N x
  have last := distance_congr (.eqRefl _) (sample_at H harmonicBody p N x).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ two (unit p) hk hp a raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first last)

theorem harmonic_factorial_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent H (nameF H harmonicBody) (L (fact N) one) (data N x) := by
  have hfactor := GaussianHarmonicLogarithmName.name_regular (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  refine equivalent_of_envelope _ _ _ _ (num 4) hfactor (regular H harmonicBody N x (harmonic_rows N x)) (.allI ?_)
  simpa only [Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianHarmonicLogarithmName.subst_data,
    subst_ap2,PTm.subst_num,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,one,fact,GaussianHarmonicLogarithmName.sample] using
    harmonic_factorial_diagonal (Γ := Γ.map Fm.shift) (var 0) (Syn.shift N) (Syn.shift x)

theorem factorial_logarithm_cross (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent logF (nameF logF logarithmBody) (O (fact N) one) (data N x) := by
  have hfactor := GaussianHarmonicLogarithmName.cross_original (fact N) one
    (.andI (GammaEulerMesh.factorial_positive (Γ := Γ) N) (le_refl one))
  have hrows := family_sum_cross logF H logarithmBody harmonicBody N x x (matching_rows (Γ := Γ) N x)
  exact cross_trans _ _ _ _ _ _ hfactor
    (cross_trans _ _ _ _ _ _ (harmonic_factorial_cross N x) (cross_symm _ _ _ _ hrows))

theorem actual_original_factorial_logarithm_finite_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent logF (nameF logF logarithmBody) (O (fact (var 0)) one) (data (var 0) (var 1))) :=
  closeUniv 2 (factorial_logarithm_cross _ _)

end LeanProofs.IPRA.Analysis.GaussianLogGammaFactorialLogSum
