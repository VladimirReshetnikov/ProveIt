import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.DenominatorBounds.GaussianBinetBoseGeometricRatio
import IPRADerivations.Analysis.Geometry.GeometricBounds.GaussianRationalGeometricPowerTail
import IPRADerivations.Analysis.Geometry.GeometricBounds.GaussianRationalInverseGeometric

/-!
# Geometric prefixes of the original Bose reciprocal

Read the positive exponential at the precise clock inherited from the
actual reciprocal. Take exact rational powers of its inverse. The
geometric error has a uniform algebraic tail at every internal cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseSeries

open_ipra
open GaussianBinetBoseDenominator (reciprocalF reciprocalData sampleClock observation_lower)
open GaussianBinetBoseExponential (expF expData)
open GaussianBinetBoseGeometricRatio (inverse_pair inverse_bound)
open GaussianRationalGeometricPowerTail (power_tail)
open GaussianRationalInverseGeometric (value finite)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical bounded distanceBounded)
open GaussianRationalReciprocal (power reciprocal reciprocal_canonical bounded_negative bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalPowerAlgebra (qmul_commutative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Den" => GaussianBinetBoseDenominator.nameF
local notation "denData" => GaussianBinetBoseDenominator.data

def denominatorClock (p B : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus B) p + GaussianNameReciprocal.anchor B

def positiveSample (p A B : PTm n) : PTm n :=
  ap2 expF (sampleClock (denominatorClock p B)) (expData false A B)

def ratio (p A B : PTm n) : PTm n := reciprocal (positiveSample p A B)
def prefixValue (p A B N : PTm n) : PTm n := value N (ratio p A B)

theorem observation_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 reciprocalF p (reciprocalData A B) ≐
    reciprocal (qsub (positiveSample p A B) qone) := by
  let x := ap2 Den (denominatorClock p B) (denData A B)
  have raw := (GaussianNameReciprocal.name_at (Γ := Γ) Den B (denData A B) p).eqTrans
    (GaussianExponentialReference.recode_fixed (reciprocal x) (reciprocal_canonical x))
  exact raw.eqTrans (GaussianNameReciprocal.reciprocal_congr
    (GaussianBinetBoseDenominator.sample_at (denominatorClock p B) A B))

theorem partial_cleared (p A B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (qsub (positiveSample p A B) qone) (prefixValue p A B N) ≐
      qsub qone (power (ratio p A B) N) :=
  finite _ _ N (inverse_pair (sampleClock (denominatorClock p B)) A B hB)

theorem partial_error (p A B N : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (prefixValue p A B N) (ap2 reciprocalF p (reciprocalData A B))
      (B*B) ((num 4*A)*(B+N*(num 4*A))) := by
  let C := num 4*A
  let r := denominatorClock p B
  let x := positiveSample p A B
  let y := ratio p A B
  let S := prefixValue p A B N
  let d := qsub x qone
  let w := reciprocal d
  let v := power y N
  let E := B+N*C
  have hC : Γ ⊢[PRAAx] le one C := positive_product _ _ (by ipra_le 3) hA
  have hE : Γ ⊢[PRAAx] le one E := le_trans hB (le_add_right B (N*C))
  have hd := GaussianRationalLowerBounds.lower_congr
    (GaussianBinetBoseDenominator.sample_at (Γ := Γ) r A B) (.eqRefl C) (.eqRefl B) (observation_lower r A B hB)
  have exactPair : Γ ⊢[PRAAx] qmul w d ≐ qone :=
    (qmul_commutative w d).eqTrans (GaussianRationalLowerBounds.reciprocal_identity_of_lower d C B hC hB hd)
  have invert : Γ ⊢[PRAAx] qmul w (qmul d S) ≐ S :=
    (qmul_associative w d S).eqSymm.eqTrans
      ((qmul_congr exactPair (.eqRefl S)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical S
          (GaussianRationalFiniteSum.sum_canonical GaussianRationalInverseGeometric.body N y)))
  have eq : Γ ⊢[PRAAx] S ≐ qmul w (qsub qone v) :=
    invert.eqSymm.eqTrans (qmul_congr (.eqRefl w) (partial_cleared p A B N hB))
  have bound := power_tail y B C N hB (inverse_bound (sampleClock r) A B hB)
  have back : Γ ⊢[PRAAx] qsub (qsub qone v) qone ≐ qnegative v :=
    qadd_sub_cancel qone (qnegative v) (qnegative_canonical v)
  have diff : Γ ⊢[PRAAx] distanceBounded (qsub qone v) qone B E :=
    bound_congr back.eqSymm (.eqRefl _) (.eqRefl _) (bounded_negative v _ _ hE bound)
  have prod := bounded_product w (qsub (qsub qone v) qone) B C B E hC hE
    (GaussianRationalLowerBounds.inverse_bound d C B hC hB hd) diff
  have dist : Γ ⊢[PRAAx] distanceBounded (qmul w (qsub qone v)) (qmul w qone) (B*B) (C*E) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference w (qsub qone v) qone).eqSymm
      (.eqRefl _) (.eqRefl _) prod
  exact GaussianRationalDistanceOrder.distance_congr eq.eqSymm
    ((qmul_one_right w (reciprocal_canonical d)).eqTrans (observation_at p A B).eqSymm)
    (.eqRefl _) (.eqRefl _) dist

theorem actual_Binet_Bose_geometric_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 1) ⋏ le one (var 2)) ⟶
      distanceBounded (prefixValue (var 0) (var 1) (var 2) (var 3))
        (ap2 reciprocalF (var 0) (reciprocalData (var 1) (var 2)))
        (var 2*var 2) ((num 4*var 1)*(var 2+var 3*(num 4*var 1)))) :=
  closeUniv 4 (.impI (partial_error _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseSeries
