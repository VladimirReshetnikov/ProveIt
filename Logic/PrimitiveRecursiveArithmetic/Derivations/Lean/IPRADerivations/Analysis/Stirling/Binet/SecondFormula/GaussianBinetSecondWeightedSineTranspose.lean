import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSineMatrix
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondRowCell
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedQuadrature
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenMatrix

/-!
# Exact transposition of the weighted positive-frequency rectangle

After transposition each retained frequency sees the original
real-damped sine quadrature on the same time grid. The second Binet
factor of two is included in the transposed columns.
-/

set_option autoImplicit false
set_option maxHeartbeats 880000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineTranspose

open_ipra
open GaussianBinetSecondWeightedSineMatrix (matrix data subst_data original_cell_at suffix_row_at)
open GaussianBinetSecondDecayPointwise (fullDecay frozenPiNumerator)
open GaussianBinetSineFrozenPiTerm (realNumerator realDenominator)
open GaussianBinetOscillatoryColumns (damping subst_damping)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalFubini
  (column rowSumBody columnSumBody columnBody column_entry row_sum_at column_sum_at rowFirst columnFirst)
open GaussianRationalHorner (qmul)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalRiemannRefinement (leftSum weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingConstant (piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def suffixBody : PTm 2 := multiplyBody (rowSumBody matrix)
def suffixData (p M T H J X Y D sign R L N cut : PTm n) : PTm n :=
  pairT (weight (D*L) one N) (pairT (monus N cut) (data p M T H J X Y D sign R L N cut))
def suffixValue (p M T H J X Y D sign R L N cut : PTm n) : PTm n :=
  leftSum suffixBody M (suffixData p M T H J X Y D sign R L N cut) T one

def transposedBody : PTm 2 := multiplyBody (columnSumBody matrix)
def transposedData (p M T H J X Y D sign R L N cut : PTm n) : PTm n :=
  pairT (qmul (fraction two one) (weight T one M)) (pairT M (data p M T H J X Y D sign R L N cut))
def transposedValue (p M T H J X Y D sign R L N cut : PTm n) : PTm n :=
  qmul (weight (D*L) one N) (sum transposedBody (monus N cut) (transposedData p M T H J X Y D sign R L N cut))

/-- The original doubled frozen sine quadrature at its effective clock. -/
def rawFrozenValue (l k i A B U T M : PTm n) : PTm n :=
  qmul (fraction two one) (GaussianBinetSineDampedQuadrature.value l (realNumerator k i) (realDenominator k) A B U T M)

@[simp] private theorem subst_realNumerator {m : ℕ} (σ : Fin n → PTm m) (k i : PTm n) :
    Syn.subst σ (realNumerator k i) = realNumerator (Syn.subst σ k) (Syn.subst σ i) := by
  simp [realNumerator,GaussianBinetKernelImaginaryRatioRows.timeNumerator,GaussianStirlingConstant.piNumerator,
    BaselQuadrature.Q,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    WallisFinite.Dm,one,two]

@[simp] private theorem subst_realDenominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (realDenominator k) = realDenominator (Syn.subst σ k) := by
  simp [realDenominator,GaussianBinetKernelImaginaryRatioRows.timeDenominator,one]

ipra_subst rawFrozenValue [one, two]

ipra_subst suffixData [one]

ipra_subst suffixValue [one]

ipra_subst transposedData [one, two]

ipra_subst transposedValue [one]

theorem suffix_at (j p M T H J X Y D sign R L N cut : PTm n) :
    Γ ⊢[PRAAx] inst2 suffixBody j (suffixData p M T H J X Y D sign R L N cut) ≐
      qmul (GaussianBinetOscillatorySineSmallStrip.suffixValue p X Y D sign (T*j) M R T L N cut)
        (fullDecay (p+N) (T*j) M H J) := by
  let w := weight (D*L) one N
  let d := data p M T H J X Y D sign R L N cut
  let C := monus N cut
  exact (multiply_body_at (rowSumBody matrix) w j (pairT C d)).eqTrans
    ((qmul_congr (.eqRefl _) (row_sum_at matrix j C d)).eqTrans (suffix_row_at j p M T H J X Y D sign R L N cut))

private theorem commute_weights (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a c))

theorem scaled_transpose (p M T H J X Y D sign R L N cut : PTm n) : Γ ⊢[PRAAx]
    qmul (fraction two one) (suffixValue p M T H J X Y D sign R L N cut) ≐
      transposedValue p M T H J X Y D sign R L N cut := by
  let d := data p M T H J X Y D sign R L N cut
  let C := monus N cut
  let fs := weight (D*L) one N
  let ft := weight T one M
  let c : PTm n := fraction two one
  let r := rowFirst matrix M C d
  let s := columnFirst matrix M C d
  have removed : Γ ⊢[PRAAx] suffixValue p M T H J X Y D sign R L N cut ≐ qmul ft (qmul fs r) :=
    qmul_congr (.eqRefl _) (sum_multiply (rowSumBody matrix) fs M (pairT C d))
  have order : Γ ⊢[PRAAx] qmul ft (qmul fs r) ≐ qmul fs (qmul ft r) := commute_weights ft fs r
  have commute : Γ ⊢[PRAAx] qmul c (qmul fs (qmul ft r)) ≐ qmul fs (qmul (qmul c ft) s) :=
    (commute_weights c fs (qmul ft r)).eqTrans (qmul_congr (.eqRefl _) ((qmul_associative c ft r).eqSymm.eqTrans
      (qmul_congr (.eqRefl _) (GaussianRationalFubini.fubini matrix M C d))))
  exact (qmul_congr (.eqRefl _) (removed.eqTrans order)).eqTrans
    (commute.eqTrans (qmul_congr (.eqRefl _) (sum_multiply (columnSumBody matrix) (qmul c ft) C (pairT M d)).eqSymm))

private theorem column_weighted_at (r p k i M T X Y D sign R L N cut : PTm n)
    (hcut : Γ ⊢[PRAAx] le one cut) :
    let j := cut+r
    let S := D*L
    let H := frozenPiNumerator i k
    let J := piDenominator k
    Γ ⊢[PRAAx] qmul (weight T one M) (column matrix r M (data p M T H J X Y D sign R L N cut)) ≐
      qmul (damping p X Y D sign S j N R)
        (GaussianBinetSineDampedQuadrature.value (p+N) (realNumerator k i) (realDenominator k) (S*j) N S T M) := by
  let j := cut+r
  let S := D*L
  let H := frozenPiNumerator i k
  let J := piDenominator k
  let w := weight T one M
  let d := data p M T H J X Y D sign R L N cut
  let e := damping p X Y D sign S j N R
  let f := GaussianBinetSineDampedQuadrature.body
  let x := GaussianBinetSineDampedQuadrature.data (p+N) (realNumerator k i) (realDenominator k) (S*j) N S T M
  have pos : Γ ⊢[PRAAx] le one j := le_trans hcut (le_add_right cut r)
  have terms : Γ ⊢[PRAAx] termsEqual (columnBody matrix) (multiplyBody f) M (pairT r d) (pairT e x) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let a : PTm (n+1) := var 0
    let Δ := lt a (s M)::Γ.map Fm.shift
    have hp : Δ ⊢[PRAAx] le one (s cut+s r) := by
      simpa [Δ,s,j,Fm.shift,Syn.shift,one] using pos.shift.wk
    let d' := data (s p) (s M) (s T) (frozenPiNumerator (s i) (s k)) (piDenominator (s k))
      (s X) (s Y) (s D) (s sign) (s R) (s L) (s N) (s cut)
    let S' := s D*s L
    let e' := damping (s p) (s X) (s Y) (s D) (s sign) S' (s cut+s r) (s N) (s R)
    let A' := S'*(s cut+s r)
    let X' := realNumerator (s k) (s i)
    let D' := realDenominator (s k)
    let x' := GaussianBinetSineDampedQuadrature.data (s p+s N) X' D' A' (s N) S' (s T) (s M)
    have orig := (column_entry (Γ := Δ) matrix a (s r) d').eqTrans
      (original_cell_at a (s r) (s p) (s M) (s T) _ _ (s X) (s Y) (s D) (s sign) (s R) (s L) (s N) (s cut))
    have known := GaussianBinetSecondRowCell.positive_cell (s cut+s r) (s p) (s k) (s i) (s X) (s Y) (s D)
      (s sign) (s T*a) (s M) (s R) (s T) (s L) (s N) hp
    have row := GaussianBinetSineDampedQuadrature.row_at (Γ := Δ) a (s p+s N) X' D' A' (s N) S' (s T) (s M)
    have rhs := (multiply_body_at (Γ := Δ) f e' a x').eqTrans (qmul_congr (.eqRefl _) row)
    simpa only [termsEqual,s,a,Δ,d,d',H,J,S,e,e',x,x',j,A',X',D',S',Syn.shift,subst_pairT,subst_data,subst_damping,
      GaussianBinetBoseFrozenMatrix.subst_frozenPiNumerator,GaussianBinetBoseFrozenMatrix.subst_piDenominator,
      subst_realNumerator,subst_realDenominator,
      GaussianBinetSineDampedQuadrature.subst_data,PTm.subst_mul,PTm.subst_add] using
      orig.eqTrans (known.eqTrans rhs.eqSymm)
  let z := sum f M x
  have bind : Γ ⊢[PRAAx] column matrix r M d ≐ qmul e z := by
    change Γ ⊢[PRAAx] sum (columnBody matrix) M (pairT r d) ≐ qmul e z
    have exactSum : Γ ⊢[PRAAx] sum (columnBody matrix) M (pairT r d) ≐ sum (multiplyBody f) M (pairT e x) :=
      GaussianRationalFiniteSum.sum_congr_bounded (columnBody matrix) (multiplyBody f) M (pairT r d) (pairT e x) terms
    exact exactSum.eqTrans (sum_multiply f e M x)
  exact (qmul_congr (.eqRefl w) bind).eqTrans (commute_weights w e z)

theorem transposed_at (r p k i M T X Y D sign R L N cut : PTm n)
    (hcut : Γ ⊢[PRAAx] le one cut) :
    let S := D*L
    let j := cut+r
    Γ ⊢[PRAAx] inst2 transposedBody r
        (transposedData p M T (frozenPiNumerator i k) (piDenominator k) X Y D sign R L N cut) ≐
      qmul (damping p X Y D sign S j N R) (rawFrozenValue (p+N) k i (S*j) N S T M) := by
  let w := weight T one M
  let c : PTm n := fraction two one
  let d := data p M T (frozenPiNumerator i k) (piDenominator k) X Y D sign R L N cut
  let q := column matrix r M d
  let e := damping p X Y D sign (D*L) (cut+r) N R
  let z := GaussianBinetSineDampedQuadrature.value (p+N) (realNumerator k i) (realDenominator k) ((D*L)*(cut+r)) N (D*L) T M
  have first := (multiply_body_at (Γ := Γ) (columnSumBody matrix) (qmul c w) r (pairT M d)).eqTrans
    (qmul_congr (.eqRefl _) (column_sum_at matrix r M d))
  have middle := (qmul_associative c w q).eqTrans
    (qmul_congr (.eqRefl _) (column_weighted_at r p k i M T X Y D sign R L N cut hcut))
  exact first.eqTrans (middle.eqTrans (commute_weights c e z))

theorem actual_weighted_second_Binet_positive_suffix_transpose_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (qmul (fraction two one)
          (suffixValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)) ≐
        transposedValue (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)) :=
  closeUniv 13 (scaled_transpose _ _ _ _ _ _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineTranspose
