import IPRADerivations.Analysis.Stirling.GaussianStirlingOddGridTelescope
import IPRADerivations.Analysis.Stirling.GaussianStirlingDifference
import IPRADerivations.Analysis.Euler.GaussianHarmonicLogarithmName

/-!
# The unreduced odd series brackets the original logarithm

The raw odd terms are evaluated at (B/(2A+B)), without a range
restriction other than positive (A). Harmonic rectangle comparison
and the original logarithm compatibility remove the finite grid and
cutoff errors with explicit clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOddLogBrackets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Un Ud low_mono log_name Ud_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos pos_of_one_le)
open GaussianStirlingOddGrid (parameter gap numerator denominator square_split parameter_positive denominator_positive)
open GaussianStirlingOddGridTelescope (grid_telescope)
open GammaMeshRobinLogBridge (leftSum rightSum rectangle_balance left_sum_bound)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (logF)
open Products (fact)
open RationalHarmonicInterval (horizon interval)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def logLower (A B K : PTm n) : PTm n := fraction (numerator A K B) (denominator A K B)
def logUpper (A B K : PTm n) : PTm n :=
  fraction (Un K B (parameter A B) (gap A B)) (Ud K B (parameter A B) (gap A B))

@[simp] theorem subst_logLower {l : ℕ} (σ : Fin n → PTm l) (A B K : PTm n) :
    Syn.subst σ (logLower A B K) = logLower (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [logLower,fraction]
@[simp] theorem subst_logUpper {l : ℕ} (σ : Fin n → PTm l) (A B K : PTm n) :
    Syn.subst σ (logUpper A B K) = logUpper (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [logUpper,Un,Ud,Dz,parameter,gap,fraction]

theorem gap_positive (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le one (gap A B) :=
  RationalAlgebra.positive_product (RationalAlgebra.positive_product (by ipra_le 3) hA)
    (le_trans hA (le_add_right _ _))

theorem upper_denominator_positive (A B K : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (Ud K B (parameter A B) (gap A B)) :=
  le_congr (.eqRefl _) (Ud_pos (pos_of_one_le (parameter_positive A B hA))
    (pos_of_one_le (gap_positive A B hA)) K B).eqSymm (zero_lt_succ _)

private theorem frame_value (A B Q : PTm n) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (interval (A+B) A Q)
      (ZT.ofNat (rightSum (Q*A) (Q*B) (fact (horizon (A+B) A Q)))) (fact (horizon (A+B) A Q)) := by
  let L := horizon (A+B) A Q
  let F := fact L
  have a : Γ ⊢[PRAAx] Q*(A+B) ≐ Q*A+Q*B := by ipra_ring
  have b : Γ ⊢[PRAAx] S (Q*(A+B)) F ≐ S (Q*A) F+rightSum (Q*A) (Q*B) F :=
    (congrAp2 (sumF hB) a (.eqRefl F)).eqTrans (sum_split hB (Q*A) (Q*B) F)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (RationalHarmonicInterval.common_value (A+B) A Q L)
  apply ZT.derive
  have eq := natEq b
  simp only [ZT.toZ_ofNat]
  simp only [RationalHarmonicInterval.numerator,ZT.toZ]
  dsimp only [F,L] at eq
  ipra_simps
  linear_combination eq

private theorem scale_value (A B Q K : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] logLower (Q*A) (Q*B) K ≐ logLower A B K := by
  let t := Q*B
  let s := parameter (Q*A) t
  let u := parameter A B
  have e : Γ ⊢[PRAAx] t*u ≐ B*s := by dsimp [t,s,u,parameter]; ipra_ring
  have l := low_mono (le_congr (.eqRefl _) e (le_refl _)) K
  have r := low_mono (le_congr (.eqRefl _) e.eqSymm (le_refl _)) K
  have both : Γ ⊢[PRAAx] Nz K t s*Dz K B u ≐ Nz K B u*Dz K t s := le_antisymm l r
  have a := denominator_positive (Q*A) K t (RationalAlgebra.positive_product hQ hA)
  have b := denominator_positive A K B hA
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ a) (RationalNormalForm.normalize_well_formed _ _ b)
    (fraction_represents _ _ a) (fraction_represents _ _ b) a b
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simpa only [numerator,denominator,IPRA.Q.mk_mul,map_mul,t,s,u] using natEq both

private theorem finite_grid (A B Q G K : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hQ : Γ ⊢[PRAAx] le one Q) (hK : Γ ⊢[PRAAx] le one K) (hGK : Γ ⊢[PRAAx] le (G*(Q*B)) K) :
    Γ ⊢[PRAAx] upper (logLower A B K) (interval (A+B) A Q) one Q ⋏
      upper (interval (A+B) A Q) (logLower A B K) B G := by
  let X := Q*A
  let T := Q*B
  let L := horizon (A+B) A Q
  let F := fact L
  let l := leftSum X T F
  let r := rightSum X T F
  let u := numerator X K T
  let d := denominator X K T
  have hX : Γ ⊢[PRAAx] le one X := RationalAlgebra.positive_product hQ hA
  have hL : Γ ⊢[PRAAx] le (X+T) L := by dsimp [X,T,L,horizon]; ipra_le 𝔞 Q*𝔞 A
  have pre := grid_telescope X G K L T hX hK hGK hL
  have bal : Γ ⊢[PRAAx] le l (r+quo F X) := le_of_eq_add (rectangle_balance X T F hX)
  have q := natEq (GammaEulerMesh.factorial_quotient X L hX
    (le_trans (le_add_right X T) hL))
  have a : Γ ⊢[PRAAx] le (X*F*u) (X*r*d+F*d) := by
    ipra_le 𝔞 X*sl pre.andE₁+𝔞 X*𝔞 d*sl bal using linear_combination -𝔞 d*q
  have hB : Γ ⊢[PRAAx] le T (X*B) := by dsimp [X,T]; ipra_le 𝔞 Q*𝔞 B*sl hA
  have left : Γ ⊢[PRAAx] le l (B*F) := by
    ipra_le sl (left_sum_bound X T F hX)+𝔞 (quo F X)*sl hB using linear_combination -𝔞 B*q
  have b : Γ ⊢[PRAAx] le (G*r*d) (F*G*u+B*F*d) := by
    ipra_le sl pre.andE₂+𝔞 d*sl left
  have pd := denominator_positive X K T hX
  have pf := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have gv := fraction_represents u d pd
  have hv := frame_value (Γ := Γ) A B Q
  have first : Γ ⊢[PRAAx] upper (logLower X T K) (interval (A+B) A Q) one X := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ pd pf gv hv
    apply zle_of_toZ (monus (X*r*d+F*d) (X*F*u))
    have e := natEq (eq_add_of_le a)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    linear_combination -e
  have second : Γ ⊢[PRAAx] upper (interval (A+B) A Q) (logLower X T K) B G := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ _ _ _ _ pf pd hv gv
    apply zle_of_toZ (monus (F*G*u+B*F*d) (G*r*d))
    have e := natEq (eq_add_of_le b)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    linear_combination -e
  have scale := scale_value A B Q K hA hQ
  have cost : Γ ⊢[PRAAx] le (one*Q) (one*X) := by dsimp [X]; ipra_le 𝔞 Q*sl hA
  exact .andI (upper_mono _ _ _ _ _ _ hX
    (upper_congr scale (.eqRefl _) (.eqRefl _) (.eqRefl _) first) cost)
    (upper_congr (.eqRefl _) scale (.eqRefl _) (.eqRefl _) second)

private theorem nested (A B K J : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (logLower A B K) (logLower A B (K+J)) ⋏
    RationalArgmin.rationalLE (logLower A B (K+J)) (logUpper A B K) := by
  have nest := log_name (pos_of_one_le (parameter_positive A B hA)) (pos_of_one_le (gap_positive A B hA))
    (square_split A B) K J
  have h := denominator_positive A K B hA
  have hl := denominator_positive A (K+J) B hA
  have hi := upper_denominator_positive A B (K+J) hA
  have ht := upper_denominator_positive A B K hA
  exact .andI (GaussianEuclideanDistanceName.fraction_order _ _ _ _ h hl (le_congr (mul_comm _ _) (.eqRefl _) nest.andE₁.andE₁))
    (RationalArgmin.transitive (GaussianEuclideanDistanceName.fraction_order _ _ _ _ hl hi (le_congr (mul_comm _ _) (.eqRefl _) nest.andE₂))
      (GaussianEuclideanDistanceName.fraction_order _ _ _ _ hi ht (le_congr (mul_comm _ _) (.eqRefl _) nest.andE₁.andE₂)))

private theorem harmonic_brackets (A B K t : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    upper (logLower A B K) (fstT (GaussianHarmonicLogarithmName.sample t (A+B) A)) one (unit t) ⋏
    upper (fstT (GaussianHarmonicLogarithmName.sample t (A+B) A)) (logUpper A B K) B (unit t) := by
  let c := GaussianHarmonicLogarithmName.clock t
  let Q := GammaEulerConstantName.mesh c
  let G := unit t
  let J := G*(Q*B)+one
  let H := interval (A+B) A Q
  have hQ := GammaEulerConstantName.mesh_positive (Γ := Γ) c
  have hK : Γ ⊢[PRAAx] le one (K+J) := by dsimp [J]; ipra_le 𝔞 K+𝔞 G*𝔞 (Q*B)
  have hJ : Γ ⊢[PRAAx] le (G*(Q*B)) (K+J) := by dsimp [J]; ipra_le 𝔞 K+1
  have f := finite_grid A B Q G (K+J) hA hQ hK hJ
  have br := nested A B K J hA
  have hclock : Γ ⊢[PRAAx] le t c := le_add_right _ _
  have clock_unit : Γ ⊢[PRAAx] le G (unit c) := GaussianBalancedRadiusArithmetic.unit_monotone t c hclock
  have mesh_eq : Γ ⊢[PRAAx] Q ≐ num 4*unit c := .eqRefl _
  have hmesh : Γ ⊢[PRAAx] le (one*G) (one*Q) := by
    have em := natEq mesh_eq
    ipra_le sl clock_unit+3*𝔞 (unit c) using linear_combination em
  have l := RationalValueBounds.upper_order_left _ _ _ _ _ br.andE₁ f.andE₁
  have r := RationalValueBounds.upper_order_right _ _ _ _ _ f.andE₂ br.andE₂
  have read : Γ ⊢[PRAAx] fstT (GaussianHarmonicLogarithmName.sample t (A+B) A) ≐ H := by
    have e := (congrFst (GaussianHarmonicLogarithmName.sample_at (Γ := Γ) t (A+B) A)).eqTrans (fst_pair _ _)
    exact e.eqTrans (RationalNormalForm.normalize_idempotent _ _ (GammaEulerMesh.factorial_positive _))
  exact .andI (upper_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _)
    (upper_mono _ _ _ _ _ _ hQ l hmesh)) (upper_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) r)

theorem original_log_brackets (A B K p : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    upper (logLower A B K) (fstT (ap2 logF p (GaussianStirlingDifference.logData A B))) one (unit p) ⋏
    upper (fstT (ap2 logF p (GaussianStirlingDifference.logData A B))) (logUpper A B K) one (unit p) := by
  let x := GaussianStirlingDifference.logData A B
  let H := GaussianHarmonicLogarithmName.nameF
  let y := GaussianHarmonicLogarithmName.data (A+B) A
  let obs := fstT (ap2 logF p x)
  let a := logLower A B K
  let b := logUpper A B K
  have cr := GaussianHarmonicLogarithmName.cross_original (A+B) A (.andI (le_trans hA (le_add_right A B)) hA)
  refine .andI ?_ ?_
  · let t := GaussianNamedRealOrderTransport.precision a obs (unit p) two
    have d := GaussianNameEquivalence.cross_at H logF y x t p (GaussianNameEquivalence.cross_symm _ _ _ _ cr)
    have rad := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
      (RationalAlgebra.positive_product (unit_positive t) (unit_positive p)) d
    have up := upper_of_radius _ _ _ _ rad
    have flat := upper_triangle _ _ _ _ _ _ _ (harmonic_brackets A B K t hA).andE₁ up
    apply GaussianNamedRealOrderTransport.remove_upper_slack a obs one (unit p) two
    exact upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product (unit_positive t)
      (RationalAlgebra.positive_product (unit_positive t) (unit_positive p))) flat
      (le_of_eq_add (d := zero) (by ipra_ring))
  · let C := B+one
    let t := GaussianNamedRealOrderTransport.precision obs b (unit p) C
    have d := GaussianNameEquivalence.cross_at H logF y x t p (GaussianNameEquivalence.cross_symm _ _ _ _ cr)
    have rad := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
      (RationalAlgebra.positive_product (unit_positive t) (unit_positive p)) d
    have up := upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ rad)
    have flat := upper_triangle _ _ _ _ _ _ _ up (harmonic_brackets A B K t hA).andE₂
    apply GaussianNamedRealOrderTransport.remove_upper_slack obs b one (unit p) C
    exact upper_mono _ _ _ _ _ _ (RationalAlgebra.positive_product
      (RationalAlgebra.positive_product (unit_positive t) (unit_positive p)) (unit_positive t)) flat
      (le_of_eq_add (d := zero) (by dsimp [C]; ipra_ring))

end LeanProofs.IPRA.Analysis.GaussianStirlingOddLogBrackets
