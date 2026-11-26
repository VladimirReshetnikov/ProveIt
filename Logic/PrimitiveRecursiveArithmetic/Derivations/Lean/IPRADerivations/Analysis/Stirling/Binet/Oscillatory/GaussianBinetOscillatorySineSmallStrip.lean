import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetSineQuotientMajorant
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetOscillatorySineRectangle

/-!
# The small positive strip of the original damped sine quadrature

The original first cell has the exact removable value. The original
later clock absorbs the mesh reciprocal at every positive cell. The
weighted prefix is bounded by its actual length times a uniform row
majorant, including when the prefix is empty.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineSmallStrip

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (scale oneCode normSq)
open GaussianBinetOscillatoryColumns (damping)
open GaussianBinetOscillatorySineRectangle (body data row_at)
open GaussianBinetOscillatorySineRows (value value_at_zero value_at_positive)
open GaussianBinetOscillatorySineQuotient (quotient)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product qadd qmul qzero ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound constantBody)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def numerator (p A B : PTm n) : PTm n := num 8*A*unit p+num 8*B

def prefixValue (p X Y D sign A B R U L N M : PTm n) : PTm n :=
  qmul (weight (D*L) one N) (sum body M (data p X Y D sign A B R U L N))

def suffixValue (p X Y D sign A B R U L N M : PTm n) : PTm n :=
  qmul (weight (D*L) one N) (sum (offB body) (monus N M) (pairT M (data p X Y D sign A B R U L N)))

@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (p X Y D sign A B R U L N M : PTm n) :
    Syn.subst σ (prefixValue p X Y D sign A B R U L N M) = prefixValue (Syn.subst σ p) (Syn.subst σ X)
      (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R)
      (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) (Syn.subst σ M) := by simp [prefixValue,one]

@[simp] theorem subst_suffixValue {m : ℕ} (σ : Fin n → PTm m) (p X Y D sign A B R U L N M : PTm n) :
    Syn.subst σ (suffixValue p X Y D sign A B R U L N M) = suffixValue (Syn.subst σ p) (Syn.subst σ X)
      (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R)
      (Syn.subst σ U) (Syn.subst σ L) (Syn.subst σ N) (Syn.subst σ M) := by simp [suffixValue,one]

theorem split_value (p X Y D sign A B R U L N M : PTm n) (hM : Γ ⊢[PRAAx] le M N) : Γ ⊢[PRAAx]
    GaussianBinetOscillatorySineRectangle.value p X Y D sign A B R U L N ≐
      qadd (prefixValue p X Y D sign A B R U L N M) (suffixValue p X Y D sign A B R U L N M) := by
  let d := data p X Y D sign A B R U L N
  let w := weight (D*L) one N
  let J := monus N M
  have s := (GaussianRationalFiniteSum.sum_index_congr body (eq_add_of_le hM) (.eqRefl d)).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split body M J d)
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) s).eqTrans
    (GaussianRationalCoefficientScaling.qmul_add w (sum body M d) (sum (offB body) J (pairT M d)))

theorem suffix_row_at (j p X Y D sign A B R U L N M : PTm n) : Γ ⊢[PRAAx]
    inst2 (offB body) j (pairT M (data p X Y D sign A B R U L N)) ≐ value (M+j) p X Y D sign A B R U L N :=
  (GaussianRationalFiniteProduct.offset_at body M j _).eqTrans (row_at (M+j) p X Y D sign A B R U L N)

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p A B : PTm n) :
    Syn.subst σ (numerator p A B) = numerator (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ B) := by simp [numerator]

private theorem fraction_bound (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] bounded (fraction a b) a b := by
  let z := scale a oneCode
  have nz : Γ ⊢[PRAAx] normSq z ≐ a*a := (ComplexLogarithmRemainder.normSq_scale a oneCode).eqTrans
    ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring))
  exact bounded_of_cleared _ z b a b hb hb (ofGaussian_represents _ _ hb)
    (le_congr (congrMul (.eqRefl _) nz.eqSymm) (by ipra_ring) (le_refl ((b*b)*(a*a))))

theorem row_bound (j p X Y D sign A B R U L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L)
    (hA : Γ ⊢[PRAAx] le A (B*U)) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    bounded (value j p X Y D sign A B R U L N) (numerator p A B) (B*unit p) := by
  let P := unit p
  let T := D*L
  let C := U*T
  have hP := unit_positive (Γ := Γ) p
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ hz.andE₁.andE₂ hL
  have hBP : Γ ⊢[PRAAx] le one (B*P) := positive_product _ _ hB hP
  have tj : Γ ⊢[PRAAx] le (T*j) (T*N) := le_congr (mul_comm j T) (mul_comm N T) (mul_le_mul_right T hj)
  have angle : Γ ⊢[PRAAx] le (A*(T*j)) (C*(B*N)) :=
    le_congr (.eqRefl _) (by dsimp only [C,T]; ipra_ring) (le_mul_mono hA tj)
  refine .orE (zero_or_succ j) ?_ ?_
  · let Δ := (j ≐ zero) :: Γ
    have e := value_at_zero (Γ := Δ) j p X Y D sign A B R U L N Prf.hyp0
    exact bounded_radius_mono _ _ _ _ _ hB.wk hBP.wk
      (by dsimp only [numerator,P]; ipra_le 7*𝔞 A*𝔞 B*𝔞(unit p)+8*𝔞 B^2)
      (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) (fraction_bound A B hB.wk))
  · let Δ := (j ≐ succ (pred j)) :: Γ
    have pos : Δ ⊢[PRAAx] le one j := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have e := value_at_positive j p X Y D sign A B R U L N pos
    have sinc := GaussianBinetSineQuotientMajorant.clocked_mesh_bound p A B C T j N hB.wk hT.wk pos hN.wk angle.wk
    have src := GaussianBinetLaplaceExponential.exponent_bound (Γ := Δ) X Y D sign R T (T*j) N hz.wk hN.wk tj.wk
    have exp : Δ ⊢[PRAAx] bounded (damping p X Y D sign T j N R) two one :=
      GaussianBinetExponentialPanel.unit_bound (p+N) _ _ (GaussianSignedNameExponentialOrder.constant_input _ _ src)
        (GaussianBinetLaplaceExponential.exponent_nonpositive X Y D sign (T*j) N hz.andE₁.andE₂.wk hN.wk)
    exact bound_congr e.eqSymm (by dsimp only [numerator]; ipra_ring) (one_mul _)
      (bounded_product _ _ two one (num 4*A*unit p+num 4*B) (B*unit p) (le_refl one) hBP.wk exp sinc)

theorem prefix_bound (p X Y D sign A B R U L N M E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (hL : Γ ⊢[PRAAx] le one L) (hA : Γ ⊢[PRAAx] le A (B*U)) (hM : Γ ⊢[PRAAx] le M N)
    (hE : Γ ⊢[PRAAx] le one E) (hsmall : Γ ⊢[PRAAx] le (((D*L)*M)*E) N) : Γ ⊢[PRAAx]
    bounded (prefixValue p X Y D sign A B R U L N M) (numerator p A B) (E*(B*unit p)) := by
  let T := D*L
  let d := data p X Y D sign A B R U L N
  let C := numerator p A B
  let H := B*unit p
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ hB (unit_positive p)
  have rows : Γ ⊢[PRAAx] termsDistance body constantBody M d qzero C H := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift
    have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hB.shift
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift
    have ls : Δ ⊢[PRAAx] le one (s L) := by simpa [Δ,s,Fm.shift,Syn.shift] using hL.shift
    have as' : Δ ⊢[PRAAx] le (s A) (s B*s U) := by simpa [Δ,s,Fm.shift,Syn.shift] using hA.shift
    have ms : Δ ⊢[PRAAx] le (s M) (s N) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift
    have hs : Δ ⊢[PRAAx] le one (s B*unit (s p)) := positive_product _ _ bs (unit_positive _)
    have j : ((lt (var 0) (s M)) :: Δ) ⊢[PRAAx] le (var 0) (s N) := le_trans (le_of_lt Prf.hyp0) ms.wk
    have b := row_bound (var 0) (s p) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
      zs.wk bs.wk ns.wk ls.wk as'.wk j
    have read := row_at (Γ := (lt (var 0) (s M)) :: Δ) (var 0) (s p) (s X) (s Y) (s D) (s sign) (s A) (s B) (s R) (s U) (s L) (s N)
    simpa only [d,C,H,s,Δ,Syn.shift,GaussianRationalHorner.subst_qzero,GaussianRationalRiemannRefinement.constant_entry,
      GaussianBinetOscillatorySineRectangle.subst_data,subst_numerator,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul] using
      (GaussianReconstructionRoots.distance_zero_iff _ _ _ hs.wk).iffMpr (bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) b)
  have z : Γ ⊢[PRAAx] sum constantBody M qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero M).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value M)
  have sums : Γ ⊢[PRAAx] bounded (sum body M d) (M*C) H :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ hH).iffMp
      (distance_congr (.eqRefl _) z (.eqRefl _) (.eqRefl _) (sum_distance _ _ _ _ _ _ _ hH rows))
  have hD := positive_product _ _ (le_refl (Γ := Γ) one) hN
  have scaled := bounded_product _ _ T (one*N) (M*C) H hD hH (weight_bound T one N (le_refl one) hN) sums
  have cut : Γ ⊢[PRAAx] le ((T*(M*C))*(E*H)) (C*((one*N)*H)) :=
    le_congr (by dsimp only [T]; ipra_ring) (by ipra_ring) (mul_le_mul_right (C*H) hsmall)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hH) (positive_product _ _ hE hH) cut scaled

theorem discard_prefix_error (p X Y D sign A B R U L N M E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (hL : Γ ⊢[PRAAx] le one L) (hA : Γ ⊢[PRAAx] le A (B*U)) (hM : Γ ⊢[PRAAx] le M N)
    (hE : Γ ⊢[PRAAx] le one E) (hsmall : Γ ⊢[PRAAx] le (((D*L)*M)*E) N) : Γ ⊢[PRAAx]
    distanceBounded (GaussianBinetOscillatorySineRectangle.value p X Y D sign A B R U L N)
      (suffixValue p X Y D sign A B R U L N M) (numerator p A B) (E*(B*unit p)) := by
  let a := prefixValue p X Y D sign A B R U L N M
  let b := suffixValue p X Y D sign A B R U L N M
  have eq := (GaussianRationalSyntheticDivision.qsub_congr (split_value p X Y D sign A B R U L N M hM) (.eqRefl b)).eqTrans
    ((GaussianRationalSyntheticDivision.qsub_congr (GaussianReciprocalHorner.qadd_commutative a b) (.eqRefl b)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel b a (GaussianRationalHorner.qmul_canonical _ _)))
  exact bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _)
    (prefix_bound p X Y D sign A B R U L N M E hz hB hN hL hA hM hE hsmall)

end LeanProofs.IPRA.Analysis.GaussianBinetOscillatorySineSmallStrip
