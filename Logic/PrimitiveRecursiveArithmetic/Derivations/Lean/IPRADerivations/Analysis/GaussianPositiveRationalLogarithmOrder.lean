import IPRADerivations.Analysis.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.GaussianNamedRealOrderEnvelope

/-!
# Order of the original positive rational logarithm

After bringing two inputs to one denominator, the harmonic samples
compare initial sums at a common factorial scale. The exact sample
comparison gives independent-clock order on the original names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open GaussianCoefficientNameBounds (unit)
open GaussianHarmonicLogarithmName (clock)
open GaussianNameEquivalence (cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (logF data source)
open GaussianRationalHorner (positive_product)
open RationalArgmin (rationalLE rationalLE_congr transitive eq_le)
open RationalHarmonicInterval (interval horizon common common_value numerator at_common)
open RationalValueBounds (upper_of_order)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)
open Products (fact)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem interval_order (a c b Q : PTm n) (h : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] rationalLE (interval a b Q) (interval c b Q) := by
  let L := horizon c b Q
  let D := fact L
  have cover : Γ ⊢[PRAAx] le (horizon a b Q) L :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q (add_le_add_right b h))
  have order := S_mono D (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q h))
  refine rationalLE_congr (at_common a b Q L cover) (.eqRefl _) ?_
  change Γ ⊢[PRAAx] rationalLE (common a b Q L) (common c b Q L)
  have pos := GammaEulerMesh.factorial_positive (Γ := Γ) L
  apply RationalArithmetic.order_of_representations _ _ (numerator a b Q L) (numerator c b Q L)
    D D (common_value _ _ _ _) (common_value _ _ _ _) pos pos
  apply zle_of_toZ (monus (S (Q*c) D) (S (Q*a) D)*D)
  have e := natEq (eq_add_of_le order)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  dsimp only [D] at *
  linear_combination -Groth.ι (IPRA.Q.mk Γ (fact L))*e

theorem observation_order (p a c b : PTm n) (h : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] rationalLE
      (fstT (GaussianHarmonicLogarithmName.sample p a b))
      (fstT (GaussianHarmonicLogarithmName.sample p c b)) := by
  let Q := GammaEulerConstantName.mesh (clock p)
  let L := interval a b Q
  let R := interval c b Q
  have aL : Γ ⊢[PRAAx] fstT (GaussianHarmonicLogarithmName.sample p a b) ≐ RationalArithmetic.recode L :=
    (congrFst (GaussianHarmonicLogarithmName.sample_at p a b)).eqTrans (fst_pair _ _)
  have aR : Γ ⊢[PRAAx] fstT (GaussianHarmonicLogarithmName.sample p c b) ≐ RationalArithmetic.recode R :=
    (congrFst (GaussianHarmonicLogarithmName.sample_at p c b)).eqTrans (fst_pair _ _)
  exact rationalLE_congr aL.eqSymm aR.eqSymm
    (transitive (eq_le (RationalArithmetic.recode_equal L)) (transitive (interval_order a c b Q h)
      (eq_le (RationalArithmetic.recode_equal R).eqSymm)))

private theorem ordered_harmonic (a c b : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (h : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] realOrder GaussianHarmonicLogarithmName.nameF GaussianHarmonicLogarithmName.nameF
      (GaussianHarmonicLogarithmName.data a b) (GaussianHarmonicLogarithmName.data c b) := by
  apply GaussianNamedRealOrderEnvelope.order_from_envelope _ _ _ _ zero
    (GaussianHarmonicLogarithmName.name_regular _ _ ha) (GaussianHarmonicLogarithmName.name_regular _ _ hc)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianNamedRealOrderEnvelope.envelope,GaussianHarmonicLogarithmName.subst_data,GaussianHarmonicLogarithmName.sample,Syn.shift,
    ConciseIPRA.PTm.subst_zero] using upper_of_order _ _ zero (unit (var 0))
      (observation_order (var 0) (Syn.shift a) (Syn.shift c) (Syn.shift b) hs)

theorem logarithm_order (a b c d : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (h : Γ ⊢[PRAAx] le (a*d) (b*c)) :
    Γ ⊢[PRAAx] realOrder logF logF (data a b) (data c d) := by
  let A := a*d
  let C := b*c
  let B := b*d
  have bpos := positive_product _ _ ha.andE₂ hc.andE₂
  have sA : Γ ⊢[PRAAx] source A B := .andI (positive_product _ _ ha.andE₁ hc.andE₂) bpos
  have sC : Γ ⊢[PRAAx] source C B := .andI (positive_product _ _ ha.andE₂ hc.andE₁) bpos
  have l := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper a b A B ha sA (by dsimp [A,B]; ipra_ring)
  have r := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper C B c d sC hc (by dsimp [C,B]; ipra_ring)
  let H := GaussianHarmonicLogarithmName.nameF
  let HL := GaussianHarmonicLogarithmName.data A B
  let HR := GaussianHarmonicLogarithmName.data C B
  have left := GaussianHarmonicLogarithmName.cross_original A B sA
  have right := cross_symm logF H (data C B) HR (GaussianHarmonicLogarithmName.cross_original C B sC)
  exact GaussianNamedRealOrderTransport.transport logF H H logF (data a b) HL HR (data c d)
    (cross_trans logF logF H (data a b) (data A B) HL l left)
    (cross_trans H logF logF HR (data C B) (data c d) right r)
    (ordered_harmonic A C B sA sC h)

theorem actual_positive_rational_logarithm_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) ⟶ source (var 2) (var 3) ⟶ le (var 0*var 3) (var 1*var 2) ⟶
      realOrder logF logF (data (var 0) (var 1)) (data (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (logarithm_order _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmOrder
