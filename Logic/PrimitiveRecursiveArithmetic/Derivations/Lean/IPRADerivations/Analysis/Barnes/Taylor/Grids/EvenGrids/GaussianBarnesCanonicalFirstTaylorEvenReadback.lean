import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalCofinalTaylorEvenGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Cofinal.GaussianBarnesCanonicalCofinalTaylorGridWindows

/-!
# Literal signed quotients in the first two-sided Barnes grid

A refined native center is a packed Gaussian pair. The first two
grid nodes read exactly this center and its translate. The first
parity-weighted grid is the sum of the two raw signed quotients.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstTaylorEvenReadback

open_ipra
open ComplexLogarithmRemainder (add code im re scale zeroCode)
open GaussianBarnesCanonicalCofinalTaylorEvenGridLimit (observed)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinal_at cofinalData cofinalGrid)
open GaussianBarnesCanonicalCofinalTaylorGridWindows (native_shift)
open GaussianNamedDifferenceQuotient (actual_inverse inverse raw separated)
open GaussianPolynomialForwardDifferenceGrid (adjacent adjacent_lookup grid grid_succ grid_zero value)
open GaussianPolynomialForwardDifferenceGridLinearity (normalized_combined)
open GaussianPolynomialForwardDifferenceNormalization (normalized)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents qadd qmul qmul_canonical)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative qnegative_canonical qnegative_represents qsub)
open GaussianRationalReciprocal (reciprocal reciprocal_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qsub_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalTranslationStages (remaining)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "gneg" => ComplexLogarithmRemainder.neg

private theorem code_congr (x y u v : ZT n)
    (hr₁ : Γ ⊢[PRAAx] x.pos ≐ u.pos) (hr₂ : Γ ⊢[PRAAx] x.neg ≐ u.neg)
    (hi₁ : Γ ⊢[PRAAx] y.pos ≐ v.pos) (hi₂ : Γ ⊢[PRAAx] y.neg ≐ v.neg) :
    Γ ⊢[PRAAx] code x y ≐ code u v :=
  Common.congrPairT (Common.congrPairT hr₁ hr₂) (Common.congrPairT hi₁ hi₂)

private theorem zero_node (x y : ZT n) (h : PTm n) :
    Γ ⊢[PRAAx] add (code x y) (scale zero h) ≐ code x y := by
  let X := pairT x.pos x.neg
  let Y := pairT y.pos y.neg
  let Z : PTm n := pairT zero zero
  have scaleZero : Γ ⊢[PRAAx] scale zero h ≐ zeroCode := by
    apply code_congr <;> change Γ ⊢[PRAAx] zero*_+zero*_ ≐ zero <;> ipra_ring
  have padded : Γ ⊢[PRAAx] add (code x y) (scale zero h) ≐ add (code x y) zeroCode := by
    ipra_congr (add (var 0) (var 1) : PTm 2) with [.eqRefl _,scaleZero]
  exact padded.eqTrans (code_congr _ _ _ _
    ((congrAdd ((congrFst (fst_pair X Y)).eqTrans (fst_pair x.pos x.neg))
      ((congrFst (fst_pair Z Z)).eqTrans (fst_pair zero zero))).eqTrans (add_zero _))
    ((congrAdd ((congrSnd (fst_pair X Y)).eqTrans (snd_pair x.pos x.neg))
      ((congrSnd (fst_pair Z Z)).eqTrans (snd_pair zero zero))).eqTrans (add_zero _))
    ((congrAdd ((congrFst (snd_pair X Y)).eqTrans (fst_pair y.pos y.neg))
      ((congrFst (snd_pair Z Z)).eqTrans (fst_pair zero zero))).eqTrans (add_zero _))
    ((congrAdd ((congrSnd (snd_pair X Y)).eqTrans (snd_pair y.pos y.neg))
      ((congrSnd (snd_pair Z Z)).eqTrans (snd_pair zero zero))).eqTrans (add_zero _)))

private theorem unit_node (z h : PTm n) : Γ ⊢[PRAAx] add z (scale one h) ≐ add z h := by
  have shift : Γ ⊢[PRAAx] add z (scale one h) ≐ add z (scale (one+zero) h) := by
    ipra_congr (add (var 0) (scale (var 1) (var 2)) : PTm 3) with
      [.eqRefl _, (add_zero one).eqSymm, .eqRefl _]
  exact shift.eqTrans ((native_shift z h zero).eqTrans (zero_node (re z+re h) (im z+im h) h))

private theorem first_difference (P : PTm n) :
    Γ ⊢[PRAAx] value P one ≐ qsub (entry P one) (entry P zero) := by
  have next : Γ ⊢[PRAAx] adjacent (grid P one zero) (remaining one zero) ≐ adjacent P one := by
    ipra_congr (adjacent (var 0) (var 1) : PTm 2) with [grid_zero P one, monus_zero one] using [remaining]
  exact (entry_congr ((grid_succ P one zero).eqTrans next) (.eqRefl zero)).eqTrans
    (adjacent_lookup P one zero (zero_lt_succ zero))

private theorem normalized_one_at (t z a h R B q : PTm n) :
    Γ ⊢[PRAAx] normalized (cofinalGrid t (scale a z) h R B one) one q ≐
      qmul (reciprocal q) (qsub (ap2 V t (vd (add (scale a z) h) (R+one) B)) (ap2 V t (vd (scale a z) (R+one) B))) := by
  let w := scale a z
  let P := cofinalGrid t w h R B one
  have later : Γ ⊢[PRAAx] ap2 V t (cofinalData w h R B one) ≐ ap2 V t (vd (add w h) (R+one) B) := by
    ipra_congr (ap2 V (var 0) (vd (var 1) (var 2) (var 3)) : PTm 4) with
      [.eqRefl _,unit_node w h,.eqRefl _,.eqRefl _] using [cofinalData]
  have center : Γ ⊢[PRAAx] ap2 V t (cofinalData w h R B zero) ≐ ap2 V t (vd w (R+one) B) := by
    ipra_congr (ap2 V (var 0) (vd (var 1) (var 2) (var 3)) : PTm 4) with
      [.eqRefl _,zero_node (ZT.ofNat a*re z) (ZT.ofNat a*im z) h,.eqRefl _,.eqRefl _] using [cofinalData,w,scale]
  exact qmul_congr (GaussianRationalPowerAlgebra.power_one _ (reciprocal_canonical q))
    ((first_difference P).eqTrans
      (qsub_congr ((cofinal_at t w h R B one one (le_refl (succ one))).eqTrans later)
        ((cofinal_at t w h R B one zero (zero_lt_succ one)).eqTrans center)))

private theorem inverse_negative (h B : PTm n) (hh : Γ ⊢[PRAAx] separated h B) :
    Γ ⊢[PRAAx] inverse (gneg h) B ≐ qnegative (inverse h B) := by
  let q := ofGaussian h B
  let r := ofGaussian (gneg h) B
  let x := inverse h B
  let y := inverse (gneg h) B
  have hn : Γ ⊢[PRAAx] separated (gneg h) B :=
    .andI hh.andE₁ (le_congr (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg h).eqSymm hh.andE₂)
  have sign : Γ ⊢[PRAAx] r ≐ qnegative q :=
    canonical_unique _ _ _ B (ofGaussian_canonical _ _ hh.andE₁) (qnegative_canonical q) hh.andE₁
      (ofGaussian_represents _ _ hh.andE₁) (qnegative_represents _ _ _ (ofGaussian_represents _ _ hh.andE₁))
  have product : Γ ⊢[PRAAx] qmul r (qnegative x) ≐ qone :=
    (qmul_congr sign (.eqRefl _)).eqTrans ((GaussianScalarColumnSelection.negative_both_product q x).eqTrans
      ((qmul_commutative q x).eqTrans (actual_inverse h B hh)))
  exact (qmul_one_right y (reciprocal_canonical r)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl y) product.eqSymm).eqTrans ((qmul_associative y r (qnegative x)).eqSymm.eqTrans
      ((qmul_congr (actual_inverse (gneg h) B hn) (.eqRefl _)).eqTrans
        ((qmul_commutative qone (qnegative x)).eqTrans (qmul_one_right _ (qnegative_canonical x))))))

theorem literal_quotients (t z a h R B : PTm n) (hh : Γ ⊢[PRAAx] separated h B) :
    Γ ⊢[PRAAx] observed t (scale a z) h R B one ≐
      qadd (raw V V t t (vd (add (scale a z) h) (R+one) B) (vd (scale a z) (R+one) B) h B)
        (raw V V t t (vd (add (scale a z) (gneg h)) (R+one) B) (vd (scale a z) (R+one) B) (gneg h) B) := by
  let w := scale a z
  let q := ofGaussian h B
  let x := normalized (cofinalGrid t w h R B one) one q
  let y := qsub (ap2 V t (vd (add w (gneg h)) (R+one) B)) (ap2 V t (vd w (R+one) B))
  let r := reciprocal q
  have plus := (qmul_commutative (Γ := Γ) qone x).eqTrans
    ((qmul_one_right x (qmul_canonical _ _)).eqTrans (normalized_one_at t z a h R B q))
  have sign : Γ ⊢[PRAAx] parityPoint (one : PTm n) ≐ minusOne :=
    (GaussianRationalParityPower.parity_succ zero).eqTrans
      (GaussianInverseBinomialRows.negative_congr GaussianRationalParityPower.parity_zero)
  have factor : Γ ⊢[PRAAx] qmul (parityPoint one) r ≐ inverse (gneg h) B :=
    (qmul_congr sign (.eqRefl r)).eqTrans ((negative_as_minusOne r).eqSymm.eqTrans (inverse_negative h B hh).eqSymm)
  have back := (qmul_congr (.eqRefl (parityPoint one)) (normalized_one_at t z a (gneg h) R B q)).eqTrans
    ((qmul_associative (parityPoint one) r y).eqSymm.eqTrans (qmul_congr factor (.eqRefl y)))
  exact (normalized_combined (cofinalGrid t w h R B one) (cofinalGrid t w (gneg h) R B one)
    qone (parityPoint one) one q).eqTrans (qadd_congr plus back)

theorem actual_Barnes_first_even_grid_quotients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let t := var 0
     let z := var 1
     let a := var 2
     let h := var 3
     let R := var 4
     let B := var 5
     separated h B ⟶ observed t (scale a z) h R B one ≐
       qadd (raw V V t t (vd (add (scale a z) h) (R+one) B) (vd (scale a z) (R+one) B) h B)
         (raw V V t t (vd (add (scale a z) (gneg h)) (R+one) B) (vd (scale a z) (R+one) B) (gneg h) B)) :=
  closeUniv 6 (.impI (literal_quotients _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFirstTaylorEvenReadback
