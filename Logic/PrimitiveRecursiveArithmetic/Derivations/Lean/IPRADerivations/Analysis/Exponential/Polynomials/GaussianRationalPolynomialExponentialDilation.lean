import IPRADerivations.Analysis.Exponential.Polynomials.GaussianRationalPolynomialExponentialRecomposition
import IPRADerivations.Analysis.Polynomials.Products.GaussianPolynomialLowPrefix
import IPRADerivations.Analysis.Polynomials.Representation.GaussianRationalPolynomialDilation

/-!
# Dilation and weighted exponential recomposition

Substituting t*z in the original exponent is equivalent to evaluating the
stored dilated exponent at z. The same substitution commutes with the
original finite exponential program and with its low-degree truncation.
The weighted norm can therefore supply the remainder constant uniformly
through a sequence of growing exponent degrees.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialDilation

open_ipra
open GaussianEuclideanDistanceName (fraction)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianRationalGridCoefficientEquality (gridEqual coefficient_equal)
open GaussianRationalHorner (evaluate qmul qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialDilation (dilated weightedNorm dilation_evaluation dilated_length dilated_canonical)
open GaussianRationalPolynomialExponential (polynomial polynomial_length polynomial_canonical polynomial_evaluation scalarSum)
open GaussianRationalPowerExpansion (partialSum terms terms_lookup)
open GaussianRationalSyntheticDivision (canonicalCoefficients qmul_congr qmul_zero_left)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem source_constant (C N t : PTm n) (hZero : Γ ⊢[PRAAx] entry C N ≐ qzero) : Γ ⊢[PRAAx]
    entry (dilated C N t) N ≐ qzero :=
  (GaussianRationalPolynomialDilation.dilated_lookup C N t N (le_refl N)).eqTrans
    ((qmul_congr hZero (.eqRefl _)).eqTrans (qmul_zero_left _))

theorem source_data (C N t z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialExponentialRecomposition.data (dilated C N t) z ≐
      GaussianRationalPolynomialExponentialRecomposition.data C (qmul t z) :=
  Common.congrPairT (.eqRefl _) (dilation_evaluation C N t z hC)

theorem exponential_evaluation (C N K t z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (polynomial (dilated C N t) N K) z ≐ evaluate (dilated (polynomial C N K) (K*N) t) z := by
  have law := GaussianRationalFiniteSum.sum_index_congr (Γ := Γ) GaussianRationalPolynomialExponential.scalarBody
    (.eqRefl (succ K)) (dilation_evaluation C N t z hC)
  exact (polynomial_evaluation _ N K z (dilated_length C N t)).eqTrans
    (law.eqTrans ((polynomial_evaluation C N K (qmul t z) hC).eqSymm.eqTrans
      (dilation_evaluation (polynomial C N K) (K*N) t z (polynomial_length C N K)).eqSymm))

private theorem exponential_grid (C N K t : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    gridEqual (polynomial (dilated C N t) N K) (dilated (polynomial C N K) (K*N) t) (K*N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  refine .allI (.impI ?_)
  let Δ := le (var 0) (Syn.shift (K*N)) :: Γ.map Fm.shift
  simpa only [Δ,Syn.shift,GaussianRationalPolynomialDilation.subst_dilated,
    GaussianRationalPolynomialExponential.subst_polynomial,LeanProofs.IPRA.PTm.subst_mul] using
    exponential_evaluation (Syn.shift C) (Syn.shift N) (Syn.shift K) (Syn.shift t)
      (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hs.wk

theorem exponential_coefficient (C N K t i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i (K*N)) : Γ ⊢[PRAAx]
    entry (polynomial (dilated C N t) N K) i ≐ entry (dilated (polynomial C N K) (K*N) t) i :=
  coefficient_equal _ _ _ i (polynomial_length _ _ _) (dilated_length _ _ _)
    (polynomial_canonical _ _ _) (dilated_canonical _ _ _) (exponential_grid C N K t hC) hi

theorem prefix_coefficient (C N K m t e : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] le m (K*N)) (he : Γ ⊢[PRAAx] le e m) : Γ ⊢[PRAAx]
    entry (GaussianPolynomialLowPrefix.polynomial (polynomial (dilated C N t) N K) (K*N) m) (monus m e) ≐
      entry (dilated (GaussianPolynomialLowPrefix.polynomial (polynomial C N K) (K*N) m) m t) (monus m e) := by
  let E := polynomial C N K
  let M := K*N
  let i := monus M e
  have hi : Γ ⊢[PRAAx] le i M := Common.monus_le_self M e
  have degree := GaussianRationalMonicReconstruction.complement M e (le_trans he hm)
  exact (GaussianPolynomialLowPrefix.original_reader _ M m e he).eqTrans
    ((exponential_coefficient C N K t i hC hi).eqTrans
      ((GaussianRationalPolynomialDilation.dilated_lookup E M t i hi).eqTrans
        ((qmul_congr (.eqRefl _) (congrAp2 GaussianRationalReciprocal.powerF degree (.eqRefl _))).eqTrans
          (GaussianPolynomialLowPrefix.dilated_original_reader E M m t e he).eqSymm)))

theorem prefix_value (C N m t z : PTm n) (hm : Γ ⊢[PRAAx] le m (m*N))
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialExponentialRecomposition.value (dilated C N t) N m z ≐
      GaussianRationalPolynomialExponentialRecomposition.value C N m (qmul t z) := by
  let E := polynomial C N m
  let F := polynomial (dilated C N t) N m
  let M := m*N
  change Γ ⊢[PRAAx] partialSum F M z (succ m) ≐ partialSum E M (qmul t z) (succ m)
  refine GaussianRationalSumSegments.prefix_entries_congr
    (terms F M z) (terms E M (qmul t z)) (succ m) (succ m) (.allI (.impI ?_)) (le_refl _)
  have hL : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have hD : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift m) (Syn.shift m*Syn.shift N) := by
    simpa only [Fm.shift,subst_le,LeanProofs.IPRA.PTm.subst_mul,Syn.shift] using hm.shift
  let Δ := lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift
  let c := Syn.shift C
  let d := Syn.shift N
  let k := Syn.shift m
  let a := Syn.shift t
  let w := Syn.shift z
  have hi : Δ ⊢[PRAAx] le (var 0) k := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have he : Δ ⊢[PRAAx] le (var 0) (k*d) := le_trans hi hD.wk
  have eq := (terms_lookup (Γ := Δ) (polynomial (dilated c d a) d k) (k*d) w (var 0) he).eqTrans
    ((qmul_congr (exponential_coefficient c d k a _ hL.wk
      (GaussianRationalMonicReconstruction.monus_le_left _ _)) (.eqRefl _)).eqTrans
      ((GaussianRationalPolynomialDilation.term_dilated (polynomial c d k) (k*d) a w (var 0) he).eqTrans
        (terms_lookup (polynomial c d k) (k*d) (qmul a w) (var 0) he).eqSymm))
  simpa only [E,F,M,Δ,c,d,k,a,w,Syn.shift,GaussianRationalPowerExpansion.subst_terms,
    GaussianRationalPolynomialDilation.subst_dilated,GaussianRationalPolynomialExponential.subst_polynomial,
    GaussianRationalHorner.subst_qmul,ConciseIPRA.PTm.subst_succ,LeanProofs.IPRA.PTm.subst_mul] using eq

open GaussianRationalPolynomialExponentialRecomposition (nameF data value numerator denominator input)

theorem rate_data_congr (F G : PR 2) (x y x' y' A D : PTm n)
    (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y')
    (h : Γ ⊢[PRAAx] independentRate F G x y A D) : Γ ⊢[PRAAx] independentRate F G x' y' A D := by
  simpa only [subst_independentRate,Syn.subst_var,Matrix.cons_val] using
    Prf.eqSubst (independentRate F G (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
      ![x,y,A,D] ![x',y',A,D]
      (fun i => by fin_cases i; exact hx; exact hy; exact .eqRefl _; exact .eqRefl _)
      (by simpa only [subst_independentRate,Syn.subst_var,Matrix.cons_val] using h)

theorem uniform_rate (C N m t z H B L : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hZero : Γ ⊢[PRAAx] entry C N ≐ qzero)
    (hD : Γ ⊢[PRAAx] le m (m*N)) (hB : Γ ⊢[PRAAx] le one B) (hHB : Γ ⊢[PRAAx] le H B)
    (hSmall : Γ ⊢[PRAAx] le (two*(L*H)) B) (hMass : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (fraction L one))
    (hz : Γ ⊢[PRAAx] bounded z H B) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data C (qmul t z)) (value C N m (qmul t z))
      (numerator m L (pw (num 3) L) H) (denominator m B) := by
  let W := dilated C N t
  let A := numerator m L (pw (num 3) L) H
  let D := denominator m B
  have src : Γ ⊢[PRAAx] input W N m z H B L :=
    .andI (dilated_length C N t) (.andI (source_constant C N t hZero) (.andI hD (.andI hB
      (.andI hHB (.andI hSmall (.andI hMass hz))))))
  exact rate_data_congr nameF constantF (data W z) (value W N m z) (data C (qmul t z)) (value C N m (qmul t z)) A D
    (source_data C N t z hC) (prefix_value C N m t z hD hC)
    (GaussianRationalPolynomialExponentialRecomposition.uniform_rate W N m z H B L src (dilated_canonical C N t))

theorem actual_weighted_exponential_recomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let C := var 0
     let N := var 1
     let m := var 2
     let t := var 3
     let z := var 4
     let H := var 5
     let B := var 6
     let L := var 7
     ((length C ≐ succ N) ⋏ ((entry C N ≐ qzero) ⋏ (le m (m*N) ⋏ (le one B ⋏ (le H B ⋏
       (le (two*(L*H)) B ⋏ (rationalLE (weightedNorm C N t) (fraction L one) ⋏ bounded z H B))))))) ⟶
       independentRate nameF constantF (data C (qmul t z)) (value C N m (qmul t z))
         (numerator m L (pw (num 3) L) H) (denominator m B)) :=
  closeUniv 8 (.impI (uniform_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialDilation
