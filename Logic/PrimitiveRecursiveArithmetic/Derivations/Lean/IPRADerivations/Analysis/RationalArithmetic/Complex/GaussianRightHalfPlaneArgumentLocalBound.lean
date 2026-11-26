import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRightHalfPlaneArgument
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentSlope

/-!
# Quantitative bound for the original small-chart argument

The finite upper slope at the zero endpoint bounds the actual arctangent
prefix by twice the input slope. Halving and signed chart selection keep
that exact radius at every observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentLocalBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BaselQuadrature (Qb)
open ComplexLogarithmRemainder (oneCode scale mul normSq normSq_eval eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (prefixValue total source)
open GaussianArctangentPartialQuadrature (mesh clearing mesh_positive observation_source)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianRationalHorner (ofGaussian_represents qmul qmul_represents positive_product)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr)
open GaussianRightHalfPlaneArgument (smallF smallData unsignedF unsignedData wide wide_zero largeF largeData)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "atanF" => GaussianArctangentPartialQuadrature.nameF
local notation "atData" => GaussianArctangentPartialQuadrature.data
local notation "H" => GaussianRightHalfPlaneArgument.half
local notation "F" => GaussianRightHalfPlaneArgument.nameF
local notation "X" => GaussianRightHalfPlaneArgument.data

private theorem total_bound (j M L : PTm n) (hs : Γ ⊢[PRAAx] source M L) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] le (M*total j M L) (j*fact L) := by
  have h := (GaussianArctangentSlope.finite_slope zero j M L hs (le_congr (zero_add _).eqSymm (.eqRefl _) hj)).andE₂
  have e : Γ ⊢[PRAAx] total zero M L ≐ zero := sum_zero Qb (pairT M L)
  have left : Γ ⊢[PRAAx] M*total (zero+j) M L ≐ M*total j M L :=
    congrMul (.eqRefl M) (congrAp2 (sumF Qb) (zero_add j) (.eqRefl (pairT M L)))
  have right : Γ ⊢[PRAAx] M*total zero M L+j*fact L ≐ j*fact L :=
    (congrAdd (congrMul (.eqRefl M) e) (.eqRefl _)).eqTrans
      ((congrAdd (mul_zero M) (.eqRefl _)).eqTrans (zero_add _))
  exact le_congr left right h

private theorem half_prefix_bound (j M L : PTm n)
    (hs : Γ ⊢[PRAAx] source M L) (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] bounded (qmul H (prefixValue j M L)) j M := by
  let T := two*total j M L
  let a := scale T imaginaryCode
  let v := mul oneCode a
  let D := two*fact L
  have hf := GaussianRationalPolynomialExponential.factorial_positive (Γ := Γ) L
  have ht : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ ht hf
  have r := qmul_represents H (prefixValue j M L) oneCode a two (fact L) ht hf
    (ofGaussian_represents _ _ ht) (ofGaussian_represents _ _ hf)
  have norm : Γ ⊢[PRAAx] normSq v ≐ T*T := by
    apply deriveNat
    rw [normSq_eval]
    simp only [v,a,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_one,
      GaussianRootAlgebra.im_one,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,imaginaryCode,
      eval_re_code,eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  have k : Γ ⊢[PRAAx] le (M*T) (j*D) :=
    le_congr (by dsimp only [T]; ipra_ring) (by dsimp only [D]; ipra_ring)
      (le_mul_mono (le_refl two) (total_bound j M L hs hj))
  apply bounded_of_cleared _ v D j M hd hs.andE₁ r
  exact le_congr
    ((by ipra_ring : Γ ⊢[PRAAx] (M*T)*(M*T) ≐ (M*M)*(T*T)).eqTrans
      (congrMul (.eqRefl (M*M)) norm.eqSymm))
    (by ipra_ring) (le_mul_mono k k)

theorem small_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (ap2 smallF p (smallData A B)) B A := by
  let k := GaussianBoundedConstantProductName.clock p one
  let N := mesh k
  let M := A*N
  let j := B*N
  let L := clearing M
  have nm : Γ ⊢[PRAAx] le one N := mesh_positive k
  have hs : Γ ⊢[PRAAx] source M L := observation_source A N hA nm
  have c := half_prefix_bound j M L hs (le_mul_mono hB (le_refl N))
  have read := GaussianArctangentPartialQuadrature.sample_at (Γ := Γ) k B A
  have e := (GaussianBoundedConstantProductName.sample_at (Γ := Γ) atanF p one H (atData B A)).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl H) read)
  exact bounded_radius_mono _ j M B A hs.andE₁ hA
    (le_congr (by dsimp only [j,M]; ipra_ring) (.eqRefl _) (le_refl (B*M)))
    (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) c)

private theorem unsigned_bound (p A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] bounded (ap2 unsignedF p (unsignedData A B)) B A := by
  have e := (GaussianNameBranch.sample_at (Γ := Γ) smallF largeF p
    (wide A B) (smallData A B) (largeData A B)).eqTrans
      (RationalArithmetic.select_zero _ _ _ (wide_zero A B hB))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) (small_bound p A B hA hB)

theorem sample_bound (p A B neg : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A)
    (hs : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] bounded (ap2 F p (X A B neg)) B A := by
  let g := GaussianNameConjugation.nameF unsignedF
  let x := unsignedData A B
  have e := GaussianNameBranch.sample_at (Γ := Γ) unsignedF g p neg x x
  have u := unsigned_bound p A B hA hB
  refine .orE hs ?_ ?_
  · have r := e.wk.eqTrans (RationalArithmetic.select_zero _ _ _ Prf.hyp0)
    exact bound_congr r.eqSymm (.eqRefl _) (.eqRefl _) u.wk
  · have r := (e.wk.eqTrans (RationalArithmetic.select_one _ _ _ Prf.hyp0)).eqTrans
      (GaussianNameConjugation.sample_at _ _ _)
    exact bound_congr r.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalConjugation.point_bound _ _ _ hA.wk u.wk)

theorem one_seventh (p A B neg : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le (num 7*B) A) (hs : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] bounded (ap2 F p (X A B neg)) one (num 7) := by
  have se : Γ ⊢[PRAAx] le one (num 7 : PTm n) := by ipra_le 6
  have hb := le_trans (le_congr (one_mul _) (.eqRefl _) (le_mul_mono se (le_refl B))) hB
  exact bounded_radius_mono _ _ _ _ _ hA se (le_congr (mul_comm _ _) (one_mul _).eqSymm hB)
    (sample_bound p A B neg hA hb hs)

theorem actual_right_half_plane_small_argument_radius_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ (le (var 2) (var 1) ⋏ ((var 3 ≐ zero) ⋎ (var 3 ≐ one)))) ⟶
        bounded (ap2 F (var 0) (X (var 1) (var 2) (var 3))) (var 2) (var 1)) :=
  closeUniv 4 (.impI (sample_bound _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentLocalBound
