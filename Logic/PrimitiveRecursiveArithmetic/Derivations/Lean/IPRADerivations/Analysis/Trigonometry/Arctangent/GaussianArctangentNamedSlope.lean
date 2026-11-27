import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentSlope
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentNamedChord
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalUpperAddition

/-!
# Slope of the actual partial arctangent names

Two rational endpoints are represented on the same refined grid. For
original queries p and q, the shared point count is the product of
their two meshes. Refining each query spends exactly its own dyadic
tolerance. The finite slope bounds therefore transfer to those queries
with their original two-precision error.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentNamedSlope

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open BaselQuadrature (Qb)
open ComplexLogarithmRemainder (eval_im_code)
open GaussianRootAlgebra (im_scale)
open GaussianArctangentCayleyValues (imaginaryCode)
open GaussianArctangentExponentialPrefix (prefixValue total subst_prefixValue)
open GaussianArctangentNamedChord (imaginary_coordinate_radius)
open GaussianArctangentPartialQuadrature (observation clearing nameF data mesh sample_at mesh_positive finite_refinement
  subst_clearing subst_observation)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product ofGaussian_represents scalar_congr)
open GaussianRationalMetric (distanceBounded comparison_of_cleared)
open GaussianRationalPolynomialExponential (factorial_positive)
open Products (fact)
open RationalArithmetic (represents add)
open RationalArgmin (rationalLE)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalValueBounds (positive_cancel radius_symmetric upper upper_congr upper_of_order upper_of_radius
  upper_order_right upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gapNumerator (A B C D : PTm n) : PTm n := monus (C*B) (A*D)
def gap (A B C D : PTm n) : PTm n := fraction (gapNumerator A B C D) (B*D)
def twiceGap (A B C D : PTm n) : PTm n := fraction (two*gapNumerator A B C D) (B*D)
def ordinate (p A B : PTm n) : PTm n := sndT (ap2 nameF p (data A B))

private theorem prefix_represents (j M L : PTm n) : Γ ⊢[PRAAx]
    represents (sndT (prefixValue j M L)) (ZT.ofNat (two*total j M L)) (fact L) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ (factorial_positive L)).andE₂
  apply ZT.derive
  simp only [im_scale,imaginaryCode,eval_im_code,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem add_fraction_represents (a x E K F : PTm n)
    (ha : Γ ⊢[PRAAx] represents a (ZT.ofNat x) E) (hF : Γ ⊢[PRAAx] le one F) :
    Γ ⊢[PRAAx] represents (add a (fraction K F)) (ZT.ofNat (x*F+K*E)) (E*F) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (RationalRepresentations.represents_add _ _ _ _ _ _ ha (fraction_represents K F hF))
  apply ZT.derive
  simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,Q.mk_mul,map_add,map_mul]

private theorem prefix_congr {j M k S : PTm n}
    (hj : Γ ⊢[PRAAx] j ≐ k) (hM : Γ ⊢[PRAAx] M ≐ S) :
    Γ ⊢[PRAAx] prefixValue j M (clearing M) ≐ prefixValue k S (clearing S) := by
  simpa only [subst_prefixValue,subst_clearing,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (prefixValue (var 0) (var 1) (clearing (var 1)) : PTm 2)
      (σ := ![j,M]) (σ' := ![k,S]) (fun i => by fin_cases i; exact hj; exact hM))

theorem common_grid_order (A B C D N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hC : Γ ⊢[PRAAx] le C D)
    (hord : Γ ⊢[PRAAx] le (A*D) (C*B)) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (add (sndT (observation A B (D*N))) (gap A B C D)) (sndT (observation C D (B*N))) ⋏
      rationalLE (sndT (observation C D (B*N))) (add (sndT (observation A B (D*N))) (twiceGap A B C D)) := by
  let E := B*D
  let G := gapNumerator A B C D
  let M := E*N
  let j := A*D*N
  let k := G*N
  let r := C*B*N
  let L := clearing M
  let F := fact L
  let x := sndT (prefixValue j M L)
  let y := sndT (prefixValue r M L)
  let X := two*total j M L
  let Y := two*total r M L
  have hE := positive_product B D hB hD
  have hM := positive_product E N hE hN
  have hF := factorial_positive (Γ := Γ) L
  have hEnd : Γ ⊢[PRAAx] j+k ≐ r :=
    (by dsimp only [j,k]; ipra_ring : Γ ⊢[PRAAx] j+k ≐ (A*D+G)*N).eqTrans
      (congrMul (eq_add_of_le hord).eqSymm (.eqRefl _))
  have hr : Γ ⊢[PRAAx] le r M :=
    le_congr (.eqRefl _) (by dsimp only [M,E]; ipra_ring)
      (le_mul_mono (le_mul_mono hC (le_refl B)) (le_refl N))
  have totalEnd : Γ ⊢[PRAAx] total (j+k) M L ≐ total r M L :=
    congrAp2 (sumF Qb) hEnd (.eqRefl _)
  have slopes := GaussianArctangentSlope.finite_slope j k M L (.andI hM (le_refl _))
    (le_congr hEnd.eqSymm (.eqRefl _) hr)
  have lower : Γ ⊢[PRAAx] le (X*E+G*F) (Y*E) := by
    apply positive_cancel hN
    exact le_congr (by dsimp only [X,M,k,F]; ipra_ring)
      ((congrMul (.eqRefl (two*M)) totalEnd).eqTrans (by dsimp only [Y,M]; ipra_ring)) slopes.andE₁
  have upper : Γ ⊢[PRAAx] le (Y*E) (X*E+(two*G)*F) := by
    apply positive_cancel hN
    exact le_congr ((congrMul (.eqRefl two) (congrMul (.eqRefl M) totalEnd)).eqTrans
      (by dsimp only [Y,M]; ipra_ring)) (by dsimp only [X,M,k,F]; ipra_ring)
      (le_mul_mono (le_refl two) slopes.andE₂)
  have hx : Γ ⊢[PRAAx] represents x (ZT.ofNat X) F := prefix_represents j M L
  have hy : Γ ⊢[PRAAx] represents y (ZT.ofNat Y) F := prefix_represents r M L
  have low := comparison_of_cleared (add x (fraction G E)) y (X*E+G*F) Y (F*E) F
    (positive_product F E hF hE) hF (add_fraction_represents x X F G E hx hE) hy
    (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_refl F) lower))
  have high := comparison_of_cleared y (add x (fraction (two*G) E)) Y (X*E+(two*G)*F) F (F*E)
    hF (positive_product F E hF hE) hy (add_fraction_represents x X F (two*G) E hx hE)
    (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl F) upper))
  have leftRead : Γ ⊢[PRAAx] prefixValue j M L ≐ observation A B (D*N) :=
    prefix_congr (by dsimp only [j]; ipra_ring) (by dsimp only [M,E]; ipra_ring)
  have rightRead : Γ ⊢[PRAAx] prefixValue r M L ≐ observation C D (B*N) :=
    prefix_congr (by dsimp only [r]; ipra_ring) (by dsimp only [M,E]; ipra_ring)
  have leftAdd (K : PTm n) : Γ ⊢[PRAAx] add x K ≐ add (sndT (observation A B (D*N))) K :=
    (RationalArithmetic.add_at x K).eqSymm.eqTrans
      ((congrAp2 RationalArithmetic.addF (congrSnd leftRead) (.eqRefl K)).eqTrans (RationalArithmetic.add_at _ _))
  exact .andI (RationalArgmin.rationalLE_congr (leftAdd _) (congrSnd rightRead) low)
    (RationalArgmin.rationalLE_congr (congrSnd rightRead) (leftAdd _) high)

private theorem refined_query (p A B R N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) (hR : Γ ⊢[PRAAx] le one R)
    (hre : Γ ⊢[PRAAx] R*mesh p ≐ N) :
    Γ ⊢[PRAAx] distanceBounded (observation A B N) (ap2 nameF p (data A B)) one (unit p) := by
  have first : Γ ⊢[PRAAx] observation A B (R*mesh p) ≐ observation A B N := by
    simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
      (Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![A,B,R*mesh p]) (σ' := ![A,B,N])
        (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact hre))
  have den := mesh_positive (Γ := Γ) p
  have raw := finite_refinement A B (mesh p) R hB hA den hR
  exact distance_congr first (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ den (unit_positive p)
      (le_of_eq_add (d := zero) (by unfold mesh; ipra_ring)) raw)

private theorem translate_upper (a b c A B : PTm n) (h : Γ ⊢[PRAAx] upper a b A B) :
    Γ ⊢[PRAAx] upper (add a c) (add b c) A B :=
  upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (RationalUpperAddition.add_upper a b c c A B zero one h
      (upper_of_order c c zero one (RationalArgmin.reflexive _)))

def slopeBound (p q A B C D : PTm n) : Fm PTm n :=
  upper (add (ordinate p A B) (gap A B C D)) (ordinate q C D) (unit p+unit q) (unit p*unit q) ⋏
    upper (ordinate q C D) (add (ordinate p A B) (twiceGap A B C D)) (unit p+unit q) (unit p*unit q)

theorem named_slope_at (p q A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hA : Γ ⊢[PRAAx] le A B) (hC : Γ ⊢[PRAAx] le C D)
    (hord : Γ ⊢[PRAAx] le (A*D) (C*B)) :
    Γ ⊢[PRAAx] slopeBound p q A B C D := by
  let N := mesh p*mesh q
  let x := sndT (observation A B (D*N))
  let y := sndT (observation C D (B*N))
  let u := ordinate p A B
  let v := ordinate q C D
  let P := unit p
  let Q := unit q
  let g := gap A B C D
  let g2 := twiceGap A B C D
  have hN := positive_product _ _ (mesh_positive (Γ := Γ) p) (mesh_positive q)
  have comparison := common_grid_order A B C D N hB hD hC hord hN
  have left := refined_query p A B (D*mesh q) (D*N) hB hA
    (positive_product _ _ hD (mesh_positive q)) (by dsimp only [N]; ipra_ring)
  have right := refined_query q C D (B*mesh p) (B*N) hD hC
    (positive_product _ _ hB (mesh_positive p)) (by dsimp only [N]; ipra_ring)
  have xdist := imaginary_coordinate_radius _ _ _ _ (unit_positive p) left
  have ydist := imaginary_coordinate_radius _ _ _ _ (unit_positive q) right
  have early : Γ ⊢[PRAAx] upper (add u g) y one P :=
    upper_order_right _ _ _ _ _
      (translate_upper u x g one P (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ xdist))) comparison.andE₁
  have late : Γ ⊢[PRAAx] upper v (add x g2) one Q :=
    upper_order_right _ _ _ _ _ (upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ ydist)) comparison.andE₂
  refine .andI ?_ ?_
  · exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (upper_triangle _ _ _ _ _ _ _ early (upper_of_radius _ _ _ _ ydist))
  · exact upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (mul_comm Q P)
      (upper_triangle _ _ _ _ _ _ _ late (translate_upper x u g2 one P (upper_of_radius _ _ _ _ xdist)))

theorem actual_partial_arctangent_named_slope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le one (var 5) ⟶ le (var 2) (var 3) ⟶ le (var 4) (var 5) ⟶
      le (var 2*var 5) (var 4*var 3) ⟶ slopeBound (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (named_slope_at _ _ _ _ _ _ hyp2.wk.wk hyp2.wk hyp2 Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianArctangentNamedSlope
