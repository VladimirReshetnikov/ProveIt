import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.Mesh.GaussianStirlingAllOrderBernoulliMeshRefinement

/-!
# A fixed positive separation margin for the centered Bernoulli mesh

The actual values at 1/8 and 3/8 differ by a strictly positive
rational. Their literal difference gives a uniform finite margin
between the two corresponding mesh boxes on every refinement.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMeshMargin

open_ipra
open GaussianStirlingAllOrderBernoulliMeshRefinement (sample_refinement)
open GaussianStirlingAllOrderBernoulliShape (centeredShape centered_shape_has_positive)
open GaussianStirlingAllOrderBernoulliShapeClearing
  (degree scale scale_positive coefficient coefficient_value value left right cleared_identity)
open GaussianStirlingAllOrderBernoulliMeshOrder (sample_monotone)
open GaussianStirlingAllOrderCenteredBernoulli
  (numerator denominator sample sample_value sample_canonical denominator_positive factor)
open GaussianStirlingAllOrderBernoulliMesh (homogeneous toZ_value)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open BernoulliBounds (bden bden_pos zint toZ_zint)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalArgmin (rationalLE rationalLE_congr transitive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

noncomputable def difference (m : ℕ) : ℤ :=
  factor (m+1)*(homogeneous (2*(m+1)) (3:ℤ) 8-homogeneous (2*(m+1)) 1 8)

private theorem value_strict (m : ℕ) : value m (28:ℤ) 64 < value m 60 64 := by
  obtain ⟨i,hi,hpos⟩ := centered_shape_has_positive m
  have hd : i ≤ degree m := by
    by_contra! h
    have e : (centeredShape m).coeff i=0 := Polynomial.coeff_eq_zero_of_natDegree_lt h
    rw [e] at hpos
    linarith only [hpos]
  let j : Fin (degree m+1) := ⟨i,Nat.lt_succ_iff.mpr hd⟩
  have hp : 0 < coefficient m j := by
    have e := coefficient_value m j
    have s : (0:ℚ)<scale m := by exact_mod_cast scale_positive m
    have r : (0:ℚ)<(coefficient m j : ℚ) := by rw [e]; exact mul_pos hpos s
    exact_mod_cast r
  unfold value
  refine Finset.sum_lt_sum (fun k _ => ?_) ⟨j,Finset.mem_univ _,?_⟩
  · have p : (28:ℤ)^(k : ℕ)≤60^(k : ℕ) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p (by positivity)) (by positivity)
  · have p : (28:ℤ)^(j : ℕ)<60^(j : ℕ) := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by simpa [j] using hi)
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left p (by exact_mod_cast hp)) (by positivity)

theorem difference_positive (m : ℕ) : 0 < difference m := by
  let j := 2*(m+1)
  have h1 := cleared_identity m (1:ℤ) 8
  have h3 := cleared_identity m (3:ℤ) 8
  unfold left right at h1 h3
  norm_num at h1 h3
  have shifted : (scale m : ℤ)*64^(degree m)*difference m =
      (bden j:ℤ)*8^j*(value m (60:ℤ) 64-value m (28:ℤ) 64) := by
    unfold difference j
    linear_combination h3-h1
  have hd : (0:ℤ)<bden j := by exact_mod_cast bden_pos j
  apply pos_of_mul_pos_right (a := (scale m : ℤ)*64^(degree m))
  · rw [shifted]
    exact mul_pos (mul_pos hd (by positivity)) (sub_pos.mpr (value_strict m))
  · positivity

def coarseDen (m : ℕ) : PTm n := denominator (m+1) (num 8)
noncomputable def margin (m : ℕ) : PTm n := normalize (zint (difference m)) (coarseDen m)

private theorem coarse_den_positive (m : ℕ) : Γ ⊢[PRAAx] le one (coarseDen m : PTm n) :=
  denominator_positive (m+1) (num 8) (by ipra_le 7)

theorem positive_margin (m : ℕ) :
    Γ ⊢[PRAAx] rationalLE (fraction one (coarseDen m)) (margin m) := by
  let D : PTm n := coarseDen m
  have hD := coarse_den_positive (Γ := Γ) m
  apply RationalArithmetic.order_of_representations _ _ _ _ D D
    (fraction_represents one D hD) (normalize_preserves_value _ _ hD) hD hD
  let k := (difference m-1).toNat
  have e : ((k:ℕ):ℤ) = difference m-1 := Int.toNat_of_nonneg (by have := difference_positive m; omega)
  apply zle_of_toZ (num k*D)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint,IPRA.Q.mk_one,map_one,IPRA.Q.mk_mul,map_mul,IPRA.Q.mk_num,map_natCast]
  have transformed := congrArg (fun z : ℤ => (z : Groth (IPRA.Q Γ))) e
  push_cast at transformed
  linear_combination Groth.ι (IPRA.Q.mk Γ D)*transformed

private theorem numerator_gap_identity (m : ℕ) :
    Γ ⊢[PRAAx] ZT.eq (numerator (m+1) one (num 8)+zint (difference m)) (numerator (m+1) (num 3) (num 8)) := by
  apply ZT.derive
  let j := 2*(m+1)
  have liftValue (x y : ℤ) :
      ((homogeneous j x y : ℤ) : Groth (IPRA.Q Γ)) = homogeneous j (x : Groth (IPRA.Q Γ)) (y : Groth (IPRA.Q Γ)) := by
    change Int.castRingHom (Groth (IPRA.Q Γ)) (homogeneous j x y) = _
    simp [homogeneous]
  have h1 : ((homogeneous (2*(m+1)) (1:ℤ) 8 : ℤ) : Groth (IPRA.Q Γ)) =
      homogeneous (2*(m+1)) (1:Groth (IPRA.Q Γ)) 8 := by
    exact_mod_cast liftValue 1 8
  have h3 : ((homogeneous (2*(m+1)) (3:ℤ) 8 : ℤ) : Groth (IPRA.Q Γ)) =
      homogeneous (2*(m+1)) (3:Groth (IPRA.Q Γ)) 8 := by
    exact_mod_cast liftValue 3 8
  simp only [numerator,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_sub,toZ_zint,toZ_value,
    IPRA.Q.mk_one,map_one,IPRA.Q.mk_num,map_natCast,difference,Int.cast_mul,Int.cast_sub,
    h1,h3]
  ring

theorem exact_center_gap (m : ℕ) :
    Γ ⊢[PRAAx] RationalArithmetic.add (sample (m+1) one (num 8)) (margin m) ≐ sample (m+1) (num 3) (num 8) := by
  let A : PTm n := sample (m+1) one (num 8)
  let B : PTm n := sample (m+1) (num 3) (num 8)
  let D : PTm n := coarseDen m
  let h : PTm n := margin m
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have hD := coarse_den_positive (Γ := Γ) m
  have rep := RationalRepresentations.represents_add A h _ _ D D (sample_value (m+1) one _ h8)
    (normalize_preserves_value _ _ hD)
  apply RationalFiniteSum.canonical_equal _ B _ _ (D*D) D (RationalArithmetic.add_guard A h)
    (sample_canonical (m+1) (num 3) _ h8) rep (sample_value (m+1) (num 3) _ h8) (positive_product _ _ hD hD) hD
  apply ZT.derive
  have e := ZT.toZ_eq (numerator_gap_identity (Γ := Γ) m)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add,IPRA.Q.mk_mul,map_mul] at e ⊢
  linear_combination (Groth.ι (IPRA.Q.mk Γ D))^2 * e

theorem separated_mesh_margin (m : ℕ) (S p q : PTm n) (hS : Γ ⊢[PRAAx] le one S)
    (hp : Γ ⊢[PRAAx] le p (S*one)) (hq : Γ ⊢[PRAAx] le (S*num 3) q) (hMq : Γ ⊢[PRAAx] le (two*q) (S*num 8)) :
    Γ ⊢[PRAAx] rationalLE (RationalArithmetic.add (sample (m+1) p (S*num 8)) (margin m))
      (sample (m+1) q (S*num 8)) := by
  let M := S*num 8
  let a := S*one
  let b := S*num 3
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS h8
  have ha : Γ ⊢[PRAAx] le (two*a) M := by unfold a M; ipra_le 6*Groth.ι (IPRA.Q.mk Γ S)
  have lo := sample_monotone m p a M hM hp ha
  have hi := sample_monotone m b q M hM hq hMq
  have d : Γ ⊢[PRAAx] RationalArithmetic.add (sample (m+1) a M) (margin m) ≐ sample (m+1) b M :=
    (RationalAlgebra.add_congr (sample_refinement (m+1) S one (num 8) hS h8) (.eqRefl _)).eqTrans
      ((exact_center_gap m).eqTrans (sample_refinement (m+1) S (num 3) (num 8) hS h8).eqSymm)
  have ref : Γ ⊢[PRAAx] rationalLE (margin m) (margin m) := le_refl _
  exact transitive (rationalLE_congr (.eqRefl _) d
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ lo ref)) hi

theorem actual_strict_Bernoulli_grid_box_margin_closed (m : ℕ) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ (le (var 1) (var 0*one) ⋏ (le (var 0*num 3) (var 2) ⋏ le (two*var 2) (var 0*num 8)))) ⟶
       rationalLE (RationalArithmetic.add (sample (m+1) (var 1) (var 0*num 8)) (margin m))
         (sample (m+1) (var 2) (var 0*num 8))) :=
  closeUniv 3 (.impI (separated_mesh_margin m _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliMeshMargin
