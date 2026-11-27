import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaEulerReflectionHead
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# Finite products with inverse-square small factors

For K ≥ max(1,2C), the actual product of r factors starting at index K
has distance from one at most 2Cr/(K(K+r)), when the factor at index i
is within C/(i+1)² of one. The induction maintains a bound of two for
each partial product. This gives a sharp finite bound for the literal
tail of the sine product on every encoded disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianInverseSquareProductTail

open_ipra
open GaussianRationalFiniteProduct (qprod product_zero product_succ offset_at product_canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qadd_sub_cancel)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul)
open GaussianRationalMetric (qnegative qnegative_canonical qsub bounded bounded_iff distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono norm_from_distance_same)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_negative qone_bounded)
open GaussianGammaEulerReflectionHead (body squareFactor square_factor_at)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianRationalPowerDifference (distance_refl_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def product (f : PTm 2) (K r x : PTm n) : PTm n := qprod (offB f) r (pairT K x)

def tailBound (f : PTm 2) (x C K r : PTm n) : Fm PTm n :=
  distanceBounded (product f K r x) qone (two*C*r) (K*(K+r))

ipra_subst product

ipra_subst tailBound

def factorBounds (f : PTm 2) (x C K : PTm n) : Fm PTm n := .all
  (distanceBounded (inst2 f (Syn.shift K+var 0) (Syn.shift x)) qone
    (Syn.shift C) (succ (Syn.shift K+var 0)*succ (Syn.shift K+var 0)))

ipra_subst factorBounds [Syn.subst_shift, Syn.shift_subst]

theorem factor_bound_at (f : PTm 2) (x C K r : PTm n) (h : Γ ⊢[PRAAx] factorBounds f x C K) :
    Γ ⊢[PRAAx] distanceBounded (inst2 f (K+r) x) qone C (succ (K+r)*succ (K+r)) := by
  simpa only [factorBounds,GaussianRationalMetric.subst_distanceBounded,GaussianRationalSyntheticDivision.subst_qone,
    ConciseIPRA.PTm.subst_succ,PTm.subst_mul,PTm.subst_add,subst_inst2,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift] using h.allE r

theorem denominator_positive (K r : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] le one (K*(K+r)) := positive_product _ _ hK (le_trans hK (le_add_right K r))

theorem product_succ_at (f : PTm 2) (x K r : PTm n) :
    Γ ⊢[PRAAx] product f K (succ r) x ≐ qmul (product f K r x) (inst2 f (K+r) x) :=
  (product_succ (offB f) r (pairT K x)).eqTrans (qmul_congr (.eqRefl _) (offset_at f K r x))

theorem tail_zero (f : PTm 2) (x C K : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] tailBound f x C K zero :=
  distance_congr (product_zero (offB f) (pairT K x)).eqSymm (.eqRefl _) (mul_zero _).eqSymm (.eqRefl _)
    (distance_refl_zero qone (K*(K+zero)) (denominator_positive K zero hK))

theorem partial_product_bound (f : PTm 2) (x C K r : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hC : Γ ⊢[PRAAx] le (two*C) K)
    (h : Γ ⊢[PRAAx] tailBound f x C K r) :
    Γ ⊢[PRAAx] bounded (product f K r x) two one := by
  let P := product f K r x
  have mid : Γ ⊢[PRAAx] le (K*r) (K*(K+r)) :=
    le_congr (mul_comm r K) (mul_comm (K+r) K) (mul_le_mul_right K (le_add_left r K))
  have compare : Γ ⊢[PRAAx] le ((two*C*r)*one) (one*(K*(K+r))) :=
    le_congr (by ipra_ring) (by ipra_ring) (le_trans (mul_le_mul_right r hC) mid)
  have close := distance_radius_mono P qone (two*C*r) (K*(K+r)) one one
    (denominator_positive K r hK) (le_refl one) compare h
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (norm_from_distance_same (le_refl one) close qone_bounded)

theorem tail_succ (f : PTm 2) (x C K r : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hC : Γ ⊢[PRAAx] le (two*C) K)
    (hf : Γ ⊢[PRAAx] factorBounds f x C K)
    (h : Γ ⊢[PRAAx] tailBound f x C K r) :
    Γ ⊢[PRAAx] tailBound f x C K (succ r) := by
  let P := product f K r x
  let F := inst2 f (K+r) x
  let k := succ (K+r)
  let D := K*(K+r)
  let E := k*k
  have hD := denominator_positive (Γ := Γ) K r hK
  have hE := positive_product (Γ := Γ) k k (zero_lt_succ _) (zero_lt_succ _)
  have small : Γ ⊢[PRAAx] bounded (qmul P (qsub F qone)) (two*C) E := by
    exact bound_congr (.eqRefl _) (.eqRefl _) (one_mul E)
      (bounded_product P (qsub F qone) two one C E (le_refl one) hE
        (partial_product_bound f x C K r hK hC h) (factor_bound_at f x C K r hf))
  have e : Γ ⊢[PRAAx] distanceBounded (qmul P F) P (two*C) E :=
    distance_congr (.eqRefl _) (qmul_one_right P (product_canonical _ _ _)) (.eqRefl _) (.eqRefl _)
      (bound_congr (GaussianRationalRoundedPower.multiplication_difference P F qone).eqSymm
        (.eqRefl _) (.eqRefl _) small)
  have combined := GaussianReconstructionRoots.distance_triangle (qmul P F) P qone
    (two*C) E (two*C*r) D hE hD e h
  have scaled := distance_radius_mono (qmul P F) qone (two*C*D+two*C*r*E) (E*D)
    (two*C*succ r) (K*(K+succ r)) (positive_product _ _ hE hD) (denominator_positive K (succ r) hK)
    (le_of_eq_add (d := two*C*K*K*k) (by dsimp only [D,E,k]; ipra_ring)) combined
  exact distance_congr (product_succ_at f x K r).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) scaled

theorem sharp_tail (f : PTm 2) (x C K r : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hC : Γ ⊢[PRAAx] le (two*C) K)
    (hf : Γ ⊢[PRAAx] factorBounds f x C K) :
    Γ ⊢[PRAAx] tailBound f x C K r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] factorBounds f (Syn.shift x) (Syn.shift C) (Syn.shift K) := by
    simpa [Fm.shift,Syn.shift] using hf.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift,Syn.shift] using hK.shift
  have hc : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift C) (Syn.shift K) := by
    simpa [Fm.shift,Syn.shift] using hC.shift
  have law : Γ ⊢[PRAAx] .all (tailBound f (Syn.shift x) (Syn.shift C) (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_tailBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using tail_zero f x C K hK
    · simpa only [subst_tailBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        tail_succ f (Syn.shift x) (Syn.shift C) (Syn.shift K) (var 0) hk.wk hc.wk hs.wk Prf.hyp0
  simpa only [subst_tailBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using law.allE r

theorem sine_factor_bound (i z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] distanceBounded (squareFactor i z B) qone (R*R) (succ i*succ i) := by
  let j := succ i
  let E := B*j
  let p := ofGaussian z E
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hE := positive_product B j hB hj
  have q : Γ ⊢[PRAAx] bounded p R j := (bounded_iff p z E R j hE hj (ofGaussian_represents _ _ hE)).iffMpr
    (le_congr (by ipra_ring) (by dsimp only [E]; ipra_ring) (mul_le_mul_right (j*j) hz))
  have sq := bounded_product p p R j R j hj hj q q
  exact bound_congr (qadd_sub_cancel qone (qnegative (qmul p p)) (qnegative_canonical _)).eqSymm
    (.eqRefl _) (.eqRefl _) (bounded_negative _ _ _ (positive_product j j hj hj) sq)

theorem sine_product_tail (z R B K r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hK : Γ ⊢[PRAAx] le one K) (hR : Γ ⊢[PRAAx] le (two*(R*R)) K) :
    Γ ⊢[PRAAx] tailBound body (pairT z B) (R*R) K r := by
  apply sharp_tail _ _ _ _ _ hK hR
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hd : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  refine .allI ?_
  simpa only [factorBounds,Syn.shift,subst_pairT,PTm.subst_mul] using
    distance_congr (square_factor_at (Syn.shift K+var 0) (Syn.shift z) (Syn.shift B)).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (sine_factor_bound (Syn.shift K+var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hb hd)

theorem actual_inverse_square_product_tail_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (two*var 1) (var 2) ⟶ factorBounds f (var 0) (var 1) (var 2) ⟶
      tailBound f (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (sharp_tail _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_sine_product_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      le one (var 3) ⟶ le (two*(var 1*var 1)) (var 3) ⟶
      tailBound body (pairT (var 0) (var 2)) (var 1*var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (sine_product_tail _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianInverseSquareProductTail
