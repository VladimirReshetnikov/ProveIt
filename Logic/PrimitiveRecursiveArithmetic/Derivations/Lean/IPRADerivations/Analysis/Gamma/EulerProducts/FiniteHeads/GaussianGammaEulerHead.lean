import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalReciprocal
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmCompositionName

/-!
# The finite polynomial head in the Euler and Gamma products

The stream entry at index i is literally 1+(z/B)/(i+1), with i internal
to the original product fold. Multiplying the fold by z/B gives the
polynomial head in C5 and C7. The original Euclidean disk yields the
polynomial part R(1+R)^(2R) of the C9 majorant.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHead

open_ipra
open GaussianRationalFiniteProduct (qprod product_zero product_succ product_split)
open GaussianRationalHorner (qadd qmul ofGaussian ofGaussian_represents positive_product canonical)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalReciprocal (bound_congr bounded_sum bounded_product_one qone_bounded)
open GaussianRationalMetric (bounded bounded_iff)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (z B : PTm n) : PTm n := pairT z B

def factor (i z B : PTm n) : PTm n := qadd qone (ofGaussian z (B*succ i))

def factorBody : PTm 2 := factor (var 0) (fstT (var 1)) (sndT (var 1))

def product (z B N : PTm n) : PTm n := qprod factorBody N (data z B)

def head (z B N : PTm n) : PTm n := qmul (ofGaussian z B) (product z B N)

ipra_subst factor

ipra_subst data

ipra_subst product

ipra_subst head

theorem factor_at (i z B : PTm n) :
    Γ ⊢[PRAAx] inst2 factorBody i (data z B) ≐ factor i z B := by
  ipra_congr (factor (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl i, (show _ ⊢[PRAAx] fstT (data z B) ≐ z from fst_pair _ _),
      (show _ ⊢[PRAAx] sndT (data z B) ≐ B from snd_pair _ _)] using [factorBody, inst2]

theorem product_step (z B N : PTm n) :
    Γ ⊢[PRAAx] product z B (succ N) ≐ qmul (product z B N) (factor N z B) :=
  (product_succ factorBody N (data z B)).eqTrans (qmul_congr (.eqRefl _) (factor_at _ _ _))

theorem head_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] head z B zero ≐ ofGaussian z B :=
  (qmul_congr (.eqRefl _) (product_zero factorBody (data z B))).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB))

theorem head_succ (z B N : PTm n) : Γ ⊢[PRAAx]
    head z B (succ N) ≐ qmul (head z B N) (factor N z B) :=
  (qmul_congr (.eqRefl _) (product_step z B N)).eqTrans (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm

theorem head_split (z B N K : PTm n) : Γ ⊢[PRAAx]
    head z B (N+K) ≐ qmul (head z B N) (qprod (offB factorBody) K (pairT N (data z B))) :=
  (qmul_congr (.eqRefl _) (product_split factorBody N K (data z B))).eqTrans
    (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm

theorem fraction_disk (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (ofGaussian z B) R one := by
  apply (bounded_iff _ _ _ _ _ hB (le_refl _) (ofGaussian_represents _ _ hB)).iffMpr
  exact le_congr (by ipra_ring) (by ipra_ring) hz

theorem factor_bound (i z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (factor i z B) (one+R) one := by
  let E := B*succ i
  have hi : Γ ⊢[PRAAx] le one (succ i) := (succ_monus_succ zero i).eqTrans (zero_le _)
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hB hi
  have es : Γ ⊢[PRAAx] le (R*B) (R*E) :=
    le_congr (by ipra_ring) (by dsimp only [E]; ipra_ring) (mul_le_mul_right (R*B) hi)
  have hex := fraction_disk z R E hE (ComplexLogarithmRemainder.bounded_mono hz es)
  exact bound_congr (.eqRefl _) (by ipra_ring) (one_mul one)
    (bounded_sum qone (ofGaussian z E) one one R one (le_refl _) (le_refl _) qone_bounded hex)

def prefixBound (z R B N : PTm n) : Fm PTm n := bounded (head z B N) (R*pw (one+R) N) one

ipra_subst prefixBound

theorem prefix_bound_zero (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] prefixBound z R B zero :=
  bound_congr (head_zero z B hB).eqSymm ((congrMul (.eqRefl _) (pw_zero _)).eqTrans (by ipra_ring)).eqSymm (.eqRefl _)
    (fraction_disk z R B hB hz)

theorem prefix_bound_succ (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (ih : Γ ⊢[PRAAx] prefixBound z R B N) : Γ ⊢[PRAAx] prefixBound z R B (succ N) := by
  have e : Γ ⊢[PRAAx] (R*pw (one+R) N)*(one+R) ≐ R*pw (one+R) (succ N) :=
    (mul_assoc _ _ _).eqTrans (congrMul (.eqRefl _) (pw_succ _ _).eqSymm)
  exact bound_congr (head_succ z B N).eqSymm e (.eqRefl _)
    (bounded_product_one ih
      (factor_bound N z R B hB hz))

theorem prefix_bound (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx] prefixBound z R B N := by
  have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hz' : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have law : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_bound_zero z R B hB hz
    · simp only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_bound_succ _ _ _ _ hB'.wk hz'.wk Prf.hyp0
  simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using law.allE N

theorem factor_is_local_constant (p i z B : PTm n) : Γ ⊢[PRAAx]
    GaussianFiniteLogarithmCompositionName.constant p (ofGaussian z (B*succ i)) ≐ factor i z B :=
  GaussianFiniteLogarithmCompositionName.constant_at _ _

def headF : PR 3 := PTm.toPR (head (var 0) (var 1) (var 2))
def run (z B N : PTm n) : PTm n := PTm.app headF ![z,B,N]

theorem program_at (z B N : PTm n) : Γ ⊢[PRAAx] run z B N ≐ head z B N := by
  simpa [run,headF] using toPR_eq (Γ := Γ) (head (var 0) (var 1) (var 2) : PTm 3) ![z,B,N]

theorem returned_head_bound (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (run z B N) (R*pw (one+R) N) one :=
  bound_congr (program_at z B N).eqSymm (.eqRefl _) (.eqRefl _) (prefix_bound z R B N hB hz)

theorem actual_euler_head_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (head (var 0) (var 1) (succ (var 2)) ≐ qmul (head (var 0) (var 1) (var 2)) (factor (var 2) (var 0) (var 1))) :=
  closeUniv 3 (head_succ _ _ _)

theorem actual_euler_head_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (head (var 0) (var 1) (var 2+var 3) ≐ qmul (head (var 0) (var 1) (var 2))
      (qprod (offB factorBody) (var 3) (pairT (var 2) (data (var 0) (var 1))))) :=
  closeUniv 4 (head_split _ _ _ _)

theorem actual_euler_head_factor_local_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianFiniteLogarithmCompositionName.constant (var 0) (ofGaussian (var 2) (var 3*succ (var 1))) ≐
      factor (var 1) (var 2) (var 3)) :=
  closeUniv 4 (factor_is_local_constant _ _ _ _)

theorem actual_euler_head_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ head (var 0) (var 1) (var 2)) :=
  closeUniv 3 (program_at _ _ _)

theorem original_euler_head_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      bounded (run (var 0) (var 2) (var 3)) (var 1*pw (one+var 1) (var 3)) one) :=
  closeUniv 4 (.impI (.impI (returned_head_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_C7_polynomial_head_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2) ⟶
      bounded (run (var 0) (var 2) (two*var 1)) (var 1*pw (one+var 1) (two*var 1)) one) :=
  closeUniv 3 (.impI (.impI (returned_head_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHead
