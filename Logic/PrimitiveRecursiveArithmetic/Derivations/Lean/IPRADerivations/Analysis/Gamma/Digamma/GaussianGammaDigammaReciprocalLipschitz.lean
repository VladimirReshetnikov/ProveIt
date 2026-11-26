import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaReciprocalPair
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaHarmonicPrefix
import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureSquareCells
import IPRADerivations.Analysis.Stirling.GaussianStirlingMultiplicativeBoundsLog
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalWendelBoundary

/-!
# A sharp elementary bound for the finite reciprocal slope

The first row contributes at most (b(c-a)/a^2). Each successive
row is dominated by the difference of consecutive reciprocal
potentials, so their exact finite sum contributes at most
((c-a)/a). The resulting bound is uniform in the runtime cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaReciprocalLipschitz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum)
open GaussianGammaDigammaHarmonicPrefix (index_succ reciprocal_succ)
open GaussianGammaDigammaReciprocalPair (fraction_gap row_gap)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero qadd positive_product ofGaussian_canonical)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianReciprocalHorner (qadd_zero_right qadd_commutative)
open GaussianStirlingRationalTelescopers (fraction_same)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingTailComparison (point_order_refl point_add_order)
open GaussianCompactRiemannName (fraction_congr)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def difference (a c b N : PTm n) : PTm n := qsub (reciprocalSum a b N) (reciprocalSum c b N)
def potential (a c b N : PTm n) : PTm n := fraction (monus c a) (index a b N)
def firstCap (a c b : PTm n) : PTm n := fraction (b*monus c a) (a*a)
def cap (a c b : PTm n) : PTm n := fraction ((a+b)*monus c a) (a*a)
def law (a c b N : PTm n) : Fm PTm n :=
  rationalLE (fstT (qadd (difference a c b (succ N)) (potential a c b N)))
    (fstT (qadd (firstCap a c b) (potential a c b zero)))

@[simp] theorem subst_difference {l : ℕ} (σ : Fin n → PTm l) (a c b N : PTm n) :
    Syn.subst σ (difference a c b N) = difference (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) :=
  by simp [difference]
@[simp] theorem subst_potential {l : ℕ} (σ : Fin n → PTm l) (a c b N : PTm n) :
    Syn.subst σ (potential a c b N) = potential (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) :=
  by simp [potential]
@[simp] theorem subst_law {l : ℕ} (σ : Fin n → PTm l) (a c b N : PTm n) :
    (law a c b N).subst σ = law (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) :=
  by simp [law,firstCap]

private theorem index_zero (a b : PTm n) : Γ ⊢[PRAAx] index a b zero ≐ a :=
  by unfold index; ipra_ring

private theorem index_positive (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] le one (index a b N) := le_trans ha (le_add_right _ _)

theorem difference_succ (a c b N : PTm n) : Γ ⊢[PRAAx]
    difference a c b (succ N) ≐ qadd (difference a c b N)
      (qsub (fraction b (index a b N)) (fraction b (index c b N))) :=
  (qsub_congr (reciprocal_succ a b N) (reciprocal_succ c b N)).eqTrans
    (GaussianNameArithmetic.sum_difference _ _ _ _)

private theorem first_value (a c b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] difference a c b (succ zero) ≐ fraction (b*monus c a) (a*c) := by
  let r := qsub (fraction b (index a b zero)) (fraction b (index c b zero))
  have z : Γ ⊢[PRAAx] difference a c b zero ≐ qzero :=
    (qsub_congr (GaussianRationalFiniteSum.sum_zero reciprocalBody _) (GaussianRationalFiniteSum.sum_zero reciprocalBody _)).eqTrans
      (GaussianCoefficientNormOrder.qsub_self _)
  have h := row_gap a c b zero ha hac
  exact (difference_succ a c b zero).eqTrans
    ((qadd_congr z (.eqRefl r)).eqTrans ((qzero_add r (qsub_canonical _ _)).eqTrans
      (h.eqTrans (fraction_congr _ _ _ _ (.eqRefl _) (congrMul (index_zero a b) (index_zero c b))))))

private theorem initial (a c b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] law a c b zero := by
  let K := b*monus c a
  have hc := le_trans ha hac
  have h₁ := positive_product _ _ ha hc
  have h₂ := positive_product _ _ ha ha
  have ordered : Γ ⊢[PRAAx] le ((a*a)*K) (K*(a*c)) := by
    ipra_le 𝔞 a*𝔞 K*sl hac
  have h := fractions_order K (a*c) K (a*a) h₁ h₂ ordered
  have l := rationalLE_congr (congrFst (first_value a c b ha hac)).eqSymm (.eqRefl _) h
  exact point_add_order _ _ _ _ l (point_order_refl _)

private theorem potential_step (a c b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qsub (potential a c b N) (potential a c b (succ N)) ≐
      fraction (b*monus c a) (index a b N*index a b (succ N)) := by
  let X := index a b N
  let Y := index a b (succ N)
  let r := monus c a
  have hx := index_positive a b N ha
  have e : Γ ⊢[PRAAx] Y ≐ X+b := index_succ a b N
  have h : Γ ⊢[PRAAx] le X Y := le_congr (.eqRefl _) e.eqSymm (le_add_right _ _)
  have m := (congrMonus e (.eqRefl X)).eqTrans ((congrMonus (add_comm X b) (zero_add X).eqSymm).eqTrans
    ((monus_add_add b zero X).eqTrans (monus_zero b)))
  exact (fraction_gap r X Y hx h).eqTrans (fraction_congr _ _ _ _ ((congrMul (.eqRefl _) m).eqTrans (mul_comm _ _)) (.eqRefl _))

private theorem absorb_row (a c b N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    rationalLE (fstT (qadd (qsub (fraction b (index a b (succ N))) (fraction b (index c b (succ N))))
      (potential a c b (succ N)))) (fstT (potential a c b N)) := by
  let j := succ N
  let X := index a b N
  let Y := index a b j
  let Z := index c b j
  let r := b*monus c a
  let P := potential a c b N
  let Q := potential a c b j
  have hx := index_positive a b N ha
  have hy := index_positive a b j ha
  have hz := index_positive c b j (le_trans ha hac)
  have e : Γ ⊢[PRAAx] le X Z :=
    le_trans (le_congr (.eqRefl _) (index_succ a b N).eqSymm (le_add_right _ _)) (add_le_add_right (j*b) hac)
  have compare : Γ ⊢[PRAAx] le ((X*Y)*r) (r*(Y*Z)) := by ipra_le 𝔞 Y*𝔞 r*sl e
  have h := fractions_order r (Y*Z) r (X*Y) (positive_product _ _ hy hz) (positive_product _ _ hx hy) compare
  have h' := rationalLE_congr (congrFst (row_gap a c b j ha hac)).eqSymm
    (congrFst (potential_step a c b N ha)).eqSymm h
  have add := point_add_order _ _ Q Q h' (point_order_refl _)
  have eq : Γ ⊢[PRAAx] qadd (qsub P Q) Q ≐ P :=
    (qadd_commutative _ _).eqTrans (GaussianRationalLinearProduct.add_sub_right _ _ (ofGaussian_canonical _ _ hx))
  exact rationalLE_congr (.eqRefl _) (congrFst eq) add

private theorem next (a c b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c)
    (ih : Γ ⊢[PRAAx] law a c b N) : Γ ⊢[PRAAx] law a c b (succ N) := by
  let S := difference a c b (succ N)
  have e := (qadd_congr (difference_succ (Γ := Γ) a c b (succ N)) (.eqRefl (potential a c b (succ N)))).eqTrans
    (qadd_associative _ _ _)
  have h := point_add_order S S _ _ (point_order_refl _) (absorb_row a c b N ha hac)
  exact transitive (rationalLE_congr (congrFst e).eqSymm (.eqRefl _) h) ih

theorem finite_conservation (a c b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] law a c b N := by
  have hall : Γ ⊢[PRAAx] .all (law (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_law,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using initial a c b ha hac
    · simp only [subst_law,subst_repl_shift]
      have ah : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using ha.shift
      have ch : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using hac.shift
      exact next (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0) ah.wk ch.wk Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using hall.allE N

private theorem cap_exact (a c b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (firstCap a c b) (potential a c b zero) ≐ cap a c b := by
  let d := monus c a
  have h := positive_product _ _ ha ha
  have p : Γ ⊢[PRAAx] potential a c b zero ≐ fraction (a*d) (a*a) :=
    (fraction_congr _ _ _ _ (.eqRefl _) (index_zero a b)).eqTrans
      (fraction_same d a (a*d) (a*a) ha h (by ipra_ring))
  exact (qadd_congr (.eqRefl _) p).eqTrans
    ((GaussianRationalQuadratureSquareCells.fraction_add_same _ _ _ h).eqTrans
      (fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)))

theorem finite_upper (a c b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hac : Γ ⊢[PRAAx] le a c) :
    Γ ⊢[PRAAx] rationalLE (fstT (difference a c b (succ N))) (fstT (cap a c b)) := by
  let S := difference a c b (succ N)
  let T := potential a c b N
  have hi := index_positive a b N ha
  have z : Γ ⊢[PRAAx] fstT (fraction zero one : PTm n) ≐ fstT qzero :=
    congrFst (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one))
  have pos := rationalLE_congr z (.eqRefl _) (fractions_order zero one (monus c a) (index a b N) (le_refl one) hi
    (by ipra_le 𝔞 (monus c a)))
  have l := point_add_order S S qzero T (point_order_refl _) pos
  have h : Γ ⊢[PRAAx] law a c b N := finite_conservation a c b N ha hac
  exact rationalLE_congr (congrFst (qadd_zero_right S (qsub_canonical _ _))) (congrFst (cap_exact a c b ha))
    (transitive l h)

theorem unit_upper (a c b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hba : Γ ⊢[PRAAx] le b a)
    (hac : Γ ⊢[PRAAx] le a c) : Γ ⊢[PRAAx]
    rationalLE (fstT (difference a c b (succ N))) (fstT (fraction (two*monus c a) b)) := by
  let δ := monus c a
  have ha := le_trans hb hba
  have hD := positive_product _ _ ha ha
  have e : Γ ⊢[PRAAx] le (b*((a+b)*δ)) ((two*δ)*(a*a)) := by
    ipra_le 𝔞 δ*(2*𝔞 a+𝔞 b)*sl hba
  exact transitive (finite_upper a c b N ha hac) (fractions_order _ _ _ _ hD hb e)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaReciprocalLipschitz
