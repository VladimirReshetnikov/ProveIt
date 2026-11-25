import IPRADerivations.Analysis.GaussianGammaDigammaReciprocalPair
import IPRADerivations.Analysis.GaussianRationalInverseQuadraticAlgebra
import IPRADerivations.Analysis.GaussianStirlingTailComparison
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsLog
import IPRADerivations.AnalyticNumberTheory.PhiLower

/-!
# Finite lower slope of the Euler digamma approximants

On a common denominator, the first reciprocal difference on [1,2]
dominates (y−x)/4. Each later reciprocal difference is nonnegative.
The same cutoff and logarithm are used at both arguments.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaSlopeLowerFinite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (fraction_congr)
open GaussianGammaDigammaReciprocalPair (fraction_gap)
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalInverseQuadraticAlgebra (subtract_sum)
open GaussianRationalLinearProduct (add_sub_right)
open GaussianRationalMetric (qsub qsub_canonical qnegative)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open RationalArgmin (rationalLE rationalLE_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def margin (a c b : PTm n) : PTm n := fraction (monus c a) (num 4*b)

@[simp] theorem subst_margin {m : ℕ} (σ : Fin n → PTm m) (a c b : PTm n) :
    Syn.subst σ (margin a c b) = margin (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) := by
  simp [margin]

def domain (a c b : PTm n) : Fm PTm n := le one b ⋏ (le b a ⋏ (le a c ⋏ le c (two*b)))

@[simp] theorem subst_domain {m : ℕ} (σ : Fin n → PTm m) (a c b : PTm n) :
    (domain a c b).subst σ = domain (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) := by
  simp [domain,two]

theorem sources (a c b : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b ⋏ GaussianStirlingGammaLogarithm.source c b :=
  let ha := le_trans h.andE₁ h.andE₂.andE₁
  .andI (.andI ha h.andE₁) (.andI (le_trans ha h.andE₂.andE₂.andE₁) h.andE₁)

private theorem first_row (a c b : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] rationalLE (fstT (qadd (margin a c b) (fraction b c))) (fstT (fraction b a)) := by
  let d := monus c a
  let D := num 4*b
  have hb : Γ ⊢[PRAAx] le one b := h.andE₁
  have hac : Γ ⊢[PRAAx] le a c := h.andE₂.andE₂.andE₁
  have hc₂ : Γ ⊢[PRAAx] le c (two*b) := h.andE₂.andE₂.andE₂
  have ha : Γ ⊢[PRAAx] le one a := (sources a c b h).andE₁.andE₁
  have hc := le_trans ha hac
  have hD : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (le_trans (le_succ_self one) (le_trans (le_succ_self two) (le_succ_self (succ two)))) hb
  have haa := le_trans hac hc₂
  have prod := AnalyticNumberTheory.PhiLower.le_mul_mono haa hc₂
  have cleared : Γ ⊢[PRAAx] le ((a*c)*d) ((b*d)*D) := by
    unfold D
    ipra_le 𝔞 d * sl prod
  have bound := fractions_order d D (b*d) (a*c) hD (positive_product _ _ ha hc) cleared
  have exactGap := fraction_gap b a c ha hac
  have addBack := (qadd_commutative (qsub (fraction b a) (fraction b c)) (fraction b c)).eqTrans
    (add_sub_right (fraction b c) (fraction b a) (GaussianRationalHorner.ofGaussian_canonical _ _ ha))
  have order := point_add_order (margin a c b) (qsub (fraction b a) (fraction b c)) (fraction b c) (fraction b c)
    (rationalLE_congr (.eqRefl _) (congrFst exactGap).eqSymm bound) (point_order_refl _)
  exact rationalLE_congr (.eqRefl _) (congrFst addBack) order

private theorem row_order (a c b k : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction b (index c b k))) (fstT (fraction b (index a b k))) := by
  have src := sources a c b h
  have ha := (GaussianGammaDigammaFiniteSum.row_source a b k src.andE₁).andE₁
  have hc := (GaussianGammaDigammaFiniteSum.row_source c b k src.andE₂).andE₁
  have hac : Γ ⊢[PRAAx] le a c := h.andE₂.andE₂.andE₁
  have hi : Γ ⊢[PRAAx] le (index a b k) (index c b k) := by
    unfold index
    exact add_le_add_right (k*b) hac
  exact fractions_order _ _ _ _ hc ha (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right b hi))

private theorem sum_next (a b k : PTm n) : Γ ⊢[PRAAx] reciprocalSum a b (succ k) ≐
    qadd (reciprocalSum a b k) (fraction b (index a b k)) :=
  (GaussianRationalFiniteSum.sum_succ reciprocalBody k (pairT a b)).eqTrans
    (qadd_congr (.eqRefl _) (reciprocal_entry a b k))

private theorem sum_first (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] reciprocalSum a b (succ zero) ≐ fraction b a := by
  have hi : Γ ⊢[PRAAx] index a b zero ≐ a := by unfold index; ipra_ring
  have sumZero : Γ ⊢[PRAAx] reciprocalSum a b zero ≐ qzero :=
    GaussianRationalFiniteSum.sum_zero reciprocalBody (pairT a b)
  have row : Γ ⊢[PRAAx] fraction b (index a b zero) ≐ fraction b a :=
    fraction_congr b b _ a (.eqRefl _) hi
  have canon : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (fraction b a) :=
    GaussianRationalHorner.ofGaussian_canonical _ _ ha
  exact (sum_next a b zero).eqTrans ((qadd_congr sumZero row).eqTrans (qzero_add _ canon))

def prefixLaw (a c b N : PTm n) : Fm PTm n :=
  rationalLE (fstT (qadd (margin a c b) (reciprocalSum c b (succ N)))) (fstT (reciprocalSum a b (succ N)))

@[simp] theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (a c b N : PTm n) :
    (prefixLaw a c b N).subst σ =
      prefixLaw (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [prefixLaw]

private theorem prefix_zero (a c b : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] prefixLaw a c b zero := by
  have src := sources a c b h
  exact rationalLE_congr
    (congrFst (qadd_congr (.eqRefl _) (sum_first c b src.andE₂.andE₁))).eqSymm
    (congrFst (sum_first a b src.andE₁.andE₁)).eqSymm (first_row a c b h)

private theorem prefix_succ (a c b N : PTm n) (h : Γ ⊢[PRAAx] domain a c b)
    (ih : Γ ⊢[PRAAx] prefixLaw a c b N) : Γ ⊢[PRAAx] prefixLaw a c b (succ N) := by
  let k := succ N
  have next := point_add_order (qadd (margin a c b) (reciprocalSum c b k)) (reciprocalSum a b k)
    (fraction b (index c b k)) (fraction b (index a b k)) ih (row_order a c b k h)
  have ec := (qadd_associative (Γ := Γ) (margin a c b) (reciprocalSum c b k) (fraction b (index c b k))).eqTrans
    (qadd_congr (.eqRefl _) (sum_next c b k).eqSymm)
  exact rationalLE_congr (congrFst ec) (congrFst (sum_next a b k)).eqSymm next

theorem prefix_order (a c b N : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] prefixLaw a c b N := by
  have hall : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero a c b h
    · have hh : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift c) (Syn.shift b) := by
        simpa only [Fm.shift,subst_domain,Syn.shift] using h.shift
      simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        prefix_succ (Syn.shift a) (Syn.shift c) (Syn.shift b) (var 0) hh.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE N

/-- Adding the common first-row margin to the lower Euler slope still
leaves that slope below the upper Euler slope. -/
theorem cutoff_order (a c b N T : PTm n) (h : Γ ⊢[PRAAx] domain a c b) :
    Γ ⊢[PRAAx] rationalLE
      (fstT (qadd (qsub T (reciprocalSum a b (succ N))) (margin a c b)))
      (fstT (qsub T (reciprocalSum c b (succ N)))) := by
  let A := reciprocalSum a b (succ N)
  let C := reciprocalSum c b (succ N)
  let m := margin a c b
  have negate (Q : PTm n) : Γ ⊢[PRAAx] fstT (qnegative Q) ≐ RationalArithmetic.negative (fstT Q) :=
    fst_pair _ _
  have rev := point_add_order T T (qnegative A) (qnegative (qadd m C)) (point_order_refl T)
    (rationalLE_congr (negate A).eqSymm (negate (qadd m C)).eqSymm
      (RationalAlgebra.negative_antitone _ _ (prefix_order a c b N h)))
  have e : Γ ⊢[PRAAx] qsub T (qadd m C) ≐ qsub (qsub T C) m :=
    (qsub_congr (.eqRefl _) (qadd_commutative m C)).eqTrans
      (subtract_sum T C m).eqSymm
  have added := point_add_order (qsub T A) (qsub (qsub T C) m) m m
    (rationalLE_congr (.eqRefl _) (congrFst e) rev) (point_order_refl m)
  have recover := (qadd_commutative (Γ := Γ) (qsub (qsub T C) m) m).eqTrans
    (add_sub_right m (qsub T C) (qsub_canonical T C))
  exact rationalLE_congr (.eqRefl _) (congrFst recover) added

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaSlopeLowerFinite
