import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.GaussianStirlingAllOrderPanelDerivative
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalHalfNinthProductLower
import IPRADerivations.Analysis.RationalArithmetic.Powers.RationalReciprocalPowerTail

/-!
# Exact discrete second-order integration by parts

The centered second differences of two literal rational rows have an
exact finite difference of their adjacent cross-products as their
pointwise difference. Summing on the actual primitive recursive sum
leaves just the two cross-products at the boundary.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderDiscreteParts

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_add
  multiply_commutative multiply_negative negative_congr negative_minus_multiply negative_involution)
open RationalReciprocalPowerTail (add_zero_right zero_fraction)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalNormalForm (wellFormed)
open RationalFiniteSum (term)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum

def sub (a b : PTm n) : PTm n := add a (negative b)
def secondDifference (a b c : PTm n) : PTm n := sub (add c a) (add b b)
def adjacent (a b c d : PTm n) : PTm n := sub (multiply b c) (multiply a d)

def defect (a₀ a₁ a₂ b₀ b₁ b₂ : PTm n) : PTm n :=
  sub (multiply (secondDifference a₀ a₁ a₂) b₁) (multiply a₁ (secondDifference b₀ b₁ b₂))

ipra_subst sub

ipra_subst adjacent

private theorem negative_add (a b : PTm n) : Γ ⊢[PRAAx] negative (add a b) ≐ add (negative a) (negative b) :=
  (negative_minus_multiply _).eqTrans ((multiply_add _ _ _).eqTrans
    (add_congr (negative_minus_multiply _).eqSymm (negative_minus_multiply _).eqSymm))

private theorem recode_eq (a : PTm n) (h : Γ ⊢[PRAAx] wellFormed a) : Γ ⊢[PRAAx] RationalArithmetic.recode a ≐ a := by
  have hd := RationalArgmin.denominator_positive (Γ := Γ) a
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalArithmetic.recode_guard _) h (RationalArithmetic.recode_value _) (RationalRepresentations.represents_self _) hd hd
    (.eqRefl _)

private theorem negative_sub (a b : PTm n) (hb : Γ ⊢[PRAAx] wellFormed b) :
    Γ ⊢[PRAAx] negative (sub a b) ≐ sub b a :=
  (negative_add a (negative b)).eqTrans
    ((add_congr (.eqRefl _) ((negative_involution b).eqTrans (recode_eq b hb))).eqTrans (add_commutative _ _))

private theorem sub_self (a : PTm n) : Γ ⊢[PRAAx] sub a a ≐ fraction zero one := by
  have hD := RationalArgmin.denominator_positive (Γ := Γ) a
  have hDD := positive_product _ _ hD hD
  have rep := RationalRepresentations.represents_add (Γ := Γ) _ _ _ _ _ _
    (RationalRepresentations.represents_self a) (RationalArithmetic.negative_value a)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) rep (fraction_represents _ _ (le_refl one)) hDD (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat]
  ipra_simps
  ring

private theorem interleave (a b c d : PTm n) : Γ ⊢[PRAAx]
    add (add a b) (add c d) ≐ add (add a c) (add b d) :=
  (add_associative a b _).eqTrans
    ((add_congr (.eqRefl a) ((add_associative b c d).eqSymm.eqTrans
      ((add_congr (add_commutative b c) (.eqRefl d)).eqTrans (add_associative c b d)))).eqTrans
      (add_associative a c _).eqSymm)

private theorem sub_common (a b e : PTm n) (he : Γ ⊢[PRAAx] wellFormed e) :
    Γ ⊢[PRAAx] sub (sub a e) (sub b e) ≐ sub a b := by
  exact (add_congr (.eqRefl _) ((negative_sub b e he).eqTrans (add_commutative _ _))).eqTrans
    ((interleave a (negative e) (negative b) e).eqTrans
      ((add_congr (.eqRefl _) ((add_commutative (negative e) e).eqTrans (sub_self e))).eqTrans
        (add_zero_right _ (RationalArithmetic.add_guard _ _))))

private theorem sub_pair (a b c d : PTm n) (hb : Γ ⊢[PRAAx] wellFormed b) :
    Γ ⊢[PRAAx] sub (add a b) (add c d) ≐ sub (sub a c) (sub d b) :=
  (add_congr (.eqRefl _) (negative_add _ _)).eqTrans
    ((interleave a b (negative c) (negative d)).eqTrans (add_congr (.eqRefl _) (negative_sub d b hb).eqSymm))

private theorem multiply_sub (w a b : PTm n) : Γ ⊢[PRAAx]
    multiply w (sub a b) ≐ sub (multiply w a) (multiply w b) :=
  (multiply_add _ _ _).eqTrans (add_congr (.eqRefl _) (multiply_negative _ _))

theorem local_identity (a₀ a₁ a₂ b₀ b₁ b₂ : PTm n) : Γ ⊢[PRAAx]
    defect a₀ a₁ a₂ b₀ b₁ b₂ ≐ sub (adjacent a₁ a₂ b₁ b₂) (adjacent a₀ a₁ b₀ b₁) := by
  let e := multiply a₁ b₁
  have l : Γ ⊢[PRAAx] multiply (secondDifference a₀ a₁ a₂) b₁ ≐
      sub (add (multiply a₂ b₁) (multiply a₀ b₁)) (add e e) :=
    (multiply_commutative _ _).eqTrans ((multiply_sub _ _ _).eqTrans
      (add_congr ((multiply_add _ _ _).eqTrans (add_congr (multiply_commutative _ _) (multiply_commutative _ _)))
        (negative_congr ((multiply_add _ _ _).eqTrans
          (add_congr (multiply_commutative _ _) (multiply_commutative _ _))))))
  have r : Γ ⊢[PRAAx] multiply a₁ (secondDifference b₀ b₁ b₂) ≐
      sub (add (multiply a₁ b₂) (multiply a₁ b₀)) (add e e) :=
    (multiply_sub _ _ _).eqTrans (add_congr (multiply_add _ _ _) (negative_congr (multiply_add _ _ _)))
  exact (add_congr l (negative_congr r)).eqTrans
    ((sub_common _ _ (add e e) (RationalArithmetic.add_guard _ _)).eqTrans
      (sub_pair _ _ _ _ (RationalArithmetic.multiply_guard _ _)))

def crossValue (f g : PTm 2) (x y i : PTm n) : PTm n :=
  adjacent (inst2 f i x) (inst2 f (succ i) x) (inst2 g i y) (inst2 g (succ i) y)

def crossBody (f g : PTm 2) : PTm 2 :=
  crossValue f g (fstT (var 1)) (sndT (var 1)) (var 0)

def body (f g : PTm 2) : PTm 2 :=
  sub (inst2 (crossBody f g) (succ (var 0)) (var 1)) (inst2 (crossBody f g) (var 0) (var 1))

ipra_subst crossValue

theorem cross_at (f g : PTm 2) (x y i : PTm n) :
    Γ ⊢[PRAAx] inst2 (crossBody f g) i (pairT x y) ≐ crossValue f g x y i := by
  have e := Prf.eqCongr (Γ := Γ) (crossValue f g (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (pairT x y),sndT (pairT x y),i]) (σ' := ![x,y,i]) (fun j => by
      fin_cases j
      exact fst_pair _ _
      exact snd_pair _ _
      exact .eqRefl _)
  simpa [crossBody,inst2] using e

private theorem term_body (f g : PTm 2) (x y i : PTm n) :
    term (body f g) i (pairT x y) =
      sub (inst2 (crossBody f g) (succ i) (pairT x y)) (inst2 (crossBody f g) i (pairT x y)) := by
  unfold term body inst2
  rw [subst_sub]
  simp only [Syn.subst_subst]
  congr 2
  all_goals
    funext j
    fin_cases j <;> simp

theorem defect_at (f g : PTm 2) (x y i : PTm n) :
    Γ ⊢[PRAAx] term (body f g) i (pairT x y) ≐
      defect (inst2 f i x) (inst2 f (succ i) x) (inst2 f (succ (succ i)) x)
        (inst2 g i y) (inst2 g (succ i) y) (inst2 g (succ (succ i)) y) := by
  have e := add_congr (cross_at (Γ := Γ) f g x y (succ i)) (negative_congr (cross_at f g x y i))
  have e' := (local_identity (Γ := Γ) (inst2 f i x) (inst2 f (succ i) x) (inst2 f (succ (succ i)) x)
    (inst2 g i y) (inst2 g (succ i) y) (inst2 g (succ (succ i)) y)).eqSymm
  rw [term_body]
  exact e.eqTrans e'

def telescopeLaw (f g : PTm 2) (x y N : PTm n) : Fm PTm n :=
  add (rsum (body f g) N (pairT x y)) (crossValue f g x y zero) ≐ crossValue f g x y N

ipra_subst telescopeLaw

private theorem sum_zero_step (f g : PTm 2) (x y : PTm n) : Γ ⊢[PRAAx] telescopeLaw f g x y zero :=
  (add_congr ((RationalFiniteSum.sum_zero _ _).eqTrans zero_fraction.eqSymm) (.eqRefl _)).eqTrans
    ((add_commutative _ _).eqTrans (add_zero_right _ (RationalArithmetic.add_guard _ _)))

private theorem sum_succ_step (f g : PTm 2) (x y N : PTm n) (ih : Γ ⊢[PRAAx] telescopeLaw f g x y N) :
    Γ ⊢[PRAAx] telescopeLaw f g x y (succ N) := by
  let a := rsum (body f g) N (pairT x y)
  let b := crossValue f g x y zero
  let u := crossValue f g x y N
  let v := crossValue f g x y (succ N)
  have e : Γ ⊢[PRAAx] term (body f g) N (pairT x y) ≐ sub v u := by
    rw [term_body]
    exact add_congr (cross_at f g x y (succ N)) (negative_congr (cross_at f g x y N))
  have reorder (r s t : PTm n) : Γ ⊢[PRAAx] add (add r s) t ≐ add (add r t) s :=
    (add_associative r s t).eqTrans ((add_congr (.eqRefl _) (add_commutative _ _)).eqTrans (add_associative _ _ _).eqSymm)
  have e' : Γ ⊢[PRAAx] add u (sub v u) ≐ v :=
    (add_commutative _ _).eqTrans ((reorder v (negative u) u).eqTrans
      (add_negative_cancel v u (RationalArithmetic.add_guard _ _)))
  exact (add_congr ((RationalFiniteSum.sum_succ _ _ _).eqTrans (add_congr (.eqRefl _) e)) (.eqRefl _)).eqTrans
    ((reorder a (sub v u) b).eqTrans ((add_congr ih (.eqRefl _)).eqTrans e'))

theorem finite_parts (f g : PTm 2) (x y N : PTm n) : Γ ⊢[PRAAx] telescopeLaw f g x y N := by
  have all : Γ ⊢[PRAAx] .all (telescopeLaw f g (Syn.shift x) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_telescopeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using sum_zero_step (Γ := Γ) f g x y
    · simp only [subst_telescopeLaw,subst_repl_shift]
      exact sum_succ_step f g (Syn.shift x) (Syn.shift y) (var 0) Prf.hyp0
  simpa only [subst_telescopeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderDiscreteParts
