import IPRADerivations.Analysis.RationalArithmetic.GaussianPositiveRealArithmetic
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Finite Euclidean domination by nonnegative rational rows

If each complex term has norm at most a nonnegative rational comparator,
the finite sum has norm at most the sum of the comparators. Each existing
rational observation keeps its own positive denominator. The accumulator
uses quantifier-free induction and the exact Euclidean triangle inequality.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRadiusFiniteSum

open_ipra
open GaussianPositiveRealArithmetic (positive numerator natural_representation)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalFiniteSum (sum)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def boundBy (z r : PTm n) : Fm PTm n :=
  positive r ⋏ bounded z (numerator (fstT r)) (denominatorOf (fstT r))

ipra_subst boundBy [numerator, RationalSupMetric.numeratorOf, denominatorOf]

theorem bound_congr {z z' r r' : PTm n}
    (hz : Γ ⊢[PRAAx] z ≐ z') (hr : Γ ⊢[PRAAx] r ≐ r') (h : Γ ⊢[PRAAx] boundBy z r) :
    Γ ⊢[PRAAx] boundBy z' r' := by
  simpa using Prf.eqSubst (boundBy (var 0) (var 1) : Fm PTm 2) ![z,r] ![z',r']
    (fun i => by fin_cases i; exact hz; exact hr) (by simpa using h)

theorem from_representation (z r A D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] positive r)
    (rep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT r) (ZT.ofNat A) D)
    (h : Γ ⊢[PRAAx] bounded z A D) : Γ ⊢[PRAAx] boundBy z r := by
  let E := denominatorOf (fstT r)
  let M := numerator (fstT r)
  have hE := RationalArgmin.denominator_positive (Γ := Γ) (fstT r)
  have scaled : Γ ⊢[PRAAx] E*(A*E) ≐ E*(M*D) := by
    ipra_lc 𝔞(E)*ZT.toZ_eq rep-𝔞(D)*ZT.toZ_eq (natural_representation (fstT r) hr.andE₂)
  have order := RationalValueBounds.positive_cancel hE (le_congr (.eqRefl _) scaled (le_refl _))
  exact .andI hr (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hD hE order h)

/-- A scalar upper comparison enlarges the positive radius using the given
rational representation of the new scalar. -/
theorem enlarge_radius (z r b S T A B : PTm n) (h : Γ ⊢[PRAAx] boundBy z r)
    (hT : Γ ⊢[PRAAx] le one T) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b (ZT.ofNat S) T)
    (hu : Γ ⊢[PRAAx] RationalValueBounds.upper (fstT r) b A B) : Γ ⊢[PRAAx]
    bounded z (S*B+A*T) (T*B) := by
  let M := numerator (fstT r)
  let E := denominatorOf (fstT r)
  let L := RationalRepresentedUpper.left (ZT.ofNat M) T B
  let U := RationalRepresentedUpper.right (ZT.ofNat S) E T A B
  have signed : Γ ⊢[PRAAx] zle L U := RationalRepresentedUpper.to_signed _ _ _ _ _ _ _ _
    (natural_representation (fstT r) h.andE₁.andE₂) hb hu
  have order : Γ ⊢[PRAAx] le (M*(T*B)) ((S*B+A*T)*E) := by
    apply le_of_eq_add (d := PolynomialBisection.slack L U)
    apply deriveNat
    have cleared := zle_toZ signed
    simp only [L,U,RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at cleared
    dsimp only [PolynomialBisection.slack,L,U,RationalRepresentedUpper.left,RationalRepresentedUpper.right]
    ipra_simps
    linear_combination -cleared
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (RationalArgmin.denominator_positive _)
    (positive_product _ _ hT hB) order h.andE₂

theorem add_bound (z w r s : PTm n) (h : Γ ⊢[PRAAx] boundBy z r) (k : Γ ⊢[PRAAx] boundBy w s) :
    Γ ⊢[PRAAx] boundBy (qadd z w) (qadd r s) := by
  let A := numerator (fstT r)
  let C := numerator (fstT s)
  let D := denominatorOf (fstT r)
  let E := denominatorOf (fstT s)
  have hD := RationalArgmin.denominator_positive (Γ := Γ) (fstT r)
  have hE := RationalArgmin.denominator_positive (Γ := Γ) (fstT s)
  have first := natural_representation (fstT r) h.andE₁.andE₂
  have second := natural_representation (fstT s) k.andE₁.andE₂
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qadd r s)) (ZT.ofNat (A*E+C*D)) (D*E) := by
    apply GaussianRationalHorner.scalar_congr (RationalGaussianRealPart.real_add _ _).eqSymm _ (.eqRefl _)
      (RationalRepresentations.represents_add _ _ _ _ _ _ first second)
    ipra_lc
  exact from_representation _ _ _ _ (positive_product _ _ hD hE)
    (GaussianPositiveRealArithmetic.positive_add _ _ h.andE₁ k.andE₁) rep
    (GaussianRationalReciprocal.bounded_sum z w A D C E hD hE h.andE₂ k.andE₂)

theorem multiply_bound (z w r s : PTm n) (h : Γ ⊢[PRAAx] boundBy z r) (k : Γ ⊢[PRAAx] boundBy w s) :
    Γ ⊢[PRAAx] boundBy (qmul z w) (qmul r s) := by
  let A := numerator (fstT r)
  let C := numerator (fstT s)
  let D := denominatorOf (fstT r)
  let E := denominatorOf (fstT s)
  have hD := RationalArgmin.denominator_positive (Γ := Γ) (fstT r)
  have hE := RationalArgmin.denominator_positive (Γ := Γ) (fstT s)
  have first := natural_representation (fstT r) h.andE₁.andE₂
  have second := natural_representation (fstT s) k.andE₁.andE₂
  have axis := RationalGaussianEmbedding.axis_multiply_representation r s h.andE₁.andE₁ k.andE₁.andE₁
  let m := RationalArithmetic.multiply (fstT r) (fstT s)
  have real : Γ ⊢[PRAAx] fstT (qmul r s) ≐ RationalArithmetic.recode m :=
    axis.fstE
  have prodRep : Γ ⊢[PRAAx] RationalArithmetic.represents m (ZT.ofNat (A*C)) (D*E) := by
    have hProd := RationalRepresentations.represents_multiply _ _ _ _ _ _ first second
    have eq : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat A*ZT.ofNat C) (ZT.ofNat (A*C)) := by
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    exact GaussianRationalHorner.scalar_congr (.eqRefl m) eq (.eqRefl (D*E)) hProd
  have same : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (A*C)) (ZT.ofNat (A*C)) := by
    apply ZT.derive
    rfl
  have rep := GaussianRationalHorner.scalar_congr real.eqSymm same (.eqRefl (D*E))
    (RationalGaussianEmbedding.scalar_recode_represents m _ _ prodRep)
  exact from_representation _ _ _ _ (positive_product _ _ hD hE)
    (GaussianPositiveRealArithmetic.positive_multiply _ _ h.andE₁ k.andE₁) rep
    (GaussianRationalReciprocal.bounded_product z w A D C E hD hE h.andE₂ k.andE₂)

theorem zero_bound : Γ ⊢[PRAAx] boundBy (qzero : PTm n) qzero := by
  have hp := GaussianPositiveRealArithmetic.positive_zero (n := n) (Γ := Γ)
  refine .andI hp ?_
  apply GaussianRationalMetric.bounded_of_cleared _ _ one _ _ (le_refl one)
    (RationalArgmin.denominator_positive _) (GaussianRationalHorner.zero_represents one)
  exact le_congr ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_zero).eqTrans (by ipra_ring)).eqSymm
    (.eqRefl _) (zero_le _)

def rowBounds (f g : PTm 2) (N x y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ boundBy (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))

ipra_subst rowBounds [Syn.subst_shift, Syn.shift_subst]

theorem row_at (f g : PTm 2) (N x y k : PTm n) (h : Γ ⊢[PRAAx] rowBounds f g N x y)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] boundBy (inst2 f k x) (inst2 g k y) := by
  have use : Γ ⊢[PRAAx] lt k N ⟶ boundBy (inst2 f k x) (inst2 g k y) := by
    simpa [rowBounds] using h.allE k
  exact .impE use hk

private def sumLaw (f g : PTm 2) (N x y k : PTm n) : Fm PTm n :=
  le k N ⟶ boundBy (sum f k x) (sum g k y)

@[simp] private theorem subst_sumLaw {m : ℕ} (σ : Fin n → PTm m) (f g : PTm 2) (N x y k : PTm n) :
    (sumLaw f g N x y k).subst σ = sumLaw f g (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ k) := by
  simp [sumLaw]

theorem sum_bound (f g : PTm 2) (N x y : PTm n) (h : Γ ⊢[PRAAx] rowBounds f g N x y) :
    Γ ⊢[PRAAx] boundBy (sum f N x) (sum g N y) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] rowBounds f g (Syn.shift N) (Syn.shift x) (Syn.shift y) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (sumLaw f g (Syn.shift N) (Syn.shift x) (Syn.shift y) (var 0)) := by
    refine PRA.qfInd _ (by simp [sumLaw,boundBy,positive,RationalGaussianEmbedding.axis,RationalArgmin.rationalEq,
      GaussianPositiveRealArithmetic.sign,GaussianRationalMetric.bounded,RationalArgmin.rationalLE,Fm.QF,le_QF]) ?_ ?_
    · simp only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (bound_congr (GaussianRationalFiniteSum.sum_zero f x).eqSymm
        (GaussianRationalFiniteSum.sum_zero g y).eqSymm zero_bound)
    · simp only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI (bound_congr (GaussianRationalFiniteSum.sum_succ f _ _).eqSymm
        (GaussianRationalFiniteSum.sum_succ g _ _).eqSymm (add_bound _ _ _ _ ?_ ?_))
      · exact .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      · exact row_at f g _ _ _ _ hs.wk.wk Prf.hyp0
  have final : Γ ⊢[PRAAx] sumLaw f g N x y N := by
    simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N
  exact .impE final (le_refl N)

theorem finite_sum_positive_rational_domination_closed (f g : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rowBounds f g (var 0) (var 1) (var 2) ⟶ boundBy (sum f (var 0) (var 1)) (sum g (var 0) (var 2))) :=
  closeUniv 3 (.impI (sum_bound f g _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPositiveRadiusFiniteSum
