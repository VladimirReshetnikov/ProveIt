import IPRADerivations.Analysis.Names.Rates.RationalNamedLocalModulus
import IPRADerivations.Analysis.Optimization.RationalConvexClockRescale
import IPRADerivations.DiophantineNumberTheory.MinkowskiRationalScaling
import IPRADerivations.Core.LinearCombination

/-!
# Original rational arguments for the two-endpoint modulus

The clock has only the two original rational endpoints as horizontal
inputs. The proof clears the denominators of the interior arguments on
an enlarged scale, transports the original rational distances and order
to that scale, and verifies that this does not affect the computed clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexArguments

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero app)
open LeanProofs.IPRA.PTm (monus)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling (rationalLT)
open RationalArgmin (rationalLE denominator_positive transitive)
open RationalArithmetic (represents recode recode_value)
open RationalSupMetric (denominatorOf)
open RationalConvexSecants (nonnegative naturalNumerator rescaled_representation compare_same_to_natural)
open GaussianRationalSyntheticBounds (natCode natCode_represents)
open GaussianRationalHorner (scalar_congr)
open GaussianRationalMetric (comparison_to_cleared comparison_of_cleared)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalConvexSecantWeights (displacement)
open RationalConvexEndpointBudget (localModulus order_of_upper)
open RationalConvexFiniteModulus (withinModulus power_positive)
open RationalConvexClockRescale (original_clock_rescale)
open RationalNestedConvexModulus (geometry)
open RationalValueBounds (upper radius)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

def endpointDen (a b : PTm n) : PTm n := denominatorOf a*denominatorOf b
def firstNumerator (a b : PTm n) : PTm n := naturalNumerator a*denominatorOf b
def secondNumerator (a b : PTm n) : PTm n := naturalNumerator b*denominatorOf a
def enlargedDen (a b u v : PTm n) : PTm n := endpointDen a b*endpointDen u v
def interiorNumerator (a b u v : PTm n) : PTm n := naturalNumerator u*(endpointDen a b*denominatorOf v)
def clock (F : PR 3) (a b k x : PTm n) : PTm n :=
  localModulus F (endpointDen a b) (firstNumerator a b) (secondNumerator a b) k x

def arguments (a b u v : PTm n) : Fm PTm n :=
  rationalLT (natCode zero) a ⋏ (rationalLE a u ⋏ (rationalLE u v ⋏ rationalLE v b))

theorem endpoint_den_positive (a b : PTm n) : Γ ⊢[PRAAx] le one (endpointDen a b) :=
  RationalAlgebra.positive_product (denominator_positive a) (denominator_positive b)

theorem first_representation (a b : PTm n) (h : Γ ⊢[PRAAx] nonnegative a) :
    Γ ⊢[PRAAx] represents a (ZT.ofNat (firstNumerator a b)) (endpointDen a b) :=
  rescaled_representation a (denominatorOf b) _ h (.eqRefl _)

theorem second_representation (a b : PTm n) (h : Γ ⊢[PRAAx] nonnegative b) :
    Γ ⊢[PRAAx] represents b (ZT.ofNat (secondNumerator a b)) (endpointDen a b) :=
  rescaled_representation b (denominatorOf a) _ h (mul_comm _ _)

theorem positive_natural_representative (a N D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] represents a (ZT.ofNat N) D) (h : Γ ⊢[PRAAx] rationalLT (natCode zero) a) :
    Γ ⊢[PRAAx] le one N := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have hzero : (N ≐ zero) :: Γ ⊢[PRAAx] le (one*N) (zero*D) :=
      le_congr ((one_mul _).eqTrans Prf.hyp0).eqSymm (zero_mul _).eqSymm (le_refl zero)
    have hbad := comparison_of_cleared a (natCode zero) N zero D one hD.wk (le_refl _)
      hr.wk (natCode_represents _) hzero
    exact le_lt_absurd _ hbad h.wk
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)

theorem first_numerator_positive (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLT (natCode zero) a) :
    Γ ⊢[PRAAx] le one (firstNumerator a b) :=
  positive_natural_representative a _ _ (endpoint_den_positive a b) (first_representation a b (le_of_lt h)) h

theorem lift_representation (q M D r : PTm n) (h : Γ ⊢[PRAAx] represents q (ZT.ofNat M) D) :
    Γ ⊢[PRAAx] represents q (ZT.ofNat (M*r)) (D*r) := by
  refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) (GaussianRationalHorner.scalar_rescale q (ZT.ofNat M) D r h)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]

theorem interior_representation (a b u v : PTm n) (h : Γ ⊢[PRAAx] nonnegative u) :
    Γ ⊢[PRAAx] represents u (ZT.ofNat (interiorNumerator a b u v)) (enlargedDen a b u v) :=
  rescaled_representation u (endpointDen a b*denominatorOf v) _ h (by unfold enlargedDen endpointDen; ipra_ring)

theorem last_representation (a b u v : PTm n) (h : Γ ⊢[PRAAx] nonnegative v) :
    Γ ⊢[PRAAx] represents v (ZT.ofNat (interiorNumerator a b v u)) (enlargedDen a b u v) :=
  rescaled_representation v (endpointDen a b*denominatorOf u) _ h (by unfold enlargedDen endpointDen; ipra_ring)

theorem original_geometry (a b u v : PTm n) (h : Γ ⊢[PRAAx] arguments a b u v) :
    Γ ⊢[PRAAx] geometry (enlargedDen a b u v)
      (firstNumerator a b*endpointDen u v) (secondNumerator a b*endpointDen u v)
      (interiorNumerator a b u v) (interiorNumerator a b v u) := by
  let D := enlargedDen a b u v
  let H := endpointDen u v
  have ha : Γ ⊢[PRAAx] nonnegative a := le_of_lt h.andE₁
  have hu := transitive ha h.andE₂.andE₁
  have hv := transitive hu h.andE₂.andE₂.andE₁
  have hb := transitive hv h.andE₂.andE₂.andE₂
  have hh := endpoint_den_positive (Γ := Γ) u v
  have hd : Γ ⊢[PRAAx] le one D := RationalAlgebra.positive_product (endpoint_den_positive a b) hh
  have ra := lift_representation a _ _ H (first_representation a b ha)
  have rb := lift_representation b _ _ H (second_representation a b hb)
  have ru := interior_representation a b u v hu
  have rv := last_representation a b u v hv
  exact .andI hd (.andI (RationalAlgebra.positive_product (first_numerator_positive a b h.andE₁) hh)
    (.andI (compare_same_to_natural a u _ _ D hd ra ru h.andE₂.andE₁)
      (.andI (compare_same_to_natural u v _ _ D hd ru rv h.andE₂.andE₂.andE₁)
        (compare_same_to_natural v b _ _ D hd rv rb h.andE₂.andE₂.andE₂))))

theorem fraction_is_original {q A D : PTm n} (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] represents q (ZT.ofNat A) D) : Γ ⊢[PRAAx] fraction A D ≐ recode q := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hD) (RationalArithmetic.recode_guard q)
    (fraction_represents _ _ hD) (recode_value q) hD (denominator_positive q)
  exact h

theorem original_interior_queries (a b u v : PTm n) (h : Γ ⊢[PRAAx] arguments a b u v) :
    Γ ⊢[PRAAx] (fraction (interiorNumerator a b u v) (enlargedDen a b u v) ≐ recode u) ⋏
      (fraction (interiorNumerator a b v u) (enlargedDen a b u v) ≐ recode v) := by
  have hd := (original_geometry a b u v h).andE₁
  have hu : Γ ⊢[PRAAx] nonnegative u := transitive (le_of_lt h.andE₁) h.andE₂.andE₁
  have hv : Γ ⊢[PRAAx] nonnegative v := transitive hu h.andE₂.andE₂.andE₁
  exact .andI (fraction_is_original hd (interior_representation a b u v hu))
    (fraction_is_original hd (last_representation a b u v hv))

theorem original_endpoint_queries (a b : PTm n) (ha : Γ ⊢[PRAAx] nonnegative a)
    (hb : Γ ⊢[PRAAx] nonnegative b) : Γ ⊢[PRAAx]
    (RationalConvexSecantWeights.leftPoint (endpointDen a b) (firstNumerator a b) ≐
      RationalArithmetic.multiply RationalAlgebra.half a) ⋏
    (RationalConvexSecantWeights.rightPoint (endpointDen a b) (secondNumerator a b) ≐
      RationalArithmetic.add b (natCode one)) := by
  let D := endpointDen a b
  let A := firstNumerator a b
  let B := secondNumerator a b
  have hd : Γ ⊢[PRAAx] le one D := endpoint_den_positive a b
  have h₂ := RationalAlgebra.positive_product (le_succ_self one) hd
  have ra := first_representation a b ha
  have rb := second_representation a b hb
  have left : Γ ⊢[PRAAx] fraction A (two*D) ≐ RationalArithmetic.multiply RationalAlgebra.half a := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ h₂) (RationalArithmetic.multiply_guard _ _)
      (fraction_represents _ _ h₂)
      (RationalRepresentations.represents_multiply _ _ _ _ _ _ RationalAlgebra.half_value ra) h₂ h₂
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_natLit]
    dsimp only [A,D]
    ipra_simps
    ring
  have right : Γ ⊢[PRAAx] fraction (B+D) D ≐ RationalArithmetic.add b (natCode one) := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (RationalNormalForm.normalize_well_formed _ _ hd) (RationalArithmetic.add_guard _ _)
      (fraction_represents _ _ hd)
      (RationalRepresentations.represents_add _ _ _ _ _ _ rb (natCode_represents one)) hd
      (RationalAlgebra.positive_product hd (le_refl one))
    ipra_lc
  exact .andI left right

theorem original_clock_at_enlarged_scale (F : PR 3) (a b u v k x : PTm n)
    (h : Γ ⊢[PRAAx] rationalLT (natCode zero) a) :
    Γ ⊢[PRAAx] localModulus F (enlargedDen a b u v) (firstNumerator a b*endpointDen u v)
      (secondNumerator a b*endpointDen u v) k x ≐ clock F a b k x :=
  original_clock_rescale F (endpointDen a b) _ _ k (endpointDen u v) x
    (endpoint_den_positive a b) (first_numerator_positive a b h) (endpoint_den_positive u v)

theorem displacement_of_upper (u v U V D k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hu : Γ ⊢[PRAAx] represents u (ZT.ofNat U) D) (hv : Γ ⊢[PRAAx] represents v (ZT.ofNat V) D)
    (hUV : Γ ⊢[PRAAx] le U V) (h : Γ ⊢[PRAAx] upper v u one (pw two k)) :
    Γ ⊢[PRAAx] le (displacement U V*pw two k) (two*D) := by
  let K := pw two k
  let E := fraction one K
  have hp : Γ ⊢[PRAAx] le one K := power_positive k
  have hc : Γ ⊢[PRAAx] rationalLE v (RationalArithmetic.add u E) := order_of_upper _ _ _ _ hp h
  have rp : Γ ⊢[PRAAx] represents (RationalArithmetic.add u E) (ZT.ofNat (U*K+D)) (D*K) := by
    refine scalar_congr (.eqRefl _) ?_ (.eqRefl _) (RationalRepresentations.represents_add _ _ _ _ _ _
      hu (fraction_represents one K hp))
    ipra_lc
  have clear : Γ ⊢[PRAAx] le (D*(K*V)) (D*(U*K+D)) :=
    le_congr (by ipra_ring) (by ipra_ring) (comparison_to_cleared _ _ _ _ _ _ hv rp hc)
  have hh := RationalValueBounds.positive_cancel hD clear
  have eq := natEq (eq_add_of_le hUV)
  unfold displacement
  ipra_le 2*sl hh using linear_combination 2*𝔟 K*eq

theorem original_proximity (F : PR 3) (a b u v k x : PTm n)
    (h : Γ ⊢[PRAAx] arguments a b u v) (hd : Γ ⊢[PRAAx] radius u v one (pw two (clock F a b k x))) :
    Γ ⊢[PRAAx] withinModulus F (enlargedDen a b u v) (firstNumerator a b*endpointDen u v)
      (secondNumerator a b*endpointDen u v) (interiorNumerator a b u v) (interiorNumerator a b v u) k x := by
  have gg := original_geometry a b u v h
  have hu : Γ ⊢[PRAAx] nonnegative u := transitive (le_of_lt h.andE₁) h.andE₂.andE₁
  have hv : Γ ⊢[PRAAx] nonnegative v := transitive hu h.andE₂.andE₂.andE₁
  have hh := RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ hd)
  have clear := displacement_of_upper u v _ _ _ (clock F a b k x) gg.andE₁
    (interior_representation a b u v hu) (last_representation a b u v hv) gg.andE₂.andE₂.andE₂.andE₁ hh
  exact le_congr (congrMul (.eqRefl _) (congrAp2 powF (original_clock_at_enlarged_scale F a b u v k x h.andE₁).eqSymm
    (.eqRefl two))) (.eqRefl _) clear

def clockF (F : PR 3) : PR 4 := PTm.toPR (clock F (var 0) (var 1) (var 2) (var 3))
def run (F : PR 3) (a b k x : PTm n) : PTm n := app (clockF F) ![a,b,k,x]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (a b k x : PTm n) :
    Syn.subst σ (clock F a b k x) = clock F (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ k) (Syn.subst σ x) := by
  simp [clock,localModulus,RationalConvexSecantWeights.modulus,RationalConvexSecantWeights.budget,
    RationalConvexSecantWeights.margin,LeanProofs.IPRA.Foundations.FiniteObservations.MetricKernel.meet,
    endpointDen,firstNumerator,secondNumerator,naturalNumerator,RationalSupMetric.numeratorOf]

theorem program_at (F : PR 3) (a b k x : PTm n) : Γ ⊢[PRAAx] run F a b k x ≐ clock F a b k x := by
  simpa only [run,clockF,subst_clock,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (clock F (var 0) (var 1) (var 2) (var 3) : PTm 4) ![a,b,k,x]

theorem actual_original_rational_endpoint_codes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((nonnegative (var 0) ⋏ nonnegative (var 1)) ⟶
      (RationalConvexSecantWeights.leftPoint (endpointDen (var 0) (var 1)) (firstNumerator (var 0) (var 1)) ≐
        RationalArithmetic.multiply RationalAlgebra.half (var 0)) ⋏
      (RationalConvexSecantWeights.rightPoint (endpointDen (var 0) (var 1)) (secondNumerator (var 0) (var 1)) ≐
        RationalArithmetic.add (var 1) (natCode one))) :=
  closeUniv 2 (.impI (original_endpoint_queries _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_rational_proximity_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (arguments (var 0) (var 1) (var 2) (var 3) ⟶
      radius (var 2) (var 3) one (pw two (clock F (var 0) (var 1) (var 4) (var 5))) ⟶
      withinModulus F (enlargedDen (var 0) (var 1) (var 2) (var 3))
        (firstNumerator (var 0) (var 1)*endpointDen (var 2) (var 3))
        (secondNumerator (var 0) (var 1)*endpointDen (var 2) (var 3))
        (interiorNumerator (var 0) (var 1) (var 2) (var 3)) (interiorNumerator (var 0) (var 1) (var 3) (var 2))
        (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (original_proximity F _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_endpoint_only_clock_program_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run F (var 0) (var 1) (var 2) (var 3) ≐ clock F (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at F _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalConvexArguments
