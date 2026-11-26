import IPRADerivations.Analysis.Optimization.Convexity.RationalOriginalConvexModulus

/-!
# The source rational log-convexity rule at the original two secants

The rule is an object-theory universal sentence for a fixed interval
presentation and a fixed precision schedule. The two instances used
by the local modulus are obtained from the original rational endpoint
and interior codes and the exact barycenter identities.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalConvexSourceRLC

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling (rationalLT)
open RationalArgmin (left)
open RationalArithmetic (represents recode)
open GaussianRationalSyntheticBounds (natCode natCode_represents natCode_congr)
open RationalNestedConvexModulus (geometry)
open RationalNamedLocalModulus (barycentric original_barycenters)
open RationalConvexSecantWeights (leftPoint rightPoint leftWidth rightWidth leftRemainder rightRemainder displacement)
open RationalConvexArguments (arguments endpointDen firstNumerator secondNumerator enlargedDen interiorNumerator original_geometry)
open RationalOriginalConvexModulus (sourceLeft sourceRight source_queries)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalIntervalPowerComparison (centerOrder)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def schedule (S : PR 6) (A B C j l x : PTm n) : PTm n := app S ![A,B,C,j,l,x]
def data (A B C j l : PTm n) : PTm n := pairT A (pairT B (pairT C (pairT j l)))

def instanceAt (L U : PR 3) (S : PR 6) (A B C j l x : PTm n) : Fm PTm n :=
  (rationalLT (natCode zero) A ⋏ (rationalLT (natCode zero) B ⋏
    (le one (j+l) ⋏ barycentric (j+l) j l A B C))) ⟶ centerOrder L U A B C j l (schedule S A B C j l x) x

def rule (L U : PR 3) (S : PR 6) (x : PTm n) : Fm PTm n := .all
  (instanceAt L U S (fstT (var 0)) (fstT (sndT (var 0))) (fstT (sndT (sndT (var 0))))
    (fstT (sndT (sndT (sndT (var 0))))) (sndT (sndT (sndT (sndT (var 0))))) (Syn.shift x))

ipra_subst schedule

ipra_subst instanceAt [barycentric, RationalMultiplicativeConvexity.weighted, RationalConvexSecants.scale]

theorem instance_at (L U : PR 3) (S : PR 6) (A B C j l x : PTm n) (h : Γ ⊢[PRAAx] rule L U S x) :
    Γ ⊢[PRAAx] instanceAt L U S A B C j l x := by
  let t := data A B C j l
  let A' := fstT t
  let B' := fstT (sndT t)
  let C' := fstT (sndT (sndT t))
  let j' := fstT (sndT (sndT (sndT t)))
  let l' := sndT (sndT (sndT (sndT t)))
  have h₀ : Γ ⊢[PRAAx] instanceAt L U S A' B' C' j' l' x := by
    simpa only [rule,subst_instanceAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,subst_fstT,subst_sndT,A',B',C',j',l']
      using h.allE t
  have r1 : Γ ⊢[PRAAx] sndT t ≐ pairT B (pairT C (pairT j l)) := snd_pair _ _
  have r2 := r1.sndE
  have r3 := r2.sndE
  have a : Γ ⊢[PRAAx] A' ≐ A := fst_pair _ _
  have b : Γ ⊢[PRAAx] B' ≐ B := r1.fstE
  have c : Γ ⊢[PRAAx] C' ≐ C := r2.fstE
  have s : Γ ⊢[PRAAx] j' ≐ j := r3.fstE
  have u : Γ ⊢[PRAAx] l' ≐ l := r3.sndE
  have e := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (instanceAt L U S (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 6)
    (![A',B',C',j',l',x] : Fin 6 → PTm n) ![A,B,C,j,l,x]
      (fun i => by fin_cases i; exact a; exact b; exact c; exact s; exact u; exact .eqRefl _) ?_
  · simpa using e
  · simpa using h₀

theorem positive_of_natural_representation (q A D : PTm n) (h : Γ ⊢[PRAAx] le one A)
    (hq : Γ ⊢[PRAAx] represents q (ZT.ofNat A) D) : Γ ⊢[PRAAx] rationalLT (natCode zero) q := by
  refine .orE (lt_or_le (left (natCode zero) q) (left q (natCode zero))) Prf.hyp0 ?_
  have c := GaussianRationalMetric.comparison_to_cleared q (natCode zero) A zero D one hq.wk (natCode_represents _) Prf.hyp0
  have d : (RationalArgmin.rationalLE q (natCode zero)) :: Γ ⊢[PRAAx] le A zero :=
    le_congr (one_mul _ ) (zero_mul _) c
  exact lt_zero_absurd _ (le_trans h.wk d)

theorem positive_fraction (A D q : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D)
    (e : Γ ⊢[PRAAx] fraction A D ≐ q) : Γ ⊢[PRAAx] rationalLT (natCode zero) q :=
  positive_of_natural_representation q A D hA
    (GaussianRationalHorner.scalar_congr e (ZT.derive rfl) (.eqRefl _) (fraction_represents _ _ hD))

theorem barycentric_congr {w w' a b X Y Z X' Y' Z' : PTm n} (ew : Γ ⊢[PRAAx] w ≐ w')
    (ex : Γ ⊢[PRAAx] X ≐ X') (ey : Γ ⊢[PRAAx] Y ≐ Y') (ez : Γ ⊢[PRAAx] Z ≐ Z')
    (h : Γ ⊢[PRAAx] barycentric w a b X Y Z) : Γ ⊢[PRAAx] barycentric w' a b X' Y' Z' :=
  (RationalAlgebra.multiply_congr (natCode_congr ew) ez).eqSymm.eqTrans
    (h.eqTrans (RationalAlgebra.add_congr (RationalAlgebra.multiply_congr (.eqRefl _) ex)
      (RationalAlgebra.multiply_congr (.eqRefl _) ey)))

def leftWeightFor (a b u v : PTm n) : PTm n := leftRemainder (firstNumerator a b*endpointDen u v) (interiorNumerator a b u v)
def rightWeightFor (a b u v : PTm n) : PTm n :=
  rightRemainder (enlargedDen a b u v) (secondNumerator a b*endpointDen u v) (interiorNumerator a b v u)
def shiftWeightFor (a b u v : PTm n) : PTm n := displacement (interiorNumerator a b u v) (interiorNumerator a b v u)

def leftOffset (S : PR 6) (a b u v x : PTm n) : PTm n :=
  schedule S (recode v) (sourceLeft a) (recode u) (leftWeightFor a b u v) (shiftWeightFor a b u v) x
def rightOffset (S : PR 6) (a b u v x : PTm n) : PTm n :=
  schedule S (recode u) (sourceRight b) (recode v) (rightWeightFor a b u v) (shiftWeightFor a b u v) x

def scheduledSecants (L U : PR 3) (S : PR 6) (a b u v x : PTm n) : Fm PTm n :=
  centerOrder L U (recode v) (sourceLeft a) (recode u) (leftWeightFor a b u v) (shiftWeightFor a b u v) (leftOffset S a b u v x) x ⋏
  centerOrder L U (recode u) (sourceRight b) (recode v) (rightWeightFor a b u v) (shiftWeightFor a b u v) (rightOffset S a b u v x) x

theorem source_secants (L U : PR 3) (S : PR 6) (a b u v x : PTm n)
    (h : Γ ⊢[PRAAx] arguments a b u v) (hc : Γ ⊢[PRAAx] rule L U S x) :
    Γ ⊢[PRAAx] scheduledSecants L U S a b u v x := by
  let D := enlargedDen a b u v
  let P := firstNumerator a b*endpointDen u v
  let Q := secondNumerator a b*endpointDen u v
  let X := interiorNumerator a b u v
  let Y := interiorNumerator a b v u
  let j := leftWeightFor a b u v
  let l := rightWeightFor a b u v
  let t := shiftWeightFor a b u v
  have g := original_geometry a b u v h
  have eq := source_queries a b u v h
  have hD := g.andE₁
  have hP := g.andE₂.andE₁
  have hX := le_trans hP g.andE₂.andE₂.andE₁
  have hY := le_trans hX g.andE₂.andE₂.andE₂.andE₁
  have hQ := le_trans hY g.andE₂.andE₂.andE₂.andE₂
  have hL := positive_fraction P (two*D) (sourceLeft a) hP
    (RationalAlgebra.positive_product (le_succ_self one) hD) eq.andE₁
  have hR := positive_fraction (Q+D) D (sourceRight b) (le_trans hQ (le_add_right _ _)) hD eq.andE₂.andE₁
  have hu := positive_fraction X D (recode u) hX hD eq.andE₂.andE₂.andE₁
  have hv := positive_fraction Y D (recode v) hY hD eq.andE₂.andE₂.andE₂
  have geo := original_barycenters D P Q X Y g
  have eL : Γ ⊢[PRAAx] leftWidth P Y ≐ j+t :=
    (RationalConvexSecantWeights.left_width P X Y g.andE₂.andE₂.andE₁ g.andE₂.andE₂.andE₂.andE₁).eqTrans (add_comm _ _)
  have eR : Γ ⊢[PRAAx] rightWidth D Q X ≐ l+t :=
    (RationalConvexSecantWeights.right_width D Q X Y g.andE₂.andE₂.andE₂.andE₁ g.andE₂.andE₂.andE₂.andE₂).eqTrans (add_comm _ _)
  have cL := barycentric_congr eL eq.andE₂.andE₂.andE₂ eq.andE₁ eq.andE₂.andE₂.andE₁ geo.andE₁
  have cR := barycentric_congr eR eq.andE₂.andE₂.andE₁ eq.andE₂.andE₁ eq.andE₂.andE₂.andE₂ geo.andE₂
  have left := le_trans (RationalNestedConvexModulus.left_weight_positive P X hP g.andE₂.andE₂.andE₁) (le_add_right j t)
  have right := le_trans (RationalNestedConvexModulus.right_weight_positive D Q Y hD g.andE₂.andE₂.andE₂.andE₂) (le_add_right l t)
  exact .andI (.impE (instance_at L U S (recode v) (sourceLeft a) (recode u) j t x hc)
    (.andI hv (.andI hL (.andI left cL))))
    (.impE (instance_at L U S (recode u) (sourceRight b) (recode v) l t x hc)
      (.andI hu (.andI hR (.andI right cR))))

theorem actual_original_rational_log_convexity_secants_closed (L U : PR 3) (S : PR 6) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (arguments (var 0) (var 1) (var 2) (var 3) ⟶ rule L U S (var 4) ⟶
      scheduledSecants L U S (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (source_secants L U S _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalConvexSourceRLC
