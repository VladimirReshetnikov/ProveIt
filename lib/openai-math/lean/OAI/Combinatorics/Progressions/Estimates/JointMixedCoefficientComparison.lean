/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.JointCoefficientRetainedTest

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem mixedFactor_product_error {I Q : Type*} [Fintype I] [Fintype Q]
    (g : I → ℝ) (a f m : Q → ℝ) {C G ε : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hg : ∀ i, |g i| ≤ C) (hf : ∀ q, |f q| ≤ C)
    (hm : ∀ q, |m q| ≤ G) (he : ∀ q, |a q-m q*f q| ≤ ε) :
    |(∏ i, g i)*(∏ q, a q) - (∏ q, m q)*((∏ i, g i)*(∏ q, f q))| ≤
      C^Fintype.card I * (Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q) := by
  have hprod := finiteProduct_cap (fun i (_ : Unit) => g i) hC (fun i _ => hg i) ()
  have herr := masked_product_error a f m hC hG hε hf hm he
  calc
    _ = |∏ i, g i| * |(∏ q, a q)-(∏ q, m q)*(∏ q, f q)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul hprod herr (abs_nonneg _) (pow_nonneg hC _)

theorem mixedFactor_average_comparison {Ω I Q : Type*}
    [Fintype Ω] [Fintype I] [Fintype Q]
    (p : FiniteProbabilityWeights Ω) (g : Ω → I → ℝ) (a f : Ω → Q → ℝ)
    (m : Q → ℝ) {C G ε η target : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hg : ∀ ω, p.weight ω ≠ 0 → ∀ i, |g ω i| ≤ C)
    (hf : ∀ ω, p.weight ω ≠ 0 → ∀ q, |f ω q| ≤ C)
    (hm : ∀ q, 0 ≤ m q ∧ m q ≤ G)
    (he : ∀ ω, p.weight ω ≠ 0 → ∀ q, |a ω q-m q*f ω q| ≤ ε)
    (hquad : |p.mean (fun ω => (∏ i, g ω i)*(∏ q, f ω q))-target| ≤ η) :
    |p.mean (fun ω => (∏ i, g ω i)*(∏ q, a ω q))-(∏ q, m q)*target| ≤
      C^Fintype.card I * (Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q) +
        G^Fintype.card Q*η := by
  have hm0 : 0 ≤ ∏ q, m q := Finset.prod_nonneg (fun q _ => (hm q).1)
  have hmG : (∏ q, m q) ≤ G^Fintype.card Q := by
    calc
      _ ≤ ∏ _q : Q, G := Finset.prod_le_prod₀ (fun q _ => (hm q).1) (fun q _ => (hm q).2)
      _ = _ := by simp
  apply finiteMean_masked_comparison_of_support p _ _ hm0 hmG hη _ hquad
  intro ω hω
  exact mixedFactor_product_error (g ω) (a ω) (f ω) m hC hG hε (hg ω hω) (hf ω hω)
    (fun q => by rw [abs_of_nonneg (hm q).1]; exact (hm q).2) (he ω hω)

theorem mixedFactor_principalTuple_comparison {I Q D α : Type*}
    [Fintype I] [Fintype Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (modulus : ℕ) (hm : 0 < modulus)
    (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α+1)*modulus ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/L j) <
      volume.real (scalarCubeDomain α))
    (g : (JointBlockParameter B h α → ℝ) → I → ℝ)
    (a : PrincipalIntegerTuples B h α L → Q → ℝ)
    (f : (JointBlockParameter B h α → ℝ) → Q → ℝ) (m : Q → ℝ)
    (C K : ℝ≥0) (hC : 1 ≤ C) {G ε : ℝ} (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hg : ∀ y i, |g y i| ≤ C) (hf : ∀ y q, |f y q| ≤ C)
    (hgLip : ∀ i, LipschitzOnWith K (fun y => g y i) (Metric.closedBall 0 1))
    (hfLip : ∀ q, LipschitzOnWith K (fun y => f y q) (Metric.closedBall 0 1))
    (hmask : ∀ q, 0 ≤ m q ∧ m q ≤ G)
    (he : ∀ y, (principalResidueWeights B h L hL modulus hm r hsize).weight y ≠ 0 →
      ∀ q, |a y q-m q*f (principalTupleNormalized L y) q| ≤ ε) :
    |(principalResidueWeights B h L hL modulus hm r hsize).mean
      (fun y => (∏ i, g (principalTupleNormalized L y) i)*(∏ q, a y q)) -
      (∏ q, m q)*(∫ y, (∏ i, g y i)*(∏ q, f y q) ∂jointBooleanSource h)| ≤
        (C : ℝ)^Fintype.card I * (Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q) +
          G^Fintype.card Q * jointTupleQuadratureError (α := α) B h
            (Fintype.card I+Fintype.card Q) C K L modulus := by
  let factors : I ⊕ Q → (JointBlockParameter B h α → ℝ) → ℝ :=
    Sum.elim (fun i y => g y i) (fun q y => f y q)
  have hLip : ∀ j, LipschitzOnWith K (factors j) (Metric.closedBall 0 1) := by
    intro j
    cases j with
    | inl i => exact hgLip i
    | inr q => exact hfLip q
  have hcap : ∀ j y, |factors j y| ≤ C := by
    intro j y
    cases j with
    | inl i => exact hg y i
    | inr q => exact hf y q
  have hquad := sharedTupleProduct_riemann B h L hL modulus hm r hsize hsmall
    factors C K hC hLip hcap
  simp only [Fintype.prod_sum_type, factors, Sum.elim_inl, Sum.elim_inr,
    Fintype.card_sum] at hquad
  exact mixedFactor_average_comparison _ (fun y => g (principalTupleNormalized L y))
    a (fun y => f (principalTupleNormalized L y)) m C.coe_nonneg hG hε
    ((abs_nonneg _).trans hquad) (fun y _ => hg _) (fun y _ => hf _) hmask he hquad

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointMixedCoefficient_principalTuple_comparison {I Q D α : Type*}
    [Fintype I] [Fintype Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {Y : I → Type*} {X : Q → Type*}
    [∀ q, Countable (X q)] [∀ q, MeasurableSpace (X q)]
    [∀ q, MeasurableSingletonClass (X q)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (modulus : ℕ) (hm : 0 < modulus)
    (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α+1)*modulus ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/L j) <
      volume.real (scalarCubeDomain α))
    (g : (JointBlockParameter B h α → ℝ) → ∀ i, Y i → ℝ)
    (p : PrincipalIntegerTuples B h α L → ∀ q, PMF (X q)) (S : Q → ℝ)
    (f : (JointBlockParameter B h α → ℝ) → ∀ q, X q → ℝ) (m : ∀ q, X q → ℝ)
    (C K : ℝ≥0) (hC : 1 ≤ C) {G ε : ℝ} (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hg : ∀ y i v, |g y i v| ≤ C) (hf : ∀ y q x, |f y q x| ≤ C)
    (hgLip : ∀ i v, LipschitzOnWith K (fun y => g y i v) (Metric.closedBall 0 1))
    (hfLip : ∀ q x, LipschitzOnWith K (fun y => f y q x) (Metric.closedBall 0 1))
    (hmask : ∀ q x, 0 ≤ m q x ∧ m q x ≤ G)
    (he : ∀ y, (principalResidueWeights B h L hL modulus hm r hsize).weight y ≠ 0 →
      ∀ q x, |S q*(p y q x).toReal-m q x*f (principalTupleNormalized L y) q x| ≤ ε)
    (v : ∀ i, Y i) (x : ∀ q, X q) :
    |(principalResidueWeights B h L hL modulus hm r hsize).mean
      (fun y => (∏ i, g (principalTupleNormalized L y) i (v i)) *
        ((∏ q, S q)*(dependentProductPMF (p y) x).toReal)) -
      (∏ q, m q (x q))*(∫ y, (∏ i, g y i (v i))*(∏ q, f y q (x q)) ∂jointBooleanSource h)| ≤
        (C : ℝ)^Fintype.card I * (Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q) +
          G^Fintype.card Q * jointTupleQuadratureError (α := α) B h
            (Fintype.card I+Fintype.card Q) C K L modulus := by
  simp_rw [dependentProductPMF_scaled]
  exact mixedFactor_principalTuple_comparison B h L hL modulus hm r hsize hsmall
    (fun y i => g y i (v i)) (fun y q => S q*(p y q (x q)).toReal)
    (fun y q => f y q (x q)) (fun q => m q (x q)) C K hC hG hε
    (fun y i => hg y i (v i)) (fun y q => hf y q (x q))
    (fun i => hgLip i (v i)) (fun q => hfLip q (x q))
    (fun q => hmask q (x q)) (fun y hy q => he y hy q (x q))

end Erdos3

end

end OAI
