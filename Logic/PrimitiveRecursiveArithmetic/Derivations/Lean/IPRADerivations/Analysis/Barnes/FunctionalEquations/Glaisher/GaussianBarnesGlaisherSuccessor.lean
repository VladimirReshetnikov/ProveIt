import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherFinite
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Glaisher.GaussianBarnesGlaisherIncrement
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Gamma.Ratios.Wendel.GaussianGammaRationalWendelUniform

/-!
# Exact named successor law for the Glaisher logarithm approximants

The original weighted log prefix advances by its next actual term.
Combining its logarithmic weight with the next approximation leaves the
same weight on the original positive rational logarithm of `(N+1)/N`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherSuccessor

open_ipra
open GaussianBarnesGlaisherFinite (nameF data sumData squareQuarter)
open GaussianBarnesGlaisherQuartic (negativeWeight correction)
open GaussianBarnesGlaisherIncrement (cube cube_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianNameRingLaws (zeroF zero_fast negativeF negativeData negative_fast
  add_associative add_commutative multiply_commutative distributive add_negative)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianPositiveRationalLogarithm (baseF logF)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The proof uses common operation syntax for a sampler, its datum, and
its existing regularity derivation. -/
private structure RegularName (Γ : List (Fm PTm n)) where
  sampler : PR 2
  datum : PTm n
  regular : Γ ⊢[PRAAx] pointCN sampler datum

private def namedConstant (a : PTm n) : RegularName Γ := ⟨constantF,a,constant_regular a⟩

private def namedSum (u v : RegularName Γ) : RegularName Γ :=
  ⟨addF u.sampler v.sampler,addData u.datum v.datum,add_fast _ _ _ _ u.regular v.regular⟩

private def namedProduct (u v : RegularName Γ) : RegularName Γ :=
  ⟨multiplyF u.sampler v.sampler,multiplyData u.sampler v.sampler u.datum v.datum,
    multiply_fast _ _ _ _ u.regular v.regular⟩

private def namedNegative (u : RegularName Γ) : RegularName Γ :=
  ⟨negativeF u.sampler,negativeData u.datum,negative_fast _ _ u.regular⟩

private def same (u v : RegularName Γ) : Prop :=
  Γ ⊢[PRAAx] crossEquivalent u.sampler v.sampler u.datum v.datum

local infixl:65 " ⊞ " => namedSum
local infixl:70 " ⊠ " => namedProduct
local infix:50 " ≈ᵥ " => same

private theorem same_self (u : RegularName Γ) : u ≈ᵥ u :=
  cross_refl _ _ u.regular

private theorem same_symm {u v : RegularName Γ} (h : u ≈ᵥ v) : v ≈ᵥ u :=
  cross_symm _ _ _ _ h

private instance sameTrans : Trans (@same n Γ) (@same n Γ) (@same n Γ) where
  trans h k := cross_trans _ _ _ _ _ _ h k

private theorem sum_congruent {a b c d : RegularName Γ} (h : a ≈ᵥ b) (k : c ≈ᵥ d) :
    a ⊞ c ≈ᵥ b ⊞ d :=
  add_cross _ _ _ _ _ _ _ _ a.regular b.regular c.regular d.regular h k

private theorem product_congruent {a b c d : RegularName Γ} (h : a ≈ᵥ b) (k : c ≈ᵥ d) :
    a ⊠ c ≈ᵥ b ⊠ d :=
  GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _ a.regular b.regular c.regular d.regular h k

private theorem regroup (a b c : RegularName Γ) : (a ⊞ b) ⊞ c ≈ᵥ a ⊞ (b ⊞ c) :=
  add_associative _ _ _ _ _ _ a.regular b.regular c.regular

private theorem swap (a b : RegularName Γ) : a ⊞ b ≈ᵥ b ⊞ a :=
  add_commutative _ _ _ _ a.regular b.regular

private theorem product_swap (a b : RegularName Γ) : a ⊠ b ≈ᵥ b ⊠ a :=
  multiply_commutative _ _ _ _ a.regular b.regular

private theorem distribute (a b c : RegularName Γ) : a ⊠ (b ⊞ c) ≈ᵥ (a ⊠ b) ⊞ (a ⊠ c) :=
  distributive _ _ _ _ _ _ a.regular b.regular c.regular

private theorem distribute_right (a b c : RegularName Γ) :
    (a ⊞ b) ⊠ c ≈ᵥ (a ⊠ c) ⊞ (b ⊠ c) := calc
  (a ⊞ b) ⊠ c ≈ᵥ c ⊠ (a ⊞ b) := product_swap _ _
  _ ≈ᵥ (c ⊠ a) ⊞ (c ⊠ b) := distribute _ _ _
  _ ≈ᵥ (a ⊠ c) ⊞ (b ⊠ c) := sum_congruent (product_swap _ _) (product_swap _ _)

private theorem shuffle (a b c d : RegularName Γ) :
    (a ⊞ b) ⊞ (c ⊞ d) ≈ᵥ (a ⊞ c) ⊞ (d ⊞ b) := calc
  (a ⊞ b) ⊞ (c ⊞ d) ≈ᵥ a ⊞ (b ⊞ (c ⊞ d)) := regroup _ _ _
  _ ≈ᵥ a ⊞ ((c ⊞ d) ⊞ b) := sum_congruent (same_self _) (swap _ _)
  _ ≈ᵥ a ⊞ (c ⊞ (d ⊞ b)) := sum_congruent (same_self _) (regroup _ _ _)
  _ ≈ᵥ (a ⊞ c) ⊞ (d ⊞ b) := same_symm (regroup _ _ _)

private def baseLog (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : RegularName Γ :=
  ⟨baseF,N,GaussianGammaFiniteApproximantName.log_regular N hN⟩

private def ratioLog (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : RegularName Γ :=
  ⟨logF,GaussianPositiveRationalLogarithm.data (succ N) N,
    GaussianPositiveRationalLogarithm.name_regular _ _ (.andI (zero_lt_succ _) hN)⟩

private theorem base_log_step (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    baseLog (succ N) (zero_lt_succ _) ≈ᵥ baseLog N hN ⊞ ratioLog N hN := by
  let a := baseLog N hN
  let b := baseLog (succ N) (zero_lt_succ (Γ := Γ) _)
  let m := namedNegative a
  let r := ratioLog N hN
  let u : RegularName Γ := ⟨zeroF,a.datum,zero_fast _⟩
  let v : RegularName Γ := ⟨zeroF,b.datum,zero_fast _⟩
  have hr : r ≈ᵥ b ⊞ m := GaussianPositiveRationalLogarithm.original_logarithm_difference _ _
    (.andI (zero_lt_succ _) hN)
  have hz : u ≈ᵥ v := by
    exact cross_trans _ _ _ _ _ _ (GaussianGammaRationalWendelUniform.zero_constant a.datum)
      (cross_symm _ _ _ _ (GaussianGammaRationalWendelUniform.zero_constant b.datum))
  have inv : a ⊞ m ≈ᵥ u := add_negative _ _ a.regular
  calc
    b ≈ᵥ v ⊞ b := same_symm (GaussianNameRingLaws.add_zero_left _ _ b.regular)
    _ ≈ᵥ u ⊞ b := sum_congruent (same_symm hz) (same_self _)
    _ ≈ᵥ (a ⊞ m) ⊞ b := sum_congruent (same_symm inv) (same_self _)
    _ ≈ᵥ a ⊞ (m ⊞ b) := regroup _ _ _
    _ ≈ᵥ a ⊞ (b ⊞ m) := sum_congruent (same_self _) (swap _ _)
    _ ≈ᵥ a ⊞ r := sum_congruent (same_self _) (same_symm hr)

theorem successor (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF nameF GaussianBarnesGlaisherIncrement.nameF)
      (data (succ N)) (addData (data N) (GaussianBarnesGlaisherIncrement.data N)) := by
  let s : RegularName Γ := ⟨GaussianBarnesGlaisherFinite.sumF,sumData N,GaussianBarnesGlaisherFinite.sum_regular N⟩
  let t : RegularName Γ := ⟨GaussianBarnesGlaisherFinite.sumF,sumData (succ N),GaussianBarnesGlaisherFinite.sum_regular (succ N)⟩
  let a := baseLog N hN
  let b := baseLog (succ N) (zero_lt_succ (Γ := Γ) _)
  let r := ratioLog N hN
  let l := namedConstant (Γ := Γ) (naturalPoint (succ N))
  let w := namedConstant (Γ := Γ) (negativeWeight N)
  let w' := namedConstant (Γ := Γ) (negativeWeight (succ N))
  let q := namedConstant (Γ := Γ) (squareQuarter N)
  let q' := namedConstant (Γ := Γ) (squareQuarter (succ N))
  let d := namedConstant (Γ := Γ) (correction N)
  have hS : t ≈ᵥ s ⊞ (l ⊠ b) := GaussianBarnesGlaisherFinite.sum_append N
  have hW : l ⊞ w' ≈ᵥ w := constant_sum _ _ _ (GaussianBarnesGlaisherFinite.weight_step N)
  have hQ : q ⊞ d ≈ᵥ q' := constant_sum _ _ _ (GaussianBarnesGlaisherFinite.quarter_step N)
  have hL : b ≈ᵥ a ⊞ r := base_log_step N hN
  have h : (t ⊞ (w' ⊠ b)) ⊞ q' ≈ᵥ ((s ⊞ (w ⊠ a)) ⊞ q) ⊞ (d ⊞ (w ⊠ r)) := calc
    (t ⊞ (w' ⊠ b)) ⊞ q' ≈ᵥ ((s ⊞ (l ⊠ b)) ⊞ (w' ⊠ b)) ⊞ q' :=
      sum_congruent (sum_congruent hS (same_self _)) (same_self _)
    _ ≈ᵥ (s ⊞ ((l ⊠ b) ⊞ (w' ⊠ b))) ⊞ q' := sum_congruent (regroup _ _ _) (same_self _)
    _ ≈ᵥ (s ⊞ ((l ⊞ w') ⊠ b)) ⊞ q' :=
      sum_congruent (sum_congruent (same_self _) (same_symm (distribute_right _ _ _))) (same_self _)
    _ ≈ᵥ (s ⊞ (w ⊠ (a ⊞ r))) ⊞ (q ⊞ d) :=
      sum_congruent (sum_congruent (same_self _) (product_congruent hW hL)) (same_symm hQ)
    _ ≈ᵥ (s ⊞ ((w ⊠ a) ⊞ (w ⊠ r))) ⊞ (q ⊞ d) :=
      sum_congruent (sum_congruent (same_self _) (distribute _ _ _)) (same_self _)
    _ ≈ᵥ ((s ⊞ (w ⊠ a)) ⊞ (w ⊠ r)) ⊞ (q ⊞ d) :=
      sum_congruent (same_symm (regroup _ _ _)) (same_self _)
    _ ≈ᵥ ((s ⊞ (w ⊠ a)) ⊞ q) ⊞ (d ⊞ (w ⊠ r)) := shuffle _ _ _ _
  exact h

theorem successor_rate (N : PTm n) (hN : Γ ⊢[PRAAx] le two N) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data (succ N)) (data N) two (cube N) := by
  let G := GaussianBarnesGlaisherIncrement.nameF
  let x := data N
  let y := GaussianBarnesGlaisherIncrement.data N
  let D := cube N
  let A := leadingNumerator zero one two D
  let B := leadingDenominator one D
  have h1 := le_trans (le_succ_self one) hN
  have hd := cube_positive N h1
  have hb : Γ ⊢[PRAAx] le one B := positive_product _ _ (le_refl one) hd
  have hx := GaussianBarnesGlaisherFinite.regular N h1
  have sums := GaussianNamedAddRate.independent_rate nameF G nameF constantF x y x qzero zero one two D (le_refl one) hd
    (GaussianNamedDifferenceRate.self_rate nameF x hx) (GaussianBarnesGlaisherIncrement.increment_rate N hN)
  have drop := add_cross nameF nameF constantF zeroF x x qzero x hx hx (constant_regular _) (zero_fast _)
    (cross_refl _ _ hx) (cross_symm _ _ _ _ (GaussianGammaRationalWendelUniform.zero_constant x))
  have zero := cross_trans _ _ _ _ _ _ drop (GaussianNameRingLaws.add_zero _ _ hx)
  have result := GaussianNamedRateTransport.transport (addF nameF G) (addF nameF constantF) nameF nameF
    (addData x y) (addData x qzero) (data (succ N)) x A B hb sums (successor N h1) (cross_symm _ _ _ _ zero)
  exact GaussianNamedRateRadius.weaken _ _ _ _ A B two D hb hd
    (le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero) (by unfold A B leadingNumerator leadingDenominator; ipra_ring))
    result

theorem actual_Glaisher_logarithm_approximants_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent nameF (addF nameF GaussianBarnesGlaisherIncrement.nameF)
      (data (succ (var 0))) (addData (data (var 0)) (GaussianBarnesGlaisherIncrement.data (var 0)))) :=
  closeUniv 1 (.impI (successor _ Prf.hyp0))

theorem actual_Glaisher_logarithm_approximants_summable_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le two (var 0) ⟶ independentRate nameF nameF (data (succ (var 0))) (data (var 0)) two (cube (var 0))) :=
  closeUniv 1 (.impI (successor_rate _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesGlaisherSuccessor
