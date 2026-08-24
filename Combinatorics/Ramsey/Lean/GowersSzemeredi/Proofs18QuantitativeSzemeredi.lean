import GowersSzemeredi.Proofs03ProgressionExistence
import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Sections17_18

/-!
# Auditing the quantitative deduction in Section 18

The printed deduction of Theorem 18.2 uses Theorem 18.1 followed by Lemma
5.15.  Taken literally, those two live statements do not give the one-step
bounds quoted in the paper.  If

`epsilon = section18Exponent alpha d`,

then Lemma 5.15 gives a density increment of `epsilon / 4`, not `epsilon`,
and only guarantees a cell of size

`(epsilon / 4) * N ^ epsilon`,

not `N ^ epsilon`.

This module proves the exact one-step consequence and combines it with the
proved Corollary 3.6 to obtain the corresponding uniform/nonuniform
dichotomy on a prime cyclic group.  It deliberately does not claim the live
Theorem 18.2: in addition to the two factor-four losses, `theorem_18_1`
contains an opaque existential large-modulus threshold, whereas Theorem 18.2
asserts a fixed explicit tower bound.  Iteration also needs an affine transfer
from a modular progression to a new prime cyclic model and a final no-wrap
transfer back to a progression in `Finset.Icc 1 N`; neither fact is present in
the live Section 18 antecedent.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The increment actually supplied by Theorem 18.1 and Lemma 5.15. -/
def section18ActualIncrement (alpha : Real) (d : Nat) : Real :=
  section18Exponent alpha d / 4

/-- The exact prime-cyclic density-increment consequence of Theorem 18.1. -/
def section18_cyclic_density_increment : Prop :=
  ∀ (d : Nat) (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha d →
        ∃ P : ModAP N,
          P.IsProper ∧
          section18ActualIncrement alpha d *
              (N : Real) ^ section18Exponent alpha d ≤ P.carrier.card ∧
          (density A + section18ActualIncrement alpha d) * P.carrier.card ≤
            (A ∩ P.carrier).card

/-- The exact cyclic dichotomy available after adding the proved uniform
case, Corollary 3.6.  Its threshold is still the qualitative threshold
selected by Theorem 18.1. -/
def section18_cyclic_dichotomy : Prop :=
  ∀ (k : Nat) (alpha : Real), 0 < alpha → alpha ≤ 1 / 2 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ A : Finset (ZMod N),
        2 ≤ k → k ≤ N → 0 < density A →
        alpha ≤ (density A / 2) ^ ((k : Real) * 2 ^ k) →
        32 * (k : Real) ^ 2 * density A ^ (-(k : Real)) ≤ N →
        HasModAP A k ∨
          ∃ P : ModAP N,
            P.IsProper ∧
            section18ActualIncrement alpha (k - 2) *
                (N : Real) ^ section18Exponent alpha (k - 2) ≤
              P.carrier.card ∧
            (density A + section18ActualIncrement alpha (k - 2)) *
                P.carrier.card ≤ (A ∩ P.carrier).card

private def section18BalancedReal {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) : Real :=
  (if x ∈ A then 1 else 0) - density A

private lemma section18_balanced_eq_real {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    balanced A x = (section18BalancedReal A x : Complex) := by
  classical
  by_cases hx : x ∈ A <;>
    simp [balanced, indicator, section18BalancedReal, hx]

private lemma section18_density_bounds {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : 0 ≤ density A ∧ density A ≤ 1 := by
  have hcard : A.card ≤ N := by
    calc
      A.card ≤ (Finset.univ : Finset (ZMod N)).card := A.card_le_univ
      _ = N := by simp
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  constructor
  · unfold density
    positivity
  · unfold density
    rw [div_le_one hN]
    exact_mod_cast hcard

private lemma section18_balancedReal_abs_le_one {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    |section18BalancedReal A x| ≤ 1 := by
  classical
  obtain ⟨hd0, hd1⟩ := section18_density_bounds A
  by_cases hx : x ∈ A
  · simp only [section18BalancedReal, hx, if_true]
    rw [abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [section18BalancedReal, hx, if_false, zero_sub, abs_neg]
    rw [abs_of_nonneg hd0]
    exact hd1

private lemma section18_balancedReal_sum_zero {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    ∑ x : ZMod N, section18BalancedReal A x = 0 := by
  classical
  simp only [section18BalancedReal, Finset.sum_sub_distrib]
  have hindicator :
      (∑ x : ZMod N, if x ∈ A then (1 : Real) else 0) = A.card := by
    rw [← Finset.sum_filter]
    simp
  rw [hindicator]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  unfold density
  have hN : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp
  ring

private lemma section18_balancedReal_sum_inter {N : Nat} [NeZero N]
    (A S : Finset (ZMod N)) :
    ∑ x ∈ S, section18BalancedReal A x =
      ((A ∩ S).card : Real) - density A * S.card := by
  classical
  simp only [section18BalancedReal, Finset.sum_sub_distrib]
  have hindicator :
      (∑ x ∈ S, if x ∈ A then (1 : Real) else 0) =
        ((A ∩ S).card : Real) := by
    rw [← Finset.sum_filter]
    have hfilter : S.filter (fun x ↦ x ∈ A) = A ∩ S := by
      ext x
      simp [and_comm]
    rw [hfilter]
    simp
  rw [hindicator]
  simp [mul_comm]

private lemma section18_partition_index_nonempty {N M : Nat} [NeZero N]
    (P : Fin M → Finset (ZMod N)) (hP : IsPartition P Finset.univ) :
    0 < M := by
  by_contra hM
  have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
  subst M
  obtain ⟨i, _hi⟩ := (hP.1 (0 : ZMod N)).mp (Finset.mem_univ _)
  exact Fin.elim0 i

private lemma section18_partition_average {N M : Nat} [NeZero N]
    (P : Fin M → Finset (ZMod N)) (hP : IsPartition P Finset.univ) :
    averageCellSize P = (N : Real) / M := by
  have hcards : ∑ i, (P i).card = N := by
    simpa only [Finset.card_univ, ZMod.card] using IsPartition.sum_card hP
  unfold averageCellSize
  rw [hcards]

/-- The factor-four density and size losses are the exact consequence of the
two live statements; no asymptotic absorption is used. -/
theorem section18_cyclic_density_increment_holds_of_theorem_18_1
    (h181 : theorem_18_1) : section18_cyclic_density_increment := by
  classical
  intro d alpha halpha halphaHalf
  obtain ⟨N0, hN0⟩ := h181 d alpha halpha halphaHalf
  refine ⟨N0, ?_⟩
  intro N _instN _instPrime hN A hnonuniform
  obtain ⟨M, P, hpartition, hproper, havg, hdiscrepancy⟩ :=
    hN0 N hN A hnonuniform
  have hM : 0 < M :=
    section18_partition_index_nonempty (fun i ↦ (P i).carrier) hpartition
  let epsilon : Real := section18Exponent alpha d
  let f : ZMod N → Real := section18BalancedReal A
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon, section18Exponent]
    positivity
  have hf : ∀ x, |f x| ≤ 1 := section18_balancedReal_abs_le_one A
  have hmean : (∑ x : ZMod N, f x) = 0 :=
    section18_balancedReal_sum_zero A
  have hcellNorm (i : Fin M) :
      ‖∑ x ∈ (P i).carrier, balanced A x‖ =
        |∑ x ∈ (P i).carrier, f x| := by
    have hcast :
        (∑ x ∈ (P i).carrier, balanced A x) =
          ((∑ x ∈ (P i).carrier, f x : Real) : Complex) := by
      calc
        ∑ x ∈ (P i).carrier, balanced A x =
            ∑ x ∈ (P i).carrier,
              (section18BalancedReal A x : Complex) := by
                apply Finset.sum_congr rfl
                intro x _hx
                exact section18_balanced_eq_real A x
        _ = ((∑ x ∈ (P i).carrier, f x : Real) : Complex) := by
          exact (Complex.ofReal_sum (P i).carrier f).symm
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hdiscrepancyReal :
      epsilon * N ≤ ∑ i, |∑ x ∈ (P i).carrier, f x| := by
    calc
      epsilon * N ≤
          ∑ i, ‖∑ x ∈ (P i).carrier, balanced A x‖ := by
            simpa only [epsilon] using hdiscrepancy
      _ = ∑ i, |∑ x ∈ (P i).carrier, f x| := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hcellNorm i
  obtain ⟨j, hjIncrement, hjSize⟩ :=
    lemma_5_15_holds N M f (fun i ↦ (P i).carrier) epsilon hM
      hepsilon.le hf hmean hpartition hdiscrepancyReal
  have havgEq :
      averageCellSize (fun i ↦ (P i).carrier) = (N : Real) / M :=
    section18_partition_average (fun i ↦ (P i).carrier) hpartition
  have hsizeScale :
      epsilon / 4 * (N : Real) ^ epsilon ≤
        epsilon * N / (4 * M) := by
    have hMreal : (0 : Real) < M := by exact_mod_cast hM
    calc
      epsilon / 4 * (N : Real) ^ epsilon ≤
          epsilon / 4 *
            averageCellSize (fun i ↦ (P i).carrier) := by
              exact mul_le_mul_of_nonneg_left
                (by simpa only [epsilon] using havg) (by positivity)
      _ = epsilon / 4 * ((N : Real) / M) := by rw [havgEq]
      _ = epsilon * N / (4 * M) := by
        field_simp
  have hcellSize :
      section18ActualIncrement alpha d *
          (N : Real) ^ section18Exponent alpha d ≤
        (P j).carrier.card := by
    change epsilon / 4 * (N : Real) ^ epsilon ≤ (P j).carrier.card
    exact hsizeScale.trans hjSize
  have hcellIncrement :
      (density A + section18ActualIncrement alpha d) *
          (P j).carrier.card ≤ (A ∩ (P j).carrier).card := by
    have hformula := section18_balancedReal_sum_inter A (P j).carrier
    dsimp only [f] at hjIncrement
    rw [hformula] at hjIncrement
    change (density A + epsilon / 4) * ((P j).carrier.card : Real) ≤
      ((A ∩ (P j).carrier).card : Real)
    nlinarith
  exact ⟨P j, hproper j, hcellSize, hcellIncrement⟩

/-- Combining the exact density increment with the proved uniform case gives
the strongest direct prime-cyclic consequence currently justified by the
live Section 18 interfaces. -/
theorem section18_cyclic_dichotomy_holds_of_theorem_18_1
    (h181 : theorem_18_1) : section18_cyclic_dichotomy := by
  intro k alpha halpha halphaHalf
  obtain ⟨N0, hinc⟩ :=
    section18_cyclic_density_increment_holds_of_theorem_18_1 h181
      (k - 2) alpha halpha halphaHalf
  refine ⟨N0, ?_⟩
  intro N _instN _instPrime hN A hk hkN hdensity halphaUniform hscale
  by_cases huniform : UniformSetOfDegree A alpha (k - 2)
  · left
    apply corollary_3_6_holds N k hkN A alpha (density A) hdensity hk
    · unfold density
      have hNreal : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
      field_simp
    · exact huniform
    · exact halphaUniform
    · exact hscale
  · right
    exact hinc N hN A huniform

end LeanProofs.GowersSzemeredi
