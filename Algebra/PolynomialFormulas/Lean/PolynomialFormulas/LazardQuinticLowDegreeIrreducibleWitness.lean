import PolynomialFormulas.LazardQuinticLowDegreeSpecialization
import PolynomialFormulas.Fin5DihedralCore
import PolynomialFormulas.LazardQuinticPrimitiveFifthRoot
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

/-!
# An irreducible binomial witness for Lazard's degree-five resolvent bound

Lazard defines a resolvent to be *always separable* when it is separable for
every irreducible polynomial in the stated class.  A collision on an
arbitrary split tuple is therefore not, by itself, the advertised lower
bound.  This file closes that quantifier gap with the concrete irreducible
rational quintic `X^5 - 2`.

We construct one complex fifth root `alpha` of `2` and use the already proved
primitive fifth root `omega`.  The five values `alpha * omega^i` are distinct
and are exactly roots of the scalar extension of `X^5 - 2`.  Every rational
`C5`-invariant of total degree below five, and every rational `D5`-invariant
of that degree, has a nonseparable literal relative orbit product on this
irreducible quintic.

This module is source-only until its focused and public kernel checks pass.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.LazardQuinticLowDegreeIrreducibleWitness

/- Lean 4.32 has no namespace-assignment aliases.  Re-export the small local
interfaces used by the witness statements. -/
namespace Low
export LeanProofs.PolynomialFormulas.LazardQuinticLowDegreeSpecialization
  (lowDegree_cyclic_relativeResolvent_not_separable
    lowDegree_dihedral_relativeResolvent_not_separable radicalRootTuple
    radicalRootTuple_injective radicalRootTuple_isRoot)
end Low

namespace Action
export LeanProofs.PolynomialFormulas.LazardGeneralResolventExplicit
  (InvariantUnder renameAction specializedOrbitValue)
end Action

namespace Resolvent
export LeanProofs.PolynomialFormulas.LazardGeneralResolventCriterion
  (orbitResolvent)
end Resolvent

namespace Classification
export LeanProofs.PolynomialFormulas.Fin5DihedralCore
  (standardC5 standardD5)
end Classification

noncomputable section

noncomputable local instance cosetsFintype
    (G : Subgroup (Equiv.Perm (Fin 5))) :
    Fintype (LeanProofs.PolynomialFormulas.LazardGeneralResolventCriterion.Cosets G) :=
  Fintype.ofFinite _

/-! ## The irreducible rational quintic `X^5 - 2` -/

def x5SubTwoZ : ℤ[X] := X ^ 5 - C 2

def x5SubTwoQ : ℚ[X] := x5SubTwoZ.map (algebraMap ℤ ℚ)

theorem x5SubTwoZ_monic : x5SubTwoZ.Monic := by
  simp only [x5SubTwoZ]
  monicity!

theorem x5SubTwoZ_natDegree : x5SubTwoZ.natDegree = 5 := by
  simp only [x5SubTwoZ]
  compute_degree!

local notation "P2" => Ideal.span ({(2 : ℤ)} : Set ℤ)

theorem twoIdeal_isPrime : (P2).IsPrime := by
  exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2
    (by norm_num)

theorem x5SubTwoZ_isEisensteinAt : x5SubTwoZ.IsEisensteinAt P2 := by
  refine x5SubTwoZ_monic.isEisensteinAt_of_mem_of_notMem
    twoIdeal_isPrime.ne_top ?_ ?_
  · intro n hn
    rw [x5SubTwoZ_natDegree] at hn
    interval_cases n <;>
      norm_num [x5SubTwoZ, Ideal.mem_span_singleton]
  · rw [show x5SubTwoZ.coeff 0 = -2 by norm_num [x5SubTwoZ],
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

theorem x5SubTwoZ_irreducible : Irreducible x5SubTwoZ :=
  x5SubTwoZ_isEisensteinAt.irreducible twoIdeal_isPrime
    x5SubTwoZ_monic.isPrimitive
    (by rw [x5SubTwoZ_natDegree]; norm_num)

theorem x5SubTwoQ_monic : x5SubTwoQ.Monic := by
  simpa only [x5SubTwoQ] using
    x5SubTwoZ_monic.map (algebraMap ℤ ℚ)

theorem x5SubTwoQ_natDegree : x5SubTwoQ.natDegree = 5 := by
  rw [x5SubTwoQ, natDegree_map_eq_of_injective
    Int.cast_injective x5SubTwoZ, x5SubTwoZ_natDegree]

theorem x5SubTwoQ_irreducible : Irreducible x5SubTwoQ := by
  exact (x5SubTwoZ_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp x5SubTwoZ_irreducible

theorem x5SubTwoQ_map_complex :
    x5SubTwoQ.map (algebraMap ℚ ℂ) = X ^ 5 - C (2 : ℂ) := by
  simp [x5SubTwoQ, x5SubTwoZ]
  exact (Polynomial.C_eq_natCast (R := ℂ) 2).symm

/-! ## An actual ordered root tuple in `ℂ` -/

noncomputable def alpha : ℂ :=
  Classical.choose (by
    have hmap0 : x5SubTwoQ.map (algebraMap ℚ ℂ) ≠ 0 :=
      map_ne_zero x5SubTwoQ_irreducible.ne_zero
    have hmapDegree :
        (x5SubTwoQ.map (algebraMap ℚ ℂ)).degree ≠ 0 := by
      rw [degree_eq_natDegree hmap0,
        natDegree_map_eq_of_injective
          (algebraMap ℚ ℂ).injective x5SubTwoQ,
        x5SubTwoQ_natDegree]
      norm_num
    exact IsAlgClosed.exists_root
      (x5SubTwoQ.map (algebraMap ℚ ℂ)) hmapDegree)

theorem alpha_isRoot :
    (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot alpha := by
  unfold alpha
  exact Classical.choose_spec _

theorem alpha_pow_five : alpha ^ 5 = (2 : ℂ) := by
  have hroot := alpha_isRoot
  rw [x5SubTwoQ_map_complex] at hroot
  simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C,
    sub_eq_zero] using hroot

theorem alpha_ne_zero : alpha ≠ 0 := by
  intro h
  have hpow := alpha_pow_five
  rw [h] at hpow
  norm_num at hpow

abbrev omega : ℂ := squareRadicalPrimitiveFifthRoot

theorem omega_primitive : IsPrimitiveRoot omega 5 :=
  squareRadicalPrimitiveFifthRoot_primitive

def roots : Fin 5 → ℂ := Low.radicalRootTuple alpha omega

theorem roots_injective : Function.Injective roots := by
  exact Low.radicalRootTuple_injective alpha_ne_zero omega_primitive

theorem roots_are_roots (i : Fin 5) :
    (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot (roots i) := by
  rw [x5SubTwoQ_map_complex, ← alpha_pow_five]
  exact Low.radicalRootTuple_isRoot omega_primitive i

/-! The preceding pointwise statement is now upgraded to an exact root
multiset computation.  Thus the five displayed values are not merely five
distinct zeros: they exhaust all roots, with multiplicity, and give the
literal monic linear-factor decomposition of `X^5 - 2`. -/

def rootsMultiset : Multiset ℂ :=
  Finset.univ.1.map roots

@[simp]
theorem rootsMultiset_card : rootsMultiset.card = 5 := by
  simp [rootsMultiset]

theorem rootsMultiset_nodup : rootsMultiset.Nodup := by
  exact Finset.univ.nodup.map roots_injective

theorem rootsMultiset_eq_polynomial_roots :
    rootsMultiset = (x5SubTwoQ.map (algebraMap ℚ ℂ)).roots := by
  have hmap0 : x5SubTwoQ.map (algebraMap ℚ ℂ) ≠ 0 :=
    map_ne_zero x5SubTwoQ_irreducible.ne_zero
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset rootsMultiset_nodup]
    intro z hz
    simp only [rootsMultiset, Multiset.mem_map] at hz
    obtain ⟨i, _, rfl⟩ := hz
    exact (Polynomial.mem_roots hmap0).2 (roots_are_roots i)
  · rw [← (IsAlgClosed.splits
        (x5SubTwoQ.map (algebraMap ℚ ℂ))).natDegree_eq_card_roots,
      natDegree_map_eq_of_injective
        (algebraMap ℚ ℂ).injective x5SubTwoQ,
      x5SubTwoQ_natDegree, rootsMultiset_card]

theorem x5SubTwoQ_map_complex_factorization :
    x5SubTwoQ.map (algebraMap ℚ ℂ) =
      ∏ i : Fin 5, (X - C (roots i)) := by
  rw [(IsAlgClosed.splits
      (x5SubTwoQ.map (algebraMap ℚ ℂ))).eq_prod_roots_of_monic
        (x5SubTwoQ_monic.map (algebraMap ℚ ℂ)),
    ← rootsMultiset_eq_polynomial_roots]
  rw [Finset.prod_eq_multiset_prod]
  simp only [rootsMultiset, Multiset.map_map, Function.comp_apply]

theorem x5SubTwoQ_map_complex_isRoot_iff (z : ℂ) :
    (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot z ↔
      ∃ i : Fin 5, roots i = z := by
  have hmap0 : x5SubTwoQ.map (algebraMap ℚ ℂ) ≠ 0 :=
    map_ne_zero x5SubTwoQ_irreducible.ne_zero
  rw [← Polynomial.mem_roots hmap0,
    ← rootsMultiset_eq_polynomial_roots]
  constructor
  · intro hz
    rw [rootsMultiset, Multiset.mem_map] at hz
    obtain ⟨i, _, hi⟩ := hz
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    rw [rootsMultiset, Multiset.mem_map]
    exact ⟨i, by simp, hi⟩

/-! ## Scalar extension of rational invariants -/

def liftInvariant (p : MvPolynomial (Fin 5) ℚ) :
    MvPolynomial (Fin 5) ℂ :=
  MvPolynomial.map (algebraMap ℚ ℂ) p

theorem liftInvariant_invariantUnder
    {G : Subgroup (Equiv.Perm (Fin 5))}
    {p : MvPolynomial (Fin 5) ℚ}
    (hG : Action.InvariantUnder G p) :
    Action.InvariantUnder G (liftInvariant p) := by
  intro g hg
  have h := congrArg (MvPolynomial.map (algebraMap ℚ ℂ)) (hG g hg)
  simpa only [liftInvariant, Action.renameAction,
    MvPolynomial.map_rename] using h

theorem liftInvariant_totalDegree_le (p : MvPolynomial (Fin 5) ℚ) :
    (liftInvariant p).totalDegree ≤ p.totalDegree := by
  rw [liftInvariant, MvPolynomial.totalDegree, MvPolynomial.totalDegree,
    MvPolynomial.support_map_of_injective p (algebraMap ℚ ℂ).injective]

theorem liftInvariant_totalDegree_lt_five
    {p : MvPolynomial (Fin 5) ℚ} (hdegree : p.totalDegree < 5) :
    (liftInvariant p).totalDegree < 5 :=
  (liftInvariant_totalDegree_le p).trans_lt hdegree

/-! ## Paper-level irreducible witnesses for both relative groups -/

/-- The literal `S5/C5` orbit product fails separability on the irreducible
quintic `X^5 - 2`; the input supplies invariance and a degree bound, not a
collision or nonseparability certificate. -/
theorem irreducible_x5SubTwo_C5_relativeResolvent_not_separable
    {p : MvPolynomial (Fin 5) ℚ}
    (hC : Action.InvariantUnder Classification.standardC5 p)
    (hdegree : p.totalDegree < 5) :
    Irreducible x5SubTwoQ ∧
      Function.Injective roots ∧
      (∀ i : Fin 5,
        (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot (roots i)) ∧
      x5SubTwoQ.map (algebraMap ℚ ℂ) =
        ∏ i : Fin 5, (X - C (roots i)) ∧
      (∀ z : ℂ, (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot z ↔
        ∃ i : Fin 5, roots i = z) ∧
      ¬ (Resolvent.orbitResolvent Classification.standardC5
          (Action.specializedOrbitValue Classification.standardC5
            (liftInvariant p) (liftInvariant_invariantUnder hC) roots)).Separable := by
  refine ⟨x5SubTwoQ_irreducible, roots_injective, roots_are_roots,
    x5SubTwoQ_map_complex_factorization,
    x5SubTwoQ_map_complex_isRoot_iff, ?_⟩
  exact Low.lowDegree_cyclic_relativeResolvent_not_separable
    omega_primitive (liftInvariant_invariantUnder hC)
    (liftInvariant_totalDegree_lt_five hdegree)

/-- The separate literal `S5/D5` orbit product has the same failure on the
same irreducible quintic. -/
theorem irreducible_x5SubTwo_D5_relativeResolvent_not_separable
    {p : MvPolynomial (Fin 5) ℚ}
    (hD : Action.InvariantUnder Classification.standardD5 p)
    (hdegree : p.totalDegree < 5) :
    Irreducible x5SubTwoQ ∧
      Function.Injective roots ∧
      (∀ i : Fin 5,
        (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot (roots i)) ∧
      x5SubTwoQ.map (algebraMap ℚ ℂ) =
        ∏ i : Fin 5, (X - C (roots i)) ∧
      (∀ z : ℂ, (x5SubTwoQ.map (algebraMap ℚ ℂ)).IsRoot z ↔
        ∃ i : Fin 5, roots i = z) ∧
      ¬ (Resolvent.orbitResolvent Classification.standardD5
          (Action.specializedOrbitValue Classification.standardD5
            (liftInvariant p) (liftInvariant_invariantUnder hD) roots)).Separable := by
  refine ⟨x5SubTwoQ_irreducible, roots_injective, roots_are_roots,
    x5SubTwoQ_map_complex_factorization,
    x5SubTwoQ_map_complex_isRoot_iff, ?_⟩
  exact Low.lowDegree_dihedral_relativeResolvent_not_separable
    omega_primitive (liftInvariant_invariantUnder hD)
    (liftInvariant_totalDegree_lt_five hdegree)

end

end LeanProofs.PolynomialFormulas.LazardQuinticLowDegreeIrreducibleWitness
