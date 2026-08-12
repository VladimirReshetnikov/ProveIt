import PolynomialFormulas.LazardOptimality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

/-!
# The Artin--Schreier counterexample to Lazard's Section 2 scope

Lazard states the usual Galois-solvability/radical-solvability equivalence
over every coefficient field satisfying only `2 ≠ 0` and `5 ≠ 0`.  The
positive-characteristic converse needs an additional hypothesis.

We work over

`K = (algebraic closure of F_3)(t)`

and with `A(X) = X^3 - X - t`.  Degree at infinity proves that `A` is
irreducible; its derivative is `-1`, so it is separable.  Its three roots are
`a`, `a + 1`, and `a - 1`, hence its splitting field and Galois group both
have degree/order three.  In particular the Galois group is cyclic and
solvable.

The last part uses the *literal* prime-radical tower predicate from
`LazardOptimality`.  The algebraic closure of `F_3` supplies all roots of
unity of order prime to three.  A prime radical step of exponent three is
purely inseparable; a step of any other prime exponent has separable degree
one or that prime.  The tower law therefore makes the separable degree of a
finite ordinary radical tower prime to three.  Such a tower cannot contain a
root of `A`, since that root generates a separable cubic subextension.

There are no external certificates or assumed mathematical facts in the
endpoint: the counterexample is a closed theorem.  The focused module has
been accepted by Lean's kernel; its public aggregate and audit are checked
separately.
-/

noncomputable section

namespace LeanProofs.PolynomialFormulas.LazardArtinSchreierRadicalCounterexample

open Polynomial IntermediateField
open LeanProofs.PolynomialFormulas.LazardOptimality

set_option autoImplicit false

/-! ## The concrete coefficient field and polynomial -/

/-- An algebraically closed constant field of characteristic three. -/
abbrev Constants := AlgebraicClosure (ZMod 3)

/-- The rational function field over the algebraically closed constants. -/
abbrev F3barT := RatFunc Constants

local instance : CharP F3barT 3 := inferInstance

/-- The Artin--Schreier polynomial `X^3-X-t`. -/
def artinSchreierCubic : F3barT[X] :=
  X ^ 3 - (X + C (RatFunc.X : F3barT))

private theorem eval₂_artinSchreierCubic
    {E : Type*} [Ring E] (f : F3barT →+* E) (x : E) :
    artinSchreierCubic.eval₂ f x = x ^ 3 - (x + f RatFunc.X) := by
  simp [artinSchreierCubic]

/-- A useful strict form of the nonarchimedean degree rule. -/
private theorem intDegree_add_eq_left_of_gt
    {x y : F3barT} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0)
    (hdegree : RatFunc.intDegree y < RatFunc.intDegree x) :
    RatFunc.intDegree (x + y) = RatFunc.intDegree x := by
  have hupper := RatFunc.intDegree_add_le hy hxy
  have hreverse := RatFunc.intDegree_add_le
    (x := x + y) (y := -y) (neg_ne_zero.mpr hy) (by simpa using hx)
  simp only [add_neg_cancel_right, RatFunc.intDegree_neg] at hreverse
  omega

/-- No rational function over any field can satisfy `b^3-b=t`.  At infinity,
the left side has either nonpositive degree or positive degree divisible by
three, whereas `t` has degree one. -/
theorem ratFunc_cube_sub_self_ne_X (b : F3barT) :
    b ^ 3 - b ≠ (RatFunc.X : F3barT) := by
  intro h
  have hb : b ≠ 0 := by
    intro hb
    subst b
    apply RatFunc.X_ne_zero (K := Constants)
    simpa using h.symm
  have hpow : b ^ 3 ≠ 0 := pow_ne_zero 3 hb
  have hsum : b ^ 3 + -b ≠ 0 := by
    intro hzero
    apply RatFunc.X_ne_zero (K := Constants)
    calc
      (RatFunc.X : F3barT) = b ^ 3 - b := h.symm
      _ = b ^ 3 + -b := by rw [sub_eq_add_neg]
      _ = 0 := hzero
  have hdegree_pow :
      RatFunc.intDegree (b ^ 3) =
        RatFunc.intDegree b + RatFunc.intDegree b + RatFunc.intDegree b := by
    rw [show b ^ 3 = (b * b) * b by ring,
      RatFunc.intDegree_mul (mul_ne_zero hb hb) hb,
      RatFunc.intDegree_mul hb hb]
  have hdegree_result : RatFunc.intDegree (b ^ 3 - b) = 1 := by
    rw [h, RatFunc.intDegree_X]
  by_cases hpositive : 0 < RatFunc.intDegree b
  . have hstrict : RatFunc.intDegree (-b) < RatFunc.intDegree (b ^ 3) := by
      rw [RatFunc.intDegree_neg, hdegree_pow]
      omega
    have heq := intDegree_add_eq_left_of_gt hpow (neg_ne_zero.mpr hb)
      hsum hstrict
    rw [sub_eq_add_neg, heq, hdegree_pow] at hdegree_result
    omega
  . have hupper := RatFunc.intDegree_add_le
      (x := b ^ 3) (y := -b) (neg_ne_zero.mpr hb) hsum
    rw [show b ^ 3 + -b = b ^ 3 - b by ring,
      hdegree_result, RatFunc.intDegree_neg, hdegree_pow] at hupper
    omega

theorem artinSchreierCubic_natDegree : artinSchreierCubic.natDegree = 3 := by
  rw [artinSchreierCubic, natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simp

theorem artinSchreierCubic_monic : artinSchreierCubic.Monic := by
  rw [artinSchreierCubic]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  norm_num

theorem artinSchreierCubic_not_isRoot (b : F3barT) :
    ¬ artinSchreierCubic.IsRoot b := by
  intro hb
  apply ratFunc_cube_sub_self_ne_X b
  have hzero : b ^ 3 - (b + (RatFunc.X : F3barT)) = 0 := by
    simpa [Polynomial.IsRoot, artinSchreierCubic] using hb
  linear_combination hzero

theorem artinSchreierCubic_irreducible :
    Irreducible artinSchreierCubic := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  . simp [artinSchreierCubic_natDegree]
  . exact artinSchreierCubic_not_isRoot

theorem artinSchreierCubic_derivative :
    artinSchreierCubic.derivative = -1 := by
  have hthree : (3 : F3barT) = 0 := CharP.cast_eq_zero F3barT 3
  have htwo : (2 : F3barT) = -1 := by
    linear_combination hthree
  simp [artinSchreierCubic, htwo]

theorem artinSchreierCubic_separable : artinSchreierCubic.Separable := by
  rw [separable_iff_derivative_ne_zero artinSchreierCubic_irreducible,
    artinSchreierCubic_derivative]
  exact neg_ne_zero.mpr one_ne_zero

/-- Characteristic three satisfies exactly the two global exclusions printed
by Lazard. -/
theorem paper_global_characteristic_conditions :
    (2 : F3barT) ≠ 0 ∧ (5 : F3barT) ≠ 0 := by
  constructor
  . intro htwo
    have : 3 ∣ 2 := by
      rwa [← CharP.cast_eq_zero_iff F3barT 3 2]
    norm_num at this
  . intro hfive
    have : 3 ∣ 5 := by
      rwa [← CharP.cast_eq_zero_iff F3barT 3 5]
    norm_num at this

/-! ## The splitting field and its cyclic group of order three -/

section ArtinSchreierFactorization

variable {E : Type*} [Field E] [CharP E 3]

/-- Once one Artin--Schreier root is present, translating it by the three
prime-field constants gives the complete factorization. -/
theorem artinSchreier_factorization (a t : E) (ha : a ^ 3 - a = t) :
    X ^ 3 - (X + C t) =
      (X - C a) * (X - C (a + 1)) * (X - C (a - 1)) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [← ha]
  have hfrob :
      (X - C a : E[X]) ^ 3 = X ^ 3 - (C a) ^ 3 :=
    sub_pow_char (X : E[X]) (C a)
  calc
    X ^ 3 - (X + C (a ^ 3 - a)) =
        (X - C a) ^ 3 - (X - C a) := by
      rw [hfrob]
      simp only [map_sub, map_pow]
      ring
    _ = (X - C a) * (X - C (a + 1)) * (X - C (a - 1)) := by
      simp only [map_add, map_sub, map_one]
      ring

end ArtinSchreierFactorization

/-- A root in the canonical splitting field. -/
def splittingRoot : artinSchreierCubic.SplittingField :=
  rootOfSplits (SplittingField.splits artinSchreierCubic) (by
    rw [degree_map, degree_eq_natDegree artinSchreierCubic_monic.ne_zero,
      artinSchreierCubic_natDegree]
    norm_num)

theorem splittingRoot_isRoot :
    (artinSchreierCubic.map
      (algebraMap F3barT artinSchreierCubic.SplittingField)).IsRoot
      splittingRoot := by
  rw [Polynomial.IsRoot]
  simpa [splittingRoot] using
    eval_rootOfSplits (SplittingField.splits artinSchreierCubic) (by
      rw [degree_map, degree_eq_natDegree artinSchreierCubic_monic.ne_zero,
        artinSchreierCubic_natDegree]
      norm_num)

theorem splittingRoot_equation :
    splittingRoot ^ 3 - splittingRoot =
      algebraMap F3barT artinSchreierCubic.SplittingField RatFunc.X := by
  have hzero := splittingRoot_isRoot
  rw [Polynomial.IsRoot, Polynomial.eval_map,
    eval₂_artinSchreierCubic] at hzero
  linear_combination hzero

/-- The polynomial already splits after adjoining a single root. -/
theorem artinSchreierCubic_splits_adjoin_splittingRoot :
    (artinSchreierCubic.map
      (algebraMap F3barT F3barT⟮splittingRoot⟯)).Splits := by
  let a : F3barT⟮splittingRoot⟯ :=
    AdjoinSimple.gen F3barT splittingRoot
  have ha : a ^ 3 - a =
      algebraMap F3barT F3barT⟮splittingRoot⟯ RatFunc.X := by
    apply Subtype.ext
    simpa [a, AdjoinSimple.gen] using splittingRoot_equation
  rw [show artinSchreierCubic.map
      (algebraMap F3barT F3barT⟮splittingRoot⟯) =
        X ^ 3 -
          (X + C (algebraMap F3barT F3barT⟮splittingRoot⟯ RatFunc.X)) by
      simp [artinSchreierCubic]
      rfl]
  rw [artinSchreier_factorization a _ ha]
  exact ((Splits.X_sub_C a).mul (Splits.X_sub_C (a + 1))).mul
    (Splits.X_sub_C (a - 1))

/-- The simple field generated by one root is itself a splitting field. -/
theorem artinSchreierCubic_isSplittingField_adjoin_splittingRoot :
    Polynomial.IsSplittingField F3barT F3barT⟮splittingRoot⟯
      artinSchreierCubic := by
  apply IntermediateField.isSplittingField_iff.mpr
  refine ⟨artinSchreierCubic_splits_adjoin_splittingRoot, ?_⟩
  apply le_antisymm
  . rw [IntermediateField.adjoin_simple_le_iff]
    apply IntermediateField.subset_adjoin
    rw [artinSchreierCubic_monic.mem_rootSet]
    simpa [Polynomial.aeval_def] using splittingRoot_isRoot
  . rw [IntermediateField.adjoin_le_iff]
    intro y hy
    have hyroot := artinSchreierCubic_monic.mem_rootSet.mp hy
    have hyint : IsIntegral F3barT y :=
      ⟨artinSchreierCubic, artinSchreierCubic_monic, by
        exact hyroot⟩
    have hmin : minpoly F3barT y = artinSchreierCubic :=
      (minpoly.eq_of_irreducible_of_monic artinSchreierCubic_irreducible
        hyroot artinSchreierCubic_monic).symm
    apply hyint.mem_intermediateField_of_minpoly_splits
    simpa [hmin] using artinSchreierCubic_splits_adjoin_splittingRoot

/-- The canonical splitting field has degree three. -/
theorem artinSchreierCubic_splittingField_finrank :
    Module.finrank F3barT artinSchreierCubic.SplittingField = 3 := by
  letI : Polynomial.IsSplittingField F3barT F3barT⟮splittingRoot⟯
      artinSchreierCubic :=
    artinSchreierCubic_isSplittingField_adjoin_splittingRoot
  let e : F3barT⟮splittingRoot⟯ ≃ₐ[F3barT]
      artinSchreierCubic.SplittingField :=
    Polynomial.IsSplittingField.algEquiv
      (L := F3barT⟮splittingRoot⟯) artinSchreierCubic
  have hrootIntegral : IsIntegral F3barT splittingRoot :=
    ⟨artinSchreierCubic, artinSchreierCubic_monic, by
      simpa [Polynomial.aeval_def] using splittingRoot_isRoot⟩
  have hmin : minpoly F3barT splittingRoot = artinSchreierCubic :=
    (minpoly.eq_of_irreducible_of_monic artinSchreierCubic_irreducible
      (by simpa [Polynomial.aeval_def] using splittingRoot_isRoot)
      artinSchreierCubic_monic).symm
  rw [← LinearEquiv.finrank_eq e.toLinearEquiv,
    IntermediateField.adjoin.finrank hrootIntegral,
    hmin,
    artinSchreierCubic_natDegree]

theorem artinSchreierCubic_gal_card :
    Nat.card artinSchreierCubic.Gal = 3 := by
  rw [Polynomial.Gal.card_of_separable artinSchreierCubic_separable,
    artinSchreierCubic_splittingField_finrank]

theorem artinSchreierCubic_gal_isCyclic :
    IsCyclic artinSchreierCubic.Gal := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact isCyclic_of_prime_card artinSchreierCubic_gal_card

theorem artinSchreierCubic_gal_isSolvable :
    IsSolvable artinSchreierCubic.Gal := by
  letI : IsCyclic artinSchreierCubic.Gal :=
    artinSchreierCubic_gal_isCyclic
  exact isSolvable_of_comm IsMulCommutative.is_comm.comm

/-! ## Prime radical steps have separable degree prime to three -/

section RadicalDegree

variable {Omega : Type*} [Field Omega] [Algebra F3barT Omega]

/-- Every root of unity of prime order different from three which occurs in
the ambient field already belongs to every intermediate field over
`F3barT`.  This is where algebraically closed constants are used. -/
theorem prime_rootOfUnity_mem (K : IntermediateField F3barT Omega)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) (z : Omega)
    (hz : z ^ p = 1) : z ∈ K := by
  have hpCast : (p : ZMod 3) ≠ 0 := by
    intro hzero
    have hdvd : 3 ∣ p := by
      rwa [← CharP.cast_eq_zero_iff (R := ZMod 3)]
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    . norm_num at h
    . exact hp3 h.symm
  letI : NeZero (p : ZMod 3) := ⟨hpCast⟩
  obtain ⟨zeta, hzeta⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot Constants p
  let cK : Constants →+* K :=
    (algebraMap F3barT K).comp (algebraMap Constants F3barT)
  have hzetaK : IsPrimitiveRoot (cK zeta) p :=
    hzeta.map_of_injective cK.injective
  have hsplit : (X ^ p - 1 : K[X]).Splits :=
    by
      simpa using X_pow_sub_C_splits_of_isPrimitiveRoot
        (α := (1 : K)) (a := (1 : K)) hzetaK (by simp)
  have hroot :
      ((X ^ p - 1 : K[X]).map K.val).IsRoot z := by
    simp [hz]
  have hrange := hsplit.mem_range_of_isRoot
    (by simpa using X_pow_sub_C_ne_zero hp.pos (1 : K)) hroot
  obtain ⟨w, rfl⟩ := hrange
  exact w.property

/-- The element in a simple radical step is integral over the preceding
field. -/
private theorem integral_of_prime_pow_mem
    (K : IntermediateField F3barT Omega) (alpha : Omega) (p : ℕ)
    (hp : p.Prime) (hpow : alpha ^ p ∈ K) : IsIntegral K alpha := by
  let a : K := ⟨alpha ^ p, hpow⟩
  refine ⟨X ^ p - C a, monic_X_pow_sub_C a hp.ne_zero, ?_⟩
  simp [a]

/-- For a non-characteristic prime step, either the generator was already
present or its pure polynomial is irreducible of that prime degree. -/
private theorem purePolynomial_irreducible_of_not_mem
    (K : IntermediateField F3barT Omega) (alpha : Omega) (p : ℕ)
    (hp : p.Prime) (hp3 : p ≠ 3) (hpow : alpha ^ p ∈ K)
    (halpha : alpha ∉ K) :
    Irreducible (X ^ p - C (⟨alpha ^ p, hpow⟩ : K)) := by
  apply X_pow_sub_C_irreducible_of_prime hp
  intro b hb
  have hbp : (b : Omega) ^ p = alpha ^ p := congrArg Subtype.val hb
  have halpha0 : alpha ≠ 0 := by
    intro ha
    exact halpha (ha.symm ▸ K.zero_mem)
  have hb0 : (b : Omega) ≠ 0 := by
    intro hbzero
    apply halpha0
    apply eq_zero_of_pow_eq_zero
    rw [← hbp, hbzero, zero_pow hp.ne_zero]
  let z : Omega := alpha / (b : Omega)
  have halphaPow0 : alpha ^ p ≠ 0 := pow_ne_zero p halpha0
  have hz : z ^ p = 1 := by
    dsimp [z]
    rw [div_pow, hbp]
    exact div_self halphaPow0
  have hzK : z ∈ K := prime_rootOfUnity_mem K p hp hp3 z hz
  apply halpha
  have hbK : (b : Omega) ∈ K := b.property
  have hmul : z * (b : Omega) ∈ K := K.mul_mem hzK hbK
  have hzmul : z * (b : Omega) = alpha := by
    dsimp [z]
    exact div_mul_cancel₀ alpha hb0
  exact hzmul ▸ hmul

/-- A single prime radical adjunction has separable degree one or its prime
exponent; exponent three contributes only the first alternative. -/
theorem primeRadicalAdjoin_finSepDegree
    (K : IntermediateField F3barT Omega) (alpha : Omega) (p : ℕ)
    (hp : p.Prime) (hpow : alpha ^ p ∈ K) :
    Field.finSepDegree K K⟮alpha⟯ = 1 ∨
      (p ≠ 3 ∧ Field.finSepDegree K K⟮alpha⟯ = p) := by
  have halg := (integral_of_prime_pow_mem K alpha p hp hpow).isAlgebraic
  by_cases hp3 : p = 3
  . subst p
    left
    have hpure : IsPurelyInseparable K K⟮alpha⟯ :=
      (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem
        K Omega 3).2 ⟨1, ?_⟩
    . letI : IsPurelyInseparable K K⟮alpha⟯ := hpure
      exact IsPurelyInseparable.finSepDegree_eq_one K K⟮alpha⟯
    . refine ⟨(⟨alpha ^ 3, hpow⟩ : K), ?_⟩
      simp
  . by_cases halpha : alpha ∈ K
    . left
      have hadjoin : K⟮alpha⟯ = ⊥ := by
        rw [IntermediateField.adjoin_simple_eq_bot_iff,
          IntermediateField.mem_bot]
        exact ⟨(⟨alpha, halpha⟩ : K), rfl⟩
      rw [hadjoin, IntermediateField.finSepDegree_bot]
    . right
      refine ⟨hp3, ?_⟩
      have hirr := purePolynomial_irreducible_of_not_mem
        K alpha p hp hp3 hpow halpha
      have hmin : minpoly K alpha =
          X ^ p - C (⟨alpha ^ p, hpow⟩ : K) := by
        symm
        exact minpoly.eq_of_irreducible_of_monic hirr (by simp)
          (monic_X_pow_sub_C _ hp.ne_zero)
      have hpCast : (p : ZMod 3) ≠ 0 := by
        intro hzero
        have hdvd : 3 ∣ p := by
          rwa [← CharP.cast_eq_zero_iff (R := ZMod 3)]
        rcases (Nat.dvd_prime hp).mp hdvd with h | h
        . norm_num at h
        . exact hp3 h.symm
      letI : NeZero (p : ZMod 3) := ⟨hpCast⟩
      obtain ⟨zeta, hzeta⟩ :=
        HasEnoughRootsOfUnity.exists_primitiveRoot Constants p
      let cK : Constants →+* K :=
        (algebraMap F3barT K).comp (algebraMap Constants F3barT)
      have hzetaK : IsPrimitiveRoot (cK zeta) p :=
        hzeta.map_of_injective cK.injective
      have hroots : (primitiveRoots p K).Nonempty := by
        refine ⟨cK zeta, ?_⟩
        rwa [mem_primitiveRoots hp.pos]
      have hsep :
          (X ^ p - C (⟨alpha ^ p, hpow⟩ : K)).Separable :=
        Polynomial.separable_X_pow_sub_C_of_irreducible hroots _ hirr
      rw [IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
          K Omega halg,
        hmin, hsep.natSepDegree_eq_natDegree,
        natDegree_X_pow_sub_C]

/-- Transport the preceding calculation from `K⟮alpha⟯` to the literal
`K ⊔ F3barT⟮alpha⟯` used in `IsSimpleRadicalStep`. -/
private theorem simpleRadicalStep_relative_finSepDegree
    {K L : IntermediateField F3barT Omega}
    (h : IsSimpleRadicalStep F3barT Omega K L) :
    letI : Algebra K L := (IntermediateField.inclusion (h.le F3barT Omega)).toAlgebra
    Field.finSepDegree K L = 1 ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧ Field.finSepDegree K L = p := by
  obtain ⟨alpha, p, hp, hpow, rfl⟩ := h
  let L : IntermediateField F3barT Omega := K ⊔ F3barT⟮alpha⟯
  have hKL : K ≤ L := le_sup_left
  have hext : IntermediateField.extendScalars hKL = K⟮alpha⟯ := by
    apply IntermediateField.restrictScalars_injective F3barT
    rw [IntermediateField.extendScalars_restrictScalars]
    exact (IntermediateField.restrictScalars_adjoin_eq_sup
      (F := F3barT) K ({alpha} : Set Omega)).symm
  have hdegree := primeRadicalAdjoin_finSepDegree K alpha p hp hpow
  rw [← hext] at hdegree
  exact hdegree.imp_right
    (fun hpdeg => ⟨p, hp, hpdeg.1, hpdeg.2⟩)

/-- Every literal simple radical step is algebraic. -/
private theorem simpleRadicalStep_isAlgebraic
    {K L : IntermediateField F3barT Omega}
    (h : IsSimpleRadicalStep F3barT Omega K L) :
    letI : Algebra K L := (IntermediateField.inclusion (h.le F3barT Omega)).toAlgebra
    Algebra.IsAlgebraic K L := by
  obtain ⟨alpha, p, hp, hpow, rfl⟩ := h
  let L : IntermediateField F3barT Omega := K ⊔ F3barT⟮alpha⟯
  have hKL : K ≤ L := le_sup_left
  have hext : IntermediateField.extendScalars hKL = K⟮alpha⟯ := by
    apply IntermediateField.restrictScalars_injective F3barT
    rw [IntermediateField.extendScalars_restrictScalars]
    exact (IntermediateField.restrictScalars_adjoin_eq_sup
      (F := F3barT) K ({alpha} : Set Omega)).symm
  have halg := integral_of_prime_pow_mem K alpha p hp hpow
  have hadjoin : Algebra.IsAlgebraic K K⟮alpha⟯ :=
    IntermediateField.isAlgebraic_adjoin_simple halg
  rw [← hext] at hadjoin
  exact hadjoin

/-- A finite literal radical tower is algebraic over its base.  This is
proved from the defining prime-power equation at every step; no ambient
algebraicity assumption is used. -/
theorem radicalExtension_isAlgebraic
    {L : IntermediateField F3barT Omega}
    (h : IsRadicalExtension F3barT Omega ⊥ L) :
    Algebra.IsAlgebraic F3barT L := by
  induction h with
  | refl =>
      exact (IntermediateField.botEquiv F3barT Omega).symm.isAlgebraic
  | @tail K M hreach hstep ih =>
      have hKM : K ≤ M := hstep.le F3barT Omega
      letI : Algebra K M := (IntermediateField.inclusion hKM).toAlgebra
      haveI : IsScalarTower F3barT K M :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra.IsAlgebraic F3barT K := ih
      letI : Algebra.IsAlgebraic K M :=
        simpleRadicalStep_isAlgebraic hstep
      exact Algebra.IsAlgebraic.trans F3barT K M

/-- The separable degree of every finite literal prime-radical tower over
`F3barT` is prime to three. -/
theorem radicalExtension_finSepDegree_not_dvd_three
    {L : IntermediateField F3barT Omega}
    (h : IsRadicalExtension F3barT Omega ⊥ L) :
    ¬ 3 ∣ Field.finSepDegree F3barT L := by
  induction h with
  | refl =>
      rw [IntermediateField.finSepDegree_bot]
      norm_num
  | @tail K M hreach hstep ih =>
      have hKM : K ≤ M := hstep.le F3barT Omega
      letI : Algebra K M := (IntermediateField.inclusion hKM).toAlgebra
      haveI : IsScalarTower F3barT K M :=
        IsScalarTower.of_algebraMap_eq' rfl
      haveI : Algebra.IsAlgebraic K M :=
        simpleRadicalStep_isAlgebraic hstep
      have htower :=
        Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F3barT K M
      rcases simpleRadicalStep_relative_finSepDegree hstep with hdegree | hdegree
      . rw [hdegree, mul_one] at htower
        rwa [← htower]
      . obtain ⟨p, hp, hp3, hdegree⟩ := hdegree
        rw [hdegree] at htower
        intro hthree
        have hdiv : 3 ∣ Field.finSepDegree F3barT K * p := by
          rwa [htower]
        rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdiv with hleft | hright
        . exact ih hleft
        . rcases (Nat.dvd_prime hp).mp hright with h | h
          . norm_num at h
          . exact hp3 h.symm

end RadicalDegree

/-! ## No ordinary radical tower contains an Artin--Schreier root -/

/-- A root of the concrete cubic generates a separable extension of degree
three in any ambient field. -/
theorem root_finSepDegree
    {Omega : Type*} [Field Omega] [Algebra F3barT Omega]
    (x : Omega) (hx : Polynomial.aeval x artinSchreierCubic = 0) :
    Field.finSepDegree F3barT F3barT⟮x⟯ = 3 := by
  have hmin : minpoly F3barT x = artinSchreierCubic :=
    (minpoly.eq_of_irreducible_of_monic artinSchreierCubic_irreducible
      hx artinSchreierCubic_monic).symm
  have hxint : IsIntegral F3barT x :=
    ⟨artinSchreierCubic, artinSchreierCubic_monic, hx⟩
  have hxalg : IsAlgebraic F3barT x := hxint.isAlgebraic
  rw [IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree
      F3barT Omega hxalg,
    hmin, artinSchreierCubic_separable.natSepDegree_eq_natDegree,
    artinSchreierCubic_natDegree]

/-- The exact no-tower theorem: this quantifies over the same
`IsRadicalExtension` definition used for Lazard's displayed radical fields. -/
theorem no_radicalExtension_contains_root
    {Omega : Type*} [Field Omega] [Algebra F3barT Omega]
    {x : Omega} (hx : Polynomial.aeval x artinSchreierCubic = 0) :
    ¬ ∃ L : IntermediateField F3barT Omega,
      IsRadicalExtension F3barT Omega ⊥ L ∧ x ∈ L := by
  rintro ⟨L, hradical, hxL⟩
  have hprimeToThree :=
    radicalExtension_finSepDegree_not_dvd_three hradical
  let A : IntermediateField F3barT Omega := F3barT⟮x⟯
  have hAL : A ≤ L := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact hxL
  letI : Algebra A L := (IntermediateField.inclusion hAL).toAlgebra
  haveI : IsScalarTower F3barT A L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsAlgebraic F3barT L :=
    radicalExtension_isAlgebraic hradical
  haveI : Algebra.IsAlgebraic A L := by
    exact Algebra.IsAlgebraic.tower_top (K := F3barT) A
  have htower :=
    Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F3barT A L
  have hA : Field.finSepDegree F3barT A = 3 := root_finSepDegree x hx
  apply hprimeToThree
  refine ⟨Field.finSepDegree A L, ?_⟩
  simpa [hA] using htower.symm

/-- The paper-facing ordinary-radical notion: one finite literal radical
tower in an algebraic closure contains every root. -/
def SolvableByOrdinaryRadicals (p : F3barT[X]) : Prop :=
  ∃ L : IntermediateField F3barT (AlgebraicClosure F3barT),
    IsRadicalExtension F3barT (AlgebraicClosure F3barT) ⊥ L ∧
      ∀ x : AlgebraicClosure F3barT,
        (p.map (algebraMap F3barT (AlgebraicClosure F3barT))).IsRoot x →
          x ∈ L

theorem artinSchreierCubic_not_solvableByOrdinaryRadicals :
    ¬ SolvableByOrdinaryRadicals artinSchreierCubic := by
  rintro ⟨L, hradical, hall⟩
  have hdegree :
      (artinSchreierCubic.map
        (algebraMap F3barT (AlgebraicClosure F3barT))).degree ≠ 0 := by
    rw [degree_map, degree_eq_natDegree artinSchreierCubic_monic.ne_zero,
      artinSchreierCubic_natDegree]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    (artinSchreierCubic.map
      (algebraMap F3barT (AlgebraicClosure F3barT))) hdegree
  apply no_radicalExtension_contains_root
    (Omega := AlgebraicClosure F3barT)
    (x := x) (by simpa [Polynomial.aeval_def] using hx)
  exact ⟨L, hradical, hall x hx⟩

/-- Closed literal refutation of the Section 2 equivalence at the paper's
printed characteristic scope. -/
theorem closed_sectionTwo_solvabilityEquivalence_counterexample :
    (2 : F3barT) ≠ 0 ∧
      (5 : F3barT) ≠ 0 ∧
      artinSchreierCubic.Monic ∧
      Irreducible artinSchreierCubic ∧
      artinSchreierCubic.Separable ∧
      Nat.card artinSchreierCubic.Gal = 3 ∧
      IsCyclic artinSchreierCubic.Gal ∧
      IsSolvable artinSchreierCubic.Gal ∧
      ¬ SolvableByOrdinaryRadicals artinSchreierCubic := by
  exact ⟨paper_global_characteristic_conditions.1,
    paper_global_characteristic_conditions.2,
    artinSchreierCubic_monic,
    artinSchreierCubic_irreducible,
    artinSchreierCubic_separable,
    artinSchreierCubic_gal_card,
    artinSchreierCubic_gal_isCyclic,
    artinSchreierCubic_gal_isSolvable,
    artinSchreierCubic_not_solvableByOrdinaryRadicals⟩

/-- The exact biconditional printed in Section 2 is false. -/
theorem sectionTwo_solvabilityEquivalence_is_false :
    ¬ (SolvableByOrdinaryRadicals artinSchreierCubic ↔
      IsSolvable artinSchreierCubic.Gal) := by
  intro hiff
  exact artinSchreierCubic_not_solvableByOrdinaryRadicals
    (hiff.mpr artinSchreierCubic_gal_isSolvable)

end LeanProofs.PolynomialFormulas.LazardArtinSchreierRadicalCounterexample
