import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Tactic
import PolynomialFormulas.LazardQuinticDiscriminant
import PolynomialFormulas.LazardQuinticF20Action
import PolynomialFormulas.QuinticX5Add20XAdd32DihedralFinite
import PolynomialFormulas.QuinticX5Add20XAdd32DihedralDiscriminant
import PolynomialFormulas.QuinticScalarResolventCriterion

/-!
# The Galois group of `X^5 + 20 X + 32`

The exact Galois group of `X^5 + 20 X + 32` is the dihedral group of order
ten, not the Frobenius group of order twenty.  The proof deliberately keeps
the three independent certificates visible:

* Eisenstein after the translation `X \mapsto X + 3` proves irreducibility;
* `40` is a root of the Frobenius--Dummit sextic, so the Galois group is
  solvable;
* the polynomial discriminant is `64000^2`, so every root permutation is
  even.

Complex conjugation is nontrivial because this strictly increasing real
quintic has at most one real root while it has five complex roots.  It
therefore supplies an element of order two.  A transitive solvable subgroup
of `S_5` consisting of even permutations and containing an involution is a
conjugate of the displayed standard `D_5`.

Besides the concrete example, this module records the two reusable bridges
that the argument needs: the square-discriminant parity criterion for a monic
irreducible quintic, and the corresponding finite-group recognition lemma.
-/

open scoped BigOperators Polynomial
open Polynomial Equiv

namespace LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral

open LazardQuintic
open QuinticRadicalDecidability
open QuinticDummitCoefficients
open ComputableDummitCoefficients

set_option autoImplicit false

/-! ## Recognizing the dihedral subgroup -/

/-- A transitive solvable subgroup of `S_5` which is even and has an
involution is dihedral.  Solvability first puts it in a conjugate of `F_20`;
the preceding intersection calculation sharpens this to a conjugate of
`D_5`.  Divisibility by both `5` and `2` then forces equality. -/
theorem isConjugateTo_standardD5_of_solvable_even_of_order_two
    (H : Subgroup Classification.S5)
    [MulAction.IsPretransitive H (Fin 5)]
    (hsolvable : IsSolvable H)
    (heven : H ≤ Classification.standardA5)
    (htwo : ∃ a : H, orderOf a = 2) :
    Classification.IsConjugateTo H Classification.standardD5 := by
  letI : IsSolvable H := hsolvable
  obtain ⟨g, hF⟩ :=
    Fin5Solvable.solvable_transitive_le_map_conj_standardF20 H
  let e : MulAut Classification.S5 := MulAut.conj g
  have hAmap :
      Classification.standardA5.map e.toMonoidHom =
        Classification.standardA5 := by
    rw [MulEquiv.toMonoidHom_eq_coe]
    simpa only [e] using
      (Subgroup.Normal.map_conj_eq
        (H := Classification.standardA5) g)
  have hDmap :
      Classification.standardD5.map e.toMonoidHom =
        Classification.standardF20.map e.toMonoidHom ⊓
          Classification.standardA5 := by
    calc
      Classification.standardD5.map e.toMonoidHom =
          (Classification.standardF20 ⊓
              Classification.standardA5).map e.toMonoidHom :=
        congrArg (fun K : Subgroup Classification.S5 => K.map e.toMonoidHom)
          Classification.standardF20_inf_standardA5_eq_standardD5.symm
      _ = Classification.standardF20.map e.toMonoidHom ⊓
          Classification.standardA5.map e.toMonoidHom :=
        Subgroup.map_inf _ _ _ e.injective
      _ = Classification.standardF20.map e.toMonoidHom ⊓
          Classification.standardA5 := by rw [hAmap]
  have hD : H ≤ Classification.standardD5.map e.toMonoidHom := by
    rw [hDmap]
    exact le_inf hF heven
  have hcardD :
      Nat.card (Classification.standardD5.map e.toMonoidHom) = 10 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Classification.natCard_standardD5]
  have hcardLe : Nat.card H ≤ 10 := by
    have h := Nat.card_le_card_of_injective
      (Subgroup.inclusion hD) (Subgroup.inclusion_injective hD)
    simpa only [hcardD] using h
  have hfive : 5 ∣ Nat.card H :=
    Fin5TransitiveC5.five_dvd_natCard_of_pretransitive H
  obtain ⟨a, ha⟩ := htwo
  have htwoDvd : 2 ∣ Nat.card H := by
    simpa only [ha] using orderOf_dvd_natCard a
  have hten : 10 ∣ Nat.card H := by
    simpa only [show 10 = 2 * 5 by norm_num] using
      (show Nat.Coprime 2 5 by norm_num).mul_dvd_of_dvd_of_dvd
        htwoDvd hfive
  have hcardPos : 0 < Nat.card H := Nat.card_pos
  have hcardH : Nat.card H = 10 := by
    obtain ⟨k, hk⟩ := hten
    omega
  have hEq : H = Classification.standardD5.map e.toMonoidHom := by
    apply Subgroup.eq_of_le_of_card_ge hD
    rw [hcardD, hcardH]
  exact ⟨g, hEq.symm⟩

/-! ## The concrete polynomial and its three certificates -/

/-- The integral monic coefficient record for `X^5 + 20 X + 32`. -/
def target : MonicQuintic where
  B := 0
  C := 0
  D := 0
  E := 20
  H := 32

/-- Its Eisenstein translate by `X \mapsto X + 3`. -/
noncomputable def shiftedTargetZ : ℤ[X] :=
  X ^ 5 + C 15 * X ^ 4 + C 90 * X ^ 3 + C 270 * X ^ 2 +
    C 425 * X + C 335

/-- The rational polynomial whose Galois group is being classified. -/
noncomputable abbrev targetQ : ℚ[X] :=
  monicQuinticRatPolynomial target

theorem target_polynomial_comp_X_add_three :
    target.polynomial.comp (X + C 3) = shiftedTargetZ := by
  simp [target, MonicQuintic.polynomial, shiftedTargetZ]
  ring

theorem shiftedTargetZ_monic : shiftedTargetZ.Monic := by
  simp only [shiftedTargetZ]
  monicity!

theorem shiftedTargetZ_natDegree : shiftedTargetZ.natDegree = 5 := by
  simp only [shiftedTargetZ]
  compute_degree!

local notation "P5" => Ideal.span ({(5 : ℤ)} : Set ℤ)

theorem fiveIdeal_isPrime : (P5 : Ideal ℤ).IsPrime := by
  exact (Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)).2
    (by decide)

theorem shiftedTargetZ_isEisensteinAt :
    shiftedTargetZ.IsEisensteinAt P5 := by
  refine shiftedTargetZ_monic.isEisensteinAt_of_mem_of_notMem
    fiveIdeal_isPrime.ne_top ?_ ?_
  · intro n hn
    rw [shiftedTargetZ_natDegree] at hn
    interval_cases n <;>
      simp [shiftedTargetZ, Polynomial.coeff_X,
        Ideal.mem_span_singleton]
  · rw [show shiftedTargetZ.coeff 0 = 335 by
          norm_num [shiftedTargetZ],
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

theorem shiftedTargetZ_irreducible : Irreducible shiftedTargetZ :=
  shiftedTargetZ_isEisensteinAt.irreducible fiveIdeal_isPrime
    shiftedTargetZ_monic.isPrimitive
    (by rw [shiftedTargetZ_natDegree]; norm_num)

theorem target_polynomial_irreducible : Irreducible target.polynomial := by
  have himage :
      Irreducible ((Polynomial.algEquivAevalXAddC (3 : ℤ))
        target.polynomial) := by
    simpa only [Polynomial.algEquivAevalXAddC_apply,
      ← Polynomial.comp_eq_aeval, target_polynomial_comp_X_add_three] using
        shiftedTargetZ_irreducible
  exact (MulEquiv.irreducible_iff
    (Polynomial.algEquivAevalXAddC (3 : ℤ))).mp himage

theorem targetQ_irreducible : Irreducible targetQ := by
  exact (target.polynomial_monic.irreducible_iff_irreducible_map_fraction_map
    (K := ℚ)).mp target_polynomial_irreducible

@[simp] theorem targetQ_natDegree : targetQ.natDegree = 5 :=
  monicQuinticRatPolynomial_natDegree target

theorem targetQ_monic : targetQ.Monic :=
  monicQuinticRatPolynomial_monic target

/-- The seven coefficients, in ascending order, of the exact Dummit sextic
for the target quintic. -/
def targetDummitCoefficients : IntegerSextic :=
  ![-180224000000, -1638400000, 64000000, 1280000, 16000, 160, 1]

/-- Exact kernel evaluation of the certified Dummit table at
`(0,0,0,20,-32)`. -/
theorem explicitDummitCoefficients_target :
    explicitDummitCoefficients target = targetDummitCoefficients := by
  set_option maxRecDepth 1000000 in
  set_option maxHeartbeats 20000000 in
    funext i
    fin_cases i <;>
      simp [explicitDummitCoefficients, targetDummitCoefficients,
        ComputableDummitCoefficients.dummitTable,
        ComputableDummitCoefficients.SparsePolynomial.eval,
        ComputableDummitCoefficients.SparseTerm.eval,
        QuinticDummitCoefficients.elementaryCoefficients, target]

/-- `40` is an exact rational root of the Dummit sextic. -/
theorem targetDummit_hasRationalRoot :
    (explicitDummitCoefficients target).HasRationalRoot := by
  refine ⟨40, ?_⟩
  rw [IntegerSextic.polynomial_aeval,
    explicitDummitCoefficients_target]
  norm_num [IntegerSextic.evalRat, targetDummitCoefficients,
    Fin.sum_univ_succ]

/-- The exact scalar-resolvent certificate proves solvability of the Galois
group; it does not yet identify which solvable transitive subgroup occurs. -/
theorem targetQ_gal_isSolvable : IsSolvable targetQ.Gal :=
  (QuinticScalarResolventCriterion.explicitDummitCoefficients_hasRationalRoot_iff_gal_isSolvable
    target targetQ_irreducible).mp targetDummit_hasRationalRoot

/-- The same target as a depressed quintic, for the explicit discriminant
formula. -/
def targetDepressedQ : DepressedQuintic ℚ where
  p := 0
  q := 0
  r := 20
  s := 32

theorem targetQ_eq_targetDepressedQ_polynomial :
    targetQ = targetDepressedQ.polynomial := by
  ext n
  simp [targetQ, target, monicQuinticRatPolynomial,
    MonicQuintic.polynomial, targetDepressedQ, DepressedQuintic.polynomial]
  rw [← Polynomial.C_ofNat 32]

/-- The target discriminant is the rational square `64000^2`. -/
theorem targetQ_discr : targetQ.discr = (64000 : ℚ) ^ 2 := by
  rw [targetQ_eq_targetDepressedQ_polynomial,
    ← discriminant_eq_polynomial_discr]
  norm_num [targetDepressedQ, discriminant]

theorem target_rootPermutationGroup_le_standardA5 :
    QuinticScalarGaloisBridge.rootPermutationGroup targetQ
      targetQ_irreducible targetQ_natDegree ≤
      Classification.standardA5 :=
  rootPermutationGroup_le_alternating_of_discr_eq_sq targetQ
    targetQ_irreducible targetQ_monic targetQ_natDegree 64000 targetQ_discr

/-- Over the reals, `x^5 + 20x + 32` is strictly increasing, so it has at
most one real root. -/
theorem targetQ_real_rootSet_card_le_one :
    (targetQ.rootSet ℝ).toFinset.card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro x y hx hy
  have hx0 := (mem_rootSet.mp (Set.mem_toFinset.mp hx)).2
  have hy0 := (mem_rootSet.mp (Set.mem_toFinset.mp hy)).2
  have hstrict : StrictMono (fun z : ℝ => z ^ 5 + 20 * z + 32) := by
    intro a b hab
    have hpow : a ^ 5 < b ^ 5 :=
      (show Odd 5 by norm_num).strictMono_pow hab
    have hlinear : 20 * a < 20 * b :=
      mul_lt_mul_of_pos_left hab (by norm_num)
    simpa [add_comm, add_left_comm, add_assoc] using
      add_lt_add_right (add_lt_add hpow hlinear) 32
  have hx1 : x ^ 5 + 20 * x + 32 = 0 := by
    simpa [targetQ, target, monicQuinticRatPolynomial,
      MonicQuintic.polynomial, map_ofNat] using hx0
  have hy1 : y ^ 5 + 20 * y + 32 = 0 := by
    simpa [targetQ, target, monicQuinticRatPolynomial,
      MonicQuintic.polynomial, map_ofNat] using hy0
  exact hstrict.injective (hx1.trans hy1.symm)

/-- Complex conjugation gives an element of order two in the faithful
five-root permutation image.  We only need the at-most-one-real-root result:
five distinct complex roots then force conjugation to move some root. -/
theorem target_rootPermutationGroup_exists_orderOf_two :
    ∃ a : QuinticScalarGaloisBridge.rootPermutationGroup targetQ
      targetQ_irreducible
      targetQ_natDegree, orderOf a = 2 := by
  classical
  letI : Fact ((targetQ.map (algebraMap ℚ ℂ)).Splits) :=
    Polynomial.Gal.splits_ℚ_ℂ
  let tau : targetQ.Gal :=
    Polynomial.Gal.restrict targetQ ℂ
      (Complex.conjAe.restrictScalars ℚ)
  let pi : Equiv.Perm (targetQ.rootSet ℂ) :=
    Polynomial.Gal.galActionHom targetQ ℂ tau
  have hcomplex0 := card_rootSet_eq_natDegree targetQ_irreducible.separable
    (IsAlgClosed.splits (targetQ.map (algebraMap ℚ ℂ)))
  have hcomplex : (targetQ.rootSet ℂ).toFinset.card = 5 := by
    rw [Set.toFinset_card, hcomplex0, targetQ_natDegree]
  have hcard :=
    Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv targetQ
  have hreal := targetQ_real_rootSet_card_le_one
  have hsupport : 0 < pi.support.card := by
    change (targetQ.rootSet ℂ).toFinset.card =
      (targetQ.rootSet ℝ).toFinset.card + pi.support.card at hcard
    omega
  have hpiNe : pi ≠ 1 := by
    intro hpi
    have hempty : pi.support = ∅ := by
      rw [hpi, Equiv.Perm.support_one]
    rw [hempty] at hsupport
    simp at hsupport
  have htauNe : tau ≠ 1 := by
    intro htau
    apply hpiNe
    dsimp only [pi]
    rw [htau, map_one]
  have htauSq : tau ^ 2 = 1 := by
    dsimp only [tau]
    rw [← map_pow,
      show (Complex.conjAe.restrictScalars ℚ) ^ 2 = 1 from
        AlgEquiv.ext Complex.conj_conj,
      map_one]
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have htauOrder : orderOf tau = 2 := orderOf_eq_prime htauSq htauNe
  let a : QuinticScalarGaloisBridge.rootPermutationGroup targetQ
      targetQ_irreducible
      targetQ_natDegree :=
    ⟨QuinticScalarGaloisBridge.rootPermutationHom targetQ targetQ_irreducible
        targetQ_natDegree tau, ⟨tau, rfl⟩⟩
  refine ⟨a, ?_⟩
  rw [← Subgroup.orderOf_coe a]
  change orderOf (QuinticScalarGaloisBridge.rootPermutationHom targetQ
    targetQ_irreducible
    targetQ_natDegree tau) = 2
  rw [orderOf_injective
    (QuinticScalarGaloisBridge.rootPermutationHom targetQ
      targetQ_irreducible targetQ_natDegree)
    (QuinticScalarGaloisBridge.rootPermutationHom_injective targetQ
      targetQ_irreducible
      targetQ_natDegree) tau,
    htauOrder]

/-- Final corrected classification: the root-permutation Galois group is an
inner conjugate of the explicit standard dihedral subgroup of order ten. -/
theorem target_rootPermutationGroup_isConjugateTo_standardD5 :
    Classification.IsConjugateTo
      (QuinticScalarGaloisBridge.rootPermutationGroup targetQ
        targetQ_irreducible
        targetQ_natDegree)
      Classification.standardD5 := by
  let H := QuinticScalarGaloisBridge.rootPermutationGroup targetQ
    targetQ_irreducible
    targetQ_natDegree
  letI : MulAction.IsPretransitive H (Fin 5) :=
    QuinticScalarGaloisBridge.rootPermutationGroup_isPretransitive targetQ
      targetQ_irreducible
      targetQ_natDegree
  apply isConjugateTo_standardD5_of_solvable_even_of_order_two H
  · exact (QuinticScalarGaloisBridge.gal_isSolvable_iff_rootPermutationGroup_isSolvable
      targetQ targetQ_irreducible targetQ_natDegree).mp targetQ_gal_isSolvable
  · exact target_rootPermutationGroup_le_standardA5
  · exact target_rootPermutationGroup_exists_orderOf_two

/-- Thus the `F₂₀` label sometimes attached to this example is literally
false: its root-permutation group is not an inner conjugate of the order-20
standard Frobenius subgroup. -/
theorem target_rootPermutationGroup_not_isConjugateTo_standardF20 :
    ¬ Classification.IsConjugateTo
      (QuinticScalarGaloisBridge.rootPermutationGroup targetQ
        targetQ_irreducible
        targetQ_natDegree)
      Classification.standardF20 := by
  intro hF
  have hDcard := Classification.natCard_eq_of_isConjugateTo
    target_rootPermutationGroup_isConjugateTo_standardD5
  have hFcard := Classification.natCard_eq_of_isConjugateTo hF
  rw [Classification.natCard_standardD5] at hDcard
  rw [Fin5TransitiveC5.natCard_standardF20] at hFcard
  omega

/-- In particular, the abstract Galois group has order ten. -/
theorem targetQ_gal_natCard : Nat.card targetQ.Gal = 10 := by
  calc
    Nat.card targetQ.Gal =
        Nat.card (QuinticScalarGaloisBridge.rootPermutationGroup targetQ
          targetQ_irreducible
          targetQ_natDegree) :=
      Nat.card_congr
        (QuinticScalarGaloisBridge.galEquivRootPermutationGroup targetQ
          targetQ_irreducible
          targetQ_natDegree).toEquiv
    _ = Nat.card Classification.standardD5 :=
      Classification.natCard_eq_of_isConjugateTo
        target_rootPermutationGroup_isConjugateTo_standardD5
    _ = 10 := Classification.natCard_standardD5

end LeanProofs.PolynomialFormulas.QuinticX5Add20XAdd32Dihedral
