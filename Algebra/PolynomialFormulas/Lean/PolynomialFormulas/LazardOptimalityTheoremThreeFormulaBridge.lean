import PolynomialFormulas.Fin5Solvable
import PolynomialFormulas.LazardOptimalityTheoremThreeCounterexample
import PolynomialFormulas.LazardOptimalityCyclicLazardRootData
import PolynomialFormulas.LazardQuinticCertificateRadicalTower
import PolynomialFormulas.LazardQuinticDepressionCore
import PolynomialFormulas.LazardQuinticFormulaField
import PolynomialFormulas.LazardQuinticRootFourierNumeratorRelations

/-!
# From a cyclic Lazard branch to the Theorem 3 profile

This file separates the formula-specific part of the cyclic-quintic
counterexample from its one remaining Galois-descent input.

The first section adds reusable field-membership lemmas for an arbitrary
root-origin `RadicalCertificate`.  The second defines the concrete notion of
a valid Lazard branch in the common `55`th-cyclotomic ambient field.  Such a
branch supplies the actual ordered roots, the Fourier-certified radical
certificate, and the rational invariant/numerator data.

From those data alone we prove all of the following:

* the certificate field is generated over its two-square base by `P1`;
* the certificate field is a literal radical extension of `ℚ`;
* `P1` is nonzero and its fifth power lies in that base;
* the certificate field contains the cyclic-quintic field `S`;
* the certificate field is contained in `S ⊔ W`.

The last field-theoretic step is packaged as `CyclicFieldAction`: the
quadratic base descends to `W`, and a nonidentity automorphism fixes that
base while moving `P1`.  A degree-divisibility argument and the abelian
Galois structure inherited from the cyclotomic ambient field construct this
package.  Thus `toFormulaFieldProfile` discharges the formula-field profile
used by the degree obstruction from any concrete `CyclicLazardBranch`.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open IntermediateField
open LeanProofs.PolynomialFormulas.LazardOptimality
open LeanProofs.PolynomialFormulas.Fin5Solvable
open FrobeniusDummitResolvent

set_option autoImplicit false

section ReusableFieldLemmas

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-! The following cyclic-invariance lemmas are the formula-side input for
the missing fixed-field descent.  They are identities of the displayed root
expressions; no Galois hypothesis is involved. -/

@[simp] theorem rootEpsilonProduct_permute_fiveCycle
    (x : Fin 5 → K) :
    rootEpsilonProduct (permuteRootTuple x fiveCycle) =
      rootEpsilonProduct x := by
  simp [rootEpsilonProduct, permuteRootTuple, fiveCycle, finRotate_apply]
  ring

@[simp] theorem rootEpsilon_permute_fiveCycle
    [CharZero K] (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega (permuteRootTuple x fiveCycle) =
      rootEpsilon omega x := by
  simp [rootEpsilon]

@[simp] theorem rootT_permute_fiveCycle
    [CharZero K] (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootT omega (permuteRootTuple x fiveCycle) = rootT omega x := by
  simp [rootT]

@[simp] theorem rootFormulaU_permute_fiveCycle
    [CharZero K] (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaU omega (permuteRootTuple x fiveCycle) =
      rootFormulaU omega x := by
  rw [rootFormulaU_eq_neg_rootU, rootFormulaU_eq_neg_rootU, neg_inj]
  simp [rootU]

@[simp] theorem rootQuadraticTriple_permute_fiveCycle
    [CharZero K] (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootQuadraticTriple omega (permuteRootTuple x fiveCycle) =
      rootQuadraticTriple omega x := by
  exact rootQuadraticTriple_permute_fiveCycle_f20 omega x

/-- An explicit power equation over the base makes the displayed element
integral. -/
theorem isIntegral_of_pow_eq
    (n : ℕ) (hn : 0 < n) {x : K} {a : F}
    (hpow : x ^ n = algebraMap F K a) : IsIntegral F x := by
  let p : Polynomial F := Polynomial.X ^ n - Polynomial.C a
  have hp : p.Monic := by
    exact Polynomial.monic_X_pow_sub_C a hn.ne'
  have heval : Polynomial.aeval x p = 0 := by
    simp [p, hpow]
  exact ⟨p, hp, heval⟩

/-- Adjoining an element whose displayed `n`th power is in the base has
degree at most `n`.  This is the elementary minpoly bound needed for each
literal radical stage; no equality between exponent and degree is assumed. -/
theorem finrank_adjoin_simple_le_of_pow_eq
    (n : ℕ) (hn : 0 < n) {x : K} {a : F}
    (hpow : x ^ n = algebraMap F K a) :
    Module.finrank F F⟮x⟯ ≤ n := by
  let p : Polynomial F := Polynomial.X ^ n - Polynomial.C a
  have hp : p.Monic := by
    exact Polynomial.monic_X_pow_sub_C a hn.ne'
  have heval : Polynomial.aeval x p = 0 := by
    simp [p, hpow]
  have hx : IsIntegral F x := isIntegral_of_pow_eq F K n hn hpow
  rw [IntermediateField.adjoin.finrank hx]
  have hdvd : minpoly F x ∣ p := minpoly.dvd F x heval
  have hle := Polynomial.natDegree_le_of_dvd hdvd hp.ne_zero
  simpa only [p, Polynomial.natDegree_X_pow_sub_C] using hle

/-- In particular a genuine square adjunction has degree one or two. -/
theorem finrank_adjoin_simple_eq_one_or_two_of_sq_eq
    {x : K} {a : F} (hpow : x ^ 2 = algebraMap F K a) :
    Module.finrank F F⟮x⟯ = 1 ∨ Module.finrank F F⟮x⟯ = 2 := by
  have hxIntegral : IsIntegral F x :=
    isIntegral_of_pow_eq F K 2 (by norm_num) hpow
  letI : FiniteDimensional F F⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional hxIntegral
  have hle : Module.finrank F F⟮x⟯ ≤ 2 :=
    finrank_adjoin_simple_le_of_pow_eq F K 2 (by norm_num) hpow
  have hpos : 0 < Module.finrank F F⟮x⟯ := Module.finrank_pos
  omega

/-- Adjoining an element whose `n`th power belongs to an intermediate
field multiplies the degree over the original ground field by at most `n`.
This is the relative version of `finrank_adjoin_simple_le_of_pow_eq`; the
`restrictScalars_adjoin_eq_sup` identity turns the relative adjunction into
the corresponding compositum inside the fixed ambient field. -/
theorem finrank_sup_adjoin_simple_le_of_pow_mem
    (B : IntermediateField F K) (n : ℕ) (hn : 0 < n) {x : K}
    (hpow : x ^ n ∈ B) :
    Module.finrank F ((B ⊔ F⟮x⟯) : IntermediateField F K) ≤
      Module.finrank F B * n := by
  let a : B := ⟨x ^ n, hpow⟩
  have hrelative : Module.finrank B B⟮x⟯ ≤ n :=
    finrank_adjoin_simple_le_of_pow_eq B K n hn (x := x) (a := a) rfl
  rw [← IntermediateField.restrictScalars_adjoin_eq_sup F B ({x} : Set K)]
  change Module.finrank F B⟮x⟯ ≤ Module.finrank F B * n
  rw [← Module.finrank_mul_finrank F B B⟮x⟯]
  exact Nat.mul_le_mul_left (Module.finrank F B) hrelative

/-- Two successive square adjunctions have total relative degree `1`, `2`,
or `4`.  This sharper finite list, rather than merely a `≤ 4` bound, is what
makes the compositum-degree contradiction with degree `20` work. -/
theorem finrank_two_square_tower_eq_one_or_two_or_four
    {x y : K} {a : F} {b : F⟮x⟯}
    (hx : x ^ 2 = algebraMap F K a)
    (hy : y ^ 2 = algebraMap F⟮x⟯ K b) :
    Module.finrank F (F⟮x⟯⟮y⟯) = 1 ∨
      Module.finrank F (F⟮x⟯⟮y⟯) = 2 ∨
      Module.finrank F (F⟮x⟯⟮y⟯) = 4 := by
  have hxrank := finrank_adjoin_simple_eq_one_or_two_of_sq_eq F K hx
  have hyrank :=
    finrank_adjoin_simple_eq_one_or_two_of_sq_eq F⟮x⟯ K hy
  rw [← Module.finrank_mul_finrank F F⟮x⟯ (F⟮x⟯⟮y⟯)]
  rcases hxrank with hxrank | hxrank <;>
    rcases hyrank with hyrank | hyrank <;>
    simp [hxrank, hyrank]

/-- Membership of the sign-corrected first square root implies membership of
the originally selected square root as well. -/
theorem epsilon0_mem_of_correctEpsilon_mem
    [DecidableEq K]
    (B : IntermediateField F K)
    (c : DepressedQuintic K) (i : Invariants K) (epsilon0 : K)
    (h : correctEpsilon c i epsilon0 ∈ B) : epsilon0 ∈ B := by
  unfold correctEpsilon at h
  split at h
  · simpa using neg_mem h
  · exact h

/-- The field after the two square-root stages of a Lazard certificate. -/
def RadicalCertificate.quadraticBaseField
    [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K) (d : RadicalCertificate c i) :
    IntermediateField F K :=
  (B ⊔ F⟮d.epsilon0⟯) ⊔ F⟮d.t⟯

theorem RadicalCertificate.generatedField_eq_quadraticBaseField_sup
    [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K) (d : RadicalCertificate c i) :
    d.generatedField F K B = d.quadraticBaseField F K B ⊔ F⟮d.p1⟯ :=
  rfl

theorem RadicalCertificate.quadraticBaseField_le_generatedField
    [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K) (d : RadicalCertificate c i) :
    d.quadraticBaseField F K B ≤ d.generatedField F K B := by
  rw [d.generatedField_eq_quadraticBaseField_sup F K B]
  exact le_sup_left

/-- The certificate equation for `P1`, together with rational membership of
the displayed invariants, puts `P1^5` in the two-square base. -/
theorem RadicalCertificate.p1_power_mem_quadraticBaseField
    [CharZero K] [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i) :
    d.p1 ^ 5 ∈ d.quadraticBaseField F K B := by
  let B2 := d.quadraticBaseField F K B
  have hB : B ≤ B2 := by
    exact le_sup_left.trans le_sup_left
  have hchosen : QuadraticTripleIn F K B2 d.chosen := by
    simpa only [B2, RadicalCertificate.quadraticBaseField] using
      d.chosen_mem_secondQuadraticField F K hdata
  rw [d.p1_power]
  unfold q1
  exact mul_mem
    (div_mem (IntermediateField.natCast_mem B2 5)
      (IntermediateField.natCast_mem B2 4))
    (add_mem
      (add_mem (hB hdata.h_mem)
        (div_mem (hB hdata.i_mem) hchosen.epsilon_mem))
      (div_mem
        (add_mem
          (mul_mem hchosen.t_mem (hB hdata.j_mem))
          (mul_mem hchosen.u_mem (hB hdata.k_mem)))
        (hB hdata.e_mem)))

/-- The part of a Lazard certificate obtained from its two square-root
choices has degree at most four over the original base.  Both radicands are
proved to belong to the preceding field directly from the certificate
equations and the displayed invariant-membership data. -/
theorem RadicalCertificate.quadraticBaseField_finrank_le
    [CharZero K] [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i) :
    Module.finrank F (d.quadraticBaseField F K B) ≤
      Module.finrank F B * 4 := by
  let B1 : IntermediateField F K := B ⊔ F⟮d.epsilon0⟯
  have hB1 : B ≤ B1 := le_sup_left
  have hepsilon0B1 : d.epsilon0 ∈ B1 :=
    (show F⟮d.epsilon0⟯ ≤ B1 from le_sup_right)
      (mem_adjoin_simple_self F d.epsilon0)
  have hcorrectB1 : correctEpsilon c i d.epsilon0 ∈ B1 :=
    correctEpsilon_mem F K B1 c i d.epsilon0 hepsilon0B1
  have hepsilonPower : d.epsilon0 ^ 2 ∈ B := by
    rw [d.epsilon0_square]
    exact mul_mem (IntermediateField.natCast_mem B 5) hdata.d_mem
  have htPower : d.t ^ 2 ∈ B1 := by
    rw [d.t_square]
    exact mul_mem
      (div_mem (IntermediateField.natCast_mem B1 5)
        (IntermediateField.natCast_mem B1 2))
      (add_mem (hB1 hdata.e_mem)
        (div_mem (hB1 hdata.f_mem) hcorrectB1))
  have hfirst : Module.finrank F B1 ≤ Module.finrank F B * 2 := by
    exact finrank_sup_adjoin_simple_le_of_pow_mem F K B 2 (by norm_num)
      hepsilonPower
  have hsecond :
      Module.finrank F
          ((B1 ⊔ F⟮d.t⟯) : IntermediateField F K) ≤
        Module.finrank F B1 * 2 := by
    exact finrank_sup_adjoin_simple_le_of_pow_mem F K B1 2 (by norm_num)
      htPower
  change Module.finrank F
      ((B1 ⊔ F⟮d.t⟯) : IntermediateField F K) ≤
    Module.finrank F B * 4
  calc
    Module.finrank F ((B1 ⊔ F⟮d.t⟯) : IntermediateField F K) ≤
        Module.finrank F B1 * 2 := hsecond
    _ ≤ (Module.finrank F B * 2) * 2 := Nat.mul_le_mul_right 2 hfirst
    _ = Module.finrank F B * 4 := by ring

/-- A root-origin certificate's three generators all lie in the field
generated by its ordered roots and primitive fifth root. -/
theorem RootFourierCertificateWitness.generatedField_le_rootFormulaField
    [CharZero K] [DecidableEq K]
    {omega : FifthRootOfUnity K} {x : Fin 5 → K}
    (w : RootFourierCertificateWitness omega x) :
    w.certificate.generatedField F K (⊥ : IntermediateField F K) ≤
      rootFormulaField F K omega x := by
  let L := rootFormulaField F K omega x
  have hroot : QuadraticTripleIn F K L (rootQuadraticTriple omega x) :=
    rootQuadraticTriple_mem_rootFormulaField F K omega x
  have hinitial : QuadraticTripleIn F K L w.certificate.initial := by
    rw [w.initial_eq]
    exact QuadraticTripleIn.branchTriple F K hroot w.first
  have hcorrect : correctEpsilon
      (depressedOfRoots x) (rootInvariants x)
      w.certificate.epsilon0 ∈ L := by
    simpa only [RadicalCertificate.initial] using hinitial.epsilon_mem
  have hepsilon0 : w.certificate.epsilon0 ∈ L :=
    epsilon0_mem_of_correctEpsilon_mem F K L
      (depressedOfRoots x) (rootInvariants x)
      w.certificate.epsilon0 hcorrect
  have ht : w.certificate.t ∈ L := by
    simpa only [RadicalCertificate.initial] using hinitial.t_mem
  have hp1 : w.certificate.p1 ∈ L := by
    rw [w.p1_eq]
    exact sourceForBranches_rootFourierOrbit_mem_rootFormulaField
      (F := F) (K := K) omega x w.first w.second 0
  rw [w.certificate.generatedField_eq_quadraticBaseField_sup F K
    (⊥ : IntermediateField F K)]
  exact sup_le
    (sup_le
      (sup_le bot_le (adjoin_simple_le_iff.mpr hepsilon0))
      (adjoin_simple_le_iff.mpr ht))
    (adjoin_simple_le_iff.mpr hp1)

/-- The zero-index inverse-Fourier output does not require adjoining
`omega`: its formula contains only `P1,...,P4` and rational scalars. -/
theorem RadicalCertificate.solveDepressed_zero_mem_generatedField
    [CharZero K] [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : RadicalCertificate c i) (omega : FifthRootOfUnity K)
    (hdata : RadicalInvariantDataIn F K B c i)
    (hnum : FourierNumeratorDataIn F K B c i) :
    solveDepressed c i d omega 0 ∈ d.generatedField F K B := by
  let L := d.generatedField F K B
  have hp1 : d.p1 ∈ L := d.p1_mem_generatedField F K
  have hp2 := d.fourierP2_mem_generatedField F K hdata hnum
  have hp3 := d.fourierP3_mem_generatedField F K hdata hnum
  have hp4 := d.fourierP4_mem_generatedField F K hdata hnum
  rw [solveDepressed_zero]
  exact div_mem (add_mem (add_mem (add_mem hp1 hp2) hp3) hp4)
    (IntermediateField.natCast_mem L 5)

/-- Every root and the displayed primitive root lying in `A ⊔ B` is enough
to bound the root formula field by that compositum. -/
theorem rootFormulaField_le_sup
    (A B : IntermediateField F K)
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hroots : ∀ j, x j ∈ A) (homega : omega.value ∈ B) :
    rootFormulaField F K omega x ≤ A ⊔ B := by
  rw [rootFormulaField, adjoin_le_iff]
  intro y hy
  rcases hy with hy | hy
  · obtain ⟨j, rfl⟩ := hy
    exact (show A ≤ A ⊔ B from le_sup_left) (hroots j)
  · have : y = omega.value := Set.mem_singleton_iff.mp hy
    rw [this]
    exact (show B ≤ A ⊔ B from le_sup_right) homega

end ReusableFieldLemmas

end LeanProofs.PolynomialFormulas.LazardQuintic

namespace LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeFormulaBridge

open IntermediateField
open LeanProofs.PolynomialFormulas.LazardQuintic
open LeanProofs.PolynomialFormulas.LazardOptimality
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclotomicCounterexample
open LeanProofs.PolynomialFormulas.LazardOptimalityCyclicQuinticCounterexample
open LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeCounterexample
open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option autoImplicit false

noncomputable section

local instance : DecidableEq Ambient := Classical.decEq Ambient
local instance : NeZero (55 : ℚ) := ⟨by norm_num⟩

noncomputable local instance : IsCyclotomicExtension {55} ℚ Ambient :=
  CyclotomicField.isCyclotomicExtension 55 ℚ

/-- The primitive fifth root already present in the common cyclotomic
ambient field, packaged for the Lazard APIs. -/
def cyclicFifthRootOfUnity : FifthRootOfUnity Ambient where
  value := zeta5
  primitive := zeta5_isPrimitiveRoot

/-- The explicit cyclic quintic satisfies Lazard's rational-resolvent
hypothesis.  The rational root is `-1991/125`; this is a direct evaluation of
the displayed sextic, independent of any Galois-group certificate. -/
theorem cyclicResolvent_isRoot :
    (resolventPolynomial (depress cyclicGeneralQuintic)).IsRoot
      (-1991 / 125 : ℚ) := by
  change
    (resolventPolynomial (depress cyclicGeneralQuintic)).eval
      (-1991 / 125 : ℚ) = 0
  rw [resolventPolynomial_eval]
  norm_num [cyclicGeneralQuintic, depress, resolventEval,
    resolventCore, discriminant]

theorem cyclicResolvent_has_rational_root :
    ∃ q : ℚ, (resolventPolynomial (depress cyclicGeneralQuintic)).IsRoot q :=
  ⟨-1991 / 125, cyclicResolvent_isRoot⟩

/-- A root-origin Lazard branch for the concrete cyclic quintic.

This structure contains formula data only.  It deliberately does not contain
the Galois descent or cyclic automorphism later isolated in
`CyclicFieldAction`. -/
structure CyclicLazardBranch where
  roots : Fin 5 → Ambient
  roots_in_cyclicQuinticField : ∀ j, roots j ∈ CyclicQuinticField
  roots_injective : Function.Injective roots
  sum_zero : elementaryTuple roots 0 = 0
  depressed_eq_cyclic :
    depressedOfRoots roots =
      (depress cyclicGeneralQuintic).map (algebraMap ℚ Ambient)
  formula : RootFourierCertificateWitness cyclicFifthRootOfUnity roots
  radicalData : RadicalInvariantDataIn ℚ Ambient
    (⊥ : IntermediateField ℚ Ambient)
    (depressedOfRoots roots) (rootInvariants roots)
  numeratorData : FourierNumeratorDataIn ℚ Ambient
    (⊥ : IntermediateField ℚ Ambient)
    (depressedOfRoots roots) (rootInvariants roots)

/-- The concrete cyclic quintic supplies an actual root-origin branch in the
common cyclotomic ambient field.  The root ordering and its rational invariant
tuple are the explicit `C₅` data certified in
`LazardOptimalityCyclicLazardRootData`; no splitting-field lift or sextic-root
selection is involved here. -/
theorem exists_cyclicLazardBranch : Nonempty CyclicLazardBranch := by
  let roots : Fin 5 → Ambient := cyclicLazardRootData.roots
  let j : Invariants ℚ := cyclicLazardRootData.invariants
  have hrootsS : ∀ k, roots k ∈ CyclicQuinticField := by
    simpa only [roots] using
      cyclicLazardRootData.roots_in_cyclicQuinticField
  have hroots : Function.Injective roots := by
    simpa only [roots] using cyclicLazardRootData.roots_injective
  have helementary : elementaryTuple roots =
      depressedElementary
        (cyclicDepressedQuintic.map (algebraMap ℚ Ambient)) := by
    simpa only [roots] using cyclicLazardRootData.elementary_eq
  have hjmap : j.map (algebraMap ℚ Ambient) = rootInvariants roots := by
    simpa only [j, roots] using cyclicLazardRootData.invariants_eq
  have hE :
      invariantE (depressedOfRoots roots) (rootInvariants roots) ≠ 0 := by
    simpa only [roots] using cyclicLazardRootData.invariantE_ne_zero
  have hsum : elementaryTuple roots 0 = 0 := by
    rw [helementary]
    simp [depressedElementary]
  have hdepressed : depressedOfRoots roots =
      cyclicDepressedQuintic.map (algebraMap ℚ Ambient) :=
    depressedOfRoots_eq_of_elementaryTuple_eq
      (cyclicDepressedQuintic.map (algebraMap ℚ Ambient))
      roots helementary
  have hepsilon : rootEpsilon cyclicFifthRootOfUnity roots ≠ 0 :=
    rootEpsilon_ne_zero_of_elementaryTuple_eq
      cyclicDepressedQuintic
      cyclicDepressedQuintic_polynomial_irreducible
      roots helementary cyclicFifthRootOfUnity
  obtain ⟨formula⟩ := exists_rootFourierCertificateWitness
    cyclicFifthRootOfUnity roots hsum hroots hepsilon hE
  have hradical : RadicalInvariantDataIn ℚ Ambient
      (⊥ : IntermediateField ℚ Ambient)
      (depressedOfRoots roots) (rootInvariants roots) := by
    rw [hdepressed, ← hjmap]
    exact radicalInvariantDataIn_bot_map ℚ Ambient cyclicDepressedQuintic j
  have hnumerator : FourierNumeratorDataIn ℚ Ambient
      (⊥ : IntermediateField ℚ Ambient)
      (depressedOfRoots roots) (rootInvariants roots) := by
    rw [hdepressed, ← hjmap]
    exact fourierNumeratorDataIn_bot_map ℚ Ambient cyclicDepressedQuintic j
  exact ⟨{
    roots := roots
    roots_in_cyclicQuinticField := hrootsS
    roots_injective := hroots
    sum_zero := hsum
    depressed_eq_cyclic := by
      simpa only [cyclicDepressedQuintic] using hdepressed
    formula := formula
    radicalData := hradical
    numeratorData := hnumerator }⟩

namespace CyclicLazardBranch

/-- The radical certificate carried by a valid cyclic branch. -/
def certificate (b : CyclicLazardBranch) :
    RadicalCertificate (depressedOfRoots b.roots)
      (rootInvariants b.roots) :=
  b.formula.certificate

/-- The two-square base `K0` of the one-root formula field. -/
def quadraticBaseField (b : CyclicLazardBranch) :
    IntermediateField ℚ Ambient :=
  b.certificate.quadraticBaseField ℚ Ambient
    (⊥ : IntermediateField ℚ Ambient)

/-- The one-root formula field `E`, without separately adjoining `zeta5`. -/
def formulaField (b : CyclicLazardBranch) :
    IntermediateField ℚ Ambient :=
  b.certificate.generatedField ℚ Ambient
    (⊥ : IntermediateField ℚ Ambient)

/-- The actual field generated by the selected Lazard radicals is a radical
extension in the literal sense of Definition 1: two square adjunctions
followed by one fifth-root adjunction. -/
theorem formulaField_isRadicalExtension (b : CyclicLazardBranch) :
    IsRadicalExtension ℚ Ambient
      (⊥ : IntermediateField ℚ Ambient) b.formulaField := by
  simpa only [formulaField] using
    b.certificate.generatedField_isRadical ℚ Ambient b.radicalData

/-- Undo the rational depression shift on the zero-index member of an
arbitrary valid root ordering.  No distinguished cyclotomic conjugate is
required: irreducibility will show that every such root generates `S`. -/
def originalRootZero (b : CyclicLazardBranch) : Ambient :=
  b.roots 0 - algebraMap ℚ Ambient (1 / 5)

theorem originalRootZero_mem_cyclicQuinticField (b : CyclicLazardBranch) :
    b.originalRootZero ∈ CyclicQuinticField := by
  exact sub_mem (b.roots_in_cyclicQuinticField 0)
    (CyclicQuinticField.algebraMap_mem (1 / 5 : ℚ))

/-- The tuple used to define `depressedOfRoots` satisfies its own Vieta
relations. -/
theorem depressedFiveRootRelations (b : CyclicLazardBranch) :
    DepressedFiveRootRelations (depressedOfRoots b.roots) b.roots := by
  constructor
  · simpa [fiveESymm1, elementaryTuple] using b.sum_zero
  · simp [fiveESymm2, depressedOfRoots, elementaryTuple]
  · simp [fiveESymm3, depressedOfRoots, elementaryTuple]
  · simp [fiveESymm4, depressedOfRoots, elementaryTuple]
  · simp [fiveESymm5, depressedOfRoots, elementaryTuple]

theorem depressedRootZero_eval (b : CyclicLazardBranch) :
    (depressedOfRoots b.roots).eval (b.roots 0) = 0 := by
  rw [b.depressedFiveRootRelations.eval_factorization]
  exact Finset.prod_eq_zero (Finset.mem_univ 0) (sub_self (b.roots 0))

/-- Undoing the depression shift gives a root of the original mapped cyclic
quintic. -/
theorem originalRootZero_eval (b : CyclicLazardBranch) :
    (cyclicGeneralQuintic.map (algebraMap ℚ Ambient)).eval
      b.originalRootZero = 0 := by
  have h := depress_eval
    (cyclicGeneralQuintic.map (algebraMap ℚ Ambient))
    (by norm_num [cyclicGeneralQuintic, GeneralQuintic.map])
    (b.roots 0)
  have hright :
      (cyclicGeneralQuintic.map (algebraMap ℚ Ambient)).a *
          (depress
            (cyclicGeneralQuintic.map (algebraMap ℚ Ambient))).eval
              (b.roots 0) = 0 := by
    rw [depress_map, ← b.depressed_eq_cyclic, b.depressedRootZero_eval]
    ring
  simpa [originalRootZero, cyclicGeneralQuintic, GeneralQuintic.map,
    map_div, map_one, map_ofNat] using h.trans hright

theorem originalRootZero_aeval (b : CyclicLazardBranch) :
    Polynomial.aeval b.originalRootZero cyclicQuinticQ = 0 := by
  rw [← Polynomial.eval_map_algebraMap,
    ← cyclicGeneralQuintic_polynomial]
  simpa [GeneralQuintic.polynomial, GeneralQuintic.map,
    GeneralQuintic.eval] using
    b.originalRootZero_eval

theorem cyclicQuinticQ_eq_minpoly_originalRootZero
    (b : CyclicLazardBranch) :
    cyclicQuinticQ = minpoly ℚ b.originalRootZero :=
  minpoly.eq_of_irreducible_of_monic cyclicQuinticQ_irreducible
    b.originalRootZero_aeval cyclicQuinticQ_monic

/-- Any zero-index root of a valid ordering generates the same degree-five
cyclic field.  This removes the unnecessary requirement that index zero be a
particular cyclotomic conjugate. -/
theorem adjoin_originalRootZero_eq_cyclicQuinticField
    (b : CyclicLazardBranch) :
    ℚ⟮b.originalRootZero⟯ = CyclicQuinticField := by
  apply IntermediateField.eq_of_le_of_finrank_eq
  · rw [adjoin_simple_le_iff]
    exact b.originalRootZero_mem_cyclicQuinticField
  · have hint : IsIntegral ℚ b.originalRootZero :=
      IsIntegral.of_finite ℚ b.originalRootZero
    rw [IntermediateField.adjoin.finrank hint,
      ← b.cyclicQuinticQ_eq_minpoly_originalRootZero,
      cyclicQuinticQ_natDegree, cyclicQuinticField_finrank]

theorem quadraticBaseField_le_formulaField (b : CyclicLazardBranch) :
    b.quadraticBaseField ≤ b.formulaField := by
  exact b.certificate.quadraticBaseField_le_generatedField ℚ Ambient
    (⊥ : IntermediateField ℚ Ambient)

theorem p1_mem_formulaField (b : CyclicLazardBranch) :
    b.certificate.p1 ∈ b.formulaField :=
  b.certificate.p1_mem_generatedField ℚ Ambient

theorem p1_power_mem_quadraticBaseField (b : CyclicLazardBranch) :
    b.certificate.p1 ^ 5 ∈ b.quadraticBaseField := by
  exact b.certificate.p1_power_mem_quadraticBaseField ℚ Ambient
    b.radicalData

/-- The two square-root stages of the concrete formula field have degree at
most four over `ℚ`. -/
theorem quadraticBaseField_finrank_le_four (b : CyclicLazardBranch) :
    Module.finrank ℚ b.quadraticBaseField ≤ 4 := by
  change Module.finrank ℚ
      (b.certificate.quadraticBaseField ℚ Ambient
        (⊥ : IntermediateField ℚ Ambient)) ≤ 4
  simpa only [IntermediateField.finrank_bot, one_mul] using
    b.certificate.quadraticBaseField_finrank_le ℚ Ambient b.radicalData

theorem formulaField_eq_quadraticBaseField_sup (b : CyclicLazardBranch) :
    b.formulaField = b.quadraticBaseField ⊔ ℚ⟮b.certificate.p1⟯ := by
  rfl

/-- The field generated by the branch's roots and `zeta5` is exactly the
degree-`20` compositum `S ⊔ W`. -/
theorem rootFormulaField_eq_compositum (b : CyclicLazardBranch) :
    rootFormulaField ℚ Ambient cyclicFifthRootOfUnity b.roots =
      CyclicQuinticField ⊔ FifthCyclotomicField := by
  apply le_antisymm
  · exact rootFormulaField_le_sup ℚ Ambient
      CyclicQuinticField FifthCyclotomicField
      cyclicFifthRootOfUnity b.roots
      b.roots_in_cyclicQuinticField
      (by
        simpa only [cyclicFifthRootOfUnity, FifthCyclotomicField] using
          mem_adjoin_simple_self ℚ zeta5)
  · apply sup_le
    · rw [← b.adjoin_originalRootZero_eq_cyclicQuinticField,
        adjoin_simple_le_iff]
      have hy := root_mem_rootFormulaField ℚ Ambient
        cyclicFifthRootOfUnity b.roots 0
      have hq := (rootFormulaField ℚ Ambient
        cyclicFifthRootOfUnity b.roots).algebraMap_mem (1 / 5 : ℚ)
      simpa only [originalRootZero] using sub_mem hy hq
    · rw [FifthCyclotomicField, adjoin_simple_le_iff]
      simpa only [cyclicFifthRootOfUnity] using
        fifthRoot_mem_rootFormulaField ℚ Ambient
          cyclicFifthRootOfUnity b.roots

/-- Every radical selected by the root-origin certificate lies in
`S ⊔ W`. -/
theorem formulaField_le_compositum (b : CyclicLazardBranch) :
    b.formulaField ≤ CyclicQuinticField ⊔ FifthCyclotomicField := by
  have hle := b.formula.generatedField_le_rootFormulaField ℚ Ambient
  rw [b.rootFormulaField_eq_compositum] at hle
  exact hle

/-- The zero-index formula value is the zero-index depressed root.  Both
coherent branch permutations, and Fourier reversal, fix index zero. -/
theorem solveDepressed_zero_eq_root_zero (b : CyclicLazardBranch) :
    solveDepressed (depressedOfRoots b.roots) (rootInvariants b.roots)
      b.certificate cyclicFifthRootOfUnity 0 = b.roots 0 := by
  have h := congrFun
    (b.formula.solveDepressed_eq_reversedRoots b.sum_zero) 0
  have hmultiplierZero : ∀ n : ℕ,
      (FrobeniusDummitResolvent.multiplierTwo ^ n) (0 : Fin 5) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ]
        simpa [FrobeniusDummitResolvent.multiplierTwo] using ih
  simpa [certificate, reversedRootTuple, rootsForBranch, permuteRootTuple,
    hmultiplierZero] using h

/-- The one-root formula field contains the original cyclic-quintic
generator; the rational depression shift does not enlarge the field. -/
theorem cyclicQuinticField_le_formulaField (b : CyclicLazardBranch) :
    CyclicQuinticField ≤ b.formulaField := by
  rw [← b.adjoin_originalRootZero_eq_cyclicQuinticField,
    adjoin_simple_le_iff]
  have hy : b.roots 0 ∈ b.formulaField := by
    rw [← b.solveDepressed_zero_eq_root_zero]
    exact b.certificate.solveDepressed_zero_mem_generatedField ℚ Ambient
      cyclicFifthRootOfUnity b.radicalData b.numeratorData
  have hq := b.formulaField.algebraMap_mem (1 / 5 : ℚ)
  simpa only [originalRootZero] using sub_mem hy hq

/-- The same original root used in the competing extension is contained in
the field generated by Lazard's displayed radicals. -/
theorem originalRootZero_mem_formulaField (b : CyclicLazardBranch) :
    b.originalRootZero ∈ b.formulaField :=
  b.cyclicQuinticField_le_formulaField
    b.originalRootZero_mem_cyclicQuinticField

/-- The already-proved containment `K0 ≤ E ≤ S ⊔ W`, together with exact
degree divisibility, forces the two-square base into the fifth-cyclotomic
field.  Indeed, `W ⊔ K0` is a concrete subfield of `S ⊔ W`, has degree at
most `4 * 4 = 16`, and its degree is both a multiple of `[W : ℚ] = 4` and
a divisor of `[S ⊔ W : ℚ] = 20`; hence its degree is exactly four.  This is
not an inference of cyclotomic containment from a bare degree equality. -/
theorem quadraticBaseField_le_fifthCyclotomicField
    (b : CyclicLazardBranch) :
    b.quadraticBaseField ≤ FifthCyclotomicField := by
  let M : IntermediateField ℚ Ambient :=
    FifthCyclotomicField ⊔ b.quadraticBaseField
  have hMle : M ≤ CyclicQuinticField ⊔ FifthCyclotomicField := by
    exact sup_le le_sup_right
      (b.quadraticBaseField_le_formulaField.trans
        b.formulaField_le_compositum)
  have hMupper : Module.finrank ℚ M ≤ 16 := by
    calc
      Module.finrank ℚ M ≤
          Module.finrank ℚ FifthCyclotomicField *
            Module.finrank ℚ b.quadraticBaseField :=
        IntermediateField.finrank_sup_le
          FifthCyclotomicField b.quadraticBaseField
      _ ≤ 4 * 4 := by
        rw [fifthCyclotomicField_finrank]
        exact Nat.mul_le_mul_left 4 b.quadraticBaseField_finrank_le_four
      _ = 16 := by norm_num
  have hfour_dvd : 4 ∣ Module.finrank ℚ M := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (K := ℚ) (L := Ambient)
      (show FifthCyclotomicField ≤ M from le_sup_left)
    simpa only [fifthCyclotomicField_finrank] using h
  have hM_dvd_twenty : Module.finrank ℚ M ∣ 20 := by
    have h := IntermediateField.finrank_dvd_of_le_right
      (K := ℚ) (L := Ambient) hMle
    simpa only [cyclicQuinticCompositum_finrank] using h
  have hMrank : Module.finrank ℚ M = 4 := by
    rcases hfour_dvd with ⟨u, hu⟩
    rcases hM_dvd_twenty with ⟨v, hv⟩
    have hu_le : u ≤ 4 := by omega
    have hfour : 4 * 5 = 4 * (u * v) := by
      calc
        4 * 5 = 20 := by norm_num
        _ = Module.finrank ℚ M * v := hv
        _ = (4 * u) * v := by rw [hu]
        _ = 4 * (u * v) := by simp [mul_assoc]
    have huv : 5 = u * v :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) hfour
    have hudvd : u ∣ 5 := ⟨v, huv⟩
    rcases (Nat.dvd_prime Nat.prime_five).mp hudvd with huone | hufive
    · omega
    · omega
  have hWM : FifthCyclotomicField = M := by
    apply IntermediateField.eq_of_le_of_finrank_eq
      (show FifthCyclotomicField ≤ M from le_sup_left)
    rw [fifthCyclotomicField_finrank, hMrank]
  have hK0M : b.quadraticBaseField ≤ M := le_sup_right
  simpa only [hWM] using hK0M

/-- The formula field is genuinely larger than its two-square base: it
contains the degree-five cyclic field, whereas the base lies in the
degree-four fifth-cyclotomic field. -/
theorem formulaField_ne_quadraticBaseField (b : CyclicLazardBranch) :
    b.formulaField ≠ b.quadraticBaseField := by
  intro heq
  have hSleK0 : CyclicQuinticField ≤ b.quadraticBaseField := by
    simpa only [heq] using b.cyclicQuinticField_le_formulaField
  have hSleW : CyclicQuinticField ≤ FifthCyclotomicField :=
    hSleK0.trans b.quadraticBaseField_le_fifthCyclotomicField
  have hdegree := IntermediateField.finrank_le_of_le_right hSleW
  rw [cyclicQuinticField_finrank, fifthCyclotomicField_finrank] at hdegree
  omega

/-! ### The cyclic field action -/

/-- The smallest field-action package needed by the profile.  Its first
field is Lazard's quadratic-radical descent.  The remaining fields record a
nonidentity automorphism over that base and its effect on `P1`. -/
structure CyclicFieldAction (b : CyclicLazardBranch) where
  base_le_fifthCyclotomic : b.quadraticBaseField ≤ FifthCyclotomicField
  conjugation : b.formulaField ≃ₐ[ℚ] b.formulaField
  conjugation_fixes_base :
    ∀ x : b.quadraticBaseField,
      conjugation
          (⟨(x : Ambient), b.quadraticBaseField_le_formulaField x.property⟩ :
            b.formulaField) =
        (⟨(x : Ambient), b.quadraticBaseField_le_formulaField x.property⟩ :
          b.formulaField)
  conjugation_moves_p1 :
    conjugation (⟨b.certificate.p1, b.p1_mem_formulaField⟩ : b.formulaField) ≠
      (⟨b.certificate.p1, b.p1_mem_formulaField⟩ : b.formulaField)

/-- The action package follows from degree and Galois theory; no explicit
cyclotomic automorphism needs to be written down.  The two-square base lies
in `W`, the formula field is a nontrivial intermediate field of the abelian
cyclotomic ambient extension, and a nonidentity automorphism over the base
must move `P1` because the base together with `P1` generates the formula
field. -/
theorem exists_cyclicFieldAction (b : CyclicLazardBranch) :
    Nonempty (CyclicFieldAction b) := by
  let K0 := b.quadraticBaseField
  let E := b.formulaField
  have hK0E : K0 ≤ E := b.quadraticBaseField_le_formulaField
  have hE_ne_K0 : E ≠ K0 := b.formulaField_ne_quadraticBaseField
  letI : IsAbelianGalois ℚ Ambient :=
    IsCyclotomicExtension.isAbelianGalois {55} ℚ Ambient
  letI : IsAbelianGalois ℚ E :=
    IsAbelianGalois.of_algHom E.val
  letI : Algebra K0 E :=
    (IntermediateField.inclusion hK0E).toRingHom.toAlgebra
  letI : IsScalarTower ℚ K0 E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsGalois K0 E :=
    IsGalois.tower_top_of_isGalois ℚ K0 E
  have hrelative_ne_one : Module.finrank K0 E ≠ 1 := by
    intro hrelative
    have htower := Module.finrank_mul_finrank ℚ K0 E
    rw [hrelative, mul_one] at htower
    have hK0eqE : K0 = E :=
      IntermediateField.eq_of_le_of_finrank_eq hK0E htower
    exact hE_ne_K0 hK0eqE.symm
  have hrelative : 1 < Module.finrank K0 E := by
    have hpositive : 0 < Module.finrank K0 E := Module.finrank_pos
    omega
  have hcard : 1 < Nat.card (E ≃ₐ[K0] E) := by
    rw [IsGalois.card_aut_eq_finrank]
    exact hrelative
  letI : Nontrivial (E ≃ₐ[K0] E) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨sigma, hsigma⟩ : ∃ sigma : E ≃ₐ[K0] E, sigma ≠ 1 :=
    exists_ne (1 : E ≃ₐ[K0] E)
  refine ⟨{
    base_le_fifthCyclotomic :=
      b.quadraticBaseField_le_fifthCyclotomicField
    conjugation := sigma.restrictScalars ℚ
    conjugation_fixes_base := ?_
    conjugation_moves_p1 := ?_ }⟩
  · intro x
    change sigma (algebraMap K0 E x) = algebraMap K0 E x
    exact sigma.commutes x
  · intro hp1
    apply hsigma
    have hEadjoin :
        E = IntermediateField.adjoin ℚ
          ((K0 : Set Ambient) ∪ {b.certificate.p1}) := by
      rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
      simpa only [K0, E] using
        b.formulaField_eq_quadraticBaseField_sup
    have hrestricted : sigma.restrictScalars ℚ = 1 := by
      apply AlgEquiv.coe_toAlgHom_injective
      apply IntermediateField.algHom_ext_of_eq_adjoin ℚ hEadjoin
      intro x hx
      rcases hx with hx | hx
      · change
          sigma (algebraMap K0 E (⟨x, hx⟩ : K0)) =
            algebraMap K0 E (⟨x, hx⟩ : K0)
        exact sigma.commutes (⟨x, hx⟩ : K0)
      · have hx' : x = b.certificate.p1 := Set.mem_singleton_iff.mp hx
        subst x
        change
          sigma
              (⟨b.certificate.p1, b.p1_mem_formulaField⟩ :
                b.formulaField) =
            (⟨b.certificate.p1, b.p1_mem_formulaField⟩ :
              b.formulaField)
        exact hp1
    exact AlgEquiv.restrictScalars_injective ℚ hrestricted

/-- Convert the certificate and its field action into the profile consumed
by the degree obstruction. -/
def toFormulaFieldProfile (b : CyclicLazardBranch)
    (h : CyclicFieldAction b) :
    CyclicLazardFormulaFieldProfile b.quadraticBaseField b.formulaField where
  p1 := b.certificate.p1
  base_le_fifthCyclotomic := h.base_le_fifthCyclotomic
  base_le_formula := b.quadraticBaseField_le_formulaField
  cyclicQuintic_le_formula := b.cyclicQuinticField_le_formulaField
  formula_le_compositum := b.formulaField_le_compositum
  p1_mem := b.p1_mem_formulaField
  p1_ne_zero := b.certificate.p1_nonzero
  p1_pow_five_mem := b.p1_power_mem_quadraticBaseField
  formula_eq_base_adjoin := b.formulaField_eq_quadraticBaseField_sup
  conjugation := h.conjugation
  conjugation_fixes_base := h.conjugation_fixes_base
  conjugation_moves_p1 := h.conjugation_moves_p1

/-- Compatibility wrapper for callers which already carry an action. -/
theorem exists_formulaFieldProfile_of_cyclicFieldAction
    (b : CyclicLazardBranch) (h : Nonempty (CyclicFieldAction b)) :
    Nonempty
      (CyclicLazardFormulaFieldProfile
        b.quadraticBaseField b.formulaField) := by
  obtain ⟨h⟩ := h
  exact ⟨b.toFormulaFieldProfile h⟩

/-- Audit name for the field-action statement. -/
def CyclicFieldActionComplete : Prop :=
  ∀ b : CyclicLazardBranch, Nonempty (CyclicFieldAction b)

/-- The field-action part of the bridge is complete. -/
theorem cyclicFieldActionComplete : CyclicFieldActionComplete :=
  exists_cyclicFieldAction

/-- Unconditional concrete degree obstruction for the one-root Lazard
formula field of the cyclic quintic.  The witness branch is constructed from
the polynomial's actual splitting field, and its action is supplied by
`exists_cyclicFieldAction`; no formula-field profile is assumed. -/
theorem cyclicLazard_theoremThree_degree_obstruction :
    ∃ b : CyclicLazardBranch,
      Module.finrank ℚ b.formulaField = 20 ∧
        ¬ Nonempty (b.formulaField →ₐ[ℚ] ElevenField) := by
  obtain ⟨b⟩ := exists_cyclicLazardBranch
  obtain ⟨action⟩ := exists_cyclicFieldAction b
  let P := b.toFormulaFieldProfile action
  exact ⟨b, P.theoremThree_degree_obstruction⟩

/-- The literal conclusion of Theorem 3 fails for the chosen competing
extension.  There is no radical intermediate field of `ElevenField`
containing the displayed root and isomorphic over `ℚ` to the actual Lazard
formula field.  In fact, the proof uses only the stronger fact that the
formula field has no `ℚ`-algebra embedding into `ElevenField`. -/
theorem no_isomorphicFormulaSubextension
    (b : CyclicLazardBranch)
    (hno : ¬ Nonempty (b.formulaField →ₐ[ℚ] ElevenField)) :
    ¬ ∃ M : IntermediateField ℚ Ambient,
      M ≤ ElevenField ∧
        IsRadicalExtension ℚ Ambient
          (⊥ : IntermediateField ℚ Ambient) M ∧
        b.originalRootZero ∈ M ∧
        Nonempty (b.formulaField ≃ₐ[ℚ] M) := by
  rintro ⟨M, hM, _, _, ⟨e⟩⟩
  exact hno
    ⟨(IntermediateField.inclusion hM).comp e.toAlgHom⟩

/-- Full counterexample package for Lazard's literal Theorem 3.  The
competing field `ElevenField` is a radical extension in the sense of
Definition 1 and contains the displayed root of the irreducible cyclic
quintic, but the actual one-root Lazard formula field cannot even embed into
it over `ℚ`.  Consequently `ElevenField` cannot contain a subextension
isomorphic to that formula field. -/
theorem cyclicLazard_theoremThree_counterexample :
    cyclicQuinticQ.Monic ∧
      cyclicQuinticQ.natDegree = 5 ∧
      Irreducible cyclicQuinticQ ∧
      (cyclicQuinticQ.map (algebraMap ℚ Ambient)).Splits ∧
      cyclicQuinticQ.rootSet Ambient ⊆ ElevenField ∧
      ∃ b : CyclicLazardBranch,
        IsRadicalExtension ℚ Ambient
            (⊥ : IntermediateField ℚ Ambient) ElevenField ∧
          b.originalRootZero ∈ ElevenField ∧
          Polynomial.aeval b.originalRootZero cyclicQuinticQ = 0 ∧
          IsRadicalExtension ℚ Ambient
            (⊥ : IntermediateField ℚ Ambient) b.formulaField ∧
          b.originalRootZero ∈ b.formulaField ∧
          Module.finrank ℚ b.formulaField = 20 ∧
          (¬ Nonempty (b.formulaField →ₐ[ℚ] ElevenField)) ∧
          ¬ ∃ M : IntermediateField ℚ Ambient,
            M ≤ ElevenField ∧
              IsRadicalExtension ℚ Ambient
                (⊥ : IntermediateField ℚ Ambient) M ∧
              b.originalRootZero ∈ M ∧
              Nonempty (b.formulaField ≃ₐ[ℚ] M) := by
  refine ⟨cyclicQuinticQ_monic, cyclicQuinticQ_natDegree,
    cyclicQuinticQ_irreducible, cyclicQuinticQ_splits_ambient,
    cyclicQuinticQ_rootSet_subset_elevenField, ?_⟩
  obtain ⟨b⟩ := exists_cyclicLazardBranch
  obtain ⟨action⟩ := exists_cyclicFieldAction b
  let P := b.toFormulaFieldProfile action
  have hrootEleven : b.originalRootZero ∈ ElevenField :=
    cyclicQuinticField_le_elevenField
      b.originalRootZero_mem_cyclicQuinticField
  have hno := P.no_algHom_formulaField_to_elevenField
  exact ⟨b, elevenField_isRadicalExtension, hrootEleven,
    b.originalRootZero_aeval, b.formulaField_isRadicalExtension,
    b.originalRootZero_mem_formulaField, P.formulaField_finrank, hno,
    b.no_isomorphicFormulaSubextension hno⟩

end CyclicLazardBranch

end

end LeanProofs.PolynomialFormulas.LazardOptimalityTheoremThreeFormulaBridge
