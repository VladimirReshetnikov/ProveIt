import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.List.Prime

/-!
# Precise extension-theoretic framework for Lazard's optimality claims

Lazard defines a simple radical extension by adjoining an element whose
power with prime exponent lies in the preceding field, and a radical extension by a
finite chain of such steps.  We formulate that definition for intermediate
fields in a common ambient field and define the literal leastness property
used by Theorems 3 and 4.

The final lemmas prove an essential lower bound from the paper: a field that
contains every root in a nonzero pure-power orbit also contains the relevant
root of unity.  For fifth roots this is the reason a field containing all
conjugates must contain the primitive fifth root used by the formula.
-/

namespace LeanProofs.PolynomialFormulas.LazardOptimality

open IntermediateField

set_option autoImplicit false

variable (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]

/-- A single radical step inside `Ω`: `L` is obtained from `K` by adjoining
an element whose `p`th power already belongs to `K` for a prime `p`.

This is Lazard's phrase "has a prime power in `K`": here "prime power"
means a power with prime exponent, not an exponent of the form `p^m`. -/
def IsSimpleRadicalStep
    (K L : IntermediateField F Ω) : Prop :=
  ∃ (α : Ω) (p : ℕ), p.Prime ∧ α ^ p ∈ K ∧ L = K ⊔ F⟮α⟯

theorem IsSimpleRadicalStep.le
    {K L : IntermediateField F Ω}
    (h : IsSimpleRadicalStep F Ω K L) : K ≤ L := by
  obtain ⟨α, n, hn, hpow, rfl⟩ := h
  exact le_sup_left

/-- A finite tower of simple radical steps.  `ReflTransGen` includes the
zero-step tower and is closed under concatenation. -/
def IsRadicalExtension
    (K L : IntermediateField F Ω) : Prop :=
  Relation.ReflTransGen (IsSimpleRadicalStep F Ω) K L

theorem isRadicalExtension_refl (K : IntermediateField F Ω) :
    IsRadicalExtension F Ω K K :=
  Relation.ReflTransGen.refl

theorem IsSimpleRadicalStep.isRadicalExtension
    {K L : IntermediateField F Ω}
    (h : IsSimpleRadicalStep F Ω K L) :
    IsRadicalExtension F Ω K L :=
  Relation.ReflTransGen.single h

theorem IsRadicalExtension.trans
    {K L M : IntermediateField F Ω}
    (hKL : IsRadicalExtension F Ω K L)
    (hLM : IsRadicalExtension F Ω L M) :
    IsRadicalExtension F Ω K M :=
  Relation.ReflTransGen.trans hKL hLM

/-- Adjoining one element whose prime-exponent power is already in the current
field is, by definition, a simple radical step.  This constructor is the
convenient interface used when spelling out the radicals of a formula. -/
theorem isSimpleRadicalStep_sup_adjoin
    (K : IntermediateField F Ω) (α : Ω) (p : ℕ)
    (hp : p.Prime) (hpow : α ^ p ∈ K) :
    IsSimpleRadicalStep F Ω K (K ⊔ F⟮α⟯) :=
  ⟨α, p, hp, hpow, rfl⟩

/-- Append one explicitly justified prime radical to an existing
radical tower. -/
theorem IsRadicalExtension.adjoin_prime
    {B K : IntermediateField F Ω}
    (hBK : IsRadicalExtension F Ω B K)
    (α : Ω) (p : ℕ) (hp : p.Prime) (hpow : α ^ p ∈ K) :
    IsRadicalExtension F Ω B (K ⊔ F⟮α⟯) :=
  hBK.trans F Ω
    (isSimpleRadicalStep_sup_adjoin F Ω K α p hp hpow).isRadicalExtension

/-- Square-root specialization of `adjoin_prime`. -/
theorem IsRadicalExtension.adjoin_square
    {B K : IntermediateField F Ω}
    (hBK : IsRadicalExtension F Ω B K)
    (α : Ω) (hpow : α ^ 2 ∈ K) :
    IsRadicalExtension F Ω B (K ⊔ F⟮α⟯) :=
  hBK.adjoin_prime F Ω α 2 Nat.prime_two hpow

/-- Fifth-root specialization of `adjoin_prime`. -/
theorem IsRadicalExtension.adjoin_fifth
    {B K : IntermediateField F Ω}
    (hBK : IsRadicalExtension F Ω B K)
    (α : Ω) (hpow : α ^ 5 ∈ K) :
    IsRadicalExtension F Ω B (K ⊔ F⟮α⟯) :=
  hBK.adjoin_prime F Ω α 5 Nat.prime_five hpow

theorem IsRadicalExtension.le
    {K L : IntermediateField F Ω}
    (h : IsRadicalExtension F Ω K L) : K ≤ L := by
  induction h with
  | refl => exact le_rfl
  | tail hreach hstep ih =>
      exact ih.trans (IsSimpleRadicalStep.le F Ω hstep)

/-- A simple radical step remains a simple radical step after adjoining an
arbitrary fixed intermediate field on both sides. -/
theorem IsSimpleRadicalStep.sup_left
    {K L : IntermediateField F Ω}
    (h : IsSimpleRadicalStep F Ω K L)
    (A : IntermediateField F Ω) :
    IsSimpleRadicalStep F Ω (A ⊔ K) (A ⊔ L) := by
  obtain ⟨α, n, hn, hpow, rfl⟩ := h
  refine ⟨α, n, hn, (show K ≤ A ⊔ K from le_sup_right) hpow, ?_⟩
  rw [sup_assoc]

/-- Base change of a finite radical tower by a fixed intermediate field. -/
theorem IsRadicalExtension.sup_left
    {K L : IntermediateField F Ω}
    (h : IsRadicalExtension F Ω K L)
    (A : IntermediateField F Ω) :
    IsRadicalExtension F Ω (A ⊔ K) (A ⊔ L) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.sup_left F Ω A)

/-- The compositum of two radical extensions of the same base is again a
radical extension.  This is needed to combine the radical field producing
the roots with the radical field producing a primitive fifth root of unity. -/
theorem IsRadicalExtension.sup
    {B K L : IntermediateField F Ω}
    (hK : IsRadicalExtension F Ω B K)
    (hL : IsRadicalExtension F Ω B L) :
    IsRadicalExtension F Ω B (K ⊔ L) := by
  have hbaseChanged := hL.sup_left F Ω K
  have hKB : K ⊔ B = K := sup_eq_left.mpr hK.le
  rw [hKB] at hbaseChanged
  exact hK.trans F Ω hbaseChanged

/-- The three successive adjunctions occurring in the essential Lazard
radical pattern: two square-root stages followed by one fifth-root stage. -/
def squareSquareFifthField
    (K : IntermediateField F Ω) (ε t p : Ω) :
    IntermediateField F Ω :=
  ((K ⊔ F⟮ε⟯) ⊔ F⟮t⟯) ⊔ F⟮p⟯

/-- An explicit square/square/fifth chain is honestly a radical extension;
no property of the named elements is built into the kernel.  Each power
membership is an ordinary hypothesis consumed by the corresponding simple
radical step. -/
theorem isRadicalExtension_squareSquareFifthField
    (K : IntermediateField F Ω) (ε t p : Ω)
    (hε : ε ^ 2 ∈ K)
    (ht : t ^ 2 ∈ K ⊔ F⟮ε⟯)
    (hp : p ^ 5 ∈ (K ⊔ F⟮ε⟯) ⊔ F⟮t⟯) :
    IsRadicalExtension F Ω K (squareSquareFifthField F Ω K ε t p) := by
  have h0 := isRadicalExtension_refl F Ω K
  have h1 := h0.adjoin_square F Ω ε hε
  have h2 := h1.adjoin_square F Ω t ht
  exact h2.adjoin_fifth F Ω p hp

/-- `L` is literally a least radical extension of `K` containing `S` inside
the fixed ambient field `Ω`.  This separates leastness from the weaker claim
that the elements of `S` merely have radical expressions. -/
structure IsLeastRadicalExtensionContaining
    (K L : IntermediateField F Ω) (S : Set Ω) : Prop where
  radical : IsRadicalExtension F Ω K L
  contains : S ⊆ L
  least : ∀ M : IntermediateField F Ω,
    IsRadicalExtension F Ω K M → S ⊆ M → L ≤ M

theorem IsLeastRadicalExtensionContaining.base_le
    {K L : IntermediateField F Ω} {S : Set Ω}
    (h : IsLeastRadicalExtensionContaining F Ω K L S) : K ≤ L :=
  h.radical.le

theorem IsLeastRadicalExtensionContaining.unique
    {K L M : IntermediateField F Ω} {S : Set Ω}
    (hL : IsLeastRadicalExtensionContaining F Ω K L S)
    (hM : IsLeastRadicalExtensionContaining F Ω K M S) : L = M :=
  le_antisymm (hL.least M hM.radical hM.contains)
    (hM.least L hL.radical hL.contains)

/-- Refute a claimed least radical extension by exhibiting one competing
radical field that contains the specified set but omits an element of the
claimed field.  This is the lattice step used by the cyclotomic
counterexample to Lazard's Theorem 4. -/
theorem not_isLeastRadicalExtensionContaining_of_competing_missing
    {K E M : IntermediateField F Ω} {S : Set Ω} {z : Ω}
    (hMradical : IsRadicalExtension F Ω K M)
    (hMcontains : S ⊆ M) (hzE : z ∈ E) (hzM : z ∉ M) :
    ¬ IsLeastRadicalExtensionContaining F Ω K E S := by
  intro hleast
  exact hzM (hleast.least M hMradical hMcontains hzE)

/-! ## The corrected arithmetic step behind Lazard's Theorem 3 -/

/-- The additional data that the printed proof of Theorem 3 silently needs:
each simple radical step must contribute its prime exponent as its actual
extension degree, so the total tower degree is the product of those primes.

The literal `IsSimpleRadicalStep` definition does **not** provide this
profile: `ζ₁₁ ^ 11 = 1` but `ℚ(ζ₁₁)/ℚ` has degree ten. -/
structure PrimeDegreeTowerProfile where
  totalDegree : ℕ
  stepExponents : List ℕ
  step_prime : ∀ p ∈ stepExponents, p.Prime
  degree_eq_product : totalDegree = stepExponents.prod

/-- Under the missing prime-degree hypothesis, divisibility of the total
degree by five really does force a fifth-root step.  This is the valid
replacement for the invalid inference in the paper. -/
theorem PrimeDegreeTowerProfile.has_fifth_step
    (T : PrimeDegreeTowerProfile) (hfive : 5 ∣ T.totalDegree) :
    5 ∈ T.stepExponents := by
  apply mem_list_primes_of_dvd_prod (Nat.prime_five.prime)
  · intro p hp
    exact (T.step_prime p hp).prime
  · rwa [← T.degree_eq_product]

/-- Dividing two nonzero members of one multiplicative root orbit recovers
their ratio.  This elementary field argument is the root-of-unity lower bound
behind Lazard's all-roots optimality theorem. -/
theorem ratio_mem_of_mem_mul
    (L : IntermediateField F Ω) {α ζ : Ω}
    (hα : α ∈ L) (hζα : ζ * α ∈ L) (hα0 : α ≠ 0) : ζ ∈ L := by
  have h := L.mul_mem hζα (L.inv_mem hα)
  simpa [mul_assoc, hα0] using h

/-- The field generated by a nonzero element and one multiplicative twist of
it contains the twisting scalar. -/
theorem adjoin_twist_contains_ratio {α ζ : Ω} (hα0 : α ≠ 0) :
    F⟮ζ⟯ ≤ F⟮α, ζ * α⟯ := by
  rw [adjoin_simple_le_iff]
  exact ratio_mem_of_mem_mul F Ω F⟮α, ζ * α⟯
    (mem_adjoin_pair_left F α (ζ * α))
    (mem_adjoin_pair_right F α (ζ * α)) hα0

/-- If `L` contains every solution of `x^n = y`, then any `n`th root of
unity lies in `L`, provided the equation has a nonzero solution. -/
theorem rootOfUnity_mem_of_all_power_roots
    (L : IntermediateField F Ω) {n : ℕ} {y α ζ : Ω}
    (hα0 : α ≠ 0) (hα : α ^ n = y) (hζ : ζ ^ n = 1)
    (hall : ∀ β : Ω, β ^ n = y → β ∈ L) : ζ ∈ L := by
  apply ratio_mem_of_mem_mul F Ω L (hall α hα) _ hα0
  apply hall (ζ * α)
  rw [mul_pow, hζ, hα, one_mul]

theorem adjoin_rootOfUnity_le_of_all_power_roots
    (L : IntermediateField F Ω) {n : ℕ} {y α ζ : Ω}
    (hα0 : α ≠ 0) (hα : α ^ n = y) (hζ : ζ ^ n = 1)
    (hall : ∀ β : Ω, β ^ n = y → β ∈ L) : F⟮ζ⟯ ≤ L := by
  rw [adjoin_simple_le_iff]
  exact rootOfUnity_mem_of_all_power_roots F Ω L hα0 hα hζ hall

/-- Fifth-root specialization used in Lazard's Theorem 4. -/
theorem primitiveFifthRoot_mem_of_all_quintic_roots
    (L : IntermediateField F Ω) {y α ζ : Ω}
    (hα0 : α ≠ 0) (hα : α ^ 5 = y)
    (hζ : IsPrimitiveRoot ζ 5)
    (hall : ∀ β : Ω, β ^ 5 = y → β ∈ L) : ζ ∈ L :=
  rootOfUnity_mem_of_all_power_roots F Ω L hα0 hα hζ.pow_eq_one hall

theorem adjoin_primitiveFifthRoot_le_of_all_quintic_roots
    (L : IntermediateField F Ω) {y α ζ : Ω}
    (hα0 : α ≠ 0) (hα : α ^ 5 = y)
    (hζ : IsPrimitiveRoot ζ 5)
    (hall : ∀ β : Ω, β ^ 5 = y → β ∈ L) : F⟮ζ⟯ ≤ L := by
  rw [adjoin_simple_le_iff]
  exact primitiveFifthRoot_mem_of_all_quintic_roots F Ω L hα0 hα hζ hall

/-! ## The lattice-theoretic core of the all-roots minimality theorem -/

/-- The field generated by a specified family of roots together with the
root of unity used by the radical formula. -/
def generatedWithRootOfUnity (S : Set Ω) (ζ : Ω) :
    IntermediateField F Ω :=
  adjoin F S ⊔ F⟮ζ⟯

theorem subset_generatedWithRootOfUnity (S : Set Ω) (ζ : Ω) :
    S ⊆ generatedWithRootOfUnity F Ω S ζ := by
  intro x hx
  exact (show adjoin F S ≤ generatedWithRootOfUnity F Ω S ζ from le_sup_left)
    (subset_adjoin F S hx)

theorem rootOfUnity_mem_generatedWithRootOfUnity (S : Set Ω) (ζ : Ω) :
    ζ ∈ generatedWithRootOfUnity F Ω S ζ :=
  (show F⟮ζ⟯ ≤ generatedWithRootOfUnity F Ω S ζ from le_sup_right)
    (mem_adjoin_simple_self F ζ)

/-- A useful normal form for every upper-bound argument involving the field
generated by the roots and a root of unity. -/
theorem generatedWithRootOfUnity_le_iff
    (S : Set Ω) (ζ : Ω) (L : IntermediateField F Ω) :
    generatedWithRootOfUnity F Ω S ζ ≤ L ↔ S ⊆ L ∧ ζ ∈ L := by
  rw [generatedWithRootOfUnity, sup_le_iff, adjoin_le_iff,
    adjoin_simple_le_iff]

/-- Abstract minimality step in Lazard's Theorem 4.  Once the displayed
all-roots field is known to be radical and every competing radical field
containing the roots is known to contain `ζ`, lattice minimality is automatic.
This theorem makes those two genuinely mathematical obligations explicit. -/
theorem isLeast_generatedWithRootOfUnity_of_forced
    {K : IntermediateField F Ω} {S : Set Ω} {ζ : Ω}
    (hradical :
      IsRadicalExtension F Ω K (generatedWithRootOfUnity F Ω S ζ))
    (hforced : ∀ L : IntermediateField F Ω,
      IsRadicalExtension F Ω K L → S ⊆ L → ζ ∈ L) :
    IsLeastRadicalExtensionContaining F Ω K
      (generatedWithRootOfUnity F Ω S ζ) S where
  radical := hradical
  contains := subset_generatedWithRootOfUnity F Ω S ζ
  least L hL hS :=
    (generatedWithRootOfUnity_le_iff F Ω S ζ L).2
      ⟨hS, hforced L hL hS⟩

/-- Concrete forcing criterion for the preceding minimality theorem.  If the
specified root family contains every solution of one nonzero pure-power
equation, the required root of unity is forced into every field containing
that family. -/
theorem isLeast_generatedWithRootOfUnity_of_powerRootOrbit
    {K : IntermediateField F Ω} {S : Set Ω}
    {n : ℕ} {y α ζ : Ω}
    (hα0 : α ≠ 0) (hα : α ^ n = y) (hζ : ζ ^ n = 1)
    (horbit : ∀ β : Ω, β ^ n = y → β ∈ S)
    (hradical :
      IsRadicalExtension F Ω K (generatedWithRootOfUnity F Ω S ζ)) :
    IsLeastRadicalExtensionContaining F Ω K
      (generatedWithRootOfUnity F Ω S ζ) S := by
  apply isLeast_generatedWithRootOfUnity_of_forced F Ω hradical
  intro L _ hS
  exact rootOfUnity_mem_of_all_power_roots F Ω L hα0 hα hζ
    (fun β hβ ↦ hS (horbit β hβ))

end LeanProofs.PolynomialFormulas.LazardOptimality
