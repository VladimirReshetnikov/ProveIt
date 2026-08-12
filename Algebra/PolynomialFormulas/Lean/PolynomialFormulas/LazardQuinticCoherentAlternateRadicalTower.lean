import PolynomialFormulas.LazardQuinticCertificateRadicalTower
import PolynomialFormulas.LazardQuinticRootAlternateRecovery
import PolynomialFormulas.LazardQuinticRootFourierRelations

/-!
# Radical tower for the corrected alternate quintic projections

The standard displayed formulas for `P₂`, `P₃`, and `P₄` divide by
`invariantE`, equivalently by `T² + U²`.  They therefore cannot be used to
close Lazard's alternate path in the case for which that denominator
vanishes.  This file instead applies the corrected alternate inverse to all
four coherent sign branches.  It obtains the fifth powers of all four
Fourier components separately, adjoins four fifth roots, and only then uses
inverse Fourier reconstruction.

Thus the unconditional denominator-safe tower exhibited here has two square
adjunctions and four fifth-root adjunctions.  It deliberately makes no use of
the standard `q1` formula or of `RadicalCertificate.p1_power`.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open IntermediateField
open LeanProofs.PolynomialFormulas.LazardOptimality
open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option autoImplicit false

/-! ## The four coherent recoveries -/

/-- Branch whose zeroth source coordinate is coordinate `j` of the original
four-element orbit.  The orbit order is `P₁,P₂,P₄,P₃`. -/
def coherentAlternateBranchForIndex : Fin 4 → SignBranch :=
  ![.base, .rotateNegate, .negateTU, .rotate]

@[simp] theorem sourceForBranch_coherentAlternateBranchForIndex_zero
    {K : Type*} (source : Fin 4 → K) (j : Fin 4) :
    sourceForBranch source (coherentAlternateBranchForIndex j) 0 = source j := by
  fin_cases j <;> rfl

/-- The quotient-defined quadratic triple used after the two square-root
choices. -/
def coherentAlternateInitial
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) (epsilon0 t : K) :
    QuadraticTriple K :=
  ⟨correctEpsilon c i epsilon0, t,
    radicalU c i (correctEpsilon c i epsilon0) t⟩

/-- A denominator-safe certificate for all four Fourier components.

The first fields are exactly the two square equations and the quotient
definition of `U` used by the original certificate.  The last field replaces
the single standard-`q1` equation by four corrected alternate recovery
equations, one for each coherent branch. -/
structure CoherentAlternateFourierCertificate
    {K : Type*} [Field K] [CharZero K] [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) where
  epsilon0 : K
  epsilon0_square : epsilon0 ^ 2 = 5 * invariantD c i
  epsilon0_nonzero : epsilon0 ≠ 0
  epsilon_branches : squareBranchAvailable c i epsilon0
  t : K
  t_square : t ^ 2 =
    (5 / 2) *
      (invariantE c i + invariantF c i / correctEpsilon c i epsilon0)
  u_square :
    (radicalU c i (correctEpsilon c i epsilon0) t) ^ 2 =
      (5 / 2) *
        (invariantE c i - invariantF c i / correctEpsilon c i epsilon0)
  projections : Fin 4 → K
  fourier : Fin 4 → K
  fourier_power : ∀ j : Fin 4,
    fourier j ^ 5 =
      let v := branchTriple (coherentAlternateInitial c i epsilon0 t)
        (coherentAlternateBranchForIndex j)
      coherentAlternateRecover v.epsilon v.t v.u projections

namespace CoherentAlternateFourierCertificate

variable {K : Type*} [Field K] [CharZero K]

/-- The corrected quadratic triple stored by an alternate certificate. -/
def initial
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i) : QuadraticTriple K :=
  coherentAlternateInitial c i d.epsilon0 d.t

/-- The triple used to recover Fourier coordinate `j`. -/
def recoveryTriple
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i) (j : Fin 4) :
    QuadraticTriple K :=
  branchTriple d.initial (coherentAlternateBranchForIndex j)

/-- The denominator-safe five-output reconstruction.  The certificate orbit
is ordered `P₁,P₂,P₄,P₃`, whereas `inverseFourier` takes
`P₁,P₂,P₃,P₄`. -/
def solve
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (omega : FifthRootOfUnity K) (k : Fin 5) : K :=
  inverseFourier omega.value
    (d.fourier 0) (d.fourier 1) (d.fourier 3) (d.fourier 2) k

variable (F K : Type*) [Field F] [Field K] [CharZero K] [Algebra F K]

/-- The field after the two square-root adjunctions. -/
def secondQuadraticField
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K)
    (d : CoherentAlternateFourierCertificate c i) :
    IntermediateField F K :=
  (B ⊔ F⟮d.epsilon0⟯) ⊔ F⟮d.t⟯

/-- First of the four fifth-root adjunctions. -/
def fifthField0
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K)
    (d : CoherentAlternateFourierCertificate c i) :
    IntermediateField F K :=
  d.secondQuadraticField F K B ⊔ F⟮d.fourier 0⟯

/-- Second of the four fifth-root adjunctions. -/
def fifthField1
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K)
    (d : CoherentAlternateFourierCertificate c i) :
    IntermediateField F K :=
  d.fifthField0 F K B ⊔ F⟮d.fourier 1⟯

/-- Third of the four fifth-root adjunctions. -/
def fifthField2
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K)
    (d : CoherentAlternateFourierCertificate c i) :
    IntermediateField F K :=
  d.fifthField1 F K B ⊔ F⟮d.fourier 2⟯

/-- The full two-square/four-fifth denominator-safe formula field. -/
def generatedField
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K)
    (d : CoherentAlternateFourierCertificate c i) :
    IntermediateField F K :=
  d.fifthField2 F K B ⊔ F⟮d.fourier 3⟯

/-- Adjoin the primitive fifth root used by inverse Fourier reconstruction. -/
def generatedFieldWithRootOfUnity
    [DecidableEq K] {c : DepressedQuintic K} {i : Invariants K}
    (B : IntermediateField F K)
    (d : CoherentAlternateFourierCertificate c i)
    (omega : FifthRootOfUnity K) : IntermediateField F K :=
  d.generatedField F K B ⊔ F⟮omega.value⟯

omit [CharZero K] in
/-- Field membership is closed under the corrected alternate inverse.  No
nonzero-denominator premise is needed for this membership statement because
an intermediate field is already a field. -/
theorem coherentAlternateRecover_mem
    (L : IntermediateField F K) (v : QuadraticTriple K)
    (projections : Fin 4 → K)
    (hv : QuadraticTripleIn F K L v)
    (hprojections : ∀ j, projections j ∈ L) :
    coherentAlternateRecover v.epsilon v.t v.u projections ∈ L := by
  have hdenominator : coherentAlternateDenominator v.t v.u ∈ L := by
    unfold coherentAlternateDenominator
    exact sub_mem
      (add_mem (pow_mem hv.t_mem 2) (mul_mem hv.t_mem hv.u_mem))
      (pow_mem hv.u_mem 2)
  unfold coherentAlternateRecover
  exact add_mem
    (add_mem
      (div_mem (hprojections 0) (IntermediateField.natCast_mem L 4))
      (div_mem (hprojections 1)
        (mul_mem (IntermediateField.natCast_mem L 4) hv.epsilon_mem)))
    (div_mem
      (sub_mem
        (mul_mem
          (mul_mem hv.epsilon_mem
            (add_mem
              (mul_mem (IntermediateField.natCast_mem L 2) hv.t_mem)
              hv.u_mem))
          (hprojections 2))
        (mul_mem hv.u_mem (hprojections 3)))
      (mul_mem
        (mul_mem (IntermediateField.natCast_mem L 4) hv.epsilon_mem)
        hdenominator))

/-- The quotient-defined initial triple lies in the field after the two
square-root adjunctions. -/
theorem initial_mem_secondQuadraticField
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i) :
    QuadraticTripleIn F K (d.secondQuadraticField F K B) d.initial := by
  let B1 : IntermediateField F K := B ⊔ F⟮d.epsilon0⟯
  let B2 : IntermediateField F K := B1 ⊔ F⟮d.t⟯
  have hB1 : B ≤ B1 := le_sup_left
  have hB2 : B ≤ B2 := hB1.trans le_sup_left
  have hepsilon0B1 : d.epsilon0 ∈ B1 :=
    (show F⟮d.epsilon0⟯ ≤ B1 from le_sup_right)
      (mem_adjoin_simple_self F d.epsilon0)
  have hcorrectB1 : correctEpsilon c i d.epsilon0 ∈ B1 :=
    correctEpsilon_mem F K B1 c i d.epsilon0 hepsilon0B1
  have hcorrectB2 : correctEpsilon c i d.epsilon0 ∈ B2 :=
    (show B1 ≤ B2 from le_sup_left) hcorrectB1
  have htB2 : d.t ∈ B2 :=
    (show F⟮d.t⟯ ≤ B2 from le_sup_right)
      (mem_adjoin_simple_self F d.t)
  have huB2 :
      radicalU c i (correctEpsilon c i d.epsilon0) d.t ∈ B2 := by
    unfold radicalU
    exact div_mem
      (mul_mem (IntermediateField.natCast_mem B2 5) (hB2 hdata.g_mem))
      (mul_mem htB2 hcorrectB2)
  change QuadraticTripleIn F K B2
    (coherentAlternateInitial c i d.epsilon0 d.t)
  exact ⟨hcorrectB2, htB2, huB2⟩

/-- Every recovery branch remains in the second quadratic field. -/
theorem recoveryTriple_mem_secondQuadraticField
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i) (j : Fin 4) :
    QuadraticTripleIn F K (d.secondQuadraticField F K B)
      (d.recoveryTriple j) :=
  QuadraticTripleIn.branchTriple F K
    (d.initial_mem_secondQuadraticField F K hdata)
    (coherentAlternateBranchForIndex j)

/-- Base-field membership of the four descended projections puts every
corrected recovery value in the second quadratic field. -/
theorem recovery_mem_secondQuadraticField
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i)
    (hprojections : ∀ j, d.projections j ∈ B) (j : Fin 4) :
    coherentAlternateRecover (d.recoveryTriple j).epsilon
        (d.recoveryTriple j).t (d.recoveryTriple j).u d.projections ∈
      d.secondQuadraticField F K B := by
  have hB : B ≤ d.secondQuadraticField F K B :=
    (show B ≤ B ⊔ F⟮d.epsilon0⟯ from le_sup_left).trans le_sup_left
  exact coherentAlternateRecover_mem F K _ _ _
    (d.recoveryTriple_mem_secondQuadraticField F K hdata j)
    (fun k => hB (hprojections k))

/-- The four corrected recovery equations honestly put all four Fourier
fifth powers in the second quadratic field. -/
theorem fourier_pow_five_mem_secondQuadraticField
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i)
    (hprojections : ∀ j, d.projections j ∈ B) (j : Fin 4) :
    d.fourier j ^ 5 ∈ d.secondQuadraticField F K B := by
  rw [d.fourier_power j]
  exact d.recovery_mem_secondQuadraticField F K hdata hprojections j

/-- The full corrected alternate field is an honest radical extension:
two square-root steps followed by four fifth-root steps. -/
theorem generatedField_isRadical
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (hdata : RadicalInvariantDataIn F K B c i)
    (hprojections : ∀ j, d.projections j ∈ B) :
    IsRadicalExtension F K B (d.generatedField F K B) := by
  let B1 : IntermediateField F K := B ⊔ F⟮d.epsilon0⟯
  let B2 : IntermediateField F K := B1 ⊔ F⟮d.t⟯
  let L0 : IntermediateField F K := B2 ⊔ F⟮d.fourier 0⟯
  let L1 : IntermediateField F K := L0 ⊔ F⟮d.fourier 1⟯
  let L2 : IntermediateField F K := L1 ⊔ F⟮d.fourier 2⟯
  let L3 : IntermediateField F K := L2 ⊔ F⟮d.fourier 3⟯
  have hepsilonPower : d.epsilon0 ^ 2 ∈ B := by
    rw [d.epsilon0_square]
    exact mul_mem (IntermediateField.natCast_mem B 5) hdata.d_mem
  have hepsilon0B1 : d.epsilon0 ∈ B1 :=
    (show F⟮d.epsilon0⟯ ≤ B1 from le_sup_right)
      (mem_adjoin_simple_self F d.epsilon0)
  have hcorrectB1 : correctEpsilon c i d.epsilon0 ∈ B1 :=
    correctEpsilon_mem F K B1 c i d.epsilon0 hepsilon0B1
  have htPower : d.t ^ 2 ∈ B1 := by
    rw [d.t_square]
    exact mul_mem
      (div_mem (IntermediateField.natCast_mem B1 5)
        (IntermediateField.natCast_mem B1 2))
      (add_mem
        ((show B ≤ B1 from le_sup_left) hdata.e_mem)
        (div_mem ((show B ≤ B1 from le_sup_left) hdata.f_mem)
          hcorrectB1))
  have hp (j : Fin 4) : d.fourier j ^ 5 ∈ B2 := by
    simpa [B1, B2, secondQuadraticField] using
      d.fourier_pow_five_mem_secondQuadraticField F K
        hdata hprojections j
  have h0 := isRadicalExtension_refl F K B
  have h1 : IsRadicalExtension F K B B1 :=
    h0.adjoin_square F K d.epsilon0 hepsilonPower
  have h2 : IsRadicalExtension F K B B2 :=
    h1.adjoin_square F K d.t htPower
  have h3 : IsRadicalExtension F K B L0 :=
    h2.adjoin_fifth F K (d.fourier 0) (hp 0)
  have h4 : IsRadicalExtension F K B L1 :=
    h3.adjoin_fifth F K (d.fourier 1)
      ((show B2 ≤ L0 from le_sup_left) (hp 1))
  have h5 : IsRadicalExtension F K B L2 :=
    h4.adjoin_fifth F K (d.fourier 2)
      ((show L0 ≤ L1 from le_sup_left)
        ((show B2 ≤ L0 from le_sup_left) (hp 2)))
  have h6 : IsRadicalExtension F K B L3 :=
    h5.adjoin_fifth F K (d.fourier 3)
      ((show L1 ≤ L2 from le_sup_left)
        ((show L0 ≤ L1 from le_sup_left)
          ((show B2 ≤ L0 from le_sup_left) (hp 3))))
  simpa [B1, B2, L0, L1, L2, L3, generatedField, fifthField0,
    fifthField1, fifthField2, secondQuadraticField] using h6

/-- Each of the four fifth roots is a generator of the final field. -/
theorem fourier_mem_generatedField
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i) (j : Fin 4) :
    d.fourier j ∈ d.generatedField F K B := by
  let B2 := d.secondQuadraticField F K B
  let L0 := d.fifthField0 F K B
  let L1 := d.fifthField1 F K B
  let L2 := d.fifthField2 F K B
  let L3 := d.generatedField F K B
  have h01 : L0 ≤ L1 := le_sup_left
  have h12 : L1 ≤ L2 := le_sup_left
  have h23 : L2 ≤ L3 := le_sup_left
  fin_cases j
  · have h : d.fourier 0 ∈ L0 :=
      (show F⟮d.fourier 0⟯ ≤ L0 from le_sup_right)
        (mem_adjoin_simple_self F (d.fourier 0))
    exact h23 (h12 (h01 h))
  · have h : d.fourier 1 ∈ L1 :=
      (show F⟮d.fourier 1⟯ ≤ L1 from le_sup_right)
        (mem_adjoin_simple_self F (d.fourier 1))
    exact h23 (h12 h)
  · have h : d.fourier 2 ∈ L2 :=
      (show F⟮d.fourier 2⟯ ≤ L2 from le_sup_right)
        (mem_adjoin_simple_self F (d.fourier 2))
    exact h23 h
  · exact
      (show F⟮d.fourier 3⟯ ≤ L3 from le_sup_right)
        (mem_adjoin_simple_self F (d.fourier 3))

/-- All five inverse-Fourier outputs lie in the four-fifth-root field after
adjoining the common primitive fifth root of unity. -/
theorem solve_mem_generatedFieldWithRootOfUnity
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (omega : FifthRootOfUnity K) (k : Fin 5) :
    d.solve omega k ∈ d.generatedFieldWithRootOfUnity F K B omega := by
  let G := d.generatedField F K B
  let L := d.generatedFieldWithRootOfUnity F K B omega
  have hG : G ≤ L := le_sup_left
  have homega : omega.value ∈ L :=
    (show F⟮omega.value⟯ ≤ L from le_sup_right)
      (mem_adjoin_simple_self F omega.value)
  have hp (j : Fin 4) : d.fourier j ∈ L :=
    hG (d.fourier_mem_generatedField F K j)
  unfold solve inverseFourier
  exact div_mem
    (add_mem
      (add_mem
        (add_mem
          (mul_mem (pow_mem homega (k : ℕ)) (hp 0))
          (mul_mem (pow_mem homega (2 * (k : ℕ))) (hp 1)))
        (mul_mem (pow_mem homega (3 * (k : ℕ))) (hp 3)))
      (mul_mem (pow_mem homega (4 * (k : ℕ))) (hp 2)))
    (IntermediateField.natCast_mem L 5)

/-- Combining the denominator-safe formula field with a radical field for
the primitive fifth root preserves radicality. -/
theorem generatedFieldWithRootOfUnity_isRadical
    [DecidableEq K]
    {B : IntermediateField F K}
    {c : DepressedQuintic K} {i : Invariants K}
    (d : CoherentAlternateFourierCertificate c i)
    (omega : FifthRootOfUnity K)
    (hdata : RadicalInvariantDataIn F K B c i)
    (hprojections : ∀ j, d.projections j ∈ B)
    (homega : IsRadicalExtension F K B F⟮omega.value⟯) :
    IsRadicalExtension F K B
      (d.generatedFieldWithRootOfUnity F K B omega) :=
  (d.generatedField_isRadical F K hdata hprojections).sup F K homega

end CoherentAlternateFourierCertificate

/-! ## Direct root adapters -/

section RootAdapters

variable {K : Type*} [Field K] [CharZero K]

/-- Corrected alternate projection values are unchanged by the root
reordering realizing any coherent sign branch. -/
@[simp] theorem rootCoherentAlternateProjectionValues_rootsForBranch
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (branch : SignBranch) :
    rootCoherentAlternateProjectionValues omega (rootsForBranch x branch) =
      rootCoherentAlternateProjectionValues omega x := by
  unfold rootsForBranch
  exact rootCoherentAlternateProjectionValues_permute_multiplierTwo_pow
    omega x (branchMultiplierExponent branch)

/-- A coherent branch reordering preserves nonvanishing of root epsilon. -/
theorem rootEpsilon_rootsForBranch_ne_zero
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hepsilon : rootEpsilon omega x ≠ 0) (branch : SignBranch) :
    rootEpsilon omega (rootsForBranch x branch) ≠ 0 := by
  cases branch
  · have heq : rootEpsilon omega (rootsForBranch x .base) =
        rootEpsilon omega x := by
      simpa [rootQuadraticTriple, branchTriple] using
        congrArg QuadraticTriple.epsilon
          (rootQuadraticTriple_rootsForBranch omega x .base)
    rw [heq]
    exact hepsilon
  · have heq : rootEpsilon omega (rootsForBranch x .negateTU) =
        rootEpsilon omega x := by
      simpa [rootQuadraticTriple, branchTriple] using
        congrArg QuadraticTriple.epsilon
          (rootQuadraticTriple_rootsForBranch omega x .negateTU)
    rw [heq]
    exact hepsilon
  · have heq : rootEpsilon omega (rootsForBranch x .rotate) =
        -rootEpsilon omega x := by
      simpa [rootQuadraticTriple, branchTriple] using
        congrArg QuadraticTriple.epsilon
          (rootQuadraticTriple_rootsForBranch omega x .rotate)
    rw [heq]
    exact neg_ne_zero.mpr hepsilon
  · have heq : rootEpsilon omega (rootsForBranch x .rotateNegate) =
        -rootEpsilon omega x := by
      simpa [rootQuadraticTriple, branchTriple] using
        congrArg QuadraticTriple.epsilon
          (rootQuadraticTriple_rootsForBranch omega x .rotateNegate)
    rw [heq]
    exact neg_ne_zero.mpr hepsilon

omit [CharZero K] in
/-- Reordering an actual depressed root tuple by a coherent branch and then
reversing the positive-Fourier indices preserves its exact Vieta data. -/
theorem depressedFiveRootRelations_reversed_rootsForBranch
    (x : Fin 5 → K) (hsum : elementaryTuple x 0 = 0)
    (branch : SignBranch) :
    DepressedFiveRootRelations (depressedOfRoots x)
      (reversedRootTuple (rootsForBranch x branch)) := by
  let y := rootsForBranch x branch
  have hsumY : elementaryTuple y 0 = 0 := by
    rw [show elementaryTuple y = elementaryTuple x by
      simpa [y] using elementaryTuple_rootsForBranch x branch]
    exact hsum
  have hy : DepressedFiveRootRelations (depressedOfRoots y) y :=
    depressedFiveRootRelations_depressedOfRoots y hsumY
  have hdepressed : depressedOfRoots y = depressedOfRoots x := by
    simpa [y] using depressedOfRoots_rootsForBranch x branch
  have hreversed := reversedRootTuple_esymm y
  constructor
  · rw [hreversed.1]
    exact hy.sum
  · rw [hreversed.2.1]
    simpa [hdepressed] using hy.pairs
  · rw [hreversed.2.2.1]
    simpa [hdepressed] using hy.triples
  · rw [hreversed.2.2.2.1]
    simpa [hdepressed] using hy.quadruples
  · rw [hreversed.2.2.2.2]
    simpa [hdepressed] using hy.product

/-- Applying root-level alternate recovery after a coherent branch recovers
the corresponding coordinate of the original Fourier orbit. -/
theorem root_coherentAlternateRecover_fourierOrbit_forBranch
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) (branch : SignBranch) :
    coherentAlternateRecover
        (branchTriple (rootQuadraticTriple omega x) branch).epsilon
        (branchTriple (rootQuadraticTriple omega x) branch).t
        (branchTriple (rootQuadraticTriple omega x) branch).u
        (rootCoherentAlternateProjectionValues omega x) =
      sourceForBranch (rootFourierOrbit omega x) branch 0 ^ 5 := by
  let y := rootsForBranch x branch
  have hyinjective : Function.Injective y := by
    exact permuteRootTuple_injective hinjective _
  have hyepsilon : rootEpsilon omega y ≠ 0 := by
    exact rootEpsilon_rootsForBranch_ne_zero omega x hepsilon branch
  have h := root_coherentAlternateRecover_fourierP1_pow_five
    omega hyinjective hyepsilon
  change coherentAlternateRecover
      (rootQuadraticTriple omega y).epsilon
      (rootQuadraticTriple omega y).t
      (rootQuadraticTriple omega y).u
      (rootCoherentAlternateProjectionValues omega y) =
    rootFourierOrbit omega y 0 ^ 5 at h
  simpa [y, rootQuadraticTriple_rootsForBranch,
    rootFourierOrbit_rootsForBranch] using h

/-- Coordinatewise form: every actual Fourier fifth power is recovered from
the same corrected projection vector. -/
theorem root_coherentAlternateRecover_fourierOrbit_pow_five
    (omega : FifthRootOfUnity K) {x : Fin 5 → K}
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) (j : Fin 4) :
    rootFourierOrbit omega x j ^ 5 =
      coherentAlternateRecover
        (branchTriple (rootQuadraticTriple omega x)
          (coherentAlternateBranchForIndex j)).epsilon
        (branchTriple (rootQuadraticTriple omega x)
          (coherentAlternateBranchForIndex j)).t
        (branchTriple (rootQuadraticTriple omega x)
          (coherentAlternateBranchForIndex j)).u
        (rootCoherentAlternateProjectionValues omega x) := by
  rw [← sourceForBranch_coherentAlternateBranchForIndex_zero
    (rootFourierOrbit omega x) j]
  exact (root_coherentAlternateRecover_fourierOrbit_forBranch
    omega hinjective hepsilon (coherentAlternateBranchForIndex j)).symm

/-- The actual ordered roots construct the four-recovery certificate after
the usual epsilon-sign correction of the quadratic stage.  No standard
projection identity, `q1` equation, or nonzero `invariantE` hypothesis is
used. -/
noncomputable def rootCoherentAlternateFourierCertificate
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    CoherentAlternateFourierCertificate
      (depressedOfRoots x) (rootInvariants x) := by
  let c := depressedOfRoots x
  let i := rootInvariants x
  let v := rootQuadraticTriple omega x
  let first := correctedQuadraticBranch c i v
  let corrected := correctedQuadraticTriple c i v
  let y := rootsForBranch x first
  have hrelations : QuadraticRelations c i v := by
    simpa [c, i, v] using rootQuadraticRelations omega x hsum hepsilon
  have hcomponents : v.t ≠ 0 ∨ v.u ≠ 0 := by
    simpa [v, rootQuadraticTriple, rootFormulaU] using
      rootT_rootU_not_both_zero omega hinjective
  have hinitial :
      coherentAlternateInitial c i v.epsilon corrected.t = corrected := by
    simpa [coherentAlternateInitial, corrected] using
      hrelations.correctedInitialTriple_eq hepsilon hcomponents
  have hytriple : rootQuadraticTriple omega y = corrected := by
    calc
      rootQuadraticTriple omega y = branchTriple v first := by
        simpa [y, v] using
          rootQuadraticTriple_rootsForBranch omega x first
      _ = corrected := by
        rfl
  have hyfourier : rootFourierOrbit omega y =
      sourceForBranch (rootFourierOrbit omega x) first := by
    simpa [y] using rootFourierOrbit_rootsForBranch omega x first
  have hyprojections : rootCoherentAlternateProjectionValues omega y =
      rootCoherentAlternateProjectionValues omega x := by
    simpa [y] using
      rootCoherentAlternateProjectionValues_rootsForBranch omega x first
  have hyinjective : Function.Injective y := by
    exact permuteRootTuple_injective hinjective _
  have hyepsilon : rootEpsilon omega y ≠ 0 := by
    exact rootEpsilon_rootsForBranch_ne_zero omega x hepsilon first
  refine {
    epsilon0 := v.epsilon
    epsilon0_square := hrelations.epsilon_square
    epsilon0_nonzero := by simpa [v, rootQuadraticTriple] using hepsilon
    epsilon_branches :=
      hrelations.squareBranchAvailable_of_not_both_zero hcomponents
    t := corrected.t
    t_square := by
      change corrected.t ^ 2 =
        (5 / 2) *
          (invariantE c i + invariantF c i /
            correctEpsilon c i v.epsilon)
      exact (hrelations.toTChoice hcomponents).square
    u_square := by
      rw [← correctedQuadraticTriple_epsilon c i v]
      rw [hrelations.radicalU_correctedQuadraticTriple
        hepsilon hcomponents]
      exact hrelations.of_correctedQuadraticTriple.u_square
    projections := rootCoherentAlternateProjectionValues omega x
    fourier := sourceForBranch (rootFourierOrbit omega x) first
    fourier_power := ?_
  }
  intro j
  change sourceForBranch (rootFourierOrbit omega x) first j ^ 5 =
    coherentAlternateRecover
      (branchTriple
        (coherentAlternateInitial c i v.epsilon corrected.t)
        (coherentAlternateBranchForIndex j)).epsilon
      (branchTriple
        (coherentAlternateInitial c i v.epsilon corrected.t)
        (coherentAlternateBranchForIndex j)).t
      (branchTriple
        (coherentAlternateInitial c i v.epsilon corrected.t)
        (coherentAlternateBranchForIndex j)).u
      (rootCoherentAlternateProjectionValues omega x)
  have hrecover := root_coherentAlternateRecover_fourierOrbit_forBranch
    omega hyinjective hyepsilon (coherentAlternateBranchForIndex j)
  calc
    sourceForBranch (rootFourierOrbit omega x) first j ^ 5 =
        rootFourierOrbit omega y j ^ 5 := by
      rw [hyfourier]
    _ = sourceForBranch (rootFourierOrbit omega y)
          (coherentAlternateBranchForIndex j) 0 ^ 5 := by
      rw [sourceForBranch_coherentAlternateBranchForIndex_zero]
    _ = coherentAlternateRecover
          (branchTriple (rootQuadraticTriple omega y)
            (coherentAlternateBranchForIndex j)).epsilon
          (branchTriple (rootQuadraticTriple omega y)
            (coherentAlternateBranchForIndex j)).t
          (branchTriple (rootQuadraticTriple omega y)
            (coherentAlternateBranchForIndex j)).u
          (rootCoherentAlternateProjectionValues omega y) :=
      hrecover.symm
    _ = coherentAlternateRecover
          (branchTriple
            (coherentAlternateInitial c i v.epsilon corrected.t)
            (coherentAlternateBranchForIndex j)).epsilon
          (branchTriple
            (coherentAlternateInitial c i v.epsilon corrected.t)
            (coherentAlternateBranchForIndex j)).t
          (branchTriple
            (coherentAlternateInitial c i v.epsilon corrected.t)
            (coherentAlternateBranchForIndex j)).u
          (rootCoherentAlternateProjectionValues omega x) := by
      rw [hytriple, hinitial, hyprojections]

/-- The Fourier vector carried by the root-origin alternate certificate is
the actual Fourier orbit after the one quadratic correction reordering. -/
@[simp] theorem rootCoherentAlternateFourierCertificate_fourier
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    (rootCoherentAlternateFourierCertificate omega x hsum hinjective
      hepsilon).fourier =
      sourceForBranch (rootFourierOrbit omega x)
        (correctedQuadraticBranch (depressedOfRoots x) (rootInvariants x)
          (rootQuadraticTriple omega x)) := by
  rfl

/-- Consequently the five denominator-safe outputs are exactly all five
roots, up to the correction reordering and the reversal caused by the
positive Fourier convention. -/
theorem rootCoherentAlternateFourierCertificate_solve_eq_reversedRoots
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    (fun k => d.solve omega k) =
      reversedRootTuple
        (rootsForBranch x
          (correctedQuadraticBranch (depressedOfRoots x) (rootInvariants x)
            (rootQuadraticTriple omega x))) := by
  let first := correctedQuadraticBranch
    (depressedOfRoots x) (rootInvariants x) (rootQuadraticTriple omega x)
  let y := rootsForBranch x first
  let d := rootCoherentAlternateFourierCertificate
    omega x hsum hinjective hepsilon
  have hsumY : elementaryTuple y 0 = 0 := by
    rw [show elementaryTuple y = elementaryTuple x by
      simpa [y] using elementaryTuple_rootsForBranch x first]
    exact hsum
  have hfourier : d.fourier = rootFourierOrbit omega y := by
    calc
      d.fourier = sourceForBranch (rootFourierOrbit omega x) first := by
        simpa [d, first] using
          rootCoherentAlternateFourierCertificate_fourier
            omega x hsum hinjective hepsilon
      _ = rootFourierOrbit omega y := by
        simpa [y] using
          (rootFourierOrbit_rootsForBranch omega x first).symm
  have hinverse := inverseFourier_rootFourier omega y hsumY
  funext k
  change inverseFourier omega.value (d.fourier 0) (d.fourier 1)
      (d.fourier 3) (d.fourier 2) k = reversedRootTuple y k
  rw [hfourier]
  exact congrFun hinverse k

/-- The denominator-safe root-origin certificate carries exact Vieta data
for its five outputs.  This is derived from the actual root tuple and the
proved inverse-Fourier reconstruction; no Vieta or correctness certificate
is supplied by the caller. -/
theorem rootCoherentAlternateFourierCertificate_fiveRootRelations
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    DepressedFiveRootRelations (depressedOfRoots x)
      (fun k => d.solve omega k) := by
  let first := correctedQuadraticBranch
    (depressedOfRoots x) (rootInvariants x) (rootQuadraticTriple omega x)
  let y := rootsForBranch x first
  let d := rootCoherentAlternateFourierCertificate
    omega x hsum hinjective hepsilon
  have hsumY : elementaryTuple y 0 = 0 := by
    rw [show elementaryTuple y = elementaryTuple x by
      simpa [y] using elementaryTuple_rootsForBranch x first]
    exact hsum
  have hy : DepressedFiveRootRelations (depressedOfRoots y) y :=
    depressedFiveRootRelations_depressedOfRoots y hsumY
  have hdepressed : depressedOfRoots y = depressedOfRoots x := by
    simpa [y] using depressedOfRoots_rootsForBranch x first
  have hsolve : (fun k => d.solve omega k) = reversedRootTuple y := by
    simpa [d, first, y] using
      rootCoherentAlternateFourierCertificate_solve_eq_reversedRoots
        omega x hsum hinjective hepsilon
  have hreversed := reversedRootTuple_esymm y
  constructor
  · rw [hsolve, hreversed.1]
    exact hy.sum
  · rw [hsolve, hreversed.2.1]
    simpa [hdepressed] using hy.pairs
  · rw [hsolve, hreversed.2.2.1]
    simpa [hdepressed] using hy.triples
  · rw [hsolve, hreversed.2.2.2.1]
    simpa [hdepressed] using hy.quadruples
  · rw [hsolve, hreversed.2.2.2.2]
    simpa [hdepressed] using hy.product

/-- Exact multiplicity-sensitive factorization by the five denominator-safe
outputs, derived from the preceding root-origin Vieta theorem. -/
theorem rootCoherentAlternateFourierCertificate_eval_factorization
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) (z : K) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    (depressedOfRoots x).eval z =
      ∏ k : Fin 5, (z - d.solve omega k) := by
  exact (rootCoherentAlternateFourierCertificate_fiveRootRelations
    omega x hsum hinjective hepsilon).eval_factorization z

/-- Every denominator-safe output is an actual root. -/
theorem rootCoherentAlternateFourierCertificate_eval_root
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) (k : Fin 5) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    (depressedOfRoots x).eval (d.solve omega k) = 0 := by
  exact (rootCoherentAlternateFourierCertificate_fiveRootRelations
    omega x hsum hinjective hepsilon).eval_root k

/-- The five denominator-safe outputs exhaust the complete root set. -/
theorem rootCoherentAlternateFourierCertificate_eval_eq_zero_iff
    [DecidableEq K]
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0) (z : K) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    (depressedOfRoots x).eval z = 0 ↔
      ∃ k : Fin 5, z = d.solve omega k := by
  exact (rootCoherentAlternateFourierCertificate_fiveRootRelations
    omega x hsum hinjective hepsilon).eval_eq_zero_iff z

/-- End-to-end denominator-safe field package for an ordered root tuple.
Once the invariant radicands and the four descended corrected projections
belong to the chosen base field, the explicit two-square/four-fifth field
(together with a radical source for `omega`) is radical, contains every
output, and those outputs reconstruct the complete root tuple. -/
theorem rootCoherentAlternate_radical_contains_and_reconstructs
    [DecidableEq K]
    (F : Type*) [Field F] [Algebra F K]
    (B : IntermediateField F K)
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hsum : elementaryTuple x 0 = 0)
    (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0)
    (hdata : RadicalInvariantDataIn F K B
      (depressedOfRoots x) (rootInvariants x))
    (hprojections : ∀ j,
      rootCoherentAlternateProjectionValues omega x j ∈ B)
    (homega : IsRadicalExtension F K B F⟮omega.value⟯) :
    let d := rootCoherentAlternateFourierCertificate
      omega x hsum hinjective hepsilon
    IsRadicalExtension F K B
        (d.generatedFieldWithRootOfUnity F K B omega) ∧
      (∀ k : Fin 5,
        d.solve omega k ∈ d.generatedFieldWithRootOfUnity F K B omega) ∧
      (fun k => d.solve omega k) =
        reversedRootTuple
          (rootsForBranch x
            (correctedQuadraticBranch
              (depressedOfRoots x) (rootInvariants x)
              (rootQuadraticTriple omega x))) := by
  let d := rootCoherentAlternateFourierCertificate
    omega x hsum hinjective hepsilon
  have hdprojections : ∀ j, d.projections j ∈ B := by
    intro j
    exact hprojections j
  constructor
  · exact d.generatedFieldWithRootOfUnity_isRadical F K omega
      hdata hdprojections homega
  constructor
  · exact fun k => d.solve_mem_generatedFieldWithRootOfUnity F K omega k
  · simpa [d] using
      rootCoherentAlternateFourierCertificate_solve_eq_reversedRoots
        omega x hsum hinjective hepsilon

/-- The useful one-coordinate partial stage: base membership of the
corrected projections puts the actual `P₁⁵` in the field after the two square
adjunctions.  This theorem alone is not full alternate completeness; the
other three fifth roots are handled by the certificate above. -/
theorem rootFourierP1_pow_five_mem_secondQuadraticField
    (F : Type*) [Field F] [Algebra F K]
    (B : IntermediateField F K) (omega : FifthRootOfUnity K)
    {x : Fin 5 → K} (hinjective : Function.Injective x)
    (hepsilon : rootEpsilon omega x ≠ 0)
    (hu : rootFormulaU omega x ∈
      (B ⊔ F⟮rootEpsilon omega x⟯) ⊔ F⟮rootT omega x⟯)
    (hprojections : ∀ j,
      rootCoherentAlternateProjectionValues omega x j ∈ B) :
    rootFourierP1 omega x ^ 5 ∈
      (B ⊔ F⟮rootEpsilon omega x⟯) ⊔ F⟮rootT omega x⟯ := by
  let L : IntermediateField F K :=
    (B ⊔ F⟮rootEpsilon omega x⟯) ⊔ F⟮rootT omega x⟯
  have hepsilon_mem : rootEpsilon omega x ∈ L :=
    (show B ⊔ F⟮rootEpsilon omega x⟯ ≤ L from le_sup_left)
      ((show F⟮rootEpsilon omega x⟯ ≤
          B ⊔ F⟮rootEpsilon omega x⟯ from le_sup_right)
        (mem_adjoin_simple_self F (rootEpsilon omega x)))
  have ht_mem : rootT omega x ∈ L :=
    (show F⟮rootT omega x⟯ ≤ L from le_sup_right)
      (mem_adjoin_simple_self F (rootT omega x))
  have hB : B ≤ L :=
    (show B ≤ B ⊔ F⟮rootEpsilon omega x⟯ from le_sup_left).trans le_sup_left
  have hrecover : coherentAlternateRecover (rootEpsilon omega x)
      (rootT omega x) (rootFormulaU omega x)
      (rootCoherentAlternateProjectionValues omega x) ∈ L :=
    CoherentAlternateFourierCertificate.coherentAlternateRecover_mem
      F K L (rootQuadraticTriple omega x)
      (rootCoherentAlternateProjectionValues omega x)
      ⟨hepsilon_mem, ht_mem, hu⟩ (fun j => hB (hprojections j))
  rw [← root_coherentAlternateRecover_fourierP1_pow_five
    omega hinjective hepsilon]
  exact hrecover

end RootAdapters

end LeanProofs.PolynomialFormulas.LazardQuintic
