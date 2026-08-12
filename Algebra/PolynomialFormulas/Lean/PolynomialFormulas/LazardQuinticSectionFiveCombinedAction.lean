import PolynomialFormulas.LazardQuinticRootBranchAction
import Mathlib.Tactic.IntervalCases

/-!
# Lazard's combined root/cyclotomic action in Section 5

This file records the literal notation and action used on pp. 215--216 of
Lazard's paper.  For the five Fourier sums `s₀,...,s₄`, put

`S₁ = s₁⁵`, `S₂ = s₂ s₁³`, `S₃ = s₃ s₁²`, and `S₄ = s₄ s₁`.

The root permutation `φ : xᵢ ↦ x₂ᵢ` and the cyclotomic generator change
`ψ : ω ↦ ω²` commute.  Their composite fixes every displayed `sᵢ` and
`Sᵢ`.  We also isolate the formal implication used in the paper: a value
which is both `φ`-invariant and fixed by `φ ∘ ψ` is independent of the
generator change `ω ↦ ω²`.  Iterating that change reaches all four primitive
fifth roots, so the final independence theorem compares any two choices.

The paper's earlier printed coordinate `U` and the formula coordinate used in
Figure 3 have opposite signs.  We state the corrected `φ` action on the
printed coordinate explicitly below and keep that convention visible in the
name of the projection tuple.

All statements are over an arbitrary field.  No characteristic-zero
hypothesis is used; the supplied primitive fifth root contains exactly the
cyclotomic nondegeneracy needed by the calculations.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

open Fin5Solvable FrobeniusDummitResolvent

set_option autoImplicit false

section

variable {K : Type*} [Field K]

/-- The primitive fifth-root generator change `ω ↦ ω²`. -/
def FifthRootOfUnity.squared
    (omega : FifthRootOfUnity K) : FifthRootOfUnity K where
  value := omega.value ^ 2
  primitive := omega.primitive.pow_of_coprime 2 (by decide)

/-- The third primitive power of a chosen fifth root. -/
def FifthRootOfUnity.cubed
    (omega : FifthRootOfUnity K) : FifthRootOfUnity K where
  value := omega.value ^ 3
  primitive := omega.primitive.pow_of_coprime 3 (by decide)

/-- The fourth primitive power of a chosen fifth root. -/
def FifthRootOfUnity.fourth
    (omega : FifthRootOfUnity K) : FifthRootOfUnity K where
  value := omega.value ^ 4
  primitive := omega.primitive.pow_of_coprime 4 (by decide)

/-- Packaged primitive fifth roots are equal when their values are equal. -/
theorem FifthRootOfUnity.eq_of_value_eq
    {omega eta : FifthRootOfUnity K}
    (h : omega.value = eta.value) : omega = eta := by
  cases omega
  cases eta
  simp_all

/-- Two iterations of `ω ↦ ω²` give the fourth primitive power. -/
theorem FifthRootOfUnity.squared_squared
    (omega : FifthRootOfUnity K) :
    omega.squared.squared = omega.fourth := by
  apply FifthRootOfUnity.eq_of_value_eq
  change (omega.value ^ 2) ^ 2 = omega.value ^ 4
  ring

/-- Three iterations of `ω ↦ ω²` give the third primitive power because
`2³ = 8 = 3 (mod 5)`. -/
theorem FifthRootOfUnity.squared_squared_squared
    (omega : FifthRootOfUnity K) :
    omega.squared.squared.squared = omega.cubed := by
  apply FifthRootOfUnity.eq_of_value_eq
  change ((omega.value ^ 2) ^ 2) ^ 2 = omega.value ^ 3
  calc
    ((omega.value ^ 2) ^ 2) ^ 2 = omega.value ^ 8 := by ring
    _ = omega.value ^ (8 % 5) := omega.pow_eq_pow_mod_five 8
    _ = omega.value ^ 3 := by norm_num

/-- Every packaged primitive fifth root is one of the four primitive powers
of any fixed one. -/
theorem FifthRootOfUnity.primitive_cases
    (omega eta : FifthRootOfUnity K) :
    eta = omega ∨ eta = omega.squared ∨
      eta = omega.cubed ∨ eta = omega.fourth := by
  obtain ⟨n, hn, hcoprime, hpower⟩ :=
    (omega.primitive.isPrimitiveRoot_iff).mp eta.primitive
  interval_cases n
  · norm_num at hcoprime
  · left
    apply FifthRootOfUnity.eq_of_value_eq
    simpa using hpower.symm
  · right; left
    apply FifthRootOfUnity.eq_of_value_eq
    simpa [FifthRootOfUnity.squared] using hpower.symm
  · right; right; left
    apply FifthRootOfUnity.eq_of_value_eq
    simpa [FifthRootOfUnity.cubed] using hpower.symm
  · right; right; right
    apply FifthRootOfUnity.eq_of_value_eq
    simpa [FifthRootOfUnity.fourth] using hpower.symm

private theorem quadraticTriple_eq_of_fields
    {a b : QuadraticTriple K}
    (hepsilon : a.epsilon = b.epsilon)
    (ht : a.t = b.t) (hu : a.u = b.u) : a = b := by
  cases a
  cases b
  simp_all

/-! ## The separate `ψ` transformations -/

theorem rootEpsilon_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootEpsilon omega.squared x = -rootEpsilon omega x := by
  simp [FifthRootOfUnity.squared, rootEpsilon,
    fifthRootDiscriminantFactor]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

theorem rootT_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootT omega.squared x = -rootFormulaU omega x := by
  simp [FifthRootOfUnity.squared, rootT, rootFormulaU, rootU]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFormulaU_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaU omega.squared x = rootT omega x := by
  simp [FifthRootOfUnity.squared, rootT, rootFormulaU, rootU]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

/-- Squaring the fifth-root generator realizes the coherent
`rotateNegate` branch on the quadratic coordinates. -/
theorem rootQuadraticTriple_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootQuadraticTriple omega.squared x =
      branchTriple (rootQuadraticTriple omega x) .rotateNegate := by
  apply quadraticTriple_eq_of_fields
  · exact rootEpsilon_squared omega x
  · exact rootT_squared omega x
  · exact rootFormulaU_squared omega x

theorem rootFourierP1_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierP1 omega.squared x = rootFourierP2 omega x := by
  simp [FifthRootOfUnity.squared, rootFourierP1, rootFourierP2]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFourierP2_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierP2 omega.squared x = rootFourierP4 omega x := by
  simp [FifthRootOfUnity.squared, rootFourierP2, rootFourierP4]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFourierP4_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierP4 omega.squared x = rootFourierP3 omega x := by
  simp [FifthRootOfUnity.squared, rootFourierP4, rootFourierP3]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

theorem rootFourierP3_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierP3 omega.squared x = rootFourierP1 omega x := by
  simp [FifthRootOfUnity.squared, rootFourierP3, rootFourierP1]
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 6, omega.pow_eq_pow_mod_five 5]
  ring

/-- The four Fourier sums, in the existing orbit order `s₁,s₂,s₄,s₃`,
follow the matching `rotateNegate` permutation under `ω ↦ ω²`. -/
theorem rootFourierOrbit_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierOrbit omega.squared x =
      sourceForBranch (rootFourierOrbit omega x) .rotateNegate := by
  funext i
  fin_cases i <;>
    simp [rootFourierOrbit, sourceForBranch,
      rootFourierP1_squared, rootFourierP2_squared,
      rootFourierP3_squared, rootFourierP4_squared]

/-- The fifth-power Fourier orbit follows the same permutation under
`ω ↦ ω²`. -/
theorem rootFourierFifthOrbit_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierFifthOrbit omega.squared x =
      sourceForBranch (rootFourierFifthOrbit omega x) .rotateNegate := by
  funext i
  fin_cases i <;>
    simp [rootFourierFifthOrbit, sourceForBranch,
      rootFourierP1_squared, rootFourierP2_squared,
      rootFourierP3_squared, rootFourierP4_squared]

/-! ## Literal Section-5 notation and the combined action -/

/-- Lazard's displayed Fourier sums `s₀,...,s₄`, in that order. -/
def sectionFiveFourierS
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 5 → K :=
  ![x 0 + x 1 + x 2 + x 3 + x 4,
    rootFourierP1 omega x, rootFourierP2 omega x,
    rootFourierP3 omega x, rootFourierP4 omega x]

/-- For a centered root tuple, Lazard's zeroth Fourier sum is zero. -/
theorem sectionFiveFourierS_s0_eq_zero_of_centered
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hcentered : x 0 + x 1 + x 2 + x 3 + x 4 = 0) :
    sectionFiveFourierS omega x 0 = 0 := by
  simpa [sectionFiveFourierS] using hcentered

/-- Lazard's displayed cyclic invariants
`S₁=s₁⁵`, `S₂=s₂s₁³`, `S₃=s₃s₁²`, `S₄=s₄s₁`. -/
def sectionFiveCyclicS
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  let s := sectionFiveFourierS omega x
  ![s 1 ^ 5, s 2 * s 1 ^ 3, s 3 * s 1 ^ 2, s 4 * s 1]

/-- The displayed `S₁,...,S₄` are fixed by the cyclic root relabelling.  The
proof reuses the already-established Fourier-character covariance rather than
expanding the four Fourier sums again. -/
theorem sectionFiveCyclicS_permute_fiveCycle
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    sectionFiveCyclicS omega (permuteRootTuple x fiveCycle) =
      sectionFiveCyclicS omega x := by
  funext k
  fin_cases k
  · change rootFourierP1 omega (permuteRootTuple x fiveCycle) ^ 5 =
      rootFourierP1 omega x ^ 5
    rw [rootFourierP1_permute_fiveCycle_f20]
    exact omega.pow_mul_pow_five 4 (rootFourierP1 omega x)
  · change rootFourierP2 omega (permuteRootTuple x fiveCycle) *
        rootFourierP1 omega (permuteRootTuple x fiveCycle) ^ 3 =
      rootFourierP2 omega x * rootFourierP1 omega x ^ 3
    rw [rootFourierP2_permute_fiveCycle_f20,
      rootFourierP1_permute_fiveCycle_f20]
    calc
      (omega.value ^ 3 * rootFourierP2 omega x) *
          (omega.value ^ 4 * rootFourierP1 omega x) ^ 3 =
        omega.value ^ 15 *
          (rootFourierP2 omega x * rootFourierP1 omega x ^ 3) := by ring
      _ = rootFourierP2 omega x * rootFourierP1 omega x ^ 3 := by
        rw [omega.pow_eq_pow_mod_five 15]
        norm_num
  · change rootFourierP3 omega (permuteRootTuple x fiveCycle) *
        rootFourierP1 omega (permuteRootTuple x fiveCycle) ^ 2 =
      rootFourierP3 omega x * rootFourierP1 omega x ^ 2
    rw [rootFourierP3_permute_fiveCycle_f20,
      rootFourierP1_permute_fiveCycle_f20]
    calc
      (omega.value ^ 2 * rootFourierP3 omega x) *
          (omega.value ^ 4 * rootFourierP1 omega x) ^ 2 =
        omega.value ^ 10 *
          (rootFourierP3 omega x * rootFourierP1 omega x ^ 2) := by ring
      _ = rootFourierP3 omega x * rootFourierP1 omega x ^ 2 := by
        rw [omega.pow_eq_pow_mod_five 10]
        norm_num
  · change rootFourierP4 omega (permuteRootTuple x fiveCycle) *
        rootFourierP1 omega (permuteRootTuple x fiveCycle) =
      rootFourierP4 omega x * rootFourierP1 omega x
    rw [rootFourierP4_permute_fiveCycle_f20,
      rootFourierP1_permute_fiveCycle_f20]
    calc
      (omega.value * rootFourierP4 omega x) *
          (omega.value ^ 4 * rootFourierP1 omega x) =
        omega.value ^ 5 *
          (rootFourierP4 omega x * rootFourierP1 omega x) := by ring
      _ = rootFourierP4 omega x * rootFourierP1 omega x := by
        rw [omega.pow_eq_pow_mod_five 5]
        norm_num

/-- Denominator-safe recovery of `x₀` from the actual `s₁` and cyclic
invariants.  Here `S₁=s₁⁵` is the consistency equation, while the remaining
three entries recover `s₂,s₃,s₄`; retaining `s₀` makes the statement valid
before centering as well. -/
theorem sectionFive_x0_recover_from_s1_cyclicS
    (omega : FifthRootOfUnity K) (x : Fin 5 → K)
    (hs1 : sectionFiveFourierS omega x 1 ≠ 0)
    (hfive : (5 : K) ≠ 0) :
    let s := sectionFiveFourierS omega x
    let S := sectionFiveCyclicS omega x
    x 0 = (s 0 + s 1 + S 1 / s 1 ^ 3 + S 2 / s 1 ^ 2 + S 3 / s 1) / 5 := by
  have hp1 : rootFourierP1 omega x ≠ 0 := by
    simpa [sectionFiveFourierS] using hs1
  have hS2 :
      sectionFiveCyclicS omega x 1 /
          sectionFiveFourierS omega x 1 ^ 3 =
        sectionFiveFourierS omega x 2 := by
    change (rootFourierP2 omega x * rootFourierP1 omega x ^ 3) /
        rootFourierP1 omega x ^ 3 = rootFourierP2 omega x
    exact mul_div_cancel_right₀ _ (pow_ne_zero 3 hp1)
  have hS3 :
      sectionFiveCyclicS omega x 2 /
          sectionFiveFourierS omega x 1 ^ 2 =
        sectionFiveFourierS omega x 3 := by
    change (rootFourierP3 omega x * rootFourierP1 omega x ^ 2) /
        rootFourierP1 omega x ^ 2 = rootFourierP3 omega x
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hp1)
  have hS4 :
      sectionFiveCyclicS omega x 3 /
          sectionFiveFourierS omega x 1 =
        sectionFiveFourierS omega x 4 := by
    change (rootFourierP4 omega x * rootFourierP1 omega x) /
        rootFourierP1 omega x = rootFourierP4 omega x
    exact mul_div_cancel_right₀ _ hp1
  dsimp only
  rw [hS2, hS3, hS4]
  apply (eq_div_iff hfive).2
  simp [sectionFiveFourierS, rootFourierP1, rootFourierP2,
    rootFourierP3, rootFourierP4, omega.pow_four_eq_neg] <;> ring

/-- A chosen primitive fifth root together with an ordered root tuple. -/
structure SectionFiveConfiguration (K : Type*) [Field K] where
  omega : FifthRootOfUnity K
  roots : Fin 5 → K

/-- Lazard's `φ : xᵢ ↦ x₂ᵢ`. -/
def sectionFivePhi
    (c : SectionFiveConfiguration K) : SectionFiveConfiguration K :=
  ⟨c.omega, permuteRootTuple c.roots multiplierTwo⟩

/-- Lazard's `ψ : ω ↦ ω²`. -/
def sectionFivePsi
    (c : SectionFiveConfiguration K) : SectionFiveConfiguration K :=
  ⟨c.omega.squared, c.roots⟩

/-- The root permutation and cyclotomic generator change commute. -/
theorem sectionFive_phi_psi_commute
    (c : SectionFiveConfiguration K) :
    sectionFivePhi (sectionFivePsi c) =
      sectionFivePsi (sectionFivePhi c) := by
  rfl

/-- The corrected first identity for the printed Section-5 coordinate:
`φ(T)=-U_printed`. -/
theorem sectionFive_phi_T_eq_neg_printedU
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootT omega (permuteRootTuple x multiplierTwo) = -rootU omega x := by
  calc
    rootT omega (permuteRootTuple x multiplierTwo) =
        rootFormulaU omega x := rootT_permute_multiplierTwo omega x
    _ = -rootU omega x := rootFormulaU_eq_neg_rootU omega x

/-- Correction of the second sign in the display on p. 216 (source line
282): the printed coordinate satisfies `φ(U_printed)=T`, not `-T`.  The
formula coordinate is its negative and therefore does transform to `-T`. -/
theorem sectionFive_phi_printedU_eq_T
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootU omega (permuteRootTuple x multiplierTwo) = rootT omega x :=
  rootU_permute_multiplierTwo omega x

/-- The combined action `φ ∘ ψ` fixes the four positive Fourier sums. -/
theorem rootFourierOrbit_phiPsi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierOrbit omega.squared
        (permuteRootTuple x multiplierTwo) =
      rootFourierOrbit omega x := by
  rw [rootFourierOrbit_squared, rootFourierOrbit_permute_multiplierTwo]
  funext i
  fin_cases i <;> rfl

/-- The combined action `φ ∘ ψ` fixes every displayed `s₀,...,s₄`. -/
theorem sectionFiveFourierS_phiPsi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    sectionFiveFourierS omega.squared
        (permuteRootTuple x multiplierTwo) =
      sectionFiveFourierS omega x := by
  have horbit := rootFourierOrbit_phiPsi_fixed omega x
  funext k
  fin_cases k
  · simp [sectionFiveFourierS, permuteRootTuple, multiplierTwo] <;> ring
  · simpa [sectionFiveFourierS, rootFourierOrbit] using
      congrFun horbit (0 : Fin 4)
  · simpa [sectionFiveFourierS, rootFourierOrbit] using
      congrFun horbit (1 : Fin 4)
  · simpa [sectionFiveFourierS, rootFourierOrbit] using
      congrFun horbit (3 : Fin 4)
  · simpa [sectionFiveFourierS, rootFourierOrbit] using
      congrFun horbit (2 : Fin 4)

/-- The combined action fixes every displayed `S₁,...,S₄`. -/
theorem sectionFiveCyclicS_phiPsi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    sectionFiveCyclicS omega.squared
        (permuteRootTuple x multiplierTwo) =
      sectionFiveCyclicS omega x := by
  have hs := sectionFiveFourierS_phiPsi_fixed omega x
  funext k
  fin_cases k <;> simp [sectionFiveCyclicS, hs]

/-! ## Independence of the primitive-root generator -/

/-- If a root expression is `φ`-invariant and fixed by `φ ∘ ψ`, then it
is unchanged by `ψ`, i.e. by replacing `ω` with `ω²`. -/
theorem omegaSquared_independent_of_phi_invariant
    {A : Type*}
    (I : FifthRootOfUnity K → (Fin 5 → K) → A)
    (hphi : ∀ omega x,
      I omega (permuteRootTuple x multiplierTwo) = I omega x)
    (hphiPsi : ∀ omega x,
      I omega.squared (permuteRootTuple x multiplierTwo) = I omega x)
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    I omega.squared x = I omega x := by
  calc
    I omega.squared x =
        I omega.squared (permuteRootTuple x multiplierTwo) :=
      (hphi omega.squared x).symm
    _ = I omega x := hphiPsi omega x

/-- Invariance under `ω ↦ ω²` implies equality for every pair of primitive
fifth-root choices, since repeated squaring visits powers `1,2,4,3`. -/
theorem primitiveFifthRoot_independent_of_squared
    {A : Type*} (I : FifthRootOfUnity K → A)
    (hsquared : ∀ omega, I omega.squared = I omega)
    (omega eta : FifthRootOfUnity K) : I eta = I omega := by
  rcases omega.primitive_cases eta with rfl | rfl | rfl | rfl
  · rfl
  · exact hsquared omega
  · rw [← FifthRootOfUnity.squared_squared_squared]
    exact (hsquared omega.squared.squared).trans
      ((hsquared omega.squared).trans (hsquared omega))
  · rw [← FifthRootOfUnity.squared_squared]
    exact (hsquared omega.squared).trans (hsquared omega)

/-- The combined action fixes Lazard's quadratic triple. -/
theorem rootQuadraticTriple_phiPsi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootQuadraticTriple omega.squared
        (permuteRootTuple x multiplierTwo) =
      rootQuadraticTriple omega x := by
  rw [rootQuadraticTriple_squared,
    rootQuadraticTriple_permute_multiplierTwo]
  simp [branchTriple]

/-- The combined action fixes the four fifth-power source values. -/
theorem rootFourierFifthOrbit_phiPsi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFourierFifthOrbit omega.squared
        (permuteRootTuple x multiplierTwo) =
      rootFourierFifthOrbit omega x := by
  rw [rootFourierFifthOrbit_squared,
    rootFourierFifthOrbit_permute_multiplierTwo]
  funext i
  fin_cases i <;> rfl

/-- Lazard's literal forward Section-5 source order

`[S, φ(S), φ²(S), φ³(S)] = [P₁⁵, P₃⁵, P₄⁵, P₂⁵]`.

The existing `rootFourierFifthOrbit` uses the reverse orbit order after its
zeroth entry, so this separate definition keeps the printed convention
explicit. -/
def rootPrintedSectionFiveForwardSource
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  ![rootFourierP1 omega x ^ 5, rootFourierP3 omega x ^ 5,
    rootFourierP4 omega x ^ 5, rootFourierP2 omega x ^ 5]

/-- The description of the printed forward source as a `φ`-orbit is an
actual equivariance theorem, not merely a mnemonic for its definition.
Here every occurrence of `φ` is the literal multiplier-two permutation of
the root tuple, and the nesting makes the order
`[S, φ(S), φ²(S), φ³(S)]` unambiguous. -/
theorem rootPrintedSectionFiveForwardSource_eq_phiIterates
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootPrintedSectionFiveForwardSource omega x =
      ![rootFourierP1 omega x ^ 5,
        rootFourierP1 omega (permuteRootTuple x multiplierTwo) ^ 5,
        rootFourierP1 omega
            (permuteRootTuple
              (permuteRootTuple x multiplierTwo) multiplierTwo) ^ 5,
        rootFourierP1 omega
            (permuteRootTuple
              (permuteRootTuple
                (permuteRootTuple x multiplierTwo) multiplierTwo)
              multiplierTwo) ^ 5] := by
  have hphi₁ :
      rootFourierFifthOrbit omega (permuteRootTuple x multiplierTwo) =
        sourceForBranch (rootFourierFifthOrbit omega x) .rotate :=
    rootFourierFifthOrbit_permute_multiplierTwo omega x
  have hphi₂ :
      rootFourierFifthOrbit omega
          (permuteRootTuple
            (permuteRootTuple x multiplierTwo) multiplierTwo) =
        sourceForBranch
          (sourceForBranch (rootFourierFifthOrbit omega x) .rotate)
          .rotate := by
    calc
      rootFourierFifthOrbit omega
          (permuteRootTuple
            (permuteRootTuple x multiplierTwo) multiplierTwo) =
          sourceForBranch
            (rootFourierFifthOrbit omega
              (permuteRootTuple x multiplierTwo)) .rotate :=
        rootFourierFifthOrbit_permute_multiplierTwo omega _
      _ = sourceForBranch
            (sourceForBranch (rootFourierFifthOrbit omega x) .rotate)
            .rotate := congrArg (fun source ↦ sourceForBranch source .rotate) hphi₁
  have hphi₃ :
      rootFourierFifthOrbit omega
          (permuteRootTuple
            (permuteRootTuple
              (permuteRootTuple x multiplierTwo) multiplierTwo)
            multiplierTwo) =
        sourceForBranch
          (sourceForBranch
            (sourceForBranch (rootFourierFifthOrbit omega x) .rotate)
            .rotate) .rotate := by
    calc
      rootFourierFifthOrbit omega
          (permuteRootTuple
            (permuteRootTuple
              (permuteRootTuple x multiplierTwo) multiplierTwo)
            multiplierTwo) =
          sourceForBranch
            (rootFourierFifthOrbit omega
              (permuteRootTuple
                (permuteRootTuple x multiplierTwo) multiplierTwo))
            .rotate := rootFourierFifthOrbit_permute_multiplierTwo omega _
      _ = sourceForBranch
            (sourceForBranch
              (sourceForBranch (rootFourierFifthOrbit omega x) .rotate)
              .rotate) .rotate :=
        congrArg (fun source ↦ sourceForBranch source .rotate) hphi₂
  funext i
  fin_cases i
  · rfl
  · simpa [rootPrintedSectionFiveForwardSource, rootFourierFifthOrbit,
      sourceForBranch] using (congrFun hphi₁ (0 : Fin 4)).symm
  · simpa [rootPrintedSectionFiveForwardSource, rootFourierFifthOrbit,
      sourceForBranch] using (congrFun hphi₂ (0 : Fin 4)).symm
  · simpa [rootPrintedSectionFiveForwardSource, rootFourierFifthOrbit,
      sourceForBranch] using (congrFun hphi₃ (0 : Fin 4)).symm

/-- Lazard's literal printed tuple `[I₁,I₂,I₃,I₄]`: apply the
printed standard projection matrix to the forward source orbit, using the
printed quadratic coordinate `U`. -/
def rootPrintedSectionFiveProjectionValues
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  standardProjections (rootEpsilon omega x) (rootT omega x)
    (rootU omega x) (rootPrintedSectionFiveForwardSource omega x)

/-- The standard projection matrix evaluated in the Figure-3/formula-sign
convention.  Its quadratic coordinate is
`U_formula = rootFormulaU = -U_printed`, and its source order is

`[P₁⁵,P₂⁵,P₄⁵,P₃⁵] = [S,φ³(S),φ²(S),φ(S)]`.

Consequently, relative to the literal Section-5 convention and source order,
this tuple is `[I₁,I₂,I₃,-I₄]`, not the literal `[I₁,I₂,I₃,I₄]`. -/
def rootFormulaConventionProjectionValues
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) : Fin 4 → K :=
  standardProjections
    (rootQuadraticTriple omega x).epsilon
    (rootQuadraticTriple omega x).t
    (rootQuadraticTriple omega x).u
    (rootFourierFifthOrbit omega x)

/-- Exact comparison with Lazard's literal printed Section-5 convention.
After reversing the nonzero forward-orbit entries and replacing
`U_printed` by `U_formula = -U_printed`, the formula tuple is
`[I₁,I₂,I₃,-I₄]`. -/
theorem
    rootFormulaConventionProjectionValues_eq_printed_I1_I2_I3_neg_I4
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaConventionProjectionValues omega x =
      ![rootPrintedSectionFiveProjectionValues omega x 0,
        rootPrintedSectionFiveProjectionValues omega x 1,
        rootPrintedSectionFiveProjectionValues omega x 2,
        -rootPrintedSectionFiveProjectionValues omega x 3] := by
  funext j
  fin_cases j <;>
    simp [rootFormulaConventionProjectionValues,
      rootPrintedSectionFiveProjectionValues,
      rootPrintedSectionFiveForwardSource, rootQuadraticTriple,
      rootFormulaU, rootFourierFifthOrbit, standardProjections,
      standardProjectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

/-- The formula-convention projection vector is invariant under `φ`. -/
theorem rootFormulaConventionProjectionValues_phi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaConventionProjectionValues omega
        (permuteRootTuple x multiplierTwo) =
      rootFormulaConventionProjectionValues omega x := by
  change standardProjections
      (rootQuadraticTriple omega
        (permuteRootTuple x multiplierTwo)).epsilon
      (rootQuadraticTriple omega
        (permuteRootTuple x multiplierTwo)).t
      (rootQuadraticTriple omega
        (permuteRootTuple x multiplierTwo)).u
      (rootFourierFifthOrbit omega
        (permuteRootTuple x multiplierTwo)) = _
  rw [rootQuadraticTriple_permute_multiplierTwo,
    rootFourierFifthOrbit_permute_multiplierTwo]
  exact standardProjections_branchTriple_sourceForBranch
    (rootQuadraticTriple omega x) (rootFourierFifthOrbit omega x) .rotate

/-- The formula-convention projection vector is fixed by `φ ∘ ψ`. -/
theorem rootFormulaConventionProjectionValues_phiPsi_fixed
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaConventionProjectionValues omega.squared
        (permuteRootTuple x multiplierTwo) =
      rootFormulaConventionProjectionValues omega x := by
  simp only [rootFormulaConventionProjectionValues,
    rootQuadraticTriple_phiPsi_fixed,
    rootFourierFifthOrbit_phiPsi_fixed]

/-- The formula-convention projection values are unchanged by `ω ↦ ω²`. -/
theorem rootFormulaConventionProjectionValues_squared
    (omega : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaConventionProjectionValues omega.squared x =
      rootFormulaConventionProjectionValues omega x := by
  exact omegaSquared_independent_of_phi_invariant
    rootFormulaConventionProjectionValues
    rootFormulaConventionProjectionValues_phi_fixed
    rootFormulaConventionProjectionValues_phiPsi_fixed omega x

/-- The formula-convention projection tuple is independent of the primitive
fifth-root choice, not only of one generator squaring step. -/
theorem rootFormulaConventionProjectionValues_primitiveRoot_independent
    (omega eta : FifthRootOfUnity K) (x : Fin 5 → K) :
    rootFormulaConventionProjectionValues eta x =
      rootFormulaConventionProjectionValues omega x := by
  exact primitiveFifthRoot_independent_of_squared
    (fun z ↦ rootFormulaConventionProjectionValues z x)
    (fun z ↦ rootFormulaConventionProjectionValues_squared z x)
    omega eta

end

end LeanProofs.PolynomialFormulas.LazardQuintic
