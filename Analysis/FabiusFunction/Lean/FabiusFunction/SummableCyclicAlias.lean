import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Summable cyclic aliasing

This file gives the abstract root-of-unity filter for a summable bilateral sequence.
The values may lie in any complete Hausdorff uniform complex module with continuous scalar
multiplication.  No norm or absolute-convergence hypothesis is needed:
multiplying by a character of `ZMod q` amounts to multiplying the finitely many
residue-class subseries by fixed scalars.

The underlying convergence lemma, `summable_finite_range_smul`, is stated first in its
natural generality for an arbitrary finite label type and any continuous distributive
scalar action on a complete uniform additive group.

For `a : ℤ → E`, `intResidueTsum a r` is the subseries over the congruence class `r`,
whereas `intFourierTsum a k` is the bilateral Fourier sum at the standard additive
character of frequency `k`.  The discrete Fourier transform carries the former family
to the latter, and Fourier inversion recovers every residue-class sum as a normalized
character average.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

variable {R E β ι : Type*}

/-- A summable family remains summable after scalar multiplication by a
finite-range coefficient.

The coefficients are presented as `c (label b)` with a finite label type.  This
is the precise convergence principle behind cyclic character twists, but it is
independent of integers, residue classes, and norms. -/
theorem summable_finite_range_smul [Fintype ι] [UniformSpace E]
    [AddCommGroup E] [IsUniformAddGroup E] [CompleteSpace E] [DistribSMul R E]
    [ContinuousConstSMul R E] (a : β → E) (ha : Summable a)
    (label : β → ι) (c : ι → R) :
    Summable (fun b ↦ c (label b) • a b) := by
  classical
  have hfiber (i : ι) :
      Summable ({b : β | label b = i}.indicator (fun b ↦ c i • a b)) :=
    (ha.const_smul (c i)).indicator _
  have hpartition :
      (fun b ↦ c (label b) • a b) =
        fun b ↦ ∑ i : ι,
          {b : β | label b = i}.indicator (fun b ↦ c i • a b) b := by
    funext b
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  rw [hpartition]
  exact summable_sum (s := Finset.univ) fun i _ ↦ hfiber i

section ResidueSums

variable {q : ℕ}
variable {E : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [CompleteSpace E]

/-- The bilateral sum of `a` over the integers whose residue modulo `q` is `r`. -/
noncomputable def intResidueTsum (a : ℤ → E) (r : ZMod q) : E :=
  ∑' n : (fun n : ℤ ↦ (n : ZMod q)) ⁻¹' {r}, a n

variable [T2Space E]

/-- The residue-class subseries, indexed by all residues, sums to the original
bilateral series. -/
theorem hasSum_intResidueTsum (a : ℤ → E) (ha : Summable a) :
    HasSum (intResidueTsum (q := q) a) (∑' n : ℤ, a n) := by
  change HasSum
    (fun r : ZMod q ↦ ∑' n : (fun n : ℤ ↦ (n : ZMod q)) ⁻¹' {r}, a n)
    (∑' n : ℤ, a n)
  exact ha.hasSum.tsum_fiberwise (fun n : ℤ ↦ (n : ZMod q))

variable [NeZero q]

/-- Partitioning a summable bilateral series into its residue classes preserves its
sum. -/
theorem sum_intResidueTsum (a : ℤ → E) (ha : Summable a) :
    ∑ r : ZMod q, intResidueTsum (q := q) a r = ∑' n : ℤ, a n := by
  simpa only [tsum_fintype] using (hasSum_intResidueTsum (q := q) a ha).tsum_eq

end ResidueSums

section FourierSums

variable {q : ℕ} [NeZero q]
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [CompleteSpace E] [ContinuousConstSMul ℂ E]

/-- The bilateral Fourier sum of `a` against the standard character of `ZMod q`.

The minus sign matches Mathlib's convention for `ZMod.dft`.
-/
noncomputable def intFourierTsum (a : ℤ → E) (k : ZMod q) : E :=
  ∑' n : ℤ, ZMod.stdAddChar (-((n : ZMod q) * k)) • a n

/-- A summable bilateral sequence remains summable after twisting by a cyclic
character. -/
theorem intFourierSummand_summable (a : ℤ → E) (ha : Summable a) (k : ZMod q) :
    Summable (fun n : ℤ ↦ ZMod.stdAddChar (-((n : ZMod q) * k)) • a n) := by
  exact summable_finite_range_smul a ha (fun n : ℤ ↦ (n : ZMod q))
    (fun r ↦ ZMod.stdAddChar (-(r * k)))

variable [T2Space E]

/-- The discrete Fourier transform of the residue-class sums is the family of
bilateral Fourier sums. -/
theorem dft_intResidueTsum (a : ℤ → E) (ha : Summable a) :
    ZMod.dft (intResidueTsum (q := q) a) = intFourierTsum (q := q) a := by
  funext k
  rw [ZMod.dft_apply]
  let b : ℤ → E := fun n ↦ ZMod.stdAddChar (-((n : ZMod q) * k)) • a n
  have hb : Summable b := intFourierSummand_summable (q := q) a ha k
  have hfiber (r : ZMod q) :
      intResidueTsum (q := q) b r =
        ZMod.stdAddChar (-(r * k)) • intResidueTsum (q := q) a r := by
    rw [intResidueTsum, intResidueTsum]
    calc
      (∑' n : (fun n : ℤ ↦ (n : ZMod q)) ⁻¹' {r}, b n) =
          ∑' n : (fun n : ℤ ↦ (n : ZMod q)) ⁻¹' {r},
            ZMod.stdAddChar (-(r * k)) • a n := by
              apply tsum_congr
              intro n
              have hn := n.property
              change (n.1 : ZMod q) = r at hn
              simp only [b, hn]
      _ = ZMod.stdAddChar (-(r * k)) •
          ∑' n : (fun n : ℤ ↦ (n : ZMod q)) ⁻¹' {r}, a n :=
        (ha.subtype _).tsum_const_smul _
  calc
    ∑ r : ZMod q, ZMod.stdAddChar (-(r * k)) • intResidueTsum (q := q) a r =
        ∑ r : ZMod q, intResidueTsum (q := q) b r := by
      apply Finset.sum_congr rfl
      intro r _
      exact (hfiber r).symm
    _ = ∑' n : ℤ, b n := sum_intResidueTsum (q := q) b hb
    _ = intFourierTsum (q := q) a k := rfl

/-- A residue-class sum is the normalized inverse discrete Fourier transform of the
bilateral Fourier sums. -/
theorem intResidueTsum_eq_dft_average (a : ℤ → E) (ha : Summable a) (r : ZMod q) :
    intResidueTsum (q := q) a r =
      (q : ℂ)⁻¹ • ∑ k : ZMod q,
        ZMod.stdAddChar (k * r) • intFourierTsum (q := q) a k := by
  calc
    intResidueTsum (q := q) a r =
        (ZMod.dft (N := q) (E := E)).symm
          (ZMod.dft (intResidueTsum (q := q) a)) r := by
      rw [LinearEquiv.symm_apply_apply]
    _ = (q : ℂ)⁻¹ • ∑ k : ZMod q,
        ZMod.stdAddChar (k * r) •
          ZMod.dft (intResidueTsum (q := q) a) k :=
      ZMod.invDFT_apply _ _
    _ = (q : ℂ)⁻¹ • ∑ k : ZMod q,
        ZMod.stdAddChar (k * r) • intFourierTsum (q := q) a k := by
      rw [dft_intResidueTsum (q := q) a ha]

end FourierSums

end Fabius
