import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
Two algebraic steps in the proposed replacement for the deep-form weight bound.
The sample lemma is independent of the length of the ambient Frobenius cycle.
The specialization lemma works for target rings with nilpotents, such as a jet ring.
-/

namespace DeepFormSamples

open Polynomial

/-- Sampling twisted coefficients at a single element is injective if untwisting
sends the element to distinct interpolation nodes. -/
theorem twistedSamples_injective {K : Type*} [Field K] {r : ℕ}
    (twist : Fin r → K ≃+* K) (b : K)
    (hNodes : Function.Injective fun i => (twist i).symm b) :
    Function.Injective fun y : Fin r → K =>
      fun i : Fin r => ∑ a : Fin r, b ^ (a : ℕ) * twist i (y a) := by
  intro y z h
  have hdiff : (fun a => y a - z a) = (0 : Fin r → K) := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hNodes
    intro i
    have hrow := congrArg (fun v : Fin r → K => (twist i).symm (v i)) h
    simp only [map_sum, map_mul, map_pow, RingEquiv.symm_apply_apply] at hrow
    simpa only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hrow
  exact funext fun a => sub_eq_zero.mp (congrFun hdiff a)

/-- Specialization to a primitive field element and actual Frobenius automorphisms.
Choose h = 2*f, so p^h = P². Negative-index letters give precisely these
inverse samples on the residue field. The sample map is injective on the
entire perfect overfield as soon as all r sample values are available. -/
theorem inverseFrobeniusSamples_injective {K : Type*} [Field K] (p h r : ℕ)
    [ExpChar K p] [PerfectRing K p] (hbase : 3 ≤ p ^ h) (b : K)
    (hb : IsPrimitiveRoot b ((p ^ h) ^ r - 1)) :
    Function.Injective fun y : Fin r → K =>
      fun i : Fin r => ∑ a : Fin r, b ^ (a : ℕ) *
        (iterateFrobeniusEquiv K p (h * (i : ℕ))).symm (y a) := by
  apply twistedSamples_injective
  intro i j hij
  have hnodes : b ^ ((p ^ h) ^ (i : ℕ)) = b ^ ((p ^ h) ^ (j : ℕ)) := by
    simpa only [RingEquiv.symm_symm, iterateFrobeniusEquiv_def, pow_mul] using hij
  have hpos : 0 < p ^ h := by omega
  have hsmall (a : Fin r) : (p ^ h) ^ (a : ℕ) < (p ^ h) ^ r - 1 := by
    have hstep := Nat.pow_le_pow_right hpos (show (a : ℕ) + 1 ≤ r from a.isLt)
    rw [pow_succ] at hstep
    have hthree := Nat.mul_le_mul_left ((p ^ h) ^ (a : ℕ)) hbase
    have ha := pow_pos hpos (a : ℕ)
    omega
  exact Fin.ext (Nat.pow_right_injective (by omega : 1 < p ^ h)
    (hb.pow_inj (hsmall i) (hsmall j) hnodes))

/-- On expanding residue-field elements in a power basis, the spare coordinates
are the Vandermonde transform of the packed coefficient columns. -/
theorem gridBlock_apply {K : Type*} [Field K] {r h : ℕ}
    (b t : K) (embed : Fin h → K →+* K) (c : Fin r → Fin h → K)
    (fixed : ∀ s a i, embed s (c a i) = c a i) :
    (fun s : Fin h => ∑ a : Fin r, b ^ (a : ℕ) *
      embed s (∑ i : Fin h, c a i * t ^ (i : ℕ))) =
    (Matrix.vandermonde fun s => embed s t).mulVec
      (fun i => ∑ a : Fin r, b ^ (a : ℕ) * c a i) := by
  funext s
  simp only [map_sum, map_mul, map_pow, fixed, Matrix.mulVec, dotProduct,
    Matrix.vandermonde_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- For distinct conjugates this coordinate change is invertible over the
common overfield. -/
theorem gridBlock_bijective {K : Type*} [Field K] {h : ℕ}
    (node : Fin h → K) (hn : Function.Injective node) :
    Function.Bijective (Matrix.vandermonde node).mulVec := by
  have hu : IsUnit (Matrix.vandermonde node) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hn).isUnit
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,
         Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

/-- In a one-parameter family the lowest nonzero coefficient specializes into
every prescribed kernel, even when the coefficient substitution depends on
the parameter. Here X is the deformation parameter. -/
theorem firstCoefficient_specializes {R S I : Type*} [CommRing R] [CommRing S]
    (p : R[X]) (hp : p ≠ 0) (test : I → R[X] →+* S[X])
    (fixes : ∀ i, test i X = X) (vanishes : ∀ i, test i p = 0) :
    ∃ d : ℕ, p.coeff d ≠ 0 ∧
      ∀ i, (test i (C (p.coeff d))).coeff 0 = 0 := by
  let d := p.natTrailingDegree
  refine ⟨d, coeff_natTrailingDegree_ne_zero.mpr hp, ?_⟩
  obtain ⟨g, hfactor⟩ : X ^ d ∣ p := X_pow_dvd_iff.mpr fun j hj =>
    by_contra fun hne => (not_lt_of_ge (natTrailingDegree_le_of_ne_zero hne)) hj
  have hc : p.coeff d = g.coeff 0 := by
    simp [hfactor, coeff_X_pow_mul']
  intro i
  have hz : test i g * X ^ d = 0 := by
    simpa only [hfactor, map_mul, map_pow, fixes i, mul_comm] using vanishes i
  have hg : test i g = 0 := mul_X_pow_eq_zero hz
  have hconstant := congrArg (fun u : R[X] => (test i u).coeff 0) (divX_mul_X_add g)
  simpa [hc, fixes i, hg] using hconstant

#print axioms twistedSamples_injective
#print axioms inverseFrobeniusSamples_injective
#print axioms gridBlock_apply
#print axioms gridBlock_bijective
#print axioms firstCoefficient_specializes

end DeepFormSamples
