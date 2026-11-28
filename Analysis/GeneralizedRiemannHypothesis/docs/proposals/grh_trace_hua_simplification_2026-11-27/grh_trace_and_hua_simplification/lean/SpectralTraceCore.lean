import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact algebraic support for spectral trace interpolation

This file proves the finite interpolation and finite positive-moment transport
used by the proposed replacement of `LineDeterminant.lean`.

It does not import the GRH project and does not formalize the spectral
trace identity derived from `T * adjoint T = d * (1 + c * e)`.  The latter is
proved in the accompanying mathematical report; the final theorem here takes
its two polynomial trace identities as explicit hypotheses.
-/

noncomputable section

open Polynomial LinearMap

namespace SpectralTraceCore

/-- Values on a finite set not containing zero admit a polynomial interpolant
with zero constant term and degree at most the number of interpolation nodes. -/
theorem exists_interpolant_zero_constant {K : Type*} [Field K]
    (s : Finset K) (hs : (0 : K) ∉ s) (f : K → K) :
    ∃ p : K[X], p.coeff 0 = 0 ∧ p.natDegree ≤ s.card ∧
      ∀ x ∈ s, p.eval x = f x := by
  classical
  let g : K → K := fun x ↦ if x = 0 then 0 else f x
  let p : K[X] := Lagrange.interpolate (insert 0 s) id g
  have hinj : Set.InjOn (id : K → K) (↑(insert 0 s) : Set K) :=
    Function.injective_id.injOn
  have heval (x : K) (hx : x ∈ insert 0 s) : p.eval x = g x :=
    Lagrange.eval_interpolate_at_node (v := id) g hinj hx
  refine ⟨p, ?_, ?_, ?_⟩
  · simpa [g, coeff_zero_eq_eval_zero] using heval 0 (Finset.mem_insert_self 0 s)
  · apply natDegree_le_of_degree_le
    simpa [p, Finset.card_insert_of_notMem hs] using
      (Lagrange.degree_interpolate_le (v := id) g hinj)
  · intro x hx
    have hx0 : x ≠ 0 := fun h ↦ hs (h ▸ hx)
    simpa [g, hx0] using heval x (Finset.mem_insert_of_mem hx)

/-- Positive moments through degree `N` determine any linear functional of a
polynomial of degree at most `N` with zero constant term. No moment of order
zero, no commutation, and no spectral assumption are required for this step. -/
theorem linear_aeval_eq_of_positive_moments
    {K R R' : Type*} [Field K] [Ring R] [Ring R'] [Algebra K R] [Algebra K R']
    (L : R →ₗ[K] K) (L' : R' →ₗ[K] K) (T : R) (T' : R') (p : K[X])
    {N : ℕ} (hp0 : p.coeff 0 = 0) (hdegree : p.natDegree ≤ N)
    (hmoment : ∀ i : ℕ, 1 ≤ i → i ≤ N → L (T ^ i) = L' (T' ^ i)) :
    L (aeval T p) = L' (aeval T' p) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_smul]
  by_cases hi0 : i = 0
  · simp [hi0, hp0]
  · rw [hmoment i (Nat.one_le_iff_ne_zero.mpr hi0)
      ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hdegree)]

/-- Specialization of finite positive-moment transport to the functional
`X ↦ trace (A * X)` on an endomorphism algebra. -/
theorem trace_mul_aeval_eq_of_positive_moments
    {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup V'] [Module K V'] [Module.Finite K V']
    (A T : Module.End K V) (A' T' : Module.End K V') (p : K[X])
    {N : ℕ} (hp0 : p.coeff 0 = 0) (hdegree : p.natDegree ≤ N)
    (hmoment : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      trace K V (A * T ^ i) = trace K V' (A' * T' ^ i)) :
    trace K V (A * aeval T p) = trace K V' (A' * aeval T' p) := by
  exact linear_aeval_eq_of_positive_moments
    ((trace K V).comp (LinearMap.mulLeft K A))
    ((trace K V').comp (LinearMap.mulLeft K A')) T T' p hp0 hdegree hmoment

/-- The scalar identity extracting an idempotent rank from the determinant
norm formula. In the application `u = |det T|^2`, `n = dim V`, and `r = rank e`. -/
theorem rank_from_determinant_norm {u d c : ℝ} {n r : ℕ}
    (hd : 0 < d) (hc : 0 < c)
    (hu : u = d ^ n * (1 + c) ^ r) :
    (Real.log u - n * Real.log d) / Real.log (1 + c) = r := by
  have hlog : Real.log (1 + c) ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  rw [hu, Real.log_mul (pow_ne_zero _ hd.ne') (pow_ne_zero _ (by positivity)),
    Real.log_pow, Real.log_pow]
  field_simp
  ring

/-- The final transfer, with the two spectral trace identities stated as
explicit certificates. This theorem makes the boundary of the formalized
part explicit; it does not assume or assert those certificates implicitly. -/
theorem trace_projector_eq_of_polynomial_certificates
    {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup V'] [Module K V'] [Module.Finite K V']
    (A T e : Module.End K V) (A' T' e' : Module.End K V') (p : K[X])
    {N : ℕ} (hp0 : p.coeff 0 = 0) (hdegree : p.natDegree ≤ N)
    (hcertificate : trace K V (A * e) = trace K V (A * aeval T p))
    (hcertificate' : trace K V' (A' * e') = trace K V' (A' * aeval T' p))
    (hmoment : ∀ i : ℕ, 1 ≤ i → i ≤ N →
      trace K V (A * T ^ i) = trace K V' (A' * T' ^ i)) :
    trace K V (A * e) = trace K V' (A' * e') := by
  exact hcertificate.trans ((trace_mul_aeval_eq_of_positive_moments
    A T A' T' p hp0 hdegree hmoment).trans hcertificate'.symm)

#print axioms exists_interpolant_zero_constant
#print axioms linear_aeval_eq_of_positive_moments
#print axioms trace_mul_aeval_eq_of_positive_moments
#print axioms rank_from_determinant_norm
#print axioms trace_projector_eq_of_polynomial_certificates

end SpectralTraceCore
