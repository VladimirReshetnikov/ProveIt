import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! A primitive qth root with q=m*p^(k+1) exposes the p part of its
cyclotomic derivative. The identity is unconditional in a commutative domain. -/

namespace VacuumFrame.Cyclotomic

open Polynomial

theorem expansion_quotient (R : Type*) [CommRing R] {m p : ℕ}
    (hp : p.Prime) (hm : ¬p ∣ m) (k : ℕ) :
    expand R (p^(k+1)) (cyclotomic m R) =
       cyclotomic (m*p^(k+1)) R * expand R (p^k) (cyclotomic m R) := by
  induction k with
  | zero =>
    simpa using cyclotomic_expand_eq_cyclotomic_mul hp hm R
  | succ k ih =>
    have h := congrArg (expand R p) ih
    have hdiv : p ∣ m*p^(k+1) :=
      (dvd_pow_self p (Nat.succ_ne_zero _)).trans (dvd_mul_left _ _)
    simp only [map_mul, expand_expand, cyclotomic_expand_eq_cyclotomic hp hdiv] at h
    rw [← pow_succ' p (k+1), ← pow_succ' p k, Nat.mul_assoc, ← pow_succ] at h
    exact h

theorem mixed_derivative {R : Type*} [CommRing R] [IsDomain R] {p m : ℕ}
    (hp : p.Prime) (hm : ¬p ∣ m) (hm₀ : 0 < m) (k : ℕ) {ζ : R}
    (hζ : IsPrimitiveRoot ζ (m*p^(k+1))) :
    (cyclotomic (m*p^(k+1)) R).derivative.eval ζ *
        (cyclotomic m R).eval (ζ^(p^k)) =
      (cyclotomic m R).derivative.eval (ζ^(p^(k+1))) *
        ((p^(k+1) : ℕ) * ζ^(p^(k+1)-1)) := by
  have hr : (cyclotomic (m*p^(k+1)) R).eval ζ = 0 :=
    hζ.isRoot_cyclotomic (Nat.mul_pos hm₀ (pow_pos hp.pos _))
  have h := congrArg (fun f : R[X] => f.derivative.eval ζ)
    (expansion_quotient R hp hm k)
  simpa only [derivative_mul, derivative_expand, eval_add, eval_mul,
    expand_eval, eval_natCast, eval_pow, eval_X, hr, zero_mul, add_zero] using h.symm

private theorem units_at_tame_root {R K : Type*} [CommRing R] [Field K]
    (π : R →+* K) (reflects : ∀ t, π t ≠ 0 → IsUnit t) {m : ℕ}
    {F G : R[X]} (hfac : X^m - 1 = F*G) {r : R}
    (hr : IsUnit r) (hm : (m : K) ≠ 0) (hF : π (F.eval r) = 0) :
    IsUnit (F.derivative.eval r) ∧ IsUnit (G.eval r) := by
  have hh := congrArg (fun f : R[X] => π (f.derivative.eval r)) hfac
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero,
    derivative_mul, eval_add, eval_mul, eval_X, eval_pow, eval_natCast,
    map_add, map_mul, map_natCast, map_pow, hF, zero_mul, add_zero] at hh
  have hnz : π (F.derivative.eval r) * π (G.eval r) ≠ 0 := by
    rw [← hh]
    exact mul_ne_zero hm (pow_ne_zero _ (hr.map π).ne_zero)
  exact ⟨reflects _ (left_ne_zero_of_mul hnz), reflects _ (right_ne_zero_of_mul hnz)⟩

/-- In a domain with a residue map reflecting units, the fused mixed-conductor
different identity. Hensel lifting, explicit residue roots and valuations are
unnecessary. Apply it to the valuation ring at the selected finite place. -/
theorem mixed_conductor_associated {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] (π : R →+* K) (reflects : ∀ t, π t ≠ 0 → IsUnit t)
    {p m : ℕ} (hp : p.Prime) [CharP K p] (hm : ¬p ∣ m) (hm₀ : 0 < m)
    (k : ℕ) {ζ : R} (hζ : IsPrimitiveRoot ζ (m*p^(k+1))) :
    Associated ((ζ^(m*p^k)-1) * (cyclotomic (m*p^(k+1)) R).derivative.eval ζ)
      (p^(k+1) : ℕ) := by
  let : Fact p.Prime := ⟨hp⟩
  let u : R := ζ^(p^k)
  let w : R := ζ^(p^(k+1))
  let F := cyclotomic m R
  let S := (cyclotomic (m*p^(k+1)) R).derivative.eval ζ
  have hP : 0 < p^(k+1) := pow_pos hp.pos _
  have hunit : IsUnit ζ := hζ.isUnit (Nat.mul_pos hm₀ hP).ne'
  have hwm : IsPrimitiveRoot w m := by
    simpa [w, Nat.mul_div_cancel _ hP] using
      hζ.pow_of_dvd hP.ne' (dvd_mul_left (p^(k+1)) m)
  have hFw : F.eval w = 0 := hwm.isRoot_cyclotomic hm₀
  have hup : u^p = w := by simp [u, w, ← pow_mul, pow_succ]
  have peval (b : R) : (cyclotomic m K).eval (π b) = π (F.eval b) := by
    simpa only [F, map_cyclotomic] using
      (eval_map_apply (p := cyclotomic m R) (f := π) b)
  have hfrob : (cyclotomic m K).eval ((π u)^p) =
      ((cyclotomic m K).eval (π u))^p := by
    simpa only [map_cyclotomic, frobenius_def] using
      (eval_map_apply (p := cyclotomic m K) (f := frobenius K p) (π u))
  have hFu : π (F.eval u) = 0 := by
    have hz : (π (F.eval u))^p = 0 := by
      rw [← peval, ← hfrob, ← map_pow, hup, peval, hFw, map_zero]
    exact (pow_eq_zero_iff (Nat.Prime.ne_zero hp)).mp hz
  obtain ⟨G, hfac⟩ := cyclotomic.dvd_X_pow_sub_one m R
  have hmK : (m : K) ≠ 0 := (CharP.cast_eq_zero_iff K p m).not.mpr hm
  have hGunit : IsUnit (G.eval u) :=
    (units_at_tame_root π reflects hfac (hunit.pow _) hmK hFu).2
  have hDunit : IsUnit (F.derivative.eval w) :=
    (units_at_tame_root π reflects hfac (hunit.pow _) hmK (by rw [hFw, map_zero])).1
  have hedge : ζ^(m*p^k)-1 = F.eval u * G.eval u := by
    have hf := congrArg (fun f : R[X] => f.eval u) hfac
    simpa only [u, F, eval_sub, eval_pow, eval_X, eval_one, eval_mul,
      ← pow_mul, Nat.mul_comm (p^k) m] using hf
  have hs : S * F.eval u = F.derivative.eval w *
      ((p^(k+1) : ℕ) * ζ^(p^(k+1)-1)) := mixed_derivative hp hm hm₀ k hζ
  change Associated ((ζ^(m*p^k)-1)*S) ((p^(k+1) : ℕ) : R)
  rw [hedge, show F.eval u * G.eval u * S = (S * F.eval u)*G.eval u by ac_rfl, hs]
  have hh := associated_mul_unit_left
    (F.derivative.eval w * ((p^(k+1) : ℕ) * ζ^(p^(k+1)-1))) _ hGunit
  exact hh.trans ((associated_unit_mul_left _ _ hDunit).trans
      (associated_mul_unit_left _ _ (hunit.pow _)))

/-- Instantiation with the canonical residue field: no unit-reflection
hypothesis remains in a local integral domain. -/
theorem local_different {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {p m : ℕ} (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p] (hm : ¬p ∣ m)
    (hm₀ : 0 < m) (k : ℕ) {ζ : R} (hζ : IsPrimitiveRoot ζ (m*p^(k+1))) :
    Associated ((ζ^(m*p^k)-1) * (cyclotomic (m*p^(k+1)) R).derivative.eval ζ)
      (p^(k+1) : ℕ) :=
  mixed_conductor_associated (IsLocalRing.residue R)
    (fun t => (IsLocalRing.residue_ne_zero_iff_isUnit t).mp) hp hm hm₀ k hζ

end VacuumFrame.Cyclotomic

#print axioms VacuumFrame.Cyclotomic.expansion_quotient
#print axioms VacuumFrame.Cyclotomic.mixed_derivative

#print axioms VacuumFrame.Cyclotomic.mixed_conductor_associated
#print axioms VacuumFrame.Cyclotomic.local_different
