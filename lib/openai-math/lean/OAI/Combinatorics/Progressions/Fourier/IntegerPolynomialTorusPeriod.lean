import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Instances.AddCircle.Real

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem integerPolynomial_eval_zmod_eq {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((eval x P : ℤ) : ZMod q) = ((eval y P : ℤ) : ZMod q) := by
  change (Int.castRingHom (ZMod q)) (eval x P) = (Int.castRingHom (ZMod q)) (eval y P)
  rw [MvPolynomial.map_eval, MvPolynomial.map_eval]
  exact congrArg (fun z => eval z (MvPolynomial.map (Int.castRingHom (ZMod q)) P)) (funext hxy)

theorem integerPolynomial_eval_sub_dvd {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    (q : ℤ) ∣ eval x P - eval y P := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  rw [Int.cast_sub, integerPolynomial_eval_zmod_eq P q x y hxy, sub_self]

theorem addCircle_int_div_eq_of_dvd_sub (q : ℕ) (a b : ℤ)
    (h : (q : ℤ) ∣ a - b) :
    (((a : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      (((b : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) := by
  by_cases hq : q = 0
  · simp [hq]
  · let : NeZero q := ⟨hq⟩
    have hab : (a : ZMod q) = (b : ZMod q) := by
      apply sub_eq_zero.mp
      rw [← Int.cast_sub]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr h
    simpa only [ZMod.toAddCircle_intCast] using congrArg ZMod.toAddCircle hab

theorem integerPolynomial_eval_addCircle_div_eq {K : Type*} (P : MvPolynomial K ℤ)
    (q : ℕ) (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((((eval x P : ℤ) : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) =
      ((((eval y P : ℤ) : ℝ) / q : ℝ) : AddCircle (1 : ℝ)) :=
  addCircle_int_div_eq_of_dvd_sub q _ _ (integerPolynomial_eval_sub_dvd P q x y hxy)

theorem integerPolynomial_eval_addCircle_div_eq_of_cover {K : Type*}
    (P : MvPolynomial K ℤ) (q d : ℕ) (hd : d ∣ q)
    (x y : K → ℤ) (hxy : ∀ k, (x k : ZMod q) = (y k : ZMod q)) :
    ((((eval x P : ℤ) : ℝ) / d : ℝ) : AddCircle (1 : ℝ)) =
      ((((eval y P : ℤ) : ℝ) / d : ℝ) : AddCircle (1 : ℝ)) := by
  apply addCircle_int_div_eq_of_dvd_sub
  exact (Int.natCast_dvd_natCast.mpr hd).trans (integerPolynomial_eval_sub_dvd P q x y hxy)

end Erdos3

end

end OAI
