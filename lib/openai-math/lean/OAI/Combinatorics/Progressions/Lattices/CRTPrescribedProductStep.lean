import Mathlib.Data.Nat.GCD.BigOperators
import OAI.Combinatorics.Progressions.Polynomial.CRTPolynomialInputAffineLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V : Type*} [Fintype L] [DecidableEq L]

def prescribedCRTCofactor (p e : L → ℕ) (l : L) : ℕ :=
  ∏ k ∈ Finset.univ.erase l, p k ^ e k

theorem prescribedCRTProductStep_eq (p e : L → ℕ) (l : L) :
    (∏ k, p k ^ e k) = p l ^ e l * prescribedCRTCofactor p e l := by
  exact (Finset.mul_prod_erase Finset.univ (fun k => p k ^ e k)
    (Finset.mem_univ l)).symm

theorem prescribedCRTCofactor_coprime (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) (l : L) :
    (prescribedCRTCofactor p e l).Coprime (p l ^ A l) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro k hk
  exact Nat.coprime_pow_primes (e k) (A l) (hp k) (hp l)
    (fun h => (Finset.mem_erase.mp hk).1 (hinj h))

def prescribedCRTCofactorUnit (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) (l : L) :
    (ZMod (p l ^ A l))ˣ :=
  ZMod.unitOfCoprime (prescribedCRTCofactor p e l)
    (prescribedCRTCofactor_coprime p A e hp hinj l)

@[simp] theorem prescribedCRTCofactorUnit_coe (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) (l : L) :
    (prescribedCRTCofactorUnit p A e hp hinj l : ZMod (p l ^ A l)) =
      prescribedCRTCofactor p e l := rfl

theorem prescribedCRTCofactor_isUnit (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) (l : L) :
    IsUnit (prescribedCRTCofactor p e l : ZMod (p l ^ A l)) :=
  (prescribedCRTCofactorUnit p A e hp hinj l).isUnit

theorem prescribedCRTProductStep_cast (p A e : L → ℕ) (l : L) :
    ((∏ k, p k ^ e k : ℕ) : ZMod (p l ^ A l)) =
      (p l : ZMod (p l ^ A l)) ^ e l * prescribedCRTCofactor p e l := by
  rw [prescribedCRTProductStep_eq p e l, Nat.cast_mul, Nat.cast_pow]

def prescribedCRTProductStepEquiv (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p) :
    (∀ l, V → ZMod (p l ^ A l)) ≃+ (∀ l, V → ZMod (p l ^ A l)) where
  toFun x l v := prescribedCRTCofactorUnit p A e hp hinj l * x l v
  invFun x l v := ↑(prescribedCRTCofactorUnit p A e hp hinj l)⁻¹ * x l v
  left_inv x := by
    funext l v
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by
    funext l v
    simp only [← mul_assoc, Units.mul_inv, one_mul]
  map_add' x y := by
    funext l v
    exact mul_add _ _ _

@[simp] theorem prescribedCRTProductStepEquiv_apply (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (x : ∀ l, V → ZMod (p l ^ A l)) (l : L) (v : V) :
    prescribedCRTProductStepEquiv p A e hp hinj x l v =
      (prescribedCRTCofactor p e l : ZMod (p l ^ A l)) * x l v := rfl

theorem prescribedCRTProductStepEquiv_local_step (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (x : ∀ l, V → ZMod (p l ^ A l)) (l : L) (v : V) :
    (p l : ZMod (p l ^ A l)) ^ e l *
        prescribedCRTProductStepEquiv p A e hp hinj x l v =
      ((∏ k, p k ^ e k : ℕ) : ZMod (p l ^ A l)) * x l v := by
  rw [prescribedCRTProductStepEquiv_apply, prescribedCRTProductStep_cast, mul_assoc]

theorem prescribedCRTProductStepEquiv_symm_local_step (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (x : ∀ l, V → ZMod (p l ^ A l)) (l : L) (v : V) :
    (p l : ZMod (p l ^ A l)) ^ e l * x l v =
      ((∏ k, p k ^ e k : ℕ) : ZMod (p l ^ A l)) *
        (prescribedCRTProductStepEquiv p A e hp hinj).symm x l v := by
  simpa only [AddEquiv.apply_symm_apply] using
    prescribedCRTProductStepEquiv_local_step p A e hp hinj
      ((prescribedCRTProductStepEquiv p A e hp hinj).symm x) l v

theorem prescribedCRTPolynomialInput_product_step (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin x : ∀ l, V → ZMod (p l ^ A l)) (v : V) :
    prescribedCRTPolynomialInput p A e hq origin
        (prescribedCRTProductStepEquiv p A e hp hinj x) v =
      crtInput (fun l => p l ^ A l) hq origin v +
        (∏ l, p l ^ e l : ℕ) * crtInput (fun l => p l ^ A l) hq x v := by
  apply (ZMod.prodEquivPi (fun l => p l ^ A l) hq).injective
  funext l
  rw [ZMod.prodEquivPi_apply, ZMod.prodEquivPi_apply]
  simp only [prescribedCRTPolynomialInput, map_add, map_mul, map_natCast]
  rw [crtInput_reduce (fun l => p l ^ A l) hq _ l v,
    crtInput_reduce (fun l => p l ^ A l) hq origin l v,
    crtInput_reduce (fun l => p l ^ A l) hq x l v]
  exact congrArg (origin l v + ·)
    (prescribedCRTProductStepEquiv_local_step p A e hp hinj x l v)

theorem prescribedCRTPolynomialInput_product_step_symm (p A e : L → ℕ)
    (hp : ∀ l, (p l).Prime) (hinj : Function.Injective p)
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin x : ∀ l, V → ZMod (p l ^ A l)) (v : V) :
    prescribedCRTPolynomialInput p A e hq origin x v =
      crtInput (fun l => p l ^ A l) hq origin v +
        (∏ l, p l ^ e l : ℕ) * crtInput (fun l => p l ^ A l) hq
          ((prescribedCRTProductStepEquiv p A e hp hinj).symm x) v := by
  simpa only [AddEquiv.apply_symm_apply] using
    prescribedCRTPolynomialInput_product_step p A e hp hinj hq origin
      ((prescribedCRTProductStepEquiv p A e hp hinj).symm x) v

end Erdos3

end

end OAI
