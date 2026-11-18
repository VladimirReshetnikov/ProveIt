import IPRADerivations.Analysis.ComplexLogarithmRemainder

/-!
# Value equality for the actual signed-pair Gaussian arithmetic

Arithmetic support for the runtime root-product constructor. Gaussian values
are the existing pair of signed numerator pairs. Equality below is equality
of decoded Gaussian integer values, not equality of possibly noncanonical
raw codes. All ring identities are derived in ordinary iPRA through its
natural quotient/Grothendieck model, without a host integer-domain axiom.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im code add mul scale zeroCode oneCode eval_re_code eval_im_code normSq normSq_eval)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "ℜ" c:max => ZT.toZ Γ (re c)
local notation "ℑ" c:max => ZT.toZ Γ (im c)

def sub (a b : PTm n) : PTm n := add a (ComplexLogarithmRemainder.neg b)
def equal (a b : PTm n) : Fm PTm n := ZT.eq (re a) (re b) ⋏ ZT.eq (im a) (im b)

@[simp] theorem subst_sub {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (sub a b) = sub (Syn.subst σ a) (Syn.subst σ b) := by simp [sub]
@[simp] theorem subst_equal {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    (equal a b).subst σ = equal (Syn.subst σ a) (Syn.subst σ b) := by simp [equal]

theorem equal_of_values {a b : PTm n} (hr : ℜ a = ℜ b) (hi : ℑ a = ℑ b) : Γ ⊢[PRAAx] equal a b :=
  .andI (ZT.derive hr) (ZT.derive hi)
theorem equal_re {a b : PTm n} (h : Γ ⊢[PRAAx] equal a b) : ℜ a = ℜ b := ZT.toZ_eq (Prf.andE₁ h)
theorem equal_im {a b : PTm n} (h : Γ ⊢[PRAAx] equal a b) : ℑ a = ℑ b := ZT.toZ_eq (Prf.andE₂ h)

theorem values_of_code {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : (ℜ a = ℜ b) ∧ (ℑ a = ℑ b) := by
  constructor
  · simp only [re,ZT.toZ]
    rw [natEq (congrFst (congrFst h)),natEq (congrSnd (congrFst h))]
  · simp only [im,ZT.toZ]
    rw [natEq (congrFst (congrSnd h)),natEq (congrSnd (congrSnd h))]

theorem equal_of_code {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] equal a b :=
  equal_of_values (values_of_code h).1 (values_of_code h).2

theorem equal_refl (a : PTm n) : Γ ⊢[PRAAx] equal a a := equal_of_values rfl rfl
theorem equal_symm {a b : PTm n} (h : Γ ⊢[PRAAx] equal a b) : Γ ⊢[PRAAx] equal b a :=
  equal_of_values (equal_re h).symm (equal_im h).symm
theorem equal_trans {a b c : PTm n} (h : Γ ⊢[PRAAx] equal a b) (k : Γ ⊢[PRAAx] equal b c) : Γ ⊢[PRAAx] equal a c :=
  equal_of_values ((equal_re h).trans (equal_re k)) ((equal_im h).trans (equal_im k))

@[simp] theorem re_add (a b : PTm n) : ℜ (add a b) = ℜ a + ℜ b := by rw [add,eval_re_code,ZT.toZ_add]
@[simp] theorem im_add (a b : PTm n) : ℑ (add a b) = ℑ a + ℑ b := by rw [add,eval_im_code,ZT.toZ_add]
@[simp] theorem re_mul (a b : PTm n) : ℜ (mul a b) = ℜ a*ℜ b-ℑ a*ℑ b := by rw [mul,eval_re_code,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_mul]
@[simp] theorem im_mul (a b : PTm n) : ℑ (mul a b) = ℜ a*ℑ b+ℑ a*ℜ b := by rw [mul,eval_im_code,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_mul]
@[simp] theorem re_neg (a : PTm n) : ℜ (ComplexLogarithmRemainder.neg a) = -ℜ a := by rw [ComplexLogarithmRemainder.neg,eval_re_code,ZT.toZ_neg]
@[simp] theorem im_neg (a : PTm n) : ℑ (ComplexLogarithmRemainder.neg a) = -ℑ a := by rw [ComplexLogarithmRemainder.neg,eval_im_code,ZT.toZ_neg]
@[simp] theorem re_scale (c a : PTm n) : ℜ (scale c a) = Groth.ι (Q.mk Γ c)*ℜ a := by rw [scale,eval_re_code,ZT.toZ_mul,ZT.toZ_ofNat]
@[simp] theorem im_scale (c a : PTm n) : ℑ (scale c a) = Groth.ι (Q.mk Γ c)*ℑ a := by rw [scale,eval_im_code,ZT.toZ_mul,ZT.toZ_ofNat]
@[simp] theorem re_sub (a b : PTm n) : ℜ (sub a b) = ℜ a-ℜ b := by simp only [sub,re_add,re_neg]; ring
@[simp] theorem im_sub (a b : PTm n) : ℑ (sub a b) = ℑ a-ℑ b := by simp only [sub,im_add,im_neg]; ring
@[simp] theorem re_zero : ℜ (zeroCode : PTm n) = 0 := by rw [zeroCode,eval_re_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]
@[simp] theorem im_zero : ℑ (zeroCode : PTm n) = 0 := by rw [zeroCode,eval_im_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]
@[simp] theorem re_one : ℜ (oneCode : PTm n) = 1 := by rw [oneCode,eval_re_code,ZT.toZ_ofNat,Q.mk_one,map_one]
@[simp] theorem im_one : ℑ (oneCode : PTm n) = 0 := by rw [oneCode,eval_im_code,ZT.toZ_ofNat,Q.mk_zero,map_zero]

theorem add_equal {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] equal a a') (hb : Γ ⊢[PRAAx] equal b b') :
    Γ ⊢[PRAAx] equal (add a b) (add a' b') := by
  apply equal_of_values <;> simp only [re_add,im_add]
  · rw [equal_re ha,equal_re hb]
  · rw [equal_im ha,equal_im hb]

theorem mul_equal {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] equal a a') (hb : Γ ⊢[PRAAx] equal b b') :
    Γ ⊢[PRAAx] equal (mul a b) (mul a' b') := by
  apply equal_of_values <;> simp only [re_mul,im_mul]
  · rw [equal_re ha,equal_re hb,equal_im ha,equal_im hb]
  · rw [equal_re ha,equal_re hb,equal_im ha,equal_im hb]

theorem mul_zero (a : PTm n) : Γ ⊢[PRAAx] equal (mul a zeroCode) zeroCode := by
  apply equal_of_values <;> simp only [re_mul,im_mul,re_zero,im_zero] <;> ring

theorem zero_mul (a : PTm n) : Γ ⊢[PRAAx] equal (mul zeroCode a) zeroCode := by
  apply equal_of_values <;> simp only [re_mul,im_mul,re_zero,im_zero] <;> ring

theorem sub_self (a : PTm n) : Γ ⊢[PRAAx] equal (sub a a) zeroCode := by
  apply equal_of_values <;> simp only [re_sub,im_sub,re_zero,im_zero] <;> ring

theorem normSq_equal {a b : PTm n} (h : Γ ⊢[PRAAx] equal a b) : Γ ⊢[PRAAx] normSq a ≐ normSq b := by
  apply deriveNat
  rw [normSq_eval,normSq_eval,equal_re h,equal_im h]

end LeanProofs.IPRA.Analysis.GaussianRootAlgebra
