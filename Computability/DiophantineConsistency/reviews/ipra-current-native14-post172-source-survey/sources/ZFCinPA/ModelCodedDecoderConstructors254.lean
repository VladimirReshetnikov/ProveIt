import ZFCinPA.ModelCodedDecoder254

/-!
Literal constructor equations for the all-internal C254 decoder. The source
constructors are written as their actual arithmetic expressions, so no second
encoding or additional cached constructor module is needed. The zero implication
alias is explicit; this module does not construct proofs of decoded formulas.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoder254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma cantor_zero_iff (a b : V) : cantor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    apply cantor_injective
    simpa only [cantor, triangle, zero_add, zero_mul, Arithmetic.zero_div] using h
  · rintro ⟨rfl,rfl⟩
    simp [cantor,triangle]

lemma impCode_zero_iff (a b : V) : 4*cantor a b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [cantor_zero_iff]

theorem decode_positive (code : V) (h : code ≠ 0) :
    decode code =
      if code%4 = 0 then
        imp ℒₛₑₜ (decode (first (code/4))) (decode (second (code/4)))
      else if code%4 = 1 then atomCode 1 (first (code/4)) (second (code/4))
      else if code%4 = 2 then namedAll ℒₛₑₜ (first (code/4)) (decode (second (code/4)))
      else atomCode 0 (first (code/4)) (second (code/4)) := by
  rcases zero_or_succ code with rfl | ⟨raw,rfl⟩
  · exact (h rfl).elim
  · exact decode_succ raw

private lemma payload_tag (a b k : V) (hk : k < 4) :
    (4*cantor a b+k)/4 = cantor a b := div_mul_add' _ _ hk
private lemma remainder_tag (a b k : V) (hk : k < 4) :
    (4*cantor a b+k)%4 = k := by
  simpa only [mul_comm (4 : V)] using mod_mul_add_of_lt (cantor a b) 4 hk

theorem decode_imp (a b : V) (h : ¬(a = 0 ∧ b = 0)) :
    decode (4*cantor a b) = imp ℒₛₑₜ (decode a) (decode b) := by
  have hz : 4*cantor a b ≠ 0 := fun he => h ((impCode_zero_iff a b).mp he)
  rw [decode_positive _ hz]
  have hd : (4*cantor a b)/4 = cantor a b := by
    simpa only [add_zero] using payload_tag a b 0 (by simp)
  simp [hd]

theorem decode_imp_total (a b : V) :
    decode (4*cantor a b) =
      if a = 0 ∧ b = 0 then zeroFormula else imp ℒₛₑₜ (decode a) (decode b) := by
  classical
  by_cases h : a = 0 ∧ b = 0
  · rw [(impCode_zero_iff a b).mpr h,decode_zero,if_pos h]
  · rw [if_neg h]
    exact decode_imp a b h

theorem decode_mem (a b : V) :
    decode (4*cantor a b+1) = atomCode 1 a b := by
  rw [decode_positive _ (by simp)]
  have hk : (1 : V) < 4 := by simp
  rw [payload_tag a b 1 hk,remainder_tag a b 1 hk]
  simp

theorem decode_all (a b : V) :
    decode (4*cantor a b+2) = namedAll ℒₛₑₜ a (decode b) := by
  rw [decode_positive _ (by simp)]
  have hk : (2 : V) < 4 := by
    simpa only [Nat.cast_ofNat] using ((Nat.cast_lt (α := V)).mpr (by decide : (2 : Nat) < 4))
  rw [payload_tag a b 2 hk,remainder_tag a b 2 hk]
  simp

theorem decode_eq (a b : V) :
    decode (4*cantor a b+3) = atomCode 0 a b := by
  rw [decode_positive _ (by simp)]
  have hk : (3 : V) < 4 := by
    simpa only [Nat.cast_ofNat] using ((Nat.cast_lt (α := V)).mpr (by decide : (3 : Nat) < 4))
  rw [payload_tag a b 3 hk,remainder_tag a b 3 hk]
  simp

theorem decode_one : decode (1 : V) = atomCode 1 0 0 := by
  simpa only [cantor,triangle,zero_add,zero_mul,Arithmetic.zero_div,mul_zero] using decode_mem (0 : V) 0

end LeanProofs.ZFCinPA.ModelCodedDecoder254
