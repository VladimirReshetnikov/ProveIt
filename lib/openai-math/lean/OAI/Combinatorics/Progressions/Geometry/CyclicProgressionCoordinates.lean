import OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression

namespace OAI

section

open scoped BigOperators

namespace Erdos3.BohrProgression

namespace CyclicCenteredGAP

variable {N : ℕ}

def minParam (Q : CyclicCenteredGAP N) : Q.Param := fun _ => 0

def unitParam (Q : CyclicCenteredGAP N) (i : Fin Q.rank)
    (hi : 0 < Q.radius i) : Q.Param := fun j =>
  if hji : j = i then ⟨1, by subst j; omega⟩ else 0

def predParam (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) : Q.Param := fun j =>
  if hji : j = i then
    ⟨(x i : ℕ) - 1, by
      subst j
      have hx := (x i).isLt
      omega⟩
  else x j

@[simp] lemma minParam_apply (Q : CyclicCenteredGAP N) (i : Fin Q.rank) :
    (Q.minParam i : ℕ) = 0 := rfl

@[simp] lemma unitParam_apply_self (Q : CyclicCenteredGAP N)
    (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    (Q.unitParam i hi i : ℕ) = 1 := by
  simp [unitParam]

@[simp] lemma unitParam_apply_ne (Q : CyclicCenteredGAP N)
    (i j : Fin Q.rank) (hi : 0 < Q.radius i) (hji : j ≠ i) :
    (Q.unitParam i hi j : ℕ) = 0 := by
  simp [unitParam, hji]

@[simp] lemma predParam_apply_self (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (Q.predParam x i hi i : ℕ) = (x i : ℕ) - 1 := by
  simp [predParam]

@[simp] lemma predParam_apply_ne (Q : CyclicCenteredGAP N)
    (x : Q.Param) (i j : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hji : j ≠ i) :
    (Q.predParam x i hi j : ℕ) = x j := by
  simp [predParam, hji]

lemma eval_eq_eval_minParam_add_sum {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param) :
    Q.eval x = Q.eval Q.minParam +
      ∑ i, (x i : ZMod N) * Q.step i := by
  simp only [eval, coeff, minParam, Fin.val_zero,
    Nat.cast_zero, Int.cast_sub, Int.cast_natCast,
    zero_sub]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Int.cast_neg, Int.cast_natCast]
  ring

lemma eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (i : Fin Q.rank) (hi : 0 < Q.radius i) :
    Q.eval (Q.unitParam i hi) = Q.eval Q.minParam + Q.step i := by
  rw [Q.eval_eq_eval_minParam_add_sum]
  congr 1
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  simp only [unitParam_apply_self, Nat.cast_one, one_mul]
  have hzero : ∑ j ∈ Finset.univ.erase i,
      ((Q.unitParam i hi j : ℕ) : ZMod N) * Q.step j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hji : j ≠ i := by
      exact Finset.ne_of_mem_erase hj
    simp [Q.unitParam_apply_ne i j hi hji]
  rw [hzero, zero_add]

lemma eval_predParam_add_eval_unitParam {N : ℕ} [NeZero N]
    (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ))
    (hradius : 0 < Q.radius i) :
    Q.eval (Q.predParam x i hi) + Q.eval (Q.unitParam i hradius) =
      Q.eval x + Q.eval Q.minParam := by
  have hpred := Q.eval_eq_eval_minParam_add_sum (Q.predParam x i hi)
  have hunit := Q.eval_unitParam i hradius
  have hx := Q.eval_eq_eval_minParam_add_sum x
  rw [hpred, hunit, hx]
  have hsum :
      (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          Q.step i =
        ∑ j, (x j : ZMod N) * Q.step j := by
    rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.sum_erase_add (Finset.univ)
      (fun j => (x j : ZMod N) * Q.step j) (Finset.mem_univ i)]
    have hrest : ∑ j ∈ Finset.univ.erase i,
        ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j =
      ∑ j ∈ Finset.univ.erase i, (x j : ZMod N) * Q.step j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      rw [Q.predParam_apply_ne x i j hi hji]
    rw [hrest, Q.predParam_apply_self]
    have hxi : (x i : ℕ) - 1 + 1 = x i := Nat.sub_add_cancel hi
    rw [← hxi]
    push_cast
    ring
  calc
    Q.eval Q.minParam +
          (∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
          (Q.eval Q.minParam + Q.step i) =
        Q.eval Q.minParam + Q.eval Q.minParam +
          ((∑ j, ((Q.predParam x i hi j : ℕ) : ZMod N) * Q.step j) +
            Q.step i) := by abel
    _ = Q.eval Q.minParam + Q.eval Q.minParam +
          ∑ j, (x j : ZMod N) * Q.step j := by rw [hsum]
    _ = Q.eval Q.minParam + (∑ j, (x j : ZMod N) * Q.step j) +
          Q.eval Q.minParam := by abel

lemma sum_predParam_add_one (Q : CyclicCenteredGAP N) (x : Q.Param)
    (i : Fin Q.rank) (hi : 0 < (x i : ℕ)) :
    (∑ j, (Q.predParam x i hi j : ℕ)) + 1 = ∑ j, (x j : ℕ) := by
  rw [← Finset.sum_erase_add (Finset.univ) _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ)
    (fun j => (x j : ℕ)) (Finset.mem_univ i)]
  have hrest : ∑ j ∈ Finset.univ.erase i,
      (Q.predParam x i hi j : ℕ) =
        ∑ j ∈ Finset.univ.erase i, (x j : ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Q.predParam_apply_ne x i j hi (Finset.ne_of_mem_erase hj)
  rw [hrest, Q.predParam_apply_self]
  omega

end CyclicCenteredGAP

end Erdos3.BohrProgression

end

end OAI
