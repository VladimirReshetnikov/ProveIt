import BertrandAssembly
import BertrandFactorCount

namespace Bertrand

/-- Finite prime-power reconstruction for one positive integer. -/
def Reconstruction : Prop := ∀ {m M : Nat}, 1 ≤ m → m ≤ M → prod (atomFactor m M) M = m

private theorem floorSum_zero (p k : Nat) : floorSum 0 p k = 0 := by
  induction k <;> simp_all [floorSum]

theorem fact_expansion (recon : Reconstruction) (m M : Nat) (hM : m ≤ M) :
    prod (factFactor m M) M = Binomial.fac m := by
  induction m with
  | zero =>
    have h : factFactor 0 M = fun _ => 1 := by
      funext p
      simp [factFactor, floorSum_zero]
    rw [h, prod_one]
    rfl
  | succ m ih =>
    have h : factFactor (m+1) M = fun p => factFactor m M p * atomFactor (m+1) M p :=
      funext (factFactor_succ m M)
    rw [h, prod_mul, ih (by omega), recon (by omega) hM, Nat.mul_comm]
    rfl

theorem central_of_reconstruction (recon : Reconstruction) : CentralFactorization := by
  intro n
  let x := 2*n
  let half := factFactor n x
  have split : factFactor x x = fun p => (half p * half p) * contribution n p := by
    funext p
    by_cases h : primeB p = true
    · have pos := ((primeB_spec p).mp h).1
      dsimp only [x,half]
      simp only [factFactor, contribution, h, if_true, K]
      rw [floorSum_double n p (2*n) (by omega), Nat.pow_add, Nat.two_mul, Nat.pow_add]
    · simp [half, factFactor, contribution, h]
  have fx := fact_expansion recon x x (Nat.le_refl _)
  rw [split, prod_mul, prod_mul] at fx
  have fh : prod half x = Binomial.fac n := fact_expansion recon n x (by dsimp [x]; omega)
  rw [fh] at fx
  have cn := Binomial.factorial_choose n n
  rw [show n+n=x by dsimp [x]; omega] at cn
  apply Nat.mul_right_cancel (Nat.mul_pos (Binomial.fac_pos n) (Binomial.fac_pos n))
  exact cn.trans (by rw [← fx, Nat.mul_comm (prod (contribution n) x)])

end Bertrand
