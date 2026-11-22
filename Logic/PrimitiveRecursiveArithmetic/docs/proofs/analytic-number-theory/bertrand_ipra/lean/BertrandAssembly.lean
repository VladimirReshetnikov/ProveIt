import BertrandBounds
import BertrandValuation
import BertrandProducts
import Binomial

/-! The factor-product step and the connection to the bounded prime selector. -/
namespace Bertrand

/-- Prime-power contribution to the factorization of the middle coefficient. -/
def contribution (n p : Nat) := if primeB p then K n p else 1

/-- The central-binomial factorization, expressed with Legendre's carry sum. -/
def CentralFactorization : Prop :=
  ∀ n, Binomial.choose (2*n) n = prod (contribution n) (2*n)

private theorem primeFactor_pos (p : Nat) : 1 ≤ primeFactor p := by
  unfold primeFactor
  split
  · rename_i h
    have := ((primeB_spec p).mp h).1
    omega
  · decide

/-- Missing primes in the strict interval leave only the upper endpoint 2n-1
as a possible prime factor beyond n. -/
private theorem exceptional {n p : Nat} (hn : 4 ≤ n) (hp : Prime p)
    (hl : n < p) (hu : p ≤ 2*n)
    (none : ∀ q, n < q → q < 2*n-2 → ¬ Prime q) : p = 2*n-1 := by
  have nol : ¬ p < 2*n-2 := fun h => none p hl h hp
  have ne_top : p ≠ 2*n := by
    rintro rfl
    exact hp.2 2 (by decide) (by omega) ⟨n,rfl⟩
  have ne_even : p ≠ 2*n-2 := by
    rintro rfl
    exact hp.2 2 (by decide) (by omega) ⟨n-1,by omega⟩
  omega

theorem gap_product {n : Nat} (hn : 722 ≤ n)
    (none : ∀ q, n < q → q < 2*n-2 → ¬ Prime q) :
    prod (contribution n) (2*n) ≤ (2*n)^(Bounds.root (2*n)+1)*primorial (2*n/3) := by
  let x := 2*n
  let s := Bounds.root x
  let m := x/3
  let small := fun p => if p ≤ s then x else 1
  let middle := fun p => if p ≤ m then primeFactor p else 1
  let last := fun p => if p = x-1 then x else 1
  have hx : 2 ≤ x := by dsimp [x]; omega
  have hs := Bounds.root_spec x
  have hsle : s ≤ x := by
    have pos : s = 0 ∨ 1 ≤ s := by omega
    rcases pos with h | h
    · omega
    · have q := Nat.mul_le_mul_left s h
      simp only [Nat.mul_one] at q
      exact Nat.le_trans q hs.1
  have hmle : m ≤ x := Nat.div_le_self _ _
  have A (p : Nat) : 1 ≤ small p := by dsimp [small]; split <;> omega
  have M (p : Nat) : 1 ≤ middle p := by dsimp [middle]; split; exact primeFactor_pos _; decide
  have Z (p : Nat) : 1 ≤ last p := by dsimp [last]; split <;> omega
  have unit (p : Nat) : 1 ≤ (small p * middle p) * last p :=
    Nat.mul_le_mul (Nat.mul_le_mul (A _) (M _)) (Z _)
  have pt (p : Nat) (_ : 1 ≤ p) (hu : p ≤ x) :
      contribution n p ≤ (small p * middle p) * last p := by
    by_cases prime : primeB p = true
    · have hp := (primeB_spec p).mp prime
      rw [contribution, if_pos prime]
      by_cases hsmall : p ≤ s
      · have h := K_le_two_mul (n := n) (by omega) hp.1
        have b := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl (small p)) (M p)) (Z p)
        simp only [Nat.mul_one] at b
        exact Nat.le_trans (show K n p ≤ small p by simpa [small,hsmall,x] using h) b
      · have p2 : x < p*p := Nat.lt_of_lt_of_le hs.2 (Nat.mul_le_mul (by omega : s+1 ≤ p) (by omega : s+1 ≤ p))
        by_cases hmid : p ≤ m
        · have b := Nat.mul_le_mul (Nat.mul_le_mul (A p) (Nat.le_refl (middle p))) (Z p)
          simp only [Nat.one_mul, Nat.mul_one] at b
          have mid : middle p = p := by simp [middle,hmid,primeFactor,prime]
          exact Nat.le_trans (K_le_base hp.1 p2) (Nat.le_trans (Nat.le_of_eq mid.symm) b)
        · by_cases inN : p ≤ n
          · rw [K_eq_one hp.1 p2 (by omega : m < p) inN]
            exact unit _
          · have eq := exceptional (n := n) (by omega) hp (by omega) hu none
            have b := Nat.mul_le_mul (Nat.mul_le_mul (A p) (M p)) (Nat.le_refl (last p))
            simp only [Nat.one_mul] at b
            have ep : last p = x := if_pos eq
            exact Nat.le_trans (K_le_two_mul (hn := by omega) hp.1) (Nat.le_trans (Nat.le_of_eq ep.symm) b)
    · simpa only [contribution, if_neg prime] using unit p
  have total := prod_mono x pt
  rw [prod_mul, prod_mul] at total
  have ca : prod small x = x^s := (prod_cut (fun _ => x) hsle).trans (prod_const x s)
  have cb : prod middle x = primorial m := prod_cut primeFactor hmle
  have cc : prod last x = x := prod_single x (j := x-1) (by omega) (by omega)
  rw [ca,cb,cc] at total
  change _ ≤ x^(s+1)*primorial m
  rw [Nat.pow_succ]
  have perm : (x^s*primorial m)*x = (x^s*x)*primorial m := by ac_rfl
  exact perm ▸ total

theorem no_gap_of_factorization (fac : CentralFactorization)
    (prim : ∀ m, primorial m ≤ 4^m) : NoLargeGap := by
  intro n hn none
  have pr := gap_product hn none
  rw [← fac n] at pr
  exact Bounds.root_squeeze hn (Binomial.central_lower n)
    (Nat.le_trans pr (Nat.mul_le_mul_left _ (prim _)))

end Bertrand
