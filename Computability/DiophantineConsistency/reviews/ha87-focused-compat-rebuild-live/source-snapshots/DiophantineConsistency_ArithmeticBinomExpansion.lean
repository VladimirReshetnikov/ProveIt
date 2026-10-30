import DiophantineConsistency.ArithmeticPow
import DiophantineConsistency.ArithmeticBinomPascal

/-! The internal binomial theorem `power (X+1) n = Σ_{k≤n} binom n k * power X k`
with a represented partial sum, and the central split used by the half-binomial
argument:
`power (X+1) (2r) = Q * power X r + v`, `Q = binom (2r) r + X*w`,
`X * v ≤ 2^(2r) * power X r`. All quantities are internal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinomExpansion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPow ArithmeticBinomPascal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def zeroDef : 𝚺₁.Semisentence 3 := .mkSigma “out X n. out=0”
def succDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out previous index X n. ∃ b, !binomDef b n index ∧ ∃ p, !powerDef p X index ∧ out=previous+b*p”
def blueprint : PR.Blueprint 2 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero _ := 0
  succ parameters index previous :=
    previous+binom (parameters 1) index*power (parameters 0) index
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]

/-- `bsum X n j = Σ_{k<j} binom n k * power X k`. -/
noncomputable def bsum (X n j : V) : V := construction.result ![X,n] j
def bsumDef : 𝚺₁.Semisentence 4 := blueprint.resultDef |>.rew (Rew.subst ![#0,#3,#1,#2])
instance bsum_defined : 𝚺₁-Function₃[V] bsum via bsumDef := .mk fun v ↦ by
  simp [construction.result_defined_iff,bsumDef,bsum]
instance bsum_definable : 𝚺₁-Function₃[V] bsum := bsum_defined.to_definable

@[simp] theorem bsum_zero (X n : V) : bsum X n 0=0 := by simp [bsum,construction]
theorem bsum_succ (X n j : V) : bsum X n (j+1)=bsum X n j+binom n j*power X j := by
  simp [bsum,construction]

private theorem bsum_one (X n : V) : bsum X n 1 = 1 := by
  simpa using bsum_succ X n 0

/-- Pascal's rule summed. -/
theorem pascal_sum (X n j : V) : bsum X (n+1) (j+1)=bsum X n (j+1)+X*bsum X n j := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [bsum_one]
  case succ j ih =>
    rw [bsum_succ X (n+1) (j+1),ih,binom_succ_succ,bsum_succ X n (j+1),bsum_succ X n j,
      power_succ]
    ring

theorem bsum_stable (X n m : V) : bsum X n (n+1+m)=bsum X n (n+1) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [←add_assoc,bsum_succ,ih,binom_eq_zero_of_lt n (n+1+m) (by
      exact lt_of_lt_of_le (by simp) (le_add_of_nonneg_right (by simp))),zero_mul,add_zero]

/-- The internal binomial theorem. -/
theorem binomial_theorem (X n : V) : power (X+1) n=bsum X n (n+1) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [bsum_one]
  case succ n ih =>
    have hs := bsum_stable X n 1
    rw [power_succ,ih,pascal_sum,hs]
    ring

/-- Row sum: `Σ_k binom n k = 2^n`. -/
theorem row_sum (n : V) : bsum 1 n (n+1)=Exp.exp n := by
  rw [←binomial_theorem,show (1:V)+1=2 by ring,power_two]

theorem bsum_mono (X n j m : V) : bsum X n j≤bsum X n (j+m) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ m ih =>
    rw [←add_assoc,bsum_succ]
    exact le_trans ih (le_add_of_nonneg_right (by simp))

theorem bsum_one_le (n j : V) : bsum 1 n j≤Exp.exp n := by
  rw [←row_sum]
  rcases le_or_gt j (n+1) with h|h
  · have := bsum_mono 1 n j (n+1-j)
    rwa [add_tsub_cancel_of_le h] at this
  · have h' : j=n+1+(j-(n+1)) := (add_tsub_cancel_of_le h.le).symm
    rw [h',bsum_stable]

/-- The low-degree sum bound `X * Σ_{k<j} … ≤ (Σ_{k<j} binom n k) * X^j`. -/
theorem bsum_scaled_le (X n j : V) (hX : 1≤X) : X*bsum X n j≤bsum 1 n j*power X j := by
  induction j using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ j ih =>
    rw [bsum_succ,bsum_succ,one_power,mul_one,power_succ]
    have hp : power X j≤X*power X j := by
      simpa using mul_le_mul_of_nonneg_right hX (by simp : (0:V)≤power X j)
    calc
      X*(bsum X n j+binom n j*power X j)=X*bsum X n j+binom n j*(X*power X j) := by ring
      _≤bsum 1 n j*(X*power X j)+binom n j*(X*power X j) :=
        add_le_add (le_trans ih (mul_le_mul_of_nonneg_left hp (by simp))) le_rfl
      _=(bsum 1 n j+binom n j)*(X*power X j) := by ring

/-- Splitting the sum at degree `r`. -/
theorem bsum_split (X n r m : V) :
    ∃ w, bsum X n (r+m+1)=bsum X n r+power X r*(binom n r+X*w) := by
  induction m using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,by rw [add_zero,bsum_succ]; ring⟩
  case succ m ih =>
    rcases ih with ⟨w,hw⟩
    refine ⟨w+binom n (r+m+1)*power X m,?_⟩
    rw [show r+(m+1)+1=(r+m+1)+1 by ring,bsum_succ,hw,show r+m+1=r+(m+1) by ring,
      power_add,power_succ]
    ring

/-- The central split of `(X+1)^(2r)` at degree `r`. -/
theorem central_split (X r : V) (hX : 1≤X) :
    ∃ v w, power (X+1) (2*r)=(binom (2*r) r+X*w)*power X r+v ∧
      X*v≤Exp.exp (2*r)*power X r := by
  rcases bsum_split X (2*r) r r with ⟨w,hw⟩
  refine ⟨bsum X (2*r) r,w,?_,?_⟩
  · rw [binomial_theorem,show 2*r+1=r+r+1 by ring,hw]
    ring
  · calc
      X*bsum X (2*r) r≤bsum 1 (2*r) r*power X r := bsum_scaled_le X (2*r) r hX
      _≤Exp.exp (2*r)*power X r := mul_le_mul_of_nonneg_right (bsum_one_le _ _) (by simp)

/-- The remainder is below `X^r` once `2^(2r) < X`. -/
theorem central_split_lt (X r : V) (hX : Exp.exp (2*r)<X) :
    ∃ v w, power (X+1) (2*r)=(binom (2*r) r+X*w)*power X r+v ∧ v<power X r := by
  have hX1 : 1≤X := le_trans (one_le_exp _) hX.le
  rcases central_split X r hX1 with ⟨v,w,he,hv⟩
  refine ⟨v,w,he,?_⟩
  have hpos : 0<power X r := power_pos X r (lt_of_lt_of_le (by simp) hX1)
  have h : X*v<X*power X r := lt_of_le_of_lt hv (mul_lt_mul_of_pos_right hX hpos)
  exact lt_of_mul_lt_mul_left h (by simp)

end DiophantineConsistency.ArithmeticBinomExpansion
