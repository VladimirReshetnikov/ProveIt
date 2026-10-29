import DiophantineConsistency.ArithmeticBinomPascal

/-! Represented factorial and odd product at arbitrary internal arguments.
Main facts: the factorial identity `binom (k+j) k * k! * j! = (k+j)!`
(a bounded-column induction on Pascal, no division) and the exact split
`(2n)! = 2^n * n! * (1*3*…*(2n-1))`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticBinomFactorial
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticBinomPascal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Factorial -/

namespace Fact
def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “out. out=1”
def succDef : 𝚺₁.Semisentence 3 := .mkSigma “out previous index. out=(index+1)*previous”
def blueprint : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero _ := 1
  succ _ index previous := (index+1)*previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]
end Fact

noncomputable def fact (n : V) : V := Fact.construction.result ![] n
def factDef : 𝚺₁.Semisentence 2 := Fact.blueprint.resultDef
instance fact_defined : 𝚺₁-Function₁[V] fact via factDef := Fact.construction.result_defined
instance fact_definable : 𝚺₁-Function₁[V] fact := fact_defined.to_definable

@[simp] theorem fact_zero : fact (0:V)=1 := by simp [fact,Fact.construction]
theorem fact_succ (n : V) : fact (n+1)=(n+1)*fact n := by
  simp [fact,Fact.construction]

theorem fact_pos (n : V) : 0<fact n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => rw [fact_succ]; exact mul_pos (by simp) ih

/-! ### Odd product `1*3*…*(2n-1)` -/

namespace OddProd
def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “out. out=1”
def succDef : 𝚺₁.Semisentence 3 := .mkSigma “out previous index. out=(2*index+1)*previous”
def blueprint : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero _ := 1
  succ _ index previous := (2*index+1)*previous
  zero_defined := .mk fun e => by simp [blueprint,zeroDef]
  succ_defined := .mk fun e => by simp [blueprint,succDef]
end OddProd

noncomputable def oddProd (n : V) : V := OddProd.construction.result ![] n
def oddProdDef : 𝚺₁.Semisentence 2 := OddProd.blueprint.resultDef
instance oddProd_defined : 𝚺₁-Function₁[V] oddProd via oddProdDef := OddProd.construction.result_defined
instance oddProd_definable : 𝚺₁-Function₁[V] oddProd := oddProd_defined.to_definable

@[simp] theorem oddProd_zero : oddProd (0:V)=1 := by simp [oddProd,OddProd.construction]
theorem oddProd_succ (n : V) : oddProd (n+1)=(2*n+1)*oddProd n := by
  simp [oddProd,OddProd.construction]

/-- Products of odd elements are odd. -/
theorem odd_mul {x y : V} (hx : ∃ a, x=2*a+1) (hy : ∃ b, y=2*b+1) : ∃ c, x*y=2*c+1 := by
  rcases hx with ⟨a,rfl⟩
  rcases hy with ⟨b,rfl⟩
  exact ⟨2*a*b+a+b,by ring⟩

theorem oddProd_odd (n : V) : ∃ z, oddProd n=2*z+1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0,by simp⟩
  case succ n ih => rw [oddProd_succ]; exact odd_mul ⟨n,rfl⟩ ih

/-- The exact split `(2n)! = 2^n * n! * oddProd n`. -/
theorem fact_double (n : V) : fact (2*n)=Exp.exp n*fact n*oddProd n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    have h2 : 2*(n+1)=(2*n+1)+1 := by ring
    rw [h2,fact_succ,fact_succ,ih,exp_succ,fact_succ,oddProd_succ]
    ring

/-! ### The factorial identity for represented binomials -/

private theorem bounded_factorial (n : V) :
    ∀ k ≤ n, ∀ j ≤ n, k+j=n → binom n k*fact k*fact j=fact n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro k hk j hj _
    have hk0 : k=0 := le_antisymm hk (by simp)
    have hj0 : j=0 := le_antisymm hj (by simp)
    simp [hk0,hj0]
  case succ n ih =>
    intro k _ j _ h
    rcases zero_or_succ k with rfl|⟨k,rfl⟩
    · rw [zero_add] at h
      subst h
      simp
    · have hkj : k+j=n := add_right_cancel (by rw [←h]; ring)
      have hkn : k≤n := by rw [←hkj]; exact le_add_of_nonneg_right (by simp)
      have hjn : j≤n := by rw [←hkj]; exact le_add_of_nonneg_left (by simp)
      have T1 : binom n k*fact (k+1)*fact j=(k+1)*fact n := by
        rw [fact_succ,←ih k hkn j hjn hkj]
        ring
      have T2 : binom n (k+1)*fact (k+1)*fact j=j*fact n := by
        rcases zero_or_succ j with rfl|⟨j,rfl⟩
        · rw [add_zero] at hkj
          subst hkj
          rw [binom_eq_zero_of_lt k (k+1) (by simp)]
          simp
        · have h' : (k+1)+j=n := by rw [←hkj]; ring
          have hk1 : k+1≤n := by rw [←h']; exact le_add_of_nonneg_right (by simp)
          have hj1 : j≤n := by rw [←h']; exact le_add_of_nonneg_left (by simp)
          rw [fact_succ j,←ih (k+1) hk1 j hj1 h']
          ring
      rw [binom_succ_succ,fact_succ n]
      calc
        (binom n k+binom n (k+1))*fact (k+1)*fact j=
            binom n k*fact (k+1)*fact j+binom n (k+1)*fact (k+1)*fact j := by ring
        _=(k+1)*fact n+j*fact n := by rw [T1,T2]
        _=(n+1)*fact n := by rw [←hkj]; ring

/-- `binom (k+j) k * k! * j! = (k+j)!` at arbitrary internal `k j`. -/
theorem binom_mul_fact (k j : V) : binom (k+j) k*fact k*fact j=fact (k+j) :=
  bounded_factorial (k+j) k (le_add_of_nonneg_right (by simp)) j
    (le_add_of_nonneg_left (by simp)) rfl

/-- The central case `binom (2r) r * r! * r! = (2r)!`. -/
theorem central_binom_mul_fact (r : V) : binom (2*r) r*fact r*fact r=fact (2*r) := by
  simpa only [←two_mul] using binom_mul_fact r r

end DiophantineConsistency.ArithmeticBinomFactorial
