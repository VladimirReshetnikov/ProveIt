import ConPAMachine

/-! Transport fixed finite arithmetic Turing machine runs into IΣ₁ models. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ConPA.Machine
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem castDivTwo (n : Nat) : (((n / 2 : Nat) : V)) = (n : V) / 2 := by
  have h : ((n % 2 : Nat) : V) < 2 := by exact_mod_cast Nat.mod_lt n (by decide : 0 < 2)
  have e : (2 : V) * ((n / 2 : Nat) : V) + ((n % 2 : Nat) : V) = (n : V) := by
    exact_mod_cast Nat.div_add_mod n 2
  rw [← div_mul_add' ((n / 2 : Nat) : V) 2 h, e]

theorem castModTwo (n : Nat) : (((n % 2 : Nat) : V)) = (n : V) % 2 := by
  have h : ((n % 2 : Nat) : V) < 2 := by exact_mod_cast Nat.mod_lt n (by decide : 0 < 2)
  have e : ((n / 2 : Nat) : V) * (2 : V) + ((n % 2 : Nat) : V) = (n : V) := by
    exact_mod_cast Nat.div_add_mod' n 2
  rw [← mod_mul_add_of_lt ((n / 2 : Nat) : V) 2 h, e]

end models

abbrev PackedConf := Nat × Nat × Nat

/-- Computable output of a row on the binary tape halves. -/
def packedOut (ρ : Row) (l r : Nat) : PackedConf :=
  if ρ.right then (ρ.q',2*l+ρ.w,r/2)
  else (ρ.q',l/2,4*(r/2)+2*ρ.w+l%2)

/-- Computable table scan, preserving the priority of the first matching row. -/
def packedStep : Table → PackedConf → PackedConf
  | [], c => c
  | ρ :: T, c =>
    if c.1 = ρ.q ∧ c.2.2 % 2 = ρ.b then packedOut ρ c.2.1 c.2.2
    else packedStep T c

def packedRunFrom (T : Table) (c : PackedConf) (n : Nat) : PackedConf :=
  Nat.rec c (fun _ current => packedStep T current) n

def packedRun (T : Table) (n : Nat) : PackedConf := packedRunFrom T (0,0,0) n

/-- Fixed finite computations can be certified in consecutive chunks. -/
theorem packedRunFrom_add (T : Table) (c : PackedConf) (a b : Nat) :
    packedRunFrom T c (a+b) = packedRunFrom T (packedRunFrom T c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [Nat.add_succ]
    change packedStep T (packedRunFrom T c (a+b)) =
      packedStep T (packedRunFrom T (packedRunFrom T c a) b)
    rw [ih]

/-- Square pairing in the same order as the arithmetic configuration. -/
def packedCode (c : PackedConf) : Nat := Nat.pair c.1 (Nat.pair c.2.1 c.2.2)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem packedCode_cast (c : PackedConf) :
    (packedCode c : V) = ⟪(c.1 : V),(c.2.1 : V),(c.2.2 : V)⟫ := by
  simp [packedCode,coe_pair_eq_pair_coe]

theorem packedOut_correct (ρ : Row) (l r : Nat) :
    (packedCode (packedOut ρ l r) : V) = out (V := V) ρ (l : V) (r : V) := by
  simp only [packedOut,out]
  split <;> simp only [packedCode_cast,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,castDivTwo,castModTwo]

theorem packedStep_correct (T : Table) (c : PackedConf) :
    step (V := V) T (packedCode c : V) = (packedCode (packedStep T c) : V) := by
  induction T with
  | nil => rfl
  | cons ρ T ih =>
    simp only [step,packedCode_cast,pi₁_pair,pi₂_pair,←castModTwo,Nat.cast_inj,packedStep]
    split <;> simp_all [←packedCode_cast,packedOut_correct]

/-- A certified computation of the packed natural executor lifts directly to
the generic model run. -/
theorem packedRun_correct (T : Table) (n : Nat) :
    run (V := V) T (n : V) = (packedCode (packedRun T n) : V) := by
  induction n with
  | zero => simp [packedRun,packedRunFrom,packedCode,Nat.pair]
  | succ n ih => rw [Nat.cast_succ,run_succ,ih,packedStep_correct]; rfl

/-- Every standard clock lifts from the generic natural-number run. -/
theorem runNatCast (T : Table) (n : Nat) :
    run (V := V) T (n : V) = (run (V := Nat) T n : V) := by
  have hn : run (V := Nat) T n = packedCode (packedRun T n) := by
    simpa using packedRun_correct (V := Nat) T n
  rw [packedRun_correct,hn]

end models

#print axioms runNatCast
#print axioms packedRun_correct
end ConPA.Machine
