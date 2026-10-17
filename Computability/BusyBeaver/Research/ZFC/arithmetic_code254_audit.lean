import BusyBeaver.ZFC.ArithmeticCode254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.ArithmeticCode254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.cantor_polybound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.cantor_bounded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.pair_le_tagged
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.tagged_components
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.tagged_bounded
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.tagged_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wel_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.weq_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.tagged_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wel_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.weq_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.rho1_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.rho1_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.rho1Value_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.rho1Value_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.rho1_input_bounds
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.row3_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.row3_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeWim_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeWel_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeWal_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeWeq_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeRho1_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeRho1Value_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCode254.codeRow3_defined

section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (a b : V) : ArithmeticCantor.cantor a b ≤ (a+b)*(a+b+1)+b := cantor_polybound a b
example : Bounded₂ (ArithmeticCantor.cantor : V → V → V) := cantor_bounded
example : Bounded₃ (tagged : V → V → V → V) := tagged_bounded
example (k a b : V) : a ≤ tagged k a b ∧ b ≤ tagged k a b := tagged_components k a b
example (v : Fin 4 → V) : taggedDef.val.Evalb v ↔ v 0 = tagged (v 1) (v 2) (v 3) := tagged_defined.df v
example (v : Fin 3 → V) : wimDef.val.Evalb v ↔ v 0 = wim (v 1) (v 2) := wim_defined.df v
example (v : Fin 3 → V) : welDef.val.Evalb v ↔ v 0 = wel (v 1) (v 2) := wel_defined.df v
example (v : Fin 3 → V) : walDef.val.Evalb v ↔ v 0 = wal (v 1) (v 2) := wal_defined.df v
example (v : Fin 3 → V) : weqDef.val.Evalb v ↔ v 0 = weq (v 1) (v 2) := weq_defined.df v
example (v : Fin 3 → V) : rho1Def.val.Evalb v ↔ v 0 = rho1 (v 1) (v 2) := rho1_defined.df v
example (v : Fin 3 → V) : rho1ValueDef.val.Evalb v ↔ v 0 = rho1Value (v 1) (v 2) := rho1Value_defined.df v
example (v : Fin 2 → V) : row3Def.val.Evalb v ↔ v 0 = row3 (v 1) := row3_defined.df v
end Generic

example (a b : Nat) : wim a b = Code254.wim a b := wim_nat a b
example (a b : Nat) : wel a b = Code254.wel a b := wel_nat a b
example (a b : Nat) : wal a b = Code254.wal a b := wal_nat a b
example (a b : Nat) : weq a b = Code254.weq a b := weq_nat a b
example (a b : Nat) : rho1 a b = Code254.rho1 a b := rho1_nat a b
example (p : Nat) : row3 p = Code254.rho1 (SetTheory.Cantor.ofNat p).1 (SetTheory.Cantor.ofNat p).2 + 1 := row3_nat p
example (v : Fin 3 → Nat) : wimDef.val.Evalb v ↔ v 0 = Code254.wim (v 1) (v 2) := codeWim_defined.df v
example (v : Fin 3 → Nat) : welDef.val.Evalb v ↔ v 0 = Code254.wel (v 1) (v 2) := codeWel_defined.df v
example (v : Fin 3 → Nat) : walDef.val.Evalb v ↔ v 0 = Code254.wal (v 1) (v 2) := codeWal_defined.df v
example (v : Fin 3 → Nat) : weqDef.val.Evalb v ↔ v 0 = Code254.weq (v 1) (v 2) := codeWeq_defined.df v
example (v : Fin 3 → Nat) : rho1Def.val.Evalb v ↔ v 0 = Code254.rho1 (v 1) (v 2) := codeRho1_defined.df v
example (v : Fin 3 → Nat) : rho1ValueDef.val.Evalb v ↔ v 0 = Code254.rho1 (v 1) (v 2) + 1 := codeRho1Value_defined.df v
example (v : Fin 2 → Nat) : row3Def.val.Evalb v ↔ v 0 = Code254.rho1 (SetTheory.Cantor.ofNat (v 1)).1 (SetTheory.Cantor.ofNat (v 1)).2 + 1 := codeRow3_defined.df v
example : wim (0 : Nat) 0 = 0 := by rw [wim_nat]; rfl
example : row3 (0 : Nat) = Code254.rho1 0 0 + 1 := by rw [row3_nat]; rfl
