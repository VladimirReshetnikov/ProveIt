module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6.Source.ActualAXCode
public import M6.Source.Enumeration
public import M6.Logic.NativeCalculus
@[expose] public section
open M6.Arithmetic.PA

/-! A NEW finite proof datatype for the actual-AX logical fragment used in
the reverse rho7 audit. There is NO historical rho7 or equality-vacuity leaf,
no arbitrary historical theorem import, and no guarded-bundle leaf at all.
Only actual R1/R2/R6/R8, actual quantified R7, MP and GEN are available. -/
namespace M6.PA.NativeCalculus.ActualCore

def quantifiedR7 (a b c : Nat) :=
  wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b)))

attribute [local irreducible] rho1 rho2 rho6 rho8 quantifiedR7
set_option maxHeartbeats 1000000 in
inductive Proof : Nat → Type where
  | mp {a b} : Proof a → Proof (wim a b) → Proof b
  | all (a) {b} : Proof b → Proof (wal a b)
  | r1 (a b) : Proof (rho1 a b)
  | r2 (a b c) : Proof (rho2 a b c)
  | r6 (a b) : Proof (rho6 a b)
  | r7 (a b c) : Proof (quantifiedR7 a b c)
  | r8 (a b c u) : u ≤ a → Proof (rho8 a b c u)

theorem quantifiedR7_eq_actual (a b c : Nat) :
    quantifiedR7 a b c = M6.Source.ActualAXCode.rho7 a b c := by
  simp only [quantifiedR7,M6.Source.ActualAXCode.rho7,
    M6.Source.AXCode.wim,M6.Source.AXCode.wal,M6.Source.AXCode.weq,M6.Source.AXCode.wel,
    wim,wal,weq,wel]

theorem r1_eq_actual (a b : Nat) : rho1 a b = M6.Source.ActualAXCode.rho1 a b := by
  simp only [rho1,M6.Source.ActualAXCode.rho1,M6.Source.AXCode.rho1,
    wex,M6.Source.AXCode.wex,wn,M6.Source.AXCode.wn,wal,M6.Source.AXCode.wal,
    wim,M6.Source.AXCode.wim,weq,M6.Source.AXCode.weq]

theorem r2_eq_actual (a b c : Nat) : rho2 a b c = M6.Source.ActualAXCode.rho2 a b c := by
  simp only [rho2,M6.Source.ActualAXCode.rho2,M6.Source.AXCode.rho2,
    wim,M6.Source.AXCode.wim,wal,M6.Source.AXCode.wal]

theorem r6_eq_actual (a b : Nat) : rho6 a b = M6.Source.ActualAXCode.rho6 a b := by
  simp only [rho6,M6.Source.ActualAXCode.rho6,M6.Source.AXCode.rho6,
    wex,M6.Source.AXCode.wex,wn,M6.Source.AXCode.wn,wal,M6.Source.AXCode.wal,
    wim,M6.Source.AXCode.wim]

theorem r8_eq_actual (a b c u : Nat) : rho8 a b c u = M6.Source.ActualAXCode.rho8 a b c u := by
  simp only [rho8,M6.Source.ActualAXCode.rho8,M6.Source.AXCode.rho8,wim,M6.Source.AXCode.wim]

#print axioms quantifiedR7_eq_actual
end M6.PA.NativeCalculus.ActualCore
