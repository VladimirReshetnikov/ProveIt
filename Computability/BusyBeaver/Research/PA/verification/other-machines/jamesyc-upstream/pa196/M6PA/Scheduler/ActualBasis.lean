module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualRho7Recovery
@[expose] public section
open M6.Arithmetic.PA

/-! Finite proofs over the full literal actual AX basis. No historical
Derivation constructor is admitted. The smaller audited ActualCore embeds
by structural recursion, not by assuming the two full axiom bases equivalent. -/
namespace M6.PA.NativeCalculus.ActualBasis
open M6.Source

attribute [local irreducible] AXCode.rho1 AXCode.rho2 AXCode.rho4 AXCode.rho6 AXCode.rho8
  ActualAXCode.rho3 ActualAXCode.rho5 ActualAXCode.rho7 ActualAXCode.bundle
set_option maxHeartbeats 1000000 in
inductive Proof : Nat → Type where
  | mp {a b} : Proof a → Proof (wim a b) → Proof b
  | all (a) {b} : Proof b → Proof (wal a b)
  | r1 (a b) : Proof (ActualAXCode.rho1 a b)
  | r2 (a b c) : Proof (ActualAXCode.rho2 a b c)
  | r3 (a b c) : Proof (ActualAXCode.rho3 a b c)
  | r4 (a b c) : Proof (ActualAXCode.rho4 a b c)
  | r5 (a b c) : Proof (ActualAXCode.rho5 a b c)
  | r6 (a b) : Proof (ActualAXCode.rho6 a b)
  | r7 (a b c) : Proof (ActualAXCode.rho7 a b c)
  | r8 (a b c u) : u ≤ a → Proof (ActualAXCode.rho8 a b c u)
  | bundle (a b c) : c ≠ a → c ≠ b → Proof (ActualAXCode.bundle a b c)

def fromCore {a : Nat} : ActualCore.Proof a → Proof a
  | .mp p q => .mp (fromCore p) (fromCore q)
  | .all x p => .all x (fromCore p)
  | .r1 a b => (ActualCore.r1_eq_actual a b).symm ▸ .r1 a b
  | .r2 a b c => (ActualCore.r2_eq_actual a b c).symm ▸ .r2 a b c
  | .r6 a b => (ActualCore.r6_eq_actual a b).symm ▸ .r6 a b
  | .r7 a b c => (ActualCore.quantifiedR7_eq_actual a b c).symm ▸ .r7 a b c
  | .r8 a b c u h => (ActualCore.r8_eq_actual a b c u).symm ▸ .r8 a b c u h

#print axioms fromCore
end M6.PA.NativeCalculus.ActualBasis

