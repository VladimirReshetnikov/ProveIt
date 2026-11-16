module
public import M6PA.Theory
public import M6PA.Calibration.RelationalParameterClosure
public import M6PA.Calibration.RelationalSourceND
@[expose] public section

/-! Iterated actual-basis generalization of an already fully supplied theorem.
No open ND premise is generalized. Allocated labels and the depth-dependent
allocator are explicit, for later guarded source parameter closure. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND

/-- Repeatedly close free parameter zero; old names are shifted at each step. -/
def closeParameters : Nat → Form → Form
  | 0,p => p
  | n+1,p => closeParameter (closeParameters n p)

def closureLabels : Nat → (Nat → Nat) → Nat → (Nat → Nat)
  | 0,f,_ => f
  | n+1,f,lo => closureLabels n (shiftedLabels f lo) (lo+1)

theorem closureLabels_bound (n : Nat) (f : Nat → Nat) (lo : Nat)
    (hf : ∀ i,f i<lo) : ∀ i,closureLabels n f lo i<lo+n := by
  induction n generalizing f lo with
  | zero => exact hf
  | succ n ih =>
    have hs : ∀ i,shiftedLabels f lo i<lo+1 := by
      intro i
      cases i with
      | zero => simp [shiftedLabels]
      | succ i => simpa only [shiftedLabels,Nat.cases_succ] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
    intro i
    have hh := ih (shiftedLabels f lo) (lo+1) hs i
    simpa only [closureLabels,Nat.add_assoc,Nat.add_comm 1 n] using hh

def closeParametersSupplier (n : Nat) (p : Form) (f : Nat → Nat) (lo z : Nat)
    (d : NativeCalculus.ActualBasis.Proof (code p (closureLabels n f lo) (lo+n) z)) :
    NativeCalculus.ActualBasis.Proof (code (closeParameters n p) f lo z) := by
  induction n generalizing f lo with
  | zero => exact d
  | succ n ih =>
    apply closeParameterSupplier
    apply ih (shiftedLabels f lo) (lo+1)
    simpa only [closureLabels,Nat.add_assoc,Nat.add_comm 1 n] using d

#print axioms closureLabels_bound
#print axioms closeParametersSupplier
end M6.PA.ForwardRelational

