module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceSeparation
public import M6PA.Calibration.RelationalSourceLK
@[expose] public section

/-! Closing the first free parameter of an already supplied relational theorem.
This is actual-basis generalization, with the fresh label and shifted allocator
explicit. It does not erase a premise from an ND proof context. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def closeParameter (p : Proposition language) : Proposition language :=
  .all (Semiformula.rewAux Rew.fix p)

theorem toNamed_fixParameter (p : Proposition language) (f : Nat → Nat) (v lo : Nat) :
    toNamed (Semiformula.rewAux Rew.fix p) (Fin.cases v Fin.elim0) f lo =
      toNamed p Fin.elim0 (shiftedLabels f v) lo := by
  apply toNamed_rew
  intro t
  cases t with
  | bvar i => exact Fin.elim0 i
  | fvar i => cases i <;> rfl
  | func fn _ => nomatch fn

def closeParameterSupplier (p : Proposition language) (f : Nat → Nat) (lo z : Nat)
    (d : Proof (code p (shiftedLabels f lo) (lo+1) z)) :
    Proof (code (closeParameter p) f lo z) := by
  simpa only [code,closeParameter,toNamed,relationalCode,toNamed_fixParameter] using
    (Proof.all lo d)

def closedSeparationSupplier (p : Semiproposition language 1) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hz : lo+4+depth p ≤ z) :
    Proof (code (closeParameter (separationFormula p)) f lo z) := by
  apply closeParameterSupplier
  apply separationSupplier p (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega

#print axioms toNamed_fixParameter
#print axioms closeParameterSupplier
#print axioms closedSeparationSupplier
end M6.PA.RelationalSource

