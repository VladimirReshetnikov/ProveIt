module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalSymbolicExec
public import PA196.Arithmetic.Machine.PAInternalCallAudit
public import PA196.RuntimeContracts
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.Symbolic
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
variable (n : V) (box : BoxSt → V → V)

/-- Concrete oracle suppliers are required only for the finite audited alphabet. -/
def AllowedOracle (allowed : Nat → BoxSt → Bool) (br : Branch) : Prop :=
  ∀ q x l, allowed q x=true → ∀ q' x' extra,
    Runtime.oracle q br x=some (q',x',extra) →
    Progress false (config n box denseControl (q,false,l,[.box x]))
      (config n box denseControl (q',true,(if extra then .bit true::l else l),[.box x']))

theorem local_audit_sound (allowed : Nat → BoxSt → Bool) (br : Branch) (s : SConf)
    (ho : AllowedOracle n box allowed br) (hh : ∀ x,∃ t : V,box x 0=(1+1)*t)
    (ha : InternalCallAudit.localAllowed allowed br s=true) :
    OracleAt n box br s ∧ HeadAt box s := by
  constructor
  · intro q l x he q' x' extra hor
    subst s
    have ha' : allowed q x=true := by
      simpa only [InternalCallAudit.localAllowed,hor] using ha
    exact ho q x l ha' q' x' extra hor
  · intro q l x he
    exact hh x

theorem audit_sound (allowed : Nat → BoxSt → Bool) (br : Branch) (tgt : SConf → Bool)
    (ho : AllowedOracle n box allowed br) (hh : ∀ x,∃ t : V,box x 0=(1+1)*t) :
    ∀ f s moved, InternalCallAudit.check allowed br tgt f s moved=true →
      ExecSafe n box br tgt f s moved := by
  intro f
  induction f with
  | zero => intro s moved ha; trivial
  | succ f ih =>
    intro s moved ha
    simp only [InternalCallAudit.check] at ha
    unfold ExecSafe
    by_cases ht : (moved && tgt s)=true
    · simp only [if_pos ht]
    · rw [if_neg ht] at ha ⊢
      cases hstep : Runtime.sstep NativeTable.machine br s with
      | none => trivial
      | some pair =>
        rcases pair with ⟨s',m⟩
        simp only [hstep,Bool.and_eq_true] at ha
        have hlocal := local_audit_sound n box allowed br s ho hh ha.1
        exact ⟨hlocal.1,hlocal.2,ih s' (moved || m) ha.2⟩

/-- Existing certificate result plus proved arithmetic box obligations yields
an all-model positive segment. Neither Boolean result supplies box semantics. -/
theorem contract_sound (fuel : Nat) (c : PA196.RuntimeContracts.Contract)
    (hc : PA196.RuntimeContracts.check fuel c=true)
    (hs : ExecSafe n box c.branch (fun s => Runtime.sMatches s c.target) fuel c.initial false) :
    Progress true (config n box denseControl c.initial) (config n box denseControl c.target) := by
  unfold PA196.RuntimeContracts.check at hc
  cases he : Runtime.exec NativeTable.machine c.branch (fun s => Runtime.sMatches s c.target)
      fuel c.initial false with
  | none => simp [he] at hc
  | some last =>
    have h := exec_sound n box c.branch (fun s => Runtime.sMatches s c.target)
      fuel c.initial false last he hs
    have hm := matches_config n box denseControl last c.target h.1
    simpa only [Bool.not_false,hm] using h.2
end Models
#print axioms audit_sound
#print axioms contract_sound
end PA196.Arithmetic.Machine.PA.InternalTrace.Symbolic

