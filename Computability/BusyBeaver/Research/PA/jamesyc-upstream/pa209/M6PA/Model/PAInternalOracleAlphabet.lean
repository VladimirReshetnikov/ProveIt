module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalCallAudit
@[expose] public section
namespace M6.Arithmetic.InternalOracleAlphabet
open M6.Runtime
/-- Finite native oracle call alphabet, independent of branch guards or any
particular certificate. The mark index is always below9. -/
def allowed (q : Nat) : BoxSt → Bool
  | .plain .none => skList.contains q
  | .mark r => decide (r<9) && (q == 64 || q == 0)
  | _ => false

theorem oracle_covered {q q' : Nat} {br : Branch} {x x' : BoxSt} {extra : Bool}
    (h : oracle q br x=some (q',x',extra)) : allowed q x=true := by
  cases x with
  | plain e =>
    cases e with
    | none =>
      cases hs : skipTarget q with
      | none => simp [oracle,hs] at h
      | some r =>
        obtain ⟨hq,hr⟩ := skipTarget_sk hs
        subst q
        have hall : ∀ r : Fin 9,sk r.val ∈ skList := by decide
        simpa [allowed] using hall ⟨r,hr⟩
    | inc r => simp [oracle] at h
    | dec r => simp [oracle] at h
  | mark r =>
    by_cases hr : r<9
    · by_cases h64 : q=64
      · simp [allowed,hr,h64]
      · by_cases h0 : q=0
        · simp [allowed,hr,h0]
        · simp [oracle,hr,h64,h0] at h
    · simp [oracle,hr] at h

theorem local_covered (br : Branch) (s : SConf) :
    InternalCallAudit.localAllowed allowed br s=true := by
  rcases s with ⟨q,onl,l,r⟩
  cases onl with
  | true => rfl
  | false =>
    cases r with
    | nil => rfl
    | cons x r =>
      cases x with
      | bit b => rfl
      | run b a c => rfl
      | box x =>
        cases r with
        | cons y r => rfl
        | nil =>
          cases ho : oracle q br x with
          | none => simp [InternalCallAudit.localAllowed,ho]
          | some p =>
            rcases p with ⟨q',x',extra⟩
            simpa only [InternalCallAudit.localAllowed,ho] using oracle_covered ho

/-- Every existing finite executor has an audit certificate for this alphabet;
no per-original recomputation or inference of machine execution is involved. -/
theorem audit_covered (br : Branch) (tgt : SConf → Bool) : ∀ f s moved,
    InternalCallAudit.check allowed br tgt f s moved=true := by
  intro f
  induction f with
  | zero => intro s moved; rfl
  | succ f ih =>
    intro s moved
    simp only [InternalCallAudit.check]
    split
    · rfl
    · cases hs : sstep M6.Arithmetic.NativeTable.machine br s with
      | none => rfl
      | some p =>
        rcases p with ⟨s',m⟩
        simp only [local_covered, Bool.true_and, ih]
#print axioms oracle_covered
#print axioms audit_covered
end M6.Arithmetic.InternalOracleAlphabet

