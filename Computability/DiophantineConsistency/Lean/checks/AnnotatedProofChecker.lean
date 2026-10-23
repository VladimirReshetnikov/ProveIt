import DiophantineConsistency.AnnotatedProofChecker

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency
open DiophantineConsistency.AnnotatedProofChecker

/-- Empty, forged-assumption, forward-reference, wrong-arity and wrong-context
certificates all fail by reduction of the executable checker. -/
example : (Certificate.mk [] []).check fBot=false := by decide
example : (Certificate.mk [] [⟨.ass [] fBot,[]⟩]).check fBot=false := by decide
example : (Line.mk (.eqRefl [] 0) [0]).valid []=false := by decide
example : (Line.mk (.botE [] (fEq 0 0)) [0]).valid []=false := by decide
example : (Line.mk (.botE [] (fEq 0 0)) [1]).valid [⟨[],fBot⟩]=false := by decide
example : (Line.mk (.botE [] (fEq 0 0)) [0]).valid [⟨[fBot],fBot⟩]=false := by decide
example : (Line.mk (.botE [] (fEq 0 0)) [0,0]).valid [⟨[],fBot⟩]=false := by decide

/-- Repeated parents share an accepted line without copying its proof. -/
private def shared : Certificate := ⟨[],[
  ⟨.eqRefl [] 0,[]⟩,
  ⟨.andI [] (fEq 0 0) (fEq 0 0),[0,0]⟩]⟩
example : shared.check (fAnd (fEq 0 0) (fEq 0 0))=true := by decide
example : shared.check fBot=false := by decide

/-- Implication introduction checks the discharged context exactly. -/
private def identity : Certificate := ⟨[],[
  ⟨.ass [fBot] fBot,[]⟩,
  ⟨.impI [] fBot fBot,[0]⟩]⟩
example : identity.check (fImp fBot fBot)=true := by decide
example : (Line.mk (.impI [] fBot fBot) [0]).valid [⟨[],fBot⟩]=false := by decide

/-- The binder shift is part of the required judgment, not a trusted premise. -/
example : (Line.mk (.allI [fEq 0 0] (fEq 0 0)) [0]).valid
    [⟨[fEq 1 1],fEq 0 0⟩]=true := by decide
example : (Line.mk (.allI [fEq 0 0] (fEq 0 0)) [0]).valid
    [⟨[fEq 0 0],fEq 0 0⟩]=false := by decide

/-- Existential/equality instantiation is also computed from syntax. -/
example : (Line.mk (.exI [] (fEq 0 1) 3) [0]).valid
    [⟨[],fEq 3 0⟩]=true := by decide
example : (Line.mk (.exI [] (fEq 0 1) 3) [0]).valid
    [⟨[],fEq 0 3⟩]=false := by decide
example : (Line.mk (.eqElim [] 2 3 (fEq 0 1)) [0,1]).valid
    [⟨[],fEq 2 3⟩,⟨[],fEq 2 0⟩]=true := by decide
example : (Line.mk (.eqElim [] 2 3 (fEq 0 1)) [0,1]).valid
    [⟨[],fEq 2 3⟩,⟨[],fEq 3 0⟩]=false := by decide

/-- Both fixed and schema tags are actual sealed theory formulas. -/
example : (Certificate.mk [.choice]
    [⟨.ass [AxiomTag.choice.form] AxiomTag.choice.form,[]⟩]).check
    AxiomTag.choice.form=true := by decide
example : (Certificate.mk [.separation (fEq 0 1)]
    [⟨.ass [(AxiomTag.separation (fEq 0 1)).form]
      (AxiomTag.separation (fEq 0 1)).form,[]⟩]).check
    (AxiomTag.separation (fEq 0 1)).form=true := by decide

example (h : BProv ZFCax_s [] fBot) : ∃ c : Certificate,c.check fBot=true :=
  exists_refutation_iff.mpr h
example (h : ∀ c : Certificate,c.check fBot=false) : BCon ZFCax_s [] :=
  no_refutation_iff.mp h

#print axioms AxiomTag.form
#print axioms Rule.output
#print axioms Rule.premises
#print axioms Line.valid
#print axioms run
#print axioms Certificate.check
#print axioms AxiomTag.sound
#print axioms Rule.sound
#print axioms Line.sound
#print axioms run_sound
#print axioms fragment_exists
#print axioms Certificate.check_sound
#print axioms certificate_exists
#print axioms exists_checked_iff
#print axioms exists_refutation_iff
#print axioms no_refutation_iff
