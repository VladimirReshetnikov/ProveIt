import DiophantineConsistency.AnnotatedProofCode

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency
open DiophantineConsistency.AnnotatedProofChecker
open DiophantineConsistency.AnnotatedProofCode
open DiophantineConsistency.AnnotatedProofCode.Tree

/-- The outer decoder rejects zero and rejects insufficient fuel. -/
example : Tree.parse 0=none := by decide
example : Tree.decode 0 8=none := by decide
example : Tree.decode 1 8=none := by
  change Tree.decode 1 (fork (atom 0) (atom 0)).quote=none
  exact decode_quote_none_of_lt _ _ (by decide)
example : Tree.decode 2 8=some (fork (atom 0) (atom 0)) := by
  change Tree.decode 2 (fork (atom 0) (atom 0)).quote=some _
  exact Tree.decode_quote _ _ (by decide)
example : Tree.decode 3 8=some (fork (atom 0) (atom 0)) := by
  change Tree.decode 3 (fork (atom 0) (atom 0)).quote=some _
  exact Tree.decode_quote _ _ (by decide)
example (t : Tree) (fuel : Nat) (h : fuel<t.depth) : Tree.decode fuel t.quote=none :=
  decode_quote_none_of_lt t fuel h

/-- Constructor tags, arguments and arities are all untrusted syntax. -/
example : formCode fBot=44 := by decide
example : parseFormCode 44=some fBot := by
  change parseFormCode (formCode fBot)=some fBot
  exact parseFormCode_formCode fBot
example : decodeForm 1 44=none := by
  change decodeWith parseForm 1 (quoteForm fBot).quote=none
  simp only [decodeWith,decode_quote_none_of_lt (quoteForm fBot) 1 (by decide),Option.bind_none]
example : decodeForm 2 44=some fBot := by
  exact decodeWith_quote parseForm (quoteForm fBot) fBot (by simp) 2 (by decide)
example : parseFormCode 45=none := by
  change parseWith parseForm (fork (atom 2) (atom 1)).quote=none
  rw [parseWith_quotation]
  rfl
example : parseForm (fork (atom 8) (atom 0))=none := by decide
example : parseForm (fork (atom 0) (fork (atom 0) (fork (atom 0) (atom 0))))=none := by decide
example : parseAxiom (tagged 9 [])=none := by decide
example : parseAxiom (tagged 6 [])=none := by decide
example : parseAxiom (tagged 6 [atom 0])=none := by decide
example : parseRule (tagged 17 [])=none := by decide
example : parseRule (tagged 0 [quoteContext [],quoteForm fBot,atom 0])=none := by decide
example : parseLine (fork (quoteRule (.eqRefl [] 0)) (atom 1))=none := by decide
example : parseCertificate (fork (atom 1) (atom 0))=none := by decide
example : check 0=false := by decide
example : check 1=false := by decide
example (code : Nat) : checkWithFuel 0 code=false := by
  cases code <;> rfl

private def shared : Certificate := ⟨[],[
  ⟨.eqRefl [] 0,[]⟩,
  ⟨.andI [] (fEq 0 0) (fEq 0 0),[0,0]⟩]⟩

/-- Roundtrips do not require expanding the potentially large numeric quotation. -/
example (f : Form) : parseFormCode (formCode f)=some f := parseFormCode_formCode f
example (r : Rule) : parseRuleCode (ruleCode r)=some r := parseRuleCode_ruleCode r
example (line : Line) : parseLineCode (lineCode line)=some line := parseLineCode_lineCode line
example : parseCertificateCode (certificateCode shared)=some shared :=
  parseCertificateCode_certificateCode shared
example : checkGoal (certificateCode shared) (fAnd (fEq 0 0) (fEq 0 0))=true := by
  rw [checkGoal_certificateCode]
  decide
example : check (certificateCode shared)=false := by
  rw [check_certificateCode]
  decide
example : check (certificateCode ⟨[],[⟨.ass [] fBot,[]⟩]⟩)=false := by
  rw [check_certificateCode]
  decide
example : checkWithFuel ((quoteCertificate shared).depth-1) (certificateCode shared)=false := by
  have hd : 0<(quoteCertificate shared).depth := by decide
  have h := decode_quote_none_of_lt (quoteCertificate shared)
    ((quoteCertificate shared).depth-1) (by omega)
  simp only [checkWithFuel,decodeCertificate,decodeWith,certificateCode,h,Option.bind_none]

example (h : BProv ZFCax_s [] fBot) : ∃ code : Nat,check code=true :=
  exists_checked_code_iff.mpr h
example (h : ∀ code : Nat,check code=false) : BCon ZFCax_s [] :=
  no_checked_code_iff.mp h

#print axioms Tree.quote
#print axioms Tree.decode
#print axioms Tree.parse
#print axioms Tree.decode_quote
#print axioms Tree.quote_of_decode
#print axioms Tree.decode_quote_none_of_lt
#print axioms quoteForm
#print axioms parseForm
#print axioms quoteRule
#print axioms parseRule
#print axioms quoteCertificate
#print axioms parseCertificate
#print axioms parseFormCode_formCode
#print axioms parseRuleCode_ruleCode
#print axioms parseLineCode_lineCode
#print axioms parseCertificateCode_certificateCode
#print axioms check
#print axioms checkWithFuel
#print axioms check_sound
#print axioms checkWithFuel_sound
#print axioms exists_checked_code_iff
#print axioms exists_checked_fuel_code_iff
#print axioms no_checked_code_iff
#print axioms checkGoal_sound

/- Runtime checks exercise the executable square-root inverse as well. -/
#eval parseFormCode 44 == some fBot
#eval parseFormCode 45 == none
#eval Tree.decode 1 8 == none
#eval Tree.decode 2 8 == some (fork (atom 0) (atom 0))
