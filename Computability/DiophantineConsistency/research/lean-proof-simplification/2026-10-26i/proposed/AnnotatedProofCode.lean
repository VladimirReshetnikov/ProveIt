import DiophantineConsistency.AnnotatedProofChecker
import Mathlib.Data.Nat.Pairing

/-!
# Explicit numeric coding of the sealed-ZFC certificate checker

A small binary syntax tree separates the transparent typed parsers from the
fuel-bounded untrusted natural-number decoder. No encoding is selected by
choice. The numeric wrapper uses Mathlib's square pairing, not `Cantor.toNat`.
-/

namespace DiophantineConsistency.AnnotatedProofCode

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency
open AnnotatedProofChecker

set_option maxRecDepth 12000
set_option maxHeartbeats 600000

inductive Tree where
  | atom (n : Nat)
  | fork (left right : Tree)
  deriving DecidableEq, Repr

namespace Tree

def quote : Tree → Nat
  | atom n => Nat.pair 0 n+1
  | fork a b => Nat.pair (quote a+1) (quote b)+1

def depth : Tree → Nat
  | atom _ => 1
  | fork a b => max a.depth b.depth+1

/-- Fuel zero and code zero are rejected. Every recursive code is smaller. -/
def decode : Nat → Nat → Option Tree
  | 0, _ => none
  | _+1, 0 => none
  | fuel+1, code+1 =>
    let p := Nat.unpair code
    match p.1 with
    | 0 => some (atom p.2)
    | left+1 => do
      let a ← decode fuel left
      let b ← decode fuel p.2
      pure (fork a b)

theorem depth_le_quote (t : Tree) : t.depth≤t.quote := by
  induction t with
  | atom n => simp only [depth,quote]; omega
  | fork a b ha hb =>
    have hl := Nat.left_le_pair (a.quote+1) b.quote
    have hr := Nat.right_le_pair (a.quote+1) b.quote
    simp only [depth,quote]
    omega

theorem decode_quote (t : Tree) (fuel : Nat) (hf : t.depth≤fuel) :
    decode fuel t.quote=some t := by
  induction t generalizing fuel with
  | atom n =>
    cases fuel with
    | zero => simp [depth] at hf
    | succ fuel => simp [quote,decode]
  | fork a b ha hb =>
    cases fuel with
    | zero => simp [depth] at hf
    | succ fuel =>
      have hfa : a.depth≤fuel := by simp only [depth] at hf; omega
      have hfb : b.depth≤fuel := by simp only [depth] at hf; omega
      simp [quote,decode,ha fuel hfa,hb fuel hfb]

/-- A fixed, total parser; the input itself supplies a sufficient fuel bound. -/
def parse (code : Nat) : Option Tree := decode code code

@[simp] theorem parse_quote (t : Tree) : parse t.quote=some t :=
  decode_quote t t.quote (depth_le_quote t)

theorem decoded_spec {fuel code : Nat} {t : Tree}
    (h : decode fuel code=some t) : t.quote=code ∧ t.depth≤fuel := by
  induction fuel generalizing code t with
  | zero => simp [decode] at h
  | succ fuel ih =>
    cases code with
    | zero => simp [decode] at h
    | succ code =>
      have hp := Nat.pair_unpair code
      simp only [decode] at h
      cases he : (Nat.unpair code).1 with
      | zero =>
        simp only [he] at h hp
        cases h
        exact ⟨by simp only [quote,hp], by simp [depth]⟩
      | succ left =>
        simp only [he] at h hp
        change (decode fuel left).bind (fun a =>
          (decode fuel (Nat.unpair code).2).bind (fun b => some (fork a b))) = some t at h
        simp only [Option.bind_eq_some_iff,Option.some.injEq] at h
        obtain ⟨a,ha,b,hb,rfl⟩ := h
        obtain ⟨hqa,hda⟩ := ih ha
        obtain ⟨hqb,hdb⟩ := ih hb
        exact ⟨by simp only [quote,hqa,hqb,hp], by simp only [depth]; omega⟩

/-- The old API remains available by projection. -/
theorem decoded_depth_le {fuel code : Nat} {t : Tree}
    (h : decode fuel code=some t) : t.depth≤fuel := (decoded_spec h).2

theorem quote_of_decode {fuel code : Nat} {t : Tree}
    (h : decode fuel code=some t) : t.quote=code := (decoded_spec h).1

theorem decode_eq_some_iff (fuel code : Nat) (t : Tree) :
    decode fuel code=some t ↔ t.quote=code ∧ t.depth≤fuel := by
  constructor
  · exact decoded_spec
  · rintro ⟨rfl,hf⟩
    exact decode_quote t fuel hf

theorem quote_injective : Function.Injective quote := by
  intro a b h
  have hh := congrArg parse h
  simpa only [parse_quote,Option.some.injEq] using hh

theorem decode_quote_iff (t u : Tree) (fuel : Nat) :
    decode fuel t.quote=some u ↔ u=t ∧ t.depth≤fuel := by
  rw [decode_eq_some_iff,quote_injective.eq_iff]
  exact and_congr_right (fun h => by rw [h])

theorem decode_quote_none_of_lt (t : Tree) (fuel : Nat) (h : fuel<t.depth) :
    decode fuel t.quote=none := by
  cases hh : decode fuel t.quote with
  | none => rfl
  | some u =>
    have hf := (decode_quote_iff t u fuel).mp hh
    omega

def quoteList {α : Type} (f : α → Tree) : List α → Tree
  | [] => atom 0
  | a::as => fork (f a) (quoteList f as)

def parseList {α : Type} (f : Tree → Option α) : Tree → Option (List α)
  | atom 0 => some []
  | fork a as => do
    let x ← f a
    let xs ← parseList f as
    pure (x::xs)
  | _ => none

@[simp] theorem parseList_quoteList {α : Type} (q : α → Tree) (p : Tree → Option α)
    (h : ∀ a,p (q a)=some a) (as : List α) :
    parseList p (quoteList q as)=some as := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [quoteList,parseList,h a,ih]

def tagged (tag : Nat) (fields : List Tree) : Tree :=
  fork (atom tag) (quoteList id fields)

def untagged : Tree → Option (Nat × List Tree)
  | fork (atom tag) fields => do
    let fields ← parseList some fields
    pure (tag,fields)
  | _ => none

@[simp] theorem untagged_tagged (tag : Nat) (fields : List Tree) :
    untagged (tagged tag fields)=some (tag,fields) := by
  simp [tagged,untagged,parseList_quoteList id some (fun _ => rfl)]

def parseNat : Tree → Option Nat
  | atom n => some n
  | _ => none

@[simp] theorem parseNat_atom (n : Nat) : parseNat (atom n)=some n := rfl

end Tree

open Tree

/-- Formula tags agree with the order used by the internal formula-code syntax:
mem, equality, bottom, implication, conjunction, disjunction, all, exists. -/
def quoteForm : Form → Tree
  | fMem i j => fork (atom 0) (fork (atom i) (atom j))
  | fEq i j => fork (atom 1) (fork (atom i) (atom j))
  | fBot => fork (atom 2) (atom 0)
  | fImp a b => fork (atom 3) (fork (quoteForm a) (quoteForm b))
  | fAnd a b => fork (atom 4) (fork (quoteForm a) (quoteForm b))
  | fOr a b => fork (atom 5) (fork (quoteForm a) (quoteForm b))
  | fAll a => fork (atom 6) (quoteForm a)
  | fEx a => fork (atom 7) (quoteForm a)

def parseForm : Tree → Option Form
  | fork (atom 0) (fork (atom i) (atom j)) => some (fMem i j)
  | fork (atom 1) (fork (atom i) (atom j)) => some (fEq i j)
  | fork (atom 2) (atom 0) => some fBot
  | fork (atom 3) (fork a b) => return fImp (←parseForm a) (←parseForm b)
  | fork (atom 4) (fork a b) => return fAnd (←parseForm a) (←parseForm b)
  | fork (atom 5) (fork a b) => return fOr (←parseForm a) (←parseForm b)
  | fork (atom 6) a => return fAll (←parseForm a)
  | fork (atom 7) a => return fEx (←parseForm a)
  | _ => none

@[simp] theorem parseForm_quoteForm (f : Form) : parseForm (quoteForm f)=some f := by
  induction f <;> simp_all [quoteForm,parseForm]

def quoteContext : List Form → Tree := quoteList quoteForm

def parseContext : Tree → Option (List Form) := parseList parseForm

@[simp] theorem parseContext_quoteContext (G : List Form) :
    parseContext (quoteContext G)=some G :=
  parseList_quoteList quoteForm parseForm parseForm_quoteForm G

def quoteAxiom : AxiomTag → Tree
  | .ext => tagged 0 []
  | .reg => tagged 1 []
  | .powerset => tagged 2 []
  | .pair => tagged 3 []
  | .union => tagged 4 []
  | .infinity => tagged 5 []
  | .separation f => tagged 6 [quoteForm f]
  | .replacement f => tagged 7 [quoteForm f]
  | .choice => tagged 8 []

def parseAxiom (t : Tree) : Option AxiomTag := do
  let (tag,fields) ← untagged t
  match tag,fields with
  | 0,[] => pure .ext
  | 1,[] => pure .reg
  | 2,[] => pure .powerset
  | 3,[] => pure .pair
  | 4,[] => pure .union
  | 5,[] => pure .infinity
  | 6,[f] => return .separation (←parseForm f)
  | 7,[f] => return .replacement (←parseForm f)
  | 8,[] => pure .choice
  | _,_ => none

@[simp] theorem parseAxiom_quoteAxiom (tag : AxiomTag) :
    parseAxiom (quoteAxiom tag)=some tag := by
  cases tag <;> simp [quoteAxiom,parseAxiom]

/-- The seventeen rule tags follow the order of the frozen checker. -/
def quoteRule : Rule → Tree
  | .ass G a => tagged 0 [quoteContext G,quoteForm a]
  | .impI G a b => tagged 1 [quoteContext G,quoteForm a,quoteForm b]
  | .impE G a b => tagged 2 [quoteContext G,quoteForm a,quoteForm b]
  | .botE G a => tagged 3 [quoteContext G,quoteForm a]
  | .lem G a => tagged 4 [quoteContext G,quoteForm a]
  | .andI G a b => tagged 5 [quoteContext G,quoteForm a,quoteForm b]
  | .andE1 G a b => tagged 6 [quoteContext G,quoteForm a,quoteForm b]
  | .andE2 G a b => tagged 7 [quoteContext G,quoteForm a,quoteForm b]
  | .orI1 G a b => tagged 8 [quoteContext G,quoteForm a,quoteForm b]
  | .orI2 G a b => tagged 9 [quoteContext G,quoteForm a,quoteForm b]
  | .orE G a b c => tagged 10 [quoteContext G,quoteForm a,quoteForm b,quoteForm c]
  | .allI G a => tagged 11 [quoteContext G,quoteForm a]
  | .allE G a k => tagged 12 [quoteContext G,quoteForm a,atom k]
  | .exI G a k => tagged 13 [quoteContext G,quoteForm a,atom k]
  | .exE G a c => tagged 14 [quoteContext G,quoteForm a,quoteForm c]
  | .eqRefl G k => tagged 15 [quoteContext G,atom k]
  | .eqElim G i j a => tagged 16 [quoteContext G,atom i,atom j,quoteForm a]

def parseRule (t : Tree) : Option Rule := do
  let (tag,fields) ← untagged t
  match tag,fields with
  | 0,[G,a] => return .ass (←parseContext G) (←parseForm a)
  | 1,[G,a,b] => return .impI (←parseContext G) (←parseForm a) (←parseForm b)
  | 2,[G,a,b] => return .impE (←parseContext G) (←parseForm a) (←parseForm b)
  | 3,[G,a] => return .botE (←parseContext G) (←parseForm a)
  | 4,[G,a] => return .lem (←parseContext G) (←parseForm a)
  | 5,[G,a,b] => return .andI (←parseContext G) (←parseForm a) (←parseForm b)
  | 6,[G,a,b] => return .andE1 (←parseContext G) (←parseForm a) (←parseForm b)
  | 7,[G,a,b] => return .andE2 (←parseContext G) (←parseForm a) (←parseForm b)
  | 8,[G,a,b] => return .orI1 (←parseContext G) (←parseForm a) (←parseForm b)
  | 9,[G,a,b] => return .orI2 (←parseContext G) (←parseForm a) (←parseForm b)
  | 10,[G,a,b,c] => return .orE (←parseContext G) (←parseForm a) (←parseForm b) (←parseForm c)
  | 11,[G,a] => return .allI (←parseContext G) (←parseForm a)
  | 12,[G,a,k] => return .allE (←parseContext G) (←parseForm a) (←parseNat k)
  | 13,[G,a,k] => return .exI (←parseContext G) (←parseForm a) (←parseNat k)
  | 14,[G,a,c] => return .exE (←parseContext G) (←parseForm a) (←parseForm c)
  | 15,[G,k] => return .eqRefl (←parseContext G) (←parseNat k)
  | 16,[G,i,j,a] => return .eqElim (←parseContext G) (←parseNat i) (←parseNat j) (←parseForm a)
  | _,_ => none

@[simp] theorem parseRule_quoteRule (r : Rule) : parseRule (quoteRule r)=some r := by
  cases r <;> simp [quoteRule,parseRule]

def quoteLine (line : Line) : Tree :=
  fork (quoteRule line.rule) (quoteList atom line.parents)

def parseLine : Tree → Option Line
  | fork r parents => return ⟨←parseRule r,←parseList parseNat parents⟩
  | _ => none

@[simp] theorem parseLine_quoteLine (line : Line) : parseLine (quoteLine line)=some line := by
  cases line with
  | mk r parents => simp [quoteLine,parseLine,parseList_quoteList atom parseNat parseNat_atom]

def quoteCertificate (c : Certificate) : Tree :=
  fork (quoteList quoteAxiom c.axioms) (quoteList quoteLine c.lines)

def parseCertificate : Tree → Option Certificate
  | fork axioms lines =>
    return ⟨←parseList parseAxiom axioms,←parseList parseLine lines⟩
  | _ => none

@[simp] theorem parseCertificate_quoteCertificate (c : Certificate) :
    parseCertificate (quoteCertificate c)=some c := by
  cases c with
  | mk axioms lines =>
    simp [quoteCertificate,parseCertificate,
      parseList_quoteList quoteAxiom parseAxiom parseAxiom_quoteAxiom,
      parseList_quoteList quoteLine parseLine parseLine_quoteLine]

/-- Typed decoders never trust the result of the outer numeric parser. -/
def decodeWith {α : Type} (parse : Tree → Option α) (fuel code : Nat) : Option α :=
  (Tree.decode fuel code).bind parse

def parseWith {α : Type} (parse : Tree → Option α) (code : Nat) : Option α :=
  decodeWith parse code code

theorem decodeWith_quote {α : Type} (parse : Tree → Option α) (t : Tree) (a : α)
    (ht : parse t=some a) (fuel : Nat) (hf : t.depth≤fuel) :
    decodeWith parse fuel t.quote=some a := by
  simp only [decodeWith,Tree.decode_quote t fuel hf,Option.bind_some,ht]

@[simp] theorem parseWith_quotation {α : Type} (parse : Tree → Option α) (t : Tree) :
    parseWith parse t.quote=parse t := by
  simp only [parseWith,decodeWith,Tree.decode_quote t t.quote t.depth_le_quote,Option.bind_some]

theorem parseWith_quote {α : Type} (parse : Tree → Option α) (t : Tree) (a : α)
    (ht : parse t=some a) : parseWith parse t.quote=some a :=
  decodeWith_quote parse t a ht t.quote t.depth_le_quote

def formCode (f : Form) : Nat := (quoteForm f).quote
def ruleCode (r : Rule) : Nat := (quoteRule r).quote
def lineCode (line : Line) : Nat := (quoteLine line).quote
def certificateCode (c : Certificate) : Nat := (quoteCertificate c).quote

def decodeForm : Nat → Nat → Option Form := decodeWith parseForm
def decodeRule : Nat → Nat → Option Rule := decodeWith parseRule
def decodeLine : Nat → Nat → Option Line := decodeWith parseLine
def decodeCertificate : Nat → Nat → Option Certificate := decodeWith parseCertificate

def parseFormCode : Nat → Option Form := parseWith parseForm
def parseRuleCode : Nat → Option Rule := parseWith parseRule
def parseLineCode : Nat → Option Line := parseWith parseLine
def parseCertificateCode : Nat → Option Certificate := parseWith parseCertificate

@[simp] theorem parseFormCode_formCode (f : Form) : parseFormCode (formCode f)=some f :=
  parseWith_quote parseForm (quoteForm f) f (parseForm_quoteForm f)
@[simp] theorem parseRuleCode_ruleCode (r : Rule) : parseRuleCode (ruleCode r)=some r :=
  parseWith_quote parseRule (quoteRule r) r (parseRule_quoteRule r)
@[simp] theorem parseLineCode_lineCode (line : Line) : parseLineCode (lineCode line)=some line :=
  parseWith_quote parseLine (quoteLine line) line (parseLine_quoteLine line)
@[simp] theorem parseCertificateCode_certificateCode (c : Certificate) :
    parseCertificateCode (certificateCode c)=some c :=
  parseWith_quote parseCertificate (quoteCertificate c) c (parseCertificate_quoteCertificate c)

/-- An arbitrary natural is first parsed, then checked against bottom. -/
def check (code : Nat) : Bool :=
  match parseCertificateCode code with
  | none => false
  | some c => c.check fBot

/-- The variant with caller-supplied fuel is also total and untrusted. -/
def checkWithFuel (fuel code : Nat) : Bool :=
  match decodeCertificate fuel code with
  | none => false
  | some c => c.check fBot

@[simp] theorem check_certificateCode (c : Certificate) :
    check (certificateCode c)=c.check fBot := by
  simp only [check,parseCertificateCode_certificateCode]

theorem checkWithFuel_certificateCode (c : Certificate) (fuel : Nat)
    (hf : (quoteCertificate c).depth≤fuel) :
    checkWithFuel fuel (certificateCode c)=c.check fBot := by
  have h := decodeWith_quote parseCertificate (quoteCertificate c) c
    (parseCertificate_quoteCertificate c) fuel hf
  simp only [checkWithFuel,decodeCertificate,certificateCode,h]

theorem check_sound (code : Nat) (h : check code=true) : BProv ZFCax_s [] fBot := by
  unfold check at h
  cases hp : parseCertificateCode code with
  | none => simp [hp] at h
  | some c =>
    rw [hp] at h
    exact c.check_sound fBot h

theorem checkWithFuel_sound (fuel code : Nat) (h : checkWithFuel fuel code=true) :
    BProv ZFCax_s [] fBot := by
  unfold checkWithFuel at h
  cases hp : decodeCertificate fuel code with
  | none => simp [hp] at h
  | some c =>
    rw [hp] at h
    exact c.check_sound fBot h

/-- Numeric acceptance is exactly refutability in the original sealed theory. -/
theorem exists_checked_code_iff :
    (∃ code : Nat,check code=true) ↔ BProv ZFCax_s [] fBot := by
  constructor
  · rintro ⟨code,h⟩; exact check_sound code h
  · intro h
    obtain ⟨c,hc⟩ := exists_refutation_iff.mpr h
    exact ⟨certificateCode c,by simpa only [check_certificateCode] using hc⟩

theorem exists_checked_fuel_code_iff :
    (∃ fuel code : Nat,checkWithFuel fuel code=true) ↔ BProv ZFCax_s [] fBot := by
  constructor
  · rintro ⟨fuel,code,h⟩; exact checkWithFuel_sound fuel code h
  · intro h
    obtain ⟨c,hc⟩ := exists_refutation_iff.mpr h
    refine ⟨(quoteCertificate c).depth,certificateCode c,?_⟩
    simpa only [checkWithFuel_certificateCode c _ (Nat.le_refl _)] using hc

theorem no_checked_code_iff :
    (∀ code : Nat,check code=false) ↔ ¬BProv ZFCax_s [] fBot := by
  rw [←exists_checked_code_iff]
  simp

/-- The same numeric parser can check any specified external formula. -/
def checkGoal (code : Nat) (goal : Form) : Bool :=
  match parseCertificateCode code with
  | none => false
  | some c => c.check goal

@[simp] theorem checkGoal_certificateCode (c : Certificate) (goal : Form) :
    checkGoal (certificateCode c) goal=c.check goal := by
  simp only [checkGoal,parseCertificateCode_certificateCode]

theorem checkGoal_sound (code : Nat) (goal : Form) (h : checkGoal code goal=true) :
    BProv ZFCax_s [] goal := by
  unfold checkGoal at h
  cases hp : parseCertificateCode code with
  | none => simp [hp] at h
  | some c =>
    rw [hp] at h
    exact c.check_sound goal h

end DiophantineConsistency.AnnotatedProofCode
