/-!
A three-constructor equality-free formula codec, adapted in design from
Surreal.Algebra.RingFormulaCode: scan prefix tokens right to left, carrying
a formula stack. Native syntax, serialization, exact decoding and scope checks
are proved here using Lean core alone. NAND supplies classical negation and
implication without an extra falsity token or an irreflexivity assumption.
There are three token forms; atoms carry unbounded natural payloads. No bit
encoding, or correspondence to the Python named-variable encoding, is proved.
This is a codec, not a theorem checker or a Turing-machine compiler.
-/

namespace SetTheory.BusyBeaver.ZFC.FormulaRPN

inductive Formula where
  | mem : Nat → Nat → Formula
  | nand : Formula → Formula → Formula
  | all : Formula → Formula
  deriving DecidableEq, Repr

inductive Token where
  | mem : Nat → Nat → Token
  | nand
  | all
  deriving DecidableEq, Repr

def encode : Formula → List Token
  | .mem i j => [.mem i j]
  | .nand p q => .nand :: (encode p ++ encode q)
  | .all p => .all :: encode p

def step : Token → List Formula → Option (List Formula)
  | .mem i j, s => some (.mem i j :: s)
  | .nand, p :: q :: s => some (.nand p q :: s)
  | .all, p :: s => some (.all p :: s)
  | _, _ => none

def parse (tokens : List Token) (s : Option (List Formula)) : Option (List Formula) :=
  tokens.foldr (fun t r => r.bind (step t)) s

@[simp] theorem parse_nil (s : Option (List Formula)) : parse [] s = s := rfl

@[simp] theorem parse_cons (t : Token) (l : List Token) (s : Option (List Formula)) :
    parse (t :: l) s = (parse l s).bind (step t) := rfl

@[simp] theorem parse_append (l r : List Token) (s : Option (List Formula)) :
    parse (l ++ r) s = parse l (parse r s) := by
  simp [parse, List.foldr_append]

@[simp] theorem parse_none (l : List Token) : parse l none = none := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [ih]

theorem parse_encode (p : Formula) (s : List Formula) :
    parse (encode p) (some s) = some (p :: s) := by
  induction p generalizing s with
  | mem i j => rfl
  | nand p q hp hq => simp [encode, hp, hq, step]
  | all p hp => simp [encode, hp, step]

def decode (l : List Token) : Option Formula :=
  match parse l (some []) with
  | some [p] => some p
  | _ => none

@[simp] theorem decode_encode (p : Formula) : decode (encode p) = some p := by
  simp [decode, parse_encode]

theorem step_encode (t : Token) (s r : List Formula) (h : step t s = some r) :
    r.flatMap encode = t :: s.flatMap encode := by
  cases t with
  | mem i j => cases h; rfl
  | nand =>
      cases s with
      | nil => cases h
      | cons p s =>
          cases s with
          | nil => cases h
          | cons q s => cases h; simp [encode, List.append_assoc]
  | all =>
      cases s with
      | nil => cases h
      | cons p s => cases h; simp [encode]

theorem parse_sound (l : List Token) (s r : List Formula)
    (h : parse l (some s) = some r) :
    r.flatMap encode = l ++ s.flatMap encode := by
  induction l generalizing r with
  | nil => cases h; rfl
  | cons t l ih =>
      simp only [parse_cons] at h
      cases hl : parse l (some s) with
      | none => simp [hl] at h
      | some middle =>
          simp only [hl, Option.bind_some] at h
          rw [step_encode t middle r h, ih middle hl]
          rfl

theorem encode_of_decode {l : List Token} {p : Formula} (h : decode l = some p) :
    encode p = l := by
  unfold decode at h
  cases hp : parse l (some []) with
  | none => simp [hp] at h
  | some s =>
      cases s with
      | nil => simp [hp] at h
      | cons q s =>
          cases s with
          | nil =>
              simp only [hp, Option.some.injEq] at h
              subst q
              simpa using parse_sound l [] [p] hp
          | cons _ _ => simp [hp] at h

theorem encode_injective : Function.Injective encode := by
  intro p q h
  have hd := congrArg decode h
  simpa using hd

/-- De Bruijn indices: a quantifier adds index zero, so it needs no label payload. -/
def wellScoped : Nat → Formula → Bool
  | n, .mem i j => i < n && j < n
  | n, .nand p q => wellScoped n p && wellScoped n q
  | n, .all p => wellScoped (n + 1) p

def decodeScoped (n : Nat) (l : List Token) : Option Formula :=
  (decode l).filter (wellScoped n)

theorem decodeScoped_encode (n : Nat) (p : Formula) (h : wellScoped n p = true) :
    decodeScoped n (encode p) = some p := by
  simp [decodeScoped, h]

def consEnv {V : Type u} (x : V) (env : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => env i

def Realize {V : Type u} (mem : V → V → Prop) (env : Nat → V) : Formula → Prop
  | .mem i j => mem (env i) (env j)
  | .nand p q => ¬ (Realize mem env p ∧ Realize mem env q)
  | .all p => ∀ x, Realize mem (consEnv x env) p

def neg (p : Formula) : Formula := .nand p p
def imp (p q : Formula) : Formula := .nand p (neg q)

theorem realize_neg {V : Type u} (mem : V → V → Prop) (env : Nat → V) (p : Formula) :
    Realize mem env (neg p) ↔ ¬ Realize mem env p := by
  simp [Realize, neg]

theorem realize_imp {V : Type u} (mem : V → V → Prop) (env : Nat → V) (p q : Formula) :
    Realize mem env (imp p q) ↔ (Realize mem env p → Realize mem env q) := by
  classical
  simp [Realize, imp, neg]

/-- A fixed contradiction with no special falsity atom or semantic background axiom. -/
def contradiction : Formula := neg (imp (.mem 0 0) (.mem 0 0))

theorem contradiction_false {V : Type u} (mem : V → V → Prop) (env : Nat → V) :
    ¬ Realize mem env contradiction := by
  rw [contradiction, realize_neg, realize_imp]
  exact fun h => h (fun hx => hx)

/-- Bind the auxiliary index in the open contradiction. -/
def closedContradiction : Formula := .all contradiction

theorem closedContradiction_wellScoped : wellScoped 0 closedContradiction = true := by
  decide

/-- An environment supplies a domain witness, as required by first-order semantics. -/
theorem closedContradiction_false {V : Type u} (mem : V → V → Prop) (env : Nat → V) :
    ¬ Realize mem env closedContradiction := by
  intro h
  exact contradiction_false mem (consEnv (env 0) env) (h (env 0))

#print axioms decode_encode
#print axioms encode_of_decode
#print axioms closedContradiction_false

end SetTheory.BusyBeaver.ZFC.FormulaRPN
