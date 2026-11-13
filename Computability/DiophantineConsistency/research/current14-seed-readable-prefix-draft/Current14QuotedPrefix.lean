import DiophantineConsistency.Sign17ReadableCurrent14Endpoint

/-! SOURCE ONLY. A restricted prefix-token transcription of the displayed arithmetic. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Current14QuotedPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open ObjectCurrentEquation2011 IPRAStandardTheory IPRACurrentNativeZFC
open IPRAFoundationZFCMappedNegation Sign17LinesCurrent14Endpoint
open Sign17ReadableCurrent14Endpoint

abbrev Env := List (String × Expr (Fin 14))

def lookup (name : String) : Env → Option (Expr (Fin 14))
  | [] => none
  | (key, value) :: rest => if name = key then some value else lookup name rest

def initial (p : Fin 4 → ℤ) : Env :=
  [("J", .var 0), ("F", .var 1), ("alpha", .var 2), ("z", .var 3),
   ("f", .var 4), ("i", .var 5), ("T", .var 6), ("s", .var 7),
   ("w", .var 8), ("n", .var 9), ("eta", .var 10), ("zeta", .var 11),
   ("y", .var 12), ("gamma", .var 13),
   ("beta", .constant (p 0)), ("K", .constant (p 1)),
   ("mu", .constant (p 2)), ("omega", .constant (p 3)),
   ("1", .constant 1), ("2", .constant 2), ("3", .constant 3), ("4", .constant 4)]

def decode (env : Env) : ℕ → List String → Option (Expr (Fin 14) × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, word :: rest =>
    let binary (op : Expr (Fin 14) → Expr (Fin 14) → Expr (Fin 14)) := do
      let (a, rest) ← decode env fuel rest
      let (b, rest) ← decode env fuel rest
      some (op a b, rest)
    match word with
    | "+" => binary Expr.add
    | "-" => binary Expr.sub
    | "*" => binary Expr.mul
    | "sq" => do
        let (a, rest) ← decode env fuel rest
        some (a ^ 2, rest)
    | "cube" => do
        let (a, rest) ← decode env fuel rest
        some (a ^ 3, rest)
    | _ => do
        let a ← lookup word env
        some (a, rest)

def step (env : Env) : List String → Option Env
  | name :: "=" :: tokens => do
      if (lookup name env).isSome then none else
        let (value, rest) ← decode env 64 tokens
        if rest.isEmpty then some ((name, value) :: env) else none
  | _ => none

def compile : Env → List (List String) → Option Env
  | env, [] => some env
  | env, line :: rest => do
      let env ← step env line
      compile env rest

/-- Independently transcribed from the page; whitespace is represented by token boundaries. -/
def quoted : List (List String) := [
  ["b", "=", "*", "beta", "J"],
  ["q", "=", "+", "b", "1"],
  ["C", "=", "-", "-", "q", "F", "alpha"],
  ["X", "=", "*", "w", "q"],
  ["Y", "=", "*", "s", "cube", "q"],
  ["E", "=", "*", "X", "Y"],
  ["k", "=", "+", "eta", "zeta"],
  ["ell", "=", "*", "*", "E", "k", "Y"],
  ["c", "=", "+", "*", "k", "Y", "eta"],
  ["a", "=", "+", "E", "Y"],
  ["H", "=", "+", "*", "4", "a", "3"],
  ["Delta", "=", "+", "sq", "a", "H"],
  ["D", "=", "+", "+", "X", "*", "a", "c", "*", "gamma", "H"],
  ["R", "=", "+", "*", "+", "*", "b", "-", "q", "F", "alpha", "-", "sq", "q", "1", "*", "+", "mu", "*", "q", "omega", "J"],
  ["tau", "=", "-", "+", "*", "E", "n", "k", "R"],
  ["V", "=", "-", "*", "sq", "f", "-", "*", "c", "T", "R", "c"],
  ["P", "=", "-", "sq", "tau", "*", "ell", "+", "ell", "k"],
  ["Q", "=", "-", "sq", "D", "*", "Delta", "sq", "c"],
  ["S", "=", "*", "*", "i", "Delta", "sq", "c"],
  ["U", "=", "+", "*", "sq", "S", "-", "sq", "V", "sq", "y", "sq", "y"],
  ["W", "=", "-", "+", "*", "+", "K", "w", "C", "-", "q", "F", "*", "z", "b"],
  ["Z", "=", "-", "*", "Delta", "sq", "f", "sq", "S"],
  ["result", "=", "-", "*", "*", "*", "*", "P", "Q", "U", "W", "Z", "Delta"]]

def quotedExpr (p : Fin 4 → ℤ) : Option (Expr (Fin 14)) := do
  let env ← compile (initial p) quoted
  lookup "result" env

theorem quotedExpr_eq (p : Fin 4 → ℤ) :
    quotedExpr p = some (displayedExpr p) := by
  rfl

def quoteSentence : Option (Sentenceᵢ language) := do
  let e ← quotedExpr linePorts
  let e := positiveShift e
  some (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))])))

theorem quoteSentence_eq : quoteSentence = some displayedNoZero := by
  unfold quoteSentence
  rw [quotedExpr_eq]
  rfl

theorem quoted_endpoint : ∃ φ, quoteSentence = some φ ∧
    (standardTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding) := by
  exact ⟨displayedNoZero, quoteSentence_eq, displayed_endpoint⟩

end DiophantineConsistency.Current14QuotedPrefix
#print axioms DiophantineConsistency.Current14QuotedPrefix.quotedExpr_eq
#print axioms DiophantineConsistency.Current14QuotedPrefix.quoted_endpoint
