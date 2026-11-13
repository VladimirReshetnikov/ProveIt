import DiophantineConsistency.SharingSeed14Degree124

/-! SOURCE-ONLY: total, fuel-bounded parser for the restricted prefix format. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Prefix

def decode (p : Fin 4 → ℤ) : ℕ → List Char → Option (Expr (Fin 15) × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | n + 1, c :: cs =>
    let binary (op : Expr (Fin 15) → Expr (Fin 15) → Expr (Fin 15)) := do
      let (left, rest) ← decode p n cs
      let (right, rest) ← decode p n rest
      some (op left right, rest)
    match c with
    | '+' => binary Expr.add
    | '-' => binary Expr.sub
    | '*' => binary Expr.mul
    | 'a' => some (Expr.var 0, cs)
    | 'b' => some (Expr.var 1, cs)
    | 'c' => some (Expr.var 2, cs)
    | 'd' => some (Expr.var 3, cs)
    | 'e' => some (Expr.var 4, cs)
    | 'f' => some (Expr.var 5, cs)
    | 'g' => some (Expr.var 6, cs)
    | 'h' => some (Expr.var 7, cs)
    | 'i' => some (Expr.var 8, cs)
    | 'j' => some (Expr.var 9, cs)
    | 'k' => some (Expr.var 10, cs)
    | 'l' => some (Expr.var 11, cs)
    | 'm' => some (Expr.var 12, cs)
    | 'n' => some (Expr.var 13, cs)
    | 'o' => some (Expr.var 14, cs)
    | 'B' => some (Expr.constant (p 0), cs)
    | 'K' => some (Expr.constant (p 1), cs)
    | 'C' => some (Expr.constant (p 2), cs)
    | 'F' => some (Expr.constant (p 3), cs)
    | '1' => some (Expr.constant 1, cs)
    | '2' => some (Expr.constant 2, cs)
    | '3' => some (Expr.constant 3, cs)
    | '4' => some (Expr.constant 4, cs)
    | _ => none
end DiophantineConsistency.Sign14Prefix
