import Mathlib.Computability.Primrec.List

/-! Arity-indexed syntax for primitive-recursive function symbols.  This file
constructs functions, not a PRA theory or a proof of conservation. In particular,
primitive recursiveness is proved for each fixed code, not for a universal
evaluator with the code as an additional argument. -/

set_option autoImplicit false
namespace DiophantineConsistency.PRAFunctionCodes
open List.Vector

inductive Code : ℕ → Type
  | zero (n : ℕ) : Code n
  | succ : Code 1
  | proj {n : ℕ} (i : Fin n) : Code n
  | comp {m n : ℕ} (f : Code m) (g : Fin m → Code n) : Code n
  | prec {n : ℕ} (f : Code n) (g : Code (n + 2)) : Code (n + 1)

def eval : {n : ℕ} → Code n → List.Vector ℕ n → ℕ
  | _, .zero _, _ => 0
  | _, .succ, v => v.head + 1
  | _, .proj i, v => v.get i
  | _, .comp f g, v => eval f (List.Vector.ofFn fun i => eval (g i) v)
  | _, .prec f g, v => v.head.rec (eval f v.tail)
      (fun y ih => eval g (y ::ᵥ ih ::ᵥ v.tail))

theorem eval_primrec' {n : ℕ} (c : Code n) : Nat.Primrec' (eval c) := by
  induction c with
  | zero n => exact Nat.Primrec'.const 0
  | succ => simpa [eval, Nat.succ_eq_add_one] using Nat.Primrec'.succ
  | proj i => exact Nat.Primrec'.get i
  | comp f g ihf ihg =>
      exact Nat.Primrec'.comp (fun i => eval (g i)) ihf ihg
  | prec f g ihf ihg => exact Nat.Primrec'.prec ihf ihg

theorem eval_primrec {n : ℕ} (c : Code n) : Primrec (eval c) :=
  (eval_primrec' c).to_prim

/-- Every primitive-recursive n-ary function has a syntactic code. -/
theorem exists_code_of_primrec' {n : ℕ} {f : List.Vector ℕ n → ℕ}
    (hf : Nat.Primrec' f) : ∃ c : Code n, eval c = f := by
  classical
  induction hf with
  | zero => exact ⟨.zero 0, rfl⟩
  | succ => exact ⟨.succ, by funext v; simp [eval, Nat.succ_eq_add_one]⟩
  | get i => exact ⟨.proj i, rfl⟩
  | comp g hf hg ihf ihg =>
      obtain ⟨cf, hcf⟩ := ihf
      choose cg hcg using ihg
      refine ⟨.comp cf cg, ?_⟩
      funext v
      simp only [eval, hcf, hcg]
  | prec hf hg ihf ihg =>
      obtain ⟨cf, hcf⟩ := ihf
      obtain ⟨cg, hcg⟩ := ihg
      refine ⟨.prec cf cg, ?_⟩
      funext v
      simp only [eval, hcf, hcg]

theorem exists_code_of_primrec {n : ℕ} {f : List.Vector ℕ n → ℕ}
    (hf : Primrec f) : ∃ c : Code n, eval c = f :=
  exists_code_of_primrec' (Nat.Primrec'.of_prim hf)

/-- Primitive recursion on the first argument: `addCore(r,x) = x+r`. -/
def addCore : Code 2 :=
  .prec (.proj 0) (.comp .succ (fun _ => .proj 1))

theorem eval_addCore (r x : ℕ) :
    eval addCore (r ::ᵥ x ::ᵥ nil) = x + r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change eval addCore (r ::ᵥ x ::ᵥ nil) + 1 = x + (r + 1)
      rw [ih, Nat.add_assoc]

end DiophantineConsistency.PRAFunctionCodes
