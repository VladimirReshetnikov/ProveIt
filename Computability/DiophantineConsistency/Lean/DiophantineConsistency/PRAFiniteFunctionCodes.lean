import DiophantineConsistency.PRAFunctionCodes

/-! Finite, decidably equal primitive-recursive syntax. Composition arguments
are an arity-indexed inductive list, so a function symbol is finite syntax,
not a quotient by semantic equality. The interpretation is mediated by the
previously verified function-valued presentation. This does not define PRA or
an effective numerical encoding. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteFunctionCodes
open PRAFunctionCodes

mutual
inductive Code : ℕ → Type
  | zero (n : ℕ) : Code n
  | succ : Code 1
  | proj {n : ℕ} (i : Fin n) : Code n
  | comp {m n : ℕ} (f : Code m) (g : Codes n m) : Code n
  | prec {n : ℕ} (f : Code n) (g : Code (n + 2)) : Code (n + 1)
  deriving DecidableEq
inductive Codes : ℕ → ℕ → Type
  | nil (n : ℕ) : Codes n 0
  | cons {n m : ℕ} (head : Code n) (tail : Codes n m) : Codes n (m + 1)
  deriving DecidableEq
end

mutual
 def forget : {n : ℕ} → Code n → PRAFunctionCodes.Code n
   | _, .zero n => .zero n
   | _, .succ => .succ
   | _, .proj i => .proj i
   | _, .comp f g => .comp (forget f) (forgetMany g)
   | _, .prec f g => .prec (forget f) (forget g)
 def forgetMany : {n m : ℕ} → Codes n m → Fin m → PRAFunctionCodes.Code n
   | _, _, .nil _, i => Fin.elim0 i
   | _, _, .cons h t, i => Fin.cases (forget h) (forgetMany t) i
end

def pack {n : ℕ} : (m : ℕ) → (Fin m → Code n) → Codes n m
  | 0, _ => .nil n
  | m + 1, f => .cons (f 0) (pack m (fun i => f i.succ))

theorem forgetMany_pack {n : ℕ} (m : ℕ) (f : Fin m → Code n) :
    forgetMany (pack m f) = fun i => forget (f i) := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (ih (fun j => f j.succ)) j

/-- The finite syntax represents every tree in the first presentation. -/
theorem forget_surjective {n : ℕ} (c : PRAFunctionCodes.Code n) :
    ∃ d : Code n, forget d = c := by
  classical
  induction c with
  | zero n => exact ⟨.zero n, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | proj i => exact ⟨.proj i, rfl⟩
  | comp f g ihf ihg =>
      obtain ⟨df, hdf⟩ := ihf
      choose dg hdg using ihg
      refine ⟨.comp df (pack _ dg), ?_⟩
      simp only [forget, forgetMany_pack, hdf, hdg]
  | prec f g ihf ihg =>
      obtain ⟨df, hdf⟩ := ihf
      obtain ⟨dg, hdg⟩ := ihg
      exact ⟨.prec df dg, by simp only [forget, hdf, hdg]⟩

def eval {n : ℕ} (c : Code n) : List.Vector ℕ n → ℕ :=
  PRAFunctionCodes.eval (forget c)

theorem eval_primrec {n : ℕ} (c : Code n) : Primrec (eval c) :=
  PRAFunctionCodes.eval_primrec (forget c)

theorem exists_code_of_primrec {n : ℕ} {f : List.Vector ℕ n → ℕ}
    (hf : Primrec f) : ∃ c : Code n, eval c = f := by
  obtain ⟨c, hc⟩ := PRAFunctionCodes.exists_code_of_primrec hf
  obtain ⟨d, hd⟩ := forget_surjective c
  exact ⟨d, by simp only [eval, hd, hc]⟩

end DiophantineConsistency.PRAFiniteFunctionCodes
