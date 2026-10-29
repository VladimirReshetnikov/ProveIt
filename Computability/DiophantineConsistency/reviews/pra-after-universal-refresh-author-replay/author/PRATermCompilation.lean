import DiophantineConsistency.PRAAddOne

/-! Compile any candidate-language term to one primitive-recursive code. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRATermCompilation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

/-- Replace each term tree by one symbol, using projections and composition. -/
def compileTerm {n : ℕ} : TermN n → Code n
  | .bvar i => .proj i
  | .fvar v => nomatch v
  | .func f args => .comp f (pack _ (fun i => compileTerm (args i)))

/-- Every compiled term denotes a primitive-recursive function on ℕ. -/
theorem compiledTerm_primrec {n : ℕ} (t : TermN n) : Primrec (eval (compileTerm t)) :=
  eval_primrec (compileTerm t)

theorem getCode_pack {n : ℕ} (m : ℕ) (f : Fin m → Code n) :
    getCode (pack m f) = f := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact congrFun (ih (fun j => f j.succ)) j

def compiledEquation {n : ℕ} (t : TermN n) : Sentence language :=
  equalClosure (applyCode (compileTerm t) (vars n)) t

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelCompile {n : ℕ} (t : TermN n) (e : Fin n → M) :
    Structure.func (L := language) (compileTerm t) e = Semiterm.val e Empty.elim t := by
  induction t with
  | bvar i =>
      exact modelProjection i e
  | fvar x => exact nomatch x
  | func f args ih =>
      change Structure.func (L := language) (.comp f (pack _ (fun i => compileTerm (args i)))) e = _
      rw [modelComposition, getCode_pack]
      simp only [Semiterm.val_func]
      congr 1
      funext i
      exact ih i

theorem modelCompiledEquation {n : ℕ} (t : TermN n) :
    M↓[language] ⊧ compiledEquation t := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hv : (Semiterm.val e Empty.elim ∘ vars n) = e := by
    funext i
    rfl
  rw [hv]
  exact modelCompile t e

end models

/-- Every candidate-language term is provably equal to a single fixed-code
application, universally in all its arguments. -/
theorem PRA_proves_compiledEquation {n : ℕ} (t : TermN n) : PRA ⊢ compiledEquation t := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelCompiledEquation t

end DiophantineConsistency.PRATermCompilation
