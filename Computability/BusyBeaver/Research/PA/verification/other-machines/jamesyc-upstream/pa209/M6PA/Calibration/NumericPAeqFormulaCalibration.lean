module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaValidity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem domain_quote_context (m : Nat) :
    (⌜RelationalSource.Ordinal.domain (.bvar 0 : Term (m+1))⌝ : V)=⌜domainTemplate⌝ := by
  have h := domainCode_quote (V := V) (.bvar 0 : Term (m+1))
  have h' := domainCode_quote (V := V) (.bvar 0 : Term 1)
  simpa only [FFL.FirstOrder.Semiterm.quote_bvar,Fin.val_zero, Nat.cast_zero,domainTemplate] using h.symm.trans h'

theorem equalityTail_quote_context (m : Nat) :
    (⌜RelationalSource.PairGraph.orderIso (.bvar 1 : Term (m+1+1)) (.bvar 0)⌝ : V)=⌜equalityTail⌝ := by
  let p : Formula 2 := RelationalSource.PairGraph.orderIso (.bvar 0) (.bvar 1)
  have h (k : Nat) : templateTwo p (⌜(.bvar 1 : Term (k+1+1))⌝ : V) ⌜(.bvar 0 : Term (k+1+1))⌝=
      ⌜RelationalSource.PairGraph.orderIso (.bvar 1 : Term (k+1+1)) (.bvar 0)⌝ := by
    rw [templateTwo_quote]
    congr 1
    exact RelationalSource.PairGraph.orderIso_rew _ _ _
  have he := (h m).symm.trans (h 0)
  simpa only [FFL.FirstOrder.Semiterm.quote_bvar,Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,equalityTail] using he

theorem equalityCode_quote {m : Nat} (a b : Formula (m+1+1)) :
    equalityCode (⌜a⌝ : V) ⌜b⌝=
      ⌜∃¹ ∃¹ (a ⋏ (b ⋏ RelationalSource.PairGraph.orderIso (.bvar 1) (.bvar 0)))⌝ := by
  simp only [equalityCode,FFL.FirstOrder.Semiformula.quote_ex,FFL.FirstOrder.Semiformula.quote_and,
    equalityTail_quote_context]

theorem guardedAllCode_quote {m : Nat} (p : Formula (m+1)) :
    guardedAllCode (⌜p⌝ : V)=⌜∀¹ (RelationalSource.Ordinal.domain (.bvar 0) 🡒 p)⌝ := by
  simp only [guardedAllCode,FFL.FirstOrder.Semiformula.quote_all,Semiformula.imp_eq,
    FFL.FirstOrder.Semiformula.quote_or,FFL.FirstOrder.Semiformula.quote_def]
  simp [Bootstrapping.imp,←FFL.FirstOrder.Semiformula.quote_def,domain_quote_context]

theorem guardedExsCode_quote {m : Nat} (p : Formula (m+1)) :
    guardedExsCode (⌜p⌝ : V)=⌜∃¹ (RelationalSource.Ordinal.domain (.bvar 0) ⋏ p)⌝ := by
  simp only [guardedExsCode,FFL.FirstOrder.Semiformula.quote_ex,
    FFL.FirstOrder.Semiformula.quote_and,domain_quote_context]

#print axioms equalityCode_quote
#print axioms guardedAllCode_quote
#print axioms guardedExsCode_quote
end M6.PA.NumericPAeqFormula

