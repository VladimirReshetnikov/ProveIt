module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaConstructors
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open RelationalSource.Ordinal (Term Formula)
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem quote_arity_raise {k : Nat} (p : Formula k) {n : V} (h : (k:V)≤n) :
    IsSemiformula language n (⌜p⌝ : V) := by
  have hp := FFL.FirstOrder.Semiformula.quote_isSemiformula (V := V) p
  exact ⟨hp.isUFormula,le_trans hp.bv_le h⟩

theorem equalityCode_isSemiformula {n a b : V}
    (ha : IsSemiformula language (n+1+1) a)
    (hb : IsSemiformula language (n+1+1) b) :
    IsSemiformula language n (equalityCode a b) := by
  have ht : IsSemiformula language (n+1+1) (⌜equalityTail⌝ : V) :=
    quote_arity_raise equalityTail (by simpa [add_assoc,one_add_one_eq_two] using add_le_add_right (show (0:V)≤n from zero_le) (2:V))
  simpa only [equalityCode,IsSemiformula.exs,IsSemiformula.and] using ⟨ha,hb,ht⟩

theorem guardedAllCode_isSemiformula {n p : V}
    (hp : IsSemiformula language (n+1) p) :
    IsSemiformula language n (guardedAllCode p) := by
  have hd : IsSemiformula language (n+1) (⌜domainTemplate⌝ : V) :=
    quote_arity_raise domainTemplate (by simpa using add_le_add_right (show (0:V)≤n from zero_le) (1:V))
  simpa only [guardedAllCode,IsSemiformula.all,IsSemiformula.imp] using ⟨hd,hp⟩

theorem guardedExsCode_isSemiformula {n p : V}
    (hp : IsSemiformula language (n+1) p) :
    IsSemiformula language n (guardedExsCode p) := by
  have hd : IsSemiformula language (n+1) (⌜domainTemplate⌝ : V) :=
    quote_arity_raise domainTemplate (by simpa using add_le_add_right (show (0:V)≤n from zero_le) (1:V))
  simpa only [guardedExsCode,IsSemiformula.exs,IsSemiformula.and] using ⟨hd,hp⟩

#print axioms equalityCode_isSemiformula
#print axioms guardedAllCode_isSemiformula
#print axioms guardedExsCode_isSemiformula
end M6.PA.NumericPAeqFormula

