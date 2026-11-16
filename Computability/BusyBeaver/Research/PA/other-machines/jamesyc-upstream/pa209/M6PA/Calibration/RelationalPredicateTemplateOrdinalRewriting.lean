module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalSchema
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder

@[simp] theorem app_eq_rewAux {n m : Nat} (ω : Rew sourceLanguage Nat n Nat m)
    (p : Formula n) :
    Rewriting.app (F := Semiproposition sourceLanguage) (G := Semiproposition sourceLanguage) ω p =
      Semiformula.rewAux ω p := rfl

theorem rewrite_compose {n m k : Nat} (p : Formula n)
    (ω : Rew sourceLanguage Nat n Nat m) (τ : Rew sourceLanguage Nat m Nat k) :
    Semiformula.rewAux τ (Semiformula.rewAux ω p) = Semiformula.rewAux (τ.comp ω) p :=
  (TransitiveRewriting.comp_app ω τ p).symm

macro "finishTemplateSyntax" : tactic => `(tactic|
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.exs _ = Semiformula.exs _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1))

macro "templateOrdinalSyntax" : tactic => `(tactic|
  (simp only [zero,subset,transitive,memberTransitive,memberLinear,nonempty,
    least,greatest,internalExtrema,representative,memberIr,domain,inhabited,
    mem,eq,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   finishTemplateSyntax))

macro "templateTraceSyntax" : tactic => `(tactic|
  (simp only [predicateTrace,predicateTraceExists,traceProperty,separationFormula,
    sourceIff,mem,eq,Semiformula.shift,Semiformula.free,
    Rewriting.shift,Rewriting.free,Rewriting.subst,app_eq_rewAux,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
   try simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg];
   repeat' rw [rewrite_compose]))

theorem predicateInstanceShift (p : Formula 1) (a : Nat) :
    (p/[(.fvar a : Term 0)]).shift = p.shift/[.fvar (a+1)] := by
  change Semiformula.rewAux Rew.shift (Semiformula.rewAux (Rew.subst ![.fvar a]) p) =
    Semiformula.rewAux (Rew.subst ![.fvar (a+1)]) (Semiformula.rewAux Rew.shift p)
  rw [rewrite_compose,rewrite_compose]
  congr 1
  ext i <;> simp [Rew.comp_app]
#print axioms predicateInstanceShift
end M6.PA.RelationalPredicateTemplate.Ordinal
