module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSourceTerms
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem source_bindFree_adjoin {n f x : V} (h : IsSemitermVec L (len f) n f)
    (hx : IsSemiterm L n x) : bindFree (x∷f)=termBShift L x ∷ bindFree f := by
  simp [bindFree,NumericPAeqTerm.shiftTerms,termBShiftVec_cons hx.isUTerm h.isUTerm]

theorem atomValue_sourceShift {s k : Nat} (r : Relation k) (ts : Fin k→Term s) (P b f x : V) :
    atomValue r (Rew.shift ∘ ts) P b (x∷f)=atomValue r ts P b f := by
  cases r <;> simp only [atomValue,Function.comp_apply,termValue_sourceShift]

theorem formulaValue_sourceShift {s : Nat} (p : Formula s) {n P b f x : V}
    (h : EnvironmentsValid (s:V) n b f) (hx : IsSemiterm L n x) :
    formulaValue (Rewriting.shift p) P b (x∷f)=formulaValue p P b f := by
  change formulaValue (Semiformula.rewAux Rew.shift p) P b (x∷f)=_
  induction p generalizing n b f x with
  | verum => rfl
  | falsum => rfl
  | rel r ts => exact atomValue_sourceShift r ts P b f x
  | nrel r ts => simp only [Semiformula.rewAux,formulaValue,atomValue_sourceShift]
  | and p q ihp ihq => simp only [Semiformula.rewAux,formulaValue,ihp h hx,ihq h hx]
  | or p q ihp ihq => simp only [Semiformula.rewAux,formulaValue,ihp h hx,ihq h hx]
  | @all s p ih =>
    have hb : EnvironmentsValid ((s+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h
    simp only [Semiformula.rewAux,Rew.q_shift,formulaValue,source_bindFree_adjoin h.2 hx,
      ih hb hx.termBShift]
  | @exs s p ih =>
    have hb : EnvironmentsValid ((s+1:Nat):V) (n+1) (bindBound b) (bindFree f) := by
      simpa only [Nat.cast_add,Nat.cast_one] using bindEnvironments_valid h
    simp only [Semiformula.rewAux,Rew.q_shift,formulaValue,source_bindFree_adjoin h.2 hx,
      ih hb hx.termBShift]
#print axioms source_bindFree_adjoin
#print axioms atomValue_sourceShift
#print axioms formulaValue_sourceShift
end M6.PA.RelationalPredicateTemplate

