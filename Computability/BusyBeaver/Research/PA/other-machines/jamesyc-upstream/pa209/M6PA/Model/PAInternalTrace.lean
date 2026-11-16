module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAHaltingFormula
@[expose] public section

/-! Length-normalized certificates for the existing HFS-coded machine trace.
All semantic lemmas below quantify arbitrary PA models, not only Nat. -/
namespace M6.Arithmetic.PA.InternalTrace
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

-- Sequence reasoning treats the exact row disjunction as an opaque formula.
attribute [local irreducible] StepFormula.formula

/-- Parameters: step count, three HFS vectors, and final control/left/right. -/
def prefixFormula : ArithmeticSemisentence 7 :=
  “n qs ls rs q l r.
    !lenDef (n+1) qs ∧ !lenDef (n+1) ls ∧ !lenDef (n+1) rs ∧
    !nthDef 0 qs 0 ∧ !nthDef 0 ls 0 ∧ !nthDef 0 rs 0 ∧
    !nthDef q qs n ∧ !nthDef l ls n ∧ !nthDef r rs n ∧
    ∀ i < n, ∃ a b c a' b' c',
      !nthDef a qs i ∧ !nthDef b ls i ∧ !nthDef c rs i ∧
      !nthDef a' qs (i+1) ∧ !nthDef b' ls (i+1) ∧
      !nthDef c' rs (i+1) ∧ !StepFormula.formula a b c a' b' c'”

/-- One-step concatenation uses precisely the same six-place step formula. -/
def extensionSentence : ArithmeticSentence :=
  “∀ n qs ls rs q l r q' l' r',
    !prefixFormula n qs ls rs q l r ∧ !StepFormula.formula q l r q' l' r' →
    ∃ qs' ls' rs', !prefixFormula (n+1) qs' ls' rs' q' l' r'”

def zeroSentence : ArithmeticSentence :=
  “∃ qs ls rs, !prefixFormula 0 qs ls rs 0 0 0”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Step (q l r q' l' r' : V) : Prop :=
  V ⊧/![q,l,r,q',l',r'] StepFormula.formula

def Prefix (n qs ls rs q l r : V) : Prop :=
  len qs = n+1 ∧ len ls = n+1 ∧ len rs = n+1 ∧
  nth qs 0 = 0 ∧ nth ls 0 = 0 ∧ nth rs 0 = 0 ∧
  nth qs n = q ∧ nth ls n = l ∧ nth rs n = r ∧
  ∀ i < n, Step (nth qs i) (nth ls i) (nth rs i)
    (nth qs (i+1)) (nth ls (i+1)) (nth rs (i+1))

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma step_vector (b : Fin 6 → V) :
    (V ⊧/b StepFormula.formula) ↔ Step (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) := by
  have hb : b = ![b 0,b 1,b 2,b 3,b 4,b 5] := by
    simp [funext_iff,Fin.forall_fin_succ]
  unfold Step
  exact iff_of_eq (congrArg (fun v => (V ⊧/v StepFormula.formula)) hb)

attribute [local irreducible] Step

lemma prefix_correct (b : Fin 7 → V) :
    (V ⊧/b prefixFormula) ↔ Prefix (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) := by
  simp only [prefixFormula]
  simp [Prefix, nth_defined.df, len_defined.df, step_vector, eq_comm]

lemma prefix_zero : Prefix (0 : V) ?[0] ?[0] ?[0] 0 0 0 := by
  simp [Prefix]

lemma prefix_extend {n qs ls rs q l r q' l' r' : V}
    (h : Prefix n qs ls rs q l r) (hs : Step q l r q' l' r') :
    Prefix (n+1) (concat qs q') (concat ls l') (concat rs r') q' l' r' := by
  rcases h with ⟨hq,hl,hr,hq0,hl0,hr0,hqn,hln,hrn,hsteps⟩
  have zero_lt : (0 : V) < n+1 := by simp
  have oldq {i : V} (hi : i < n+1) : nth (concat qs q') i = nth qs i :=
    concat_nth_lt qs q' (by simpa [hq] using hi)
  have oldl {i : V} (hi : i < n+1) : nth (concat ls l') i = nth ls i :=
    concat_nth_lt ls l' (by simpa [hl] using hi)
  have oldr {i : V} (hi : i < n+1) : nth (concat rs r') i = nth rs i :=
    concat_nth_lt rs r' (by simpa [hr] using hi)
  have newq := concat_nth_len' qs q' hq
  have newl := concat_nth_len' ls l' hl
  have newr := concat_nth_len' rs r' hr
  refine ⟨by simp [hq],by simp [hl],by simp [hr],
    (oldq zero_lt).trans hq0,(oldl zero_lt).trans hl0,(oldr zero_lt).trans hr0,
    newq,newl,newr,?_⟩
  intro i hi
  rcases eq_or_lt_of_le (lt_succ_iff_le.mp hi) with rfl | hi'
  · simpa only [oldq hi,oldl hi,oldr hi,newq,newl,newr,hqn,hln,hrn] using hs
  · have his : i+1 < n+1 := by simpa using hi'
    simpa only [oldq hi,oldl hi,oldr hi,oldq his,oldl his,oldr his] using hsteps i hi'

end Models

/-- A genuine derivability theorem in ordinary PA, including nonstandard models. -/
theorem pa_proves_extension : theory ⊢ extensionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [extensionSentence, models_iff]
  simp [prefix_correct, step_vector]
  intro n qs ls rs q l r q' l' r' h hs
  exact ⟨concat qs q',concat ls l',concat rs r',prefix_extend h hs⟩

theorem pa_proves_zero : theory ⊢ zeroSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [zeroSentence,models_iff]
  simp [prefix_correct]
  exact ⟨?[0],?[0],?[0],prefix_zero⟩

#print axioms pa_proves_extension
#print axioms pa_proves_zero
end M6.Arithmetic.PA.InternalTrace

