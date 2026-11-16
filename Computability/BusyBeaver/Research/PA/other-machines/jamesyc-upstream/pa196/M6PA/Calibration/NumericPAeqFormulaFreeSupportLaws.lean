module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaFreeSupport
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language

def FreeSupported (l p : V) : Prop := IsUFormula L p ∧ freeBound p≤l
noncomputable def freeSupportedGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “l p. !((isUFormula L).sigma) p ∧ ∃ b, !freeBoundGraph b p ∧ b≤l”
theorem freeSupported_graph (l p : V) : freeSupportedGraph.val.Evalb ![l,p] ↔ FreeSupported l p := by
  simp [freeSupportedGraph,FreeSupported,freeBound_defined.df,Matrix.comp_vecCons'']

theorem freeSupported_rel {l k r ts : V} (hr : Presentation.language.IsRel k r) (ht : IsUTermVec L k ts) :
    FreeSupported l (qqRel k r ts) ↔ ∀ i<k, NumericPAeqTerm.FreeSupported l (nth ts i) := by
  simp only [FreeSupported,IsUFormula.rel,hr,ht,true_and,freeBound_rel hr ht]
  constructor
  · intro h i hi
    exact ⟨ht.nth hi,by simpa only [NumericPAeqTerm.freeBoundVec_nth ht hi] using
      listMaxss_le_iff.mp h i (by simpa [ht] using hi)⟩
  · intro h; apply listMaxss_le_iff.mpr
    intro i hi
    have hi' : i<k := by simpa [ht] using hi
    simpa only [NumericPAeqTerm.freeBoundVec_nth ht hi'] using (h i hi').2

theorem freeSupported_nrel {l k r ts : V} (hr : Presentation.language.IsRel k r) (ht : IsUTermVec L k ts) :
    FreeSupported l (qqNRel k r ts) ↔ ∀ i<k, NumericPAeqTerm.FreeSupported l (nth ts i) := by
  simpa only [FreeSupported,IsUFormula.rel,IsUFormula.nrel,hr,ht,true_and,freeBound_rel hr ht,freeBound_nrel hr ht] using freeSupported_rel (l:=l) hr ht
@[simp] theorem freeSupported_verum (l : V) : FreeSupported l qqVerum := by simp [FreeSupported]
@[simp] theorem freeSupported_falsum (l : V) : FreeSupported l qqFalsum := by simp [FreeSupported]
theorem freeSupported_and {l p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    FreeSupported l (qqAnd p q) ↔ FreeSupported l p ∧ FreeSupported l q := by
  simp [FreeSupported,hp,hq,max_le_iff]
theorem freeSupported_or {l p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    FreeSupported l (qqOr p q) ↔ FreeSupported l p ∧ FreeSupported l q := by
  simp [FreeSupported,hp,hq,max_le_iff]
theorem freeSupported_all {l p : V} (hp : IsUFormula L p) :
    FreeSupported l (qqAll p) ↔ FreeSupported l p := by simp [FreeSupported,hp]
theorem freeSupported_exs {l p : V} (hp : IsUFormula L p) :
    FreeSupported l (qqExs p) ↔ FreeSupported l p := by simp [FreeSupported,hp]

theorem freeBound_le_code {p : V} (hp : IsUFormula L p) : freeBound p≤p := by
  apply IsSemiformula.induction1 𝚺 (P:=fun (_ p : V) => freeBound p≤p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp.isSemiformula
  · definability
  · intro n k r ts hr ht
    rw [freeBound_rel hr ht.isUTerm]
    apply listMaxss_le_iff.mpr
    intro i hi
    have hi' : i<k := by simpa [ht.isUTerm] using hi
    rw [NumericPAeqTerm.freeBoundVec_nth ht.isUTerm hi']
    exact le_trans (NumericPAeqTerm.freeBound_le_code (ht.nth hi').isUTerm) (nth_lt_qqRel_of_lt (by simpa [ht.lh] using hi')).le
  · intro n k r ts hr ht
    rw [freeBound_nrel hr ht.isUTerm]
    apply listMaxss_le_iff.mpr
    intro i hi
    have hi' : i<k := by simpa [ht.isUTerm] using hi
    rw [NumericPAeqTerm.freeBoundVec_nth ht.isUTerm hi']
    exact le_trans (NumericPAeqTerm.freeBound_le_code (ht.nth hi').isUTerm) (nth_lt_qqNRel_of_lt (by simpa [ht.lh] using hi')).le
  · intro n; simp
  · intro n; simp
  · intro n p q hp hq ihp ihq
    rw [freeBound_and hp.isUFormula hq.isUFormula]
    exact max_le (le_trans ihp (lt_K!_left p q).le) (le_trans ihq (lt_K!_right p q).le)
  · intro n p q hp hq ihp ihq
    rw [freeBound_or hp.isUFormula hq.isUFormula]
    exact max_le (le_trans ihp (lt_or_left p q).le) (le_trans ihq (lt_or_right p q).le)
  · intro n p hp ih
    rw [freeBound_all hp.isUFormula]; exact le_trans ih (lt_forall p).le
  · intro n p hp ih
    rw [freeBound_ex hp.isUFormula]; exact le_trans ih (lt_exists p).le

theorem freeSupported_of_code {l p : V} (hp : IsUFormula L p) (hb : p≤l) : FreeSupported l p :=
  ⟨hp,le_trans (freeBound_le_code hp) hb⟩
#print axioms freeSupported_graph
#print axioms freeSupported_rel
#print axioms freeSupported_all
#print axioms freeBound_le_code
end M6.PA.NumericPAeqFormula

