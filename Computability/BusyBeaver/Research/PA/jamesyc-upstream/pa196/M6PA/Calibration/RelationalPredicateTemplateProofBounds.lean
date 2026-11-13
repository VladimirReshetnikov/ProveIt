module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSequent
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def sequentFreeBound (Γ : LK.Sequent sourceLanguage) : Nat :=
  (Γ.map FFL.FirstOrder.Semiformula.fvSup).foldr max 0

theorem formula_fvSup_le_sequentFreeBound {Γ : LK.Sequent sourceLanguage} {p : Formula 0}
    (hp : p∈Γ) : p.fvSup≤sequentFreeBound Γ := by
  induction Γ using Multiset.induction_on with
  | empty => simp at hp
  | cons q Γ ih =>
    simp only [sequentFreeBound,Multiset.map_cons,Multiset.foldr_cons]
    rcases Multiset.mem_cons.mp hp with rfl | hp
    · exact Nat.le_max_left _ _
    · exact (ih hp).trans (Nat.le_max_right _ _)

def termFreeBound {s : Nat} : Term s → Nat
  | .bvar _ => 0
  | .fvar i => i+1
  | .func fn _ => nomatch fn

theorem term_fvar_lt_freeBound {s : Nat} (t : Term s) {i : Nat} (hi : t.FVar? i) :
    i<termFreeBound t := by
  cases t with
  | bvar j => simp at hi
  | fvar j =>
    have he : j=i := by simpa using hi
    subst i
    simp [termFreeBound]
  | func fn _ => nomatch fn

def proofFreeBound {Γ : LK.Sequent sourceLanguage} (d : LK.Derivation Γ) : Nat :=
  max (sequentFreeBound Γ) (match d with
    | .identity _ _ => 0
    | .cut dp dn => max (proofFreeBound dp) (proofFreeBound dn)
    | .contraction dp => proofFreeBound dp
    | .weakening dp => proofFreeBound dp
    | .verum => 0
    | .or dp => proofFreeBound dp
    | .and dp dq => max (proofFreeBound dp) (proofFreeBound dq)
    | .all dp => proofFreeBound dp
    | @LK.Derivation.exs _ _ _ t dp => max (termFreeBound t) (proofFreeBound dp))

theorem sequentFreeBound_le_proofFreeBound {Γ : LK.Sequent sourceLanguage} (d : LK.Derivation Γ) :
    sequentFreeBound Γ≤proofFreeBound d := by
  unfold proofFreeBound
  exact Nat.le_max_left _ _

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem sequentCovered_of_bound {Γ : LK.Sequent sourceLanguage} {f : V}
    (h : (sequentFreeBound Γ:V)≤len f) : SequentCovered Γ f := by
  intro p hp i hi
  have hin : i<sequentFreeBound Γ :=
    (FFL.FirstOrder.Semiformula.lt_fvSup_of_fvar? hi).trans_le (formula_fvSup_le_sequentFreeBound hp)
  exact (show (i:V)<(sequentFreeBound Γ:V) by exact_mod_cast hin).trans_le h
#print axioms term_fvar_lt_freeBound
#print axioms sequentCovered_of_bound
end M6.PA.RelationalPredicateTemplate
