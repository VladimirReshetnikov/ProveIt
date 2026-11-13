module
public import PA196.Program
public import PA196.Program
public import PA196.Arithmetic.Machine.PATheory
public import PA196.Arithmetic.Machine.InternalCodedSourceInstruction
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource
open M6 PA196.Arithmetic.Machine.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def optionGraph : Option Source.Instruction → 𝚺ᴬ₁.Semisentence 2
  | none => .mkSigma “y xs. !adjoinDef y 3813 xs”
  | some i => instructionGraph i

def selectGraph : Nat → List (Option Source.Instruction) → 𝚺ᴬ₁.Semisentence 3
  | _,[] => .mkSigma “y pc xs. !adjoinDef y 3813 xs”
  | b,i::is => .mkSigma “y pc xs.
      (pc=↑b ∧ !(optionGraph i) y xs) ∨
      (pc≠↑b ∧ !(selectGraph (b+1) is) y pc xs)”

/-- Literal resolved table, not generated alternative instructions. -/
def program : List (Option Source.Instruction) :=
  (List.range 3812).map (Source.resolveAt PA196.Program.sites)

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def optionValue : Option Source.Instruction → V → V
  | none,xs => stateCode 3813 xs
  | some i,xs => instructionValue i xs
noncomputable def selectValue : Nat → List (Option Source.Instruction) → V → V → V
  | _,[],_,xs => stateCode 3813 xs
  | b,i::is,pc,xs => if pc=(b : V) then optionValue i xs else selectValue (b+1) is pc xs

instance option_defined (i : Option Source.Instruction) :
    𝚺ᴬ₁-Function₁ (optionValue i : V → V) via optionGraph i := by
  cases i with
  | none => exact .mk fun v => by simp [optionGraph,optionValue,stateCode,adjoin_defined.df,numeral_eq_natCast,Nat.cast_ofNat]
  | some i => exact instruction_defined i

instance select_defined (b : Nat) (is : List (Option Source.Instruction)) :
    𝚺ᴬ₁-Function₂ (selectValue b is : V → V → V) via selectGraph b is := by
  induction is generalizing b with
  | nil => exact .mk fun v => by simp [selectGraph,selectValue,stateCode,adjoin_defined.df,numeral_eq_natCast,Nat.cast_ofNat]
  | cons i is ih =>
    exact .mk fun v => by
      simp [selectGraph,(option_defined i).df,(ih (b+1)).df,selectValue,numeral_eq_natCast]
      split_ifs <;> simp_all

theorem select_store_valid (b : Nat) (is : List (Option Source.Instruction))
    (pc xs : V) (h : ValidStore xs) : ValidStore (store (selectValue b is pc xs)) := by
  induction is generalizing b with
  | nil => simpa only [selectValue,store_state] using h
  | cons i is ih =>
    simp only [selectValue]
    split_ifs
    · cases i with
      | none => simpa only [optionValue,store_state] using h
      | some i => exact instruction_store_valid i xs h
    · exact ih (b+1)

/-- Numeral control selects exactly its literal table row in every PA model. -/
theorem select_at (b : Nat) (is : List (Option Source.Instruction)) (j : Nat)
    (hj : j<is.length) (xs : V) :
    selectValue b is ((b+j : Nat) : V) xs=optionValue is[j] xs := by
  induction is generalizing b j with
  | nil => simp at hj
  | cons i is ih =>
    cases j with
    | zero => simp [selectValue]
    | succ j =>
      have he : b+(j+1)=(b+1)+j := by omega
      have hn : ((b+(j+1) : Nat) : V)≠(b : V) := by
        intro h
        have he := Nat.cast_inj.mp h
        omega
      simp only [selectValue,hn,ite_false,List.getElem_cons_succ]
      rw [he]
      exact ih (b+1) j (by simpa using hj)

lemma program_length : program.length=3812 := by simp [program]

/-- Exact ordinal binding, with malformed lookup kept distinct from halt. -/
theorem select_program (i : Nat) (hi : i<3812) (xs : V) :
    selectValue 1 program ((i+1 : Nat) : V) xs=
      optionValue (Source.resolveAt PA196.Program.sites i) xs := by
  have h := select_at 1 program i (by simpa [program_length] using hi) xs
  simp only [program,List.getElem_map,List.getElem_range] at h
  simpa only [program,Nat.add_comm] using h
end Models
#print axioms select_defined
#print axioms select_store_valid
#print axioms select_program
end PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource

