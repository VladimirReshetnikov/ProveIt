module
public import M6PA.Model.PATheory
public import M6PA.Model.InternalCodedSourceTable
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
attribute [local irreducible] program selectGraph selectValue

def stepGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y c. ∃ pc xs, !fstIdxDef pc c ∧ !sndIdxDef xs c ∧
    (((pc=0 ∨ pc=3948) ∧ y=c) ∨
     (pc≠0 ∧ pc≠3948 ∧ !(selectGraph 1 program) y pc xs))”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def stepValue (c : V) : V :=
  if control c=0 ∨ control c=3948 then c else selectValue 1 program (control c) (store c)

def ValidState (c : V) : Prop := ValidStore (store c) ∧ control c<3948

instance step_defined : 𝚺ᴬ₁-Function₁ (stepValue : V → V) via stepGraph := by
  exact .mk fun v => by
    simp [stepGraph,fstIdx_defined.df,sndIdx_defined.df,(select_defined 1 program).df,
      stepValue,control,store,numeral_eq_natCast,Nat.cast_ofNat]
    split_ifs <;> aesop

@[simp] theorem step_halted (xs : V) : stepValue (stateCode 0 xs)=stateCode 0 xs := by
  simp [stepValue]
@[simp] theorem step_malformed (xs : V) : stepValue (stateCode 3948 xs)=stateCode 3948 xs := by
  simp [stepValue]

theorem step_at (i : Nat) (hi : i<3947) (xs : V) :
    stepValue (stateCode ((i+1 : Nat) : V) xs)=
      optionValue (Source.resolveAt Source.exactSites i) xs := by
  have hz : ((i+1 : Nat) : V)≠0 := by exact_mod_cast (show i+1≠0 by omega)
  have hm : ((i+1 : Nat) : V)≠3948 := by exact_mod_cast (show i+1≠3948 by omega)
  simp only [stepValue,control_state,store_state,hz,hm,or_self,ite_false]
  exact select_program i hi xs

lemma destination_code_bound (n : Option Nat) (h : DestinationBound 3947 n) :
    destinationCode n<3948 := by
  cases n with
  | none => decide
  | some i => have hi := h i rfl; simp only [destinationCode]; omega

lemma instruction_control_bound (i : Source.Instruction) (hi : InstructionBound 3947 i) (xs : V) :
    control (instructionValue i xs)<3948 := by
  cases i with
  | inc r n =>
    simp only [instructionValue,control_state]
    exact_mod_cast destination_code_bound n hi
  | dec r z n =>
    simp only [instructionValue]
    split_ifs <;> simp only [control_state]
    · exact_mod_cast destination_code_bound z hi.1
    · exact_mod_cast destination_code_bound n hi.2
  | jump n =>
    simp only [instructionValue,control_state]
    exact_mod_cast destination_code_bound n hi
  | halt =>
    simp only [instructionValue,control_state]
    exact_mod_cast (show 0<3948 from by decide)

/-- Valid source controls cannot escape into the distinct malformed sentinel.
The finite numeral bound is used explicitly even in nonstandard models. -/
theorem step_valid (c : V) (h : ValidState c) : ValidState (stepValue c) := by
  by_cases hz : control c=0
  · simpa only [stepValue,hz,true_or,ite_true] using h
  · have hm : control c≠3948 := ne_of_lt h.2
    have hn : control c<ORingStructure.numeral 3948 := by
      simpa only [numeral_eq_natCast,Nat.cast_ofNat] using h.2
    obtain ⟨j,hj,he⟩ := iff_lt_numeral_exists_numeral.mp hn
    have hjz : j≠0 := by intro hjz; subst j; simp at he; exact hz he
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjz
    have hi : i<3947 := by omega
    have he' : control c=((i+1 : Nat) : V) := by simpa only [numeral_eq_natCast] using he
    obtain ⟨inst,hr⟩ := literal_resolved i hi
    have hv : stepValue c=instructionValue inst (store c) := by
      rw [stepValue,if_neg (not_or_intro hz hm),he',select_program i hi,hr]
      rfl
    rw [hv]
    exact ⟨instruction_store_valid inst (store c) h.1,
      instruction_control_bound inst (literal_instruction_bound i inst hr) (store c)⟩

theorem step_total_unique (c : V) : ∃! y, V ⊧/![y,c] stepGraph.val := by
  refine ⟨stepValue c,?_,?_⟩
  · exact (step_defined.df _).mpr rfl
  · intro y hy; exact (step_defined.df _).mp hy
end Models
#print axioms step_defined
#print axioms step_at
#print axioms step_valid
#print axioms step_total_unique
end M6.Arithmetic.PA.InternalTrace.CodedSource

