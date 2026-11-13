module
public import M6PA.Model.PATheory
public import M6PA.Model.PAInternalPhysicalRegisters
public import M6PA.Model.PAInternalFileGraphs
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.CodedSource
open M6 M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Replacement graph for a fixed logical register, not a physical file index. -/
def replaceGraph : Nat → 𝚺ᴬ₁.Semisentence 3
  | 0 => .mkSigma “y xs v. ∃ s, !sndIdxDef s xs ∧ !adjoinDef y v s”
  | n+1 => .mkSigma “y xs v. ∃ a s t, !fstIdxDef a xs ∧ !sndIdxDef s xs ∧
      !(replaceGraph n) t s v ∧ !adjoinDef y a t”
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def replace : Nat → V → V → V
  | 0,xs,v => v ∷ sndIdx xs
  | n+1,xs,v => fstIdx xs ∷ replace n (sndIdx xs) v

lemma replace_update (r : Nat) (xs v : V) :
    replace r xs v=FileEffects.update r (fun _ => v) xs := by
  induction r generalizing xs with
  | zero => rfl
  | succ r ih => simp only [replace,FileEffects.update,ih]
noncomputable def registers (xs : V) : Fin 9 → V := fun r => xs.[(r.val : V)]
/-- Literal source state is the HFS vector [pc,N,T,W,A,D,H,X,Y,L].
This is not the four-field command codec or the complete physical file. -/
noncomputable def stateCode (pc regs : V) : V := pc ∷ regs
noncomputable def control (c : V) : V := fstIdx c
noncomputable def store (c : V) : V := sndIdx c

def ValidStore (xs : V) : Prop := len xs=9

instance replace_defined (r : Nat) : 𝚺ᴬ₁-Function₂ (replace r : V → V → V) via replaceGraph r := by
  induction r with
  | zero => exact .mk fun v => by simp [replaceGraph,replace,sndIdx_defined.df,adjoin_defined.df]
  | succ r ih => exact .mk fun v => by simp [replaceGraph,replace,fstIdx_defined.df,sndIdx_defined.df,
        ih.df,adjoin_defined.df]

lemma register_bound (xs : V) (h : ValidStore xs) (r : Fin 9) : (r.val : V)<len xs := by
  rw [h]
  exact_mod_cast r.isLt

lemma replace_valid (xs v : V) (h : ValidStore xs) (r : Fin 9) :
    ValidStore (replace r.val xs v) := by
  unfold ValidStore
  rw [replace_update]
  rw [FileEffects.update_length _ _ _ (register_bound xs h r)]
  exact h

lemma registers_replace (xs v : V) (h : ValidStore xs) (r : Fin 9) :
    registers (replace r.val xs v)=PhysicalRegisters.write (registers xs) r v := by
  funext s
  simp only [registers,replace_update,PhysicalRegisters.write]
  rw [PhysicalRegisters.nth_update _ _ _ _ (register_bound xs h r)]
  have he : (s.val : V)=(r.val : V) ↔ s=r := by simp only [Nat.cast_inj,Fin.val_inj]
  simp only [he]

@[simp] theorem control_state (pc regs : V) : control (stateCode pc regs)=pc := by
  simp [control,stateCode]
@[simp] theorem store_state (pc regs : V) : store (stateCode pc regs)=regs := by
  simp [store,stateCode]
lemma state_length (pc regs : V) (h : ValidStore regs) : len (stateCode pc regs)=10 := by
  simp only [stateCode,len_adjoin,show len regs=9 from h]
  simp only [show (9 : V)+1=10 by rfl]
end Models
#print axioms replace_defined
#print axioms replace_valid
#print axioms registers_replace
#print axioms state_length
end M6.Arithmetic.PA.InternalTrace.CodedSource

