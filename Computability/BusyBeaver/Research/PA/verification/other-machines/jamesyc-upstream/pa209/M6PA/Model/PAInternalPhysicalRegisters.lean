module
public import M6PA.Model.PAInternalFileEffects
public import M6PA.Model.PAInternalFileGuards
public import M6.Source.PhysicalRegisters
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.PhysicalRegisters
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open FileEffects FileLayout M6.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Pointwise update law at EVERY model-valued index, not only the first nine
registers. This preserves arbitrarily many nonstandard spare cells. -/
theorem nth_update : ∀ (r : Nat) (f : V → V) (xs i : V), (r : V)<len xs →
    (update r f xs).[i]=if i=(r : V) then f xs.[i] else xs.[i]
  | 0,f,xs,i,h => by
    rcases zero_or_succ i with hi | ⟨j,hj⟩
    · subst i
      simp [update,nth_zero]
    · subst i
      simp [update,nth_succ]
  | n+1,f,xs,i,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs; simp at h
    · subst xs
      have hn : (n : V)<len as := by
        simpa only [Nat.cast_add,Nat.cast_one,len_adjoin,add_lt_add_iff_right] using h
      rcases zero_or_succ i with hi | ⟨j,hj⟩
      · subst i
        simp [update]
      · subst i
        simpa only [update,fstIdx_adjoin,sndIdx_adjoin,nth_adjoin_succ,
          Nat.cast_add,Nat.cast_one,add_left_inj] using nth_update n f as j hn

noncomputable def readFile (xs : V) : Fin 9 → V :=
  fun r => xs.[(Source.physicalRegister r : V)]
noncomputable def write (f : Fin 9 → V) (r : Fin 9) (v : V) : Fin 9 → V :=
  fun s => if s=r then v else f s

lemma physical_eq (r s : Fin 9) :
    (Source.physicalRegister s : V)=(Source.physicalRegister r : V) ↔ s=r := by
  rw [Nat.cast_inj,Source.physicalRegister_injective]

/-- Increment updates exactly one logical register and appends one one-valued spare;
all pre-existing physical cells keep their correct full-model interpretation. -/
theorem read_increment (xs : V) (hsize : (10 : V)≤len xs) (r : Fin 9) :
    readFile (effect (.inc (Source.physicalRegister r)) xs)=
      write (readFile xs) r (readFile xs r+1) := by
  funext s
  have hr := FileBoxes.index_valid xs hsize (Source.physicalRegister r) (Source.physicalRegister_lt r)
  have hs := FileBoxes.index_valid xs hsize (Source.physicalRegister s) (Source.physicalRegister_lt s)
  simp only [readFile,write,effect]
  rw [concat_nth_lt _ _ (by simpa only [update_length _ _ _ hr] using hs)]
  rw [nth_update _ _ _ _ hr]
  simp only [physical_eq r s]
  split <;> simp_all

theorem read_decrement (xs : V) (hsize : (10 : V)≤len xs) (r : Fin 9) :
    readFile (effect (.dec (Source.physicalRegister r)) xs)=
      write (readFile xs) r (readFile xs r-1) := by
  funext s
  have hr := FileBoxes.index_valid xs hsize (Source.physicalRegister r) (Source.physicalRegister_lt r)
  simp only [readFile,write,effect]
  rw [nth_update _ _ _ _ hr]
  simp only [physical_eq r s]
  split <;> simp_all

/-- All original cells, including arbitrary model-valued spare indices, obey
the exact update equation; the appended final cell is separate. -/
theorem increment_cell (xs : V) (r : Nat) (hr : (r : V)<len xs) (i : V) (hi : i<len xs) :
    (effect (.inc r) xs).[i]=if i=(r : V) then xs.[i]+1 else xs.[i] := by
  unfold effect
  rw [concat_nth_lt _ _ (by simpa only [update_length _ _ _ hr] using hi),nth_update _ _ _ _ hr]

theorem increment_spare (xs : V) (r : Nat) (hr : (r : V)<len xs) :
    (effect (.inc r) xs).[len xs]=1 := by
  simp only [effect]
  exact concat_nth_len' _ _ (update_length r (·+1) xs hr)
end Models
#print axioms nth_update
#print axioms read_increment
#print axioms read_decrement
#print axioms increment_cell
#print axioms increment_spare
end M6.Arithmetic.PA.InternalTrace.PhysicalRegisters

