import PA194RegisterFile
import M6.Runtime
set_option autoImplicit false
namespace PA194RegisterFileStandard
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194UnaryRuns
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem natAdd (x y : Nat) : F addCode ![x,y] = x+y := by
  change eval addCode (List.Vector.ofFn ![x,y]) = x+y
  rw [ofFn_two,eval_addCode]
  rfl

theorem natSucc (x : Nat) : F Code.succ (fun _ => x) = x+1 := by rfl

theorem natOne : F oneCode Fin.elim0 = (1 : Nat) := by rfl

def word : List Bool → Nat → Nat
  | [],t => t
  | b::bs,t => 2 * word bs t + b.toNat

theorem word_append (xs ys : List Bool) (t : Nat) :
    word (xs++ys) t = word xs (word ys t) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,word,ih]

theorem modelOnesNat (n t : Nat) : F ones ![n,t] = word (List.replicate n true) t := by
  induction n with
  | zero =>
    have h := modelOnesZero (M := Nat) t
    exact h
  | succ n ih =>
    have h := modelOnesSucc (M := Nat) n t
    change F ones ![F Code.succ (fun _ => n),t] =
      F addCode ![F addCode ![F ones ![n,t],F ones ![n,t]],F oneCode Fin.elim0] at h
    rw [natSucc,natAdd,natAdd,natOne] at h
    rw [h,ih]
    simp only [List.replicate_succ,word,Bool.toNat_true]
    omega

def valuesArg : (vs : List Nat) → Nat → Fin (vs.length+1) → Nat
  | [],t => fun _ => t
  | v::vs,t => Fin.cases v (valuesArg vs t)

theorem sourceFile (vs : List Nat) (t : Nat) :
    F (fileCode vs.length) (valuesArg vs t) = word (M6.Runtime.sepsR vs) t := by
  induction vs generalizing t with
  | nil =>
    have h := modelFileZero (M := Nat) t
    have he : (![t] : Fin 1 → Nat) = fun _ => t := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [he] at h
    simpa [M6.Runtime.sepsR,word,valuesArg] using h
  | cons v vs ih =>
    rw [M6.Runtime.sepsR]
    simp only [List.flatMap_cons]
    rw [word_append]
    simp only [word,Bool.toNat_false,add_zero,List.length_cons]
    rw [modelFileSucc]
    simp only [valuesArg,Fin.cases_zero,Fin.cases_succ]
    rw [modelBlock]
    rw [ih,modelOnesNat]
    change F addCode ![word (List.replicate (v+1) true) (word (M6.Runtime.sepsR vs) t),
      word (List.replicate (v+1) true) (word (M6.Runtime.sepsR vs) t)] = _
    rw [natAdd]
    simp only [M6.Runtime.sepsR]
    omega
/-- Trimming far-end blank cells preserves the binary number. -/
theorem word_trim (xs : List Bool) : word (M6.Zip.trim xs) 0 = word xs 0 := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    rw [M6.Zip.trim_cons]
    split
    · rename_i h
      obtain ⟨hb,ht⟩ := h
      subst b
      simp only [ht,word] at ih
      simp only [word,Bool.toNat_false,add_zero]
      omega
    · simp only [word,ih]

/-- Reading a nonempty tape side agrees with the low binary digit. -/
theorem word_head (b : Bool) (bs : List Bool) (t : Nat) :
    word (b::bs) t % 2 = b.toNat := by
  cases b <;> simp [word]

/-- Moving past the head of a nonempty side is binary division by two. -/
theorem word_tail (b : Bool) (bs : List Bool) (t : Nat) :
    word (b::bs) t / 2 = word bs t := by
  cases b <;> simp [word]; omega
#print axioms word_trim
#print axioms word_head
#print axioms word_tail
#print axioms modelOnesNat
#print axioms sourceFile
end PA194RegisterFileStandard
