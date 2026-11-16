module
public import PA196.Arithmetic.Machine.StateMapData
public import PA196.Arithmetic.Machine.PAInternalTraceCompose
@[expose] public section
namespace PA196.Arithmetic.Machine.StateMap
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def lookupGraph : List (Nat × Nat) → 𝚺ᴬ₁.Semisentence 2
  | [] => .mkSigma “y q. y=0”
  | (a,b)::rest => .mkSigma “y q.
      (q=↑a ∧ y=↑b) ∨ (q≠↑a ∧ !(lookupGraph rest) y q)”

def decodeGraph : 𝚺ᴬ₁.Semisentence 2 := lookupGraph inverseEntries

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def lookupValue : List (Nat × Nat) → V → V
  | [],_ => 0
  | (a,b)::rest,q => if q=(a : V) then (b : V) else lookupValue rest q

instance lookup_defined (entries : List (Nat × Nat)) :
    𝚺ᴬ₁-Function₁ (lookupValue entries : V → V) via lookupGraph entries := by
  induction entries with
  | nil => exact .mk fun v => by simp [lookupGraph,lookupValue]
  | cons p entries ih =>
    rcases p with ⟨a,b⟩
    exact .mk fun v => by
      simp [lookupGraph,ih.df,lookupValue,numeral_eq_natCast]
      split_ifs <;> simp_all

theorem lookup_cast (entries : List (Nat × Nat)) (n : Nat) :
    lookupValue entries (n : V)=(lookupNat entries n : V) := by
  induction entries with
  | nil => rfl
  | cons p entries ih =>
    rcases p with ⟨a,b⟩
    by_cases h : n=a
    · simp [lookupValue,lookupNat,h]
    · have h' : (n : V)≠(a : V) := by exact_mod_cast h
      simp [lookupValue,lookupNat,h,h',ih]

noncomputable def decodeTag (q : V) : V := lookupValue inverseEntries q

instance decode_defined : 𝚺ᴬ₁-Function₁ (decodeTag : V → V) via decodeGraph :=
  lookup_defined inverseEntries
instance decode_definable : 𝚺ᴬ₁-Function₁ (decodeTag : V → V) := decode_defined.to_definable
instance decode_definable' (Γ m) : Γᴬ_[m+1]-Function₁ (decodeTag : V → V) :=
  decode_definable.of_sigmaOne

theorem decode_cast (n : Nat) : decodeTag (n : V)=(literalIndex n : V) :=
  lookup_cast inverseEntries n

theorem decode_aux_control (c : Exact.Control) :
    decodeTag (PA.StepFormula.controlCode (auxControl c) : V)=
      (Exact.PA.StepFormula.controlCode c : V) := by
  rw [decode_cast,inverse_code]

@[simp] theorem decode_zero : decodeTag (0 : V)=0 := by
  simpa only [Nat.cast_zero,inverse_zero] using decode_cast (V:=V) 0
@[simp] theorem decode_halt : decodeTag (215 : V)=196 := by
  simpa only [Nat.cast_ofNat,inverse_halt] using decode_cast (V:=V) 215

def mapBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y=0”
  adjoin := .mkSigma “y x xs ih. ∃ a, !decodeGraph a x ∧ !adjoinDef y a ih”

noncomputable def mapConstruction : VecRec.Construction V mapBlueprint where
  nil _ := 0
  adjoin (_ x _ ih) := decodeTag x ∷ ih
  nil_defined := .mk fun v => by simp [mapBlueprint]
  adjoin_defined := .mk fun v => by simp [mapBlueprint,decode_defined.df,adjoin_defined.df]

noncomputable def mapVector (xs : V) : V := mapConstruction.result ![] xs
def mapGraph : 𝚺ᴬ₁.Semisentence 2 := mapBlueprint.resultDef

instance map_defined : 𝚺ᴬ₁-Function₁ (mapVector : V → V) via mapGraph :=
  mapConstruction.result_defined
instance map_definable : 𝚺ᴬ₁-Function₁ (mapVector : V → V) := map_defined.to_definable
instance map_definable' (Γ m) : Γᴬ_[m+1]-Function₁ (mapVector : V → V) :=
  map_definable.of_sigmaOne

@[simp] theorem map_nil : mapVector (0 : V)=0 := by simp [mapVector,mapConstruction]
@[simp] theorem map_cons (x xs : V) : mapVector (x ∷ xs)=decodeTag x ∷ mapVector xs := by
  simp [mapVector,mapConstruction]

@[simp] theorem map_length (xs : V) : len (mapVector xs)=len xs := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x xs ih => simp [ih]

theorem map_nth (xs : V) {i : V} (hi : i<len xs) :
    nth (mapVector xs) i=decodeTag (nth xs i) := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x xs ih =>
    rcases zero_or_succ i with rfl | ⟨i,rfl⟩
    · simp
    · simp [ih (by simpa using hi)]

end Models
#print axioms map_nth
#print axioms decode_aux_control
end PA196.Arithmetic.Machine.StateMap
