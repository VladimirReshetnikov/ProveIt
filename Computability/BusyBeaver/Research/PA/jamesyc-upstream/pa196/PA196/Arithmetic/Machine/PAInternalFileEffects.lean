module
public import PA196.Arithmetic.Machine.PAInternalFileGraphs
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.FileEffects
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits CarryCode FileLayout M6.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Exact binary meaning of model-valued HFS append, proved by definable
arithmetic induction, including nonstandard-length files. -/
theorem right_concat (xs z t : V) :
    rightFile (concat xs z) t=rightFile xs (4*repeatBits z 1 t+2) := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin a xs ih => simp only [concat_adjoin,right_adjoin,ih]

/-- Updating a fixed syntactic physical register preserves every other HFS
cell; later the length premise rules out out-of-range synthetic padding. -/
noncomputable def update (r : Nat) (f : V → V) (xs : V) : V :=
  match r with
  | 0 => f (fstIdx xs) ∷ sndIdx xs
  | n+1 => fstIdx xs ∷ update n f (sndIdx xs)

noncomputable def effect : Eff → V → V
  | .none,xs => xs
  | .inc r,xs => concat (update r (·+1) xs) 1
  | .dec r,xs => update r (·-1) xs

theorem right_update : ∀ (r : Nat) (f : V → V) (xs t : V),
    rightFile (update r f xs) t=rightFile (front r xs)
      (4*repeatBits (f (value r xs)) 1 (rightFile (suffix r xs) t)+2)
  | 0,f,xs,t => by simp [update,front,value,suffix,drop]
  | n+1,f,xs,t => by
    simp only [update,front,value,suffix,drop,right_adjoin]
    rw [right_update n f (sndIdx xs) t]
    rfl

/-- The uniform box interpretation is exactly the whole updated file,
including the append-one spare cell on increment. -/
theorem box_effect (xs : V) (e : Eff) (t : V) :
    FileBoxes.box xs (.plain e) t=rightFile (effect e xs) t := by
  cases e with
  | none => rfl
  | inc r =>
    simp only [effect,right_concat,right_update,FileBoxes.box]
    have h : 4*repeatBits (1 : V) 1 t+2=8*t+6 := by
      rw [show (1 : V)=0+1 by simp,repeat_succ,repeat_zero]
      ring1
    rw [h]
  | dec r => simp only [effect,right_update,FileBoxes.box]

/-- The complete suffix beyond the changed register is preserved. -/
theorem update_drop : ∀ (r : Nat) (f : V → V) (xs : V),
    drop (r+1) (update r f xs)=suffix r xs
  | 0,f,xs => by simp [drop,update,suffix]
  | n+1,f,xs => by
    simpa only [update,drop,sndIdx_adjoin,suffix] using update_drop n f (sndIdx xs)

/-- Original length is preserved by an in-range update. -/
theorem update_length : ∀ (r : Nat) (f : V → V) (xs : V), (r : V)<len xs →
    len (update r f xs)=len xs
  | 0,f,xs,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs; simp at h
    · simp [ha,update]
  | n+1,f,xs,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs; simp at h
    · subst xs
      have hn : (n : V)<len as := by
        simpa only [Nat.cast_add,Nat.cast_one,len_adjoin,add_lt_add_iff_right] using h
      simp only [update,fstIdx_adjoin,sndIdx_adjoin,len_adjoin,update_length n f as hn]
end Models
#print axioms right_concat
#print axioms box_effect
#print axioms update_drop
#print axioms update_length
end PA196.Arithmetic.Machine.PA.InternalTrace.FileEffects

