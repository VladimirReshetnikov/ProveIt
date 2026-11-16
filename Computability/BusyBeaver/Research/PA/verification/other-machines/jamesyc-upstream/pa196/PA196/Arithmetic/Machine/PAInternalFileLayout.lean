module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalMarkAll
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.FileLayout
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Standard bounded register index; all stored values and the residual HFS
vector are arbitrary elements of the arithmetic model. -/
noncomputable def drop : Nat → V → V
  | 0,xs => xs
  | n+1,xs => drop n (sndIdx xs)
noncomputable def front : Nat → V → V
  | 0,_ => 0
  | n+1,xs => fstIdx xs ∷ front n (sndIdx xs)
noncomputable def value (r : Nat) (xs : V) : V := fstIdx (drop r xs)
noncomputable def suffix (r : Nat) (xs : V) : V := sndIdx (drop r xs)

theorem prefix_length : ∀ (r : Nat) (xs : V), (r : V)≤len xs → len (front r xs)=(r : V)
  | 0,xs,_ => by simp [front]
  | n+1,xs,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs
      simp only [len_nil,Nat.cast_add,Nat.cast_one] at h
      exact False.elim ((not_le_of_gt (by simp : (0 : V)<(n : V)+1)) h)
    · subst xs
      have hn : (n : V)≤len as := by
        simpa only [Nat.cast_add,Nat.cast_one,len_adjoin,add_le_add_iff_right] using h
      simp only [front,fstIdx_adjoin,sndIdx_adjoin,len_adjoin,prefix_length n as hn,
        Nat.cast_add,Nat.cast_one]

theorem split_right : ∀ (r : Nat) (xs t : V), (r : V)≤len xs →
    CarryCode.rightFile xs t=CarryCode.rightFile (front r xs) (CarryCode.rightFile (drop r xs) t)
  | 0,xs,t,_ => by simp [front,drop]
  | n+1,xs,t,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs
      simp only [len_nil,Nat.cast_add,Nat.cast_one] at h
      exact False.elim ((not_le_of_gt (by simp : (0 : V)<(n : V)+1)) h)
    · subst xs
      have hn : (n : V)≤len as := by
        simpa only [Nat.cast_add,Nat.cast_one,len_adjoin,add_le_add_iff_right] using h
      simp only [front,drop,fstIdx_adjoin,sndIdx_adjoin,CarryCode.right_adjoin]
      rw [split_right n as t hn]

theorem drop_length : ∀ (r : Nat) (xs : V), (r : V)≤len xs →
    (r : V)+len (drop r xs)=len xs
  | 0,xs,_ => by simp [drop]
  | n+1,xs,h => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · subst xs
      simp only [len_nil,Nat.cast_add,Nat.cast_one] at h
      exact False.elim ((not_le_of_gt (by simp : (0 : V)<(n : V)+1)) h)
    · subst xs
      have hn : (n : V)≤len as := by
        simpa only [Nat.cast_add,Nat.cast_one,len_adjoin,add_le_add_iff_right] using h
      simp only [drop,sndIdx_adjoin,len_adjoin,Nat.cast_add,Nat.cast_one]
      calc
        (n : V)+1+len (drop n as)=((n : V)+len (drop n as))+1 := by ring1
        _=len as+1 := by rw [drop_length n as hn]

theorem selected (r : Nat) (xs : V) (h : (r : V)<len xs) :
    drop r xs=value r xs ∷ suffix r xs := by
  have hl := drop_length r xs (le_of_lt h)
  rcases nil_or_adjoin (drop r xs) with hz | ⟨a,as,ha⟩
  · rw [hz,len_nil,add_zero] at hl
    exact False.elim ((ne_of_lt h) hl)
  · simp only [value,suffix,ha,fstIdx_adjoin,sndIdx_adjoin]

theorem value_nth : ∀ (r : Nat) (xs : V), value r xs=xs.[(r : V)]
  | 0,xs => by simp [value,drop,nth_zero]
  | n+1,xs => by
    simpa only [value,drop,Nat.cast_add,Nat.cast_one,nth_succ] using value_nth n (sndIdx xs)

/-- The complete marked/unmarked decomposition, preserving the entire suffix. -/
theorem input_split (r : Nat) (xs t : V) (h : (r : V)<len xs) :
    CarryCode.rightFile xs t=CarryCode.rightFile (front r xs)
      (4*ScanBits.repeatBits (value r xs) 1 (CarryCode.rightFile (suffix r xs) t)+2) := by
  rw [split_right r xs t (le_of_lt h),selected r xs h,CarryCode.right_adjoin]
end Models
#print axioms prefix_length
#print axioms input_split
#print axioms value_nth
end PA196.Arithmetic.Machine.PA.InternalTrace.FileLayout

