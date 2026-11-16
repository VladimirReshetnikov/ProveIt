module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualProofCodeSound
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration

private theorem bind_some {α β : Type} {o : Option α} {f : α → Option β} {b : β}
    (h : o.bind f = some b) : ∃ a, o=some a ∧ f a=some b := by
  cases o with
  | none => cases h
  | some a => exact ⟨a,rfl,h⟩

theorem unpack2_bounds (n a b : Nat) (h : unpack2 n = some (a,b)) : a≤n ∧ b≤n := by
  unfold unpack2 at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨(decode_bounds n).1,Nat.le_trans (decode_bounds (decode n).2).1 (decode_bounds n).2⟩
  · cases h

theorem unpack3_bounds (n a b c : Nat) (h : unpack3 n = some (a,b,c)) :
    a≤n ∧ b≤n ∧ c≤n := by
  unfold unpack3 at h
  obtain ⟨⟨y,z⟩,hy,h⟩ := bind_some h
  have hb := unpack2_bounds _ y z hy
  cases h
  exact ⟨(decode_bounds n).1,Nat.le_trans hb.1 (decode_bounds n).2,
    Nat.le_trans hb.2 (decode_bounds n).2⟩

/-- Every recursive child queried by a rule is bounded by its payload code. -/
theorem ruleCheck_congr (rec rec' : Nat → Option Nat) (tag data : Nat)
    (hr : ∀ k, k≤data → rec k=rec' k) : ruleCheck rec tag data = ruleCheck rec' tag data := by
  unfold ruleCheck
  split
  · cases hv : unpack3 data with
    | none => simp
    | some v =>
      rcases v with ⟨b,p,q⟩
      have hb := unpack3_bounds data b p q hv
      simp [hr p hb.2.1,hr q hb.2.2]
  · cases hv : unpack2 data with
    | none => simp
    | some v =>
      rcases v with ⟨a,p⟩
      have hb := unpack2_bounds data a p hv
      simp [hr p hb.2]
  all_goals rfl

#print axioms unpack3_bounds
#print axioms ruleCheck_congr
end M6.PA.NativeCalculus.ActualBasis.Code

