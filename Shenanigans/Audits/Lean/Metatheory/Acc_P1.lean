/-
P1: baseline behaviour of Acc.rec (large elimination) under definitional
proof irrelevance.
-/

universe u v
set_option linter.unusedVariables false

section Basic

-- 1.1 proof irrelevance for Acc itself
example {α : Sort u} (r : α → α → Prop) (x : α) (h₁ h₂ : Acc r x) : h₁ = h₂ := rfl

-- 1.2 large elimination: Acc.rec into Type
noncomputable def accK {α : Sort u} {r : α → α → Prop} {x : α} (h : Acc r x) : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun _ _ _ => 0) h

-- 1.3 Is the *algorithmic* defeq a congruence?  Two stuck recursor apps.
example {α : Sort u} (r : α → α → Prop) (x : α) (h₁ h₂ : Acc r x) :
    accK h₁ = accK h₂ := rfl

end Basic

/-! ## A concrete well-founded relation with a genuinely recursive motive -/

def R (a b : Nat) : Prop := a + 1 = b

theorem Racc : ∀ n, Acc R n
  | 0     => Acc.intro 0 (fun y hy =>
      absurd (show y + 1 = 0 from hy) (Nat.succ_ne_zero y))
  | n + 1 => Acc.intro (n + 1) (fun y hy => by
      have h : y = n := Nat.add_right_cancel (show y + 1 = n + 1 from hy)
      subst h; exact Racc y)

/-- counts the length of the R-descending chain below `x`, by Acc.rec -/
noncomputable def cnt : {x : Nat} → Acc R x → Nat := fun {x} h =>
  Acc.rec (motive := fun _ _ => Nat)
    (fun x _ ih =>
      Nat.casesOn (motive := fun z => ((y : Nat) → R y z → Nat) → Nat) x
        (fun _ => 0)
        (fun k f => (f k rfl) + 1)
        (fun y hy => ih y hy))
    h

-- 2.1 does it compute on a real proof?
example : cnt (Racc 5) = 5 := rfl

-- 2.2 opaque proof: stuck?  (expect FAILURE of rfl)
example (h : Acc R 5) : cnt h = 5 := rfl

-- 2.3 but it *is* provable propositionally, from proof irrelevance
example (h : Acc R 5) : cnt h = 5 :=
  (congrArg (@cnt 5) (proof_irrel h (Racc 5))).trans rfl

-- 2.4 opaque vs. concrete, by rfl (expect FAILURE)
example (h : Acc R 5) : cnt h = cnt (Racc 5) := rfl

-- 2.5 two opaque proofs (expect SUCCESS via is_def_eq_app + proof irrel)
example (h₁ h₂ : Acc R 5) : cnt h₁ = cnt h₂ := rfl

-- 2.6 eta-expanded proof: Acc.intro rebuilt from an opaque h
example (h : Acc R 5) : cnt h = cnt (Acc.intro 5 (fun y hy => Acc.inv h hy)) := rfl

-- 2.7 the reverse orientation of 2.6
example (h : Acc R 5) : cnt (Acc.intro 5 (fun y hy => Acc.inv h hy)) = cnt h := rfl
