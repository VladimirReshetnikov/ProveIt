import Init

/-!
A standalone semantic-interface check for deleting two unused inductions.
The carrier and its natural-number predicate are arbitrary: there is no
identification with Lean Nat and no induction principle among the hypotheses.
This checks the abstract argument, not the repository-dependent adapters.
-/
namespace InternalZeroCore
universe u

structure ArithmeticAPI (V : Type u) where
  IsNat : V → Prop
  zero : V
  succ : V → V
  AddRel : V → V → V → Prop
  MulRel : V → V → V → Prop
  addValue : V → V → V
  zeroNat : IsNat zero
  zeroOrSucc : ∀ y, IsNat y → y = zero ∨ ∃ n, IsNat n ∧ y = succ n
  succNeZero : ∀ n, succ n ≠ zero
  addLeft : ∀ {x y z}, AddRel x y z → IsNat x
  addRight : ∀ {x y z}, AddRel x y z → IsNat y
  addTotal : ∀ {x y}, IsNat x → IsNat y → ∃ z, AddRel x y z
  addUnique : ∀ {x y z z'}, AddRel x y z → AddRel x y z' → z = z'
  addZero : ∀ {x}, IsNat x → AddRel x zero x
  addSucc : ∀ {x y z}, AddRel x y z → AddRel x (succ y) (succ z)
  addValueSpec : ∀ {x y}, IsNat x → IsNat y → AddRel x y (addValue x y)
  mulTotal : ∀ {x y}, IsNat x → IsNat y → ∃ z, MulRel x y z
  mulUnique : ∀ {x y z z'}, MulRel x y z → MulRel x y z' → z = z'
  mulZeroRight : ∀ {x}, IsNat x → MulRel x zero zero
  mulZeroLeft : ∀ {y}, IsNat y → MulRel zero y zero
  mulSucc : ∀ {x y z}, MulRel x y z → MulRel x (succ y) (addValue z x)
  mulResultNat : ∀ {x y z}, MulRel x y z → IsNat z

variable {V : Type u}

theorem add_zero_iff (A : ArithmeticAPI V) (x y : V) :
    A.AddRel x y A.zero ↔ x = A.zero ∧ y = A.zero := by
  constructor
  · intro hxy
    rcases A.zeroOrSucc y (A.addRight hxy) with rfl | ⟨n, hn, rfl⟩
    · exact ⟨(A.addUnique hxy (A.addZero (A.addLeft hxy))).symm, rfl⟩
    · obtain ⟨b, hb⟩ := A.addTotal (A.addLeft hxy) hn
      have he : A.zero = A.succ b := A.addUnique hxy (A.addSucc hb)
      exact False.elim (A.succNeZero b he.symm)
  · rintro ⟨rfl, rfl⟩
    exact A.addZero A.zeroNat

theorem mul_zero_iff (A : ArithmeticAPI V) {x y : V}
    (hx : A.IsNat x) (hy : A.IsNat y) :
    A.MulRel x y A.zero ↔ x = A.zero ∨ y = A.zero := by
  constructor
  · intro hxy
    rcases A.zeroOrSucc y hy with rfl | ⟨n, hn, rfl⟩
    · exact Or.inr rfl
    · obtain ⟨b, hb⟩ := A.mulTotal hx hn
      have he : A.zero = A.addValue b x := A.mulUnique hxy (A.mulSucc hb)
      have hadd : A.AddRel b x A.zero :=
        he.symm ▸ A.addValueSpec (A.mulResultNat hb) hx
      exact Or.inl ((add_zero_iff A b x).mp hadd).2
  · rintro (rfl | rfl)
    · exact A.mulZeroLeft hy
    · exact A.mulZeroRight hx

#print axioms add_zero_iff
#print axioms mul_zero_iff
end InternalZeroCore
