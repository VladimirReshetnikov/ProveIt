/- Mathematical proof draft. Not compiled in this review. No project integration claimed. -/
universe u

theorem guardedImage {V : Type u} (mem R : V → V → Prop) (a b : V)
    (support : ∀ y, mem y b → ∃ x, mem x a ∧ R x y)
    (cover : ∀ x, mem x a → (∃ y, R x y) → ∃ y, mem y b ∧ R x y)
    (functional : ∀ x y z, mem x a → R x y → R x z → y = z) :
    ∀ y, mem y b ↔ ∃ x, mem x a ∧ R x y := by
  intro y
  constructor
  · exact support y
  · rintro ⟨x, hxa, hxy⟩
    obtain ⟨z, hzb, hxz⟩ := cover x hxa ⟨y, hxy⟩
    have hyz := functional x y z hxa hxy hxz
    exact hyz.symm ▸ hzb
