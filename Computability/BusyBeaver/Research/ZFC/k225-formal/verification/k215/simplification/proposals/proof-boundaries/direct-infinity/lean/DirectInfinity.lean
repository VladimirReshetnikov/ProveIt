/-!
Direct Infinity from one instance of the seed property.

The seed definition below is exactly the shape of KSeed222.SeedProp.  This
standalone file proves the mathematical core, including transport to a quotient.
The actual FormSeed formula adapters and K215 endpoint are not instantiated here.
-/

namespace DirectInfinity

universe u v

def Seed {V : Type u} (mem R : V → V → Prop) (A : V) : Prop :=
  ∃ C, (∀ y, R A y → ∃ z, R A z ∧ mem z C) ∧
    ∀ y, mem y C → ∃ x, R x y ∧
      ∀ x', (∀ w, mem w x' → mem w y) →
        ∀ y', R x' y' → ∃ z, R x' z ∧ mem z C

def Succ {V : Type u} (mem : V → V → Prop) (x y : V) : Prop :=
  ∀ z, mem z y ↔ mem z x ∨ z = x

def Inductive {V : Type u} (mem : V → V → Prop) (e I : V) : Prop :=
  mem e I ∧ ∀ x, mem x I → ∃ y, mem y I ∧ Succ mem x y

/-- Only reflexivity of subset is used: the seed container is already closed
under one-step witnesses of every serial relation whose range stays in a domain.
This theorem is independent of set-theoretic successors and of quotients. -/
theorem seed_serial_container {V : Type u} (mem R : V → V → Prop)
    (P : V → Prop) (a : V) (ha : P a)
    (range : ∀ x y, R x y → P y)
    (serial : ∀ x, P x → ∃ y, R x y) (seed : Seed mem R a) :
    ∃ C, (∃ y, R a y ∧ mem y C) ∧
      (∀ y, mem y C → P y) ∧
      ∀ y, mem y C → ∃ z, R y z ∧ mem z C := by
  obtain ⟨C, hroot, hclosed⟩ := seed
  have tags : ∀ y, mem y C → P y := by
    intro y hy
    obtain ⟨x, hxy, _⟩ := hclosed y hy
    exact range x y hxy
  obtain ⟨y, hy⟩ := serial a ha
  refine ⟨C, hroot y hy, tags, ?_⟩
  intro y hyC
  obtain ⟨_, _, hstep⟩ := hclosed y hyC
  obtain ⟨z, hyz⟩ := serial y (tags y hyC)
  exact hstep y (fun _ hw => hw) z hyz

/-- The raw von Neumann successor preserves the marker. -/
theorem succ_tag {V : Type u} {mem : V → V → Prop} {t x y : V}
    (hx : mem t x) (h : Succ mem x y) : mem t y :=
  (h t).mpr (Or.inl hx)

/-- A single seed instance for successors gives a tagged inductive container.
`adjoin` is the bounded tagged comprehension adapter, not an Infinity assumption.
No uniqueness, choice, extensionality, or infinite sequence is required. -/
theorem seed_tagged_container {V : Type u} (mem : V → V → Prop) (t e : V)
    (he : mem t e)
    (successors : ∀ x, mem t x → ∃ y, Succ mem x y)
    (seed : Seed mem (fun x y => mem t x ∧ Succ mem x y) e)
    (adjoin : ∀ C, ∃ I, mem t I ∧
      ∀ z, mem t z → (mem z I ↔ z = e ∨ mem z C)) :
    ∃ I, mem t I ∧ mem e I ∧
      ∀ x, mem t x → mem x I →
        ∃ y, mem t y ∧ mem y I ∧ Succ mem x y := by
  obtain ⟨C, ⟨s0, ⟨_, hs0⟩, hs0C⟩, tags, next⟩ :=
    seed_serial_container mem (fun x y => mem t x ∧ Succ mem x y) (mem t) e he
      (fun _ _ h => succ_tag h.1 h.2)
      (fun x hx => by obtain ⟨y, hy⟩ := successors x hx; exact ⟨y, hx, hy⟩) seed
  obtain ⟨I, hIt, hI⟩ := adjoin C
  refine ⟨I, hIt, (hI e he).mpr (Or.inl rfl), ?_⟩
  intro x htx hxI
  rcases (hI x htx).mp hxI with hxe | hxC
  · subst x
    exact ⟨s0, succ_tag he hs0, (hI s0 (succ_tag he hs0)).mpr (Or.inr hs0C), hs0⟩
  · obtain ⟨y, ⟨_, hxy⟩, hyC⟩ := next x hxC
    exact ⟨y, tags y hyC, (hI y (tags y hyC)).mpr (Or.inr hyC), hxy⟩

/-- Restrict the raw result to the tagged subtype. -/
theorem tagged_inductive {V : Type u} {mem : V → V → Prop} {t e I : V}
    (he : mem t e) (hI : mem t I) (heI : mem e I)
    (hnext : ∀ x, mem t x → mem x I →
      ∃ y, mem t y ∧ mem y I ∧ Succ mem x y) :
    Inductive (fun x y : {x : V // mem t x} => mem x.val y.val)
      ⟨e, he⟩ ⟨I, hI⟩ := by
  refine ⟨heI, ?_⟩
  intro x hx
  obtain ⟨y, hty, hyI, hxy⟩ := hnext x.val x.property hx
  refine ⟨⟨y, hty⟩, hyI, ?_⟩
  intro z
  exact (hxy z.val).trans
    (or_congr Iff.rfl ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩)

/-- The exact atomic presentation used by the bisimulation quotient. -/
def QuotientPresentation {A : Type u} {B : Type v}
    (raw : A → A → Prop) (mem : B → B → Prop) (q : A → B) : Prop :=
  (∀ b, ∃ a, q a = b) ∧
  ∀ a b, mem (q a) (q b) ↔ ∃ z, raw z b ∧ q a = q z

/-- Exact raw successors descend to actual successors in the quotient. -/
theorem quotient_successor {A : Type u} {B : Type v}
    (raw : A → A → Prop) (mem : B → B → Prop) (q : A → B)
    (H : QuotientPresentation raw mem q) {x y : A} (hs : Succ raw x y) :
    Succ mem (q x) (q y) := by
  intro z
  obtain ⟨a, rfl⟩ := H.1 z
  rw [H.2 a y, H.2 a x]
  constructor
  · rintro ⟨b, hb, hab⟩
    rcases (hs b).mp hb with hbx | hbe
    · exact Or.inl ⟨b, hbx, hab⟩
    · exact Or.inr (hbe ▸ hab)
  · rintro (⟨b, hb, hab⟩ | hax)
    · exact ⟨b, (hs b).mpr (Or.inl hb), hab⟩
    · exact ⟨x, (hs x).mpr (Or.inr rfl), hax⟩

/-- Ordinary Infinity descends without an index construction or recursion.
The empty witness and the whole inductive container are transported explicitly. -/
theorem quotient_infinity {A : Type u} {B : Type v}
    (raw : A → A → Prop) (mem : B → B → Prop) (q : A → B)
    (H : QuotientPresentation raw mem q) {e I : A}
    (hempty : ∀ z, ¬ raw z e) (hI : Inductive raw e I) :
    (∀ z, ¬ mem z (q e)) ∧ Inductive mem (q e) (q I) := by
  refine ⟨?_, (H.2 e I).mpr ⟨e, hI.1, rfl⟩, ?_⟩
  · intro z hz
    obtain ⟨a, rfl⟩ := H.1 z
    obtain ⟨b, hb, _⟩ := (H.2 a e).mp hz
    exact hempty b hb
  · intro x hx
    obtain ⟨a, rfl⟩ := H.1 x
    obtain ⟨b, hbI, hab⟩ := (H.2 a I).mp hx
    obtain ⟨c, hcI, hbc⟩ := hI.2 b hbI
    refine ⟨q c, (H.2 c I).mpr ⟨c, hcI, rfl⟩, ?_⟩
    rw [hab]
    exact quotient_successor raw mem q H hbc

#print axioms seed_serial_container
#print axioms seed_tagged_container
#print axioms tagged_inductive
#print axioms quotient_successor
#print axioms quotient_infinity

end DirectInfinity
