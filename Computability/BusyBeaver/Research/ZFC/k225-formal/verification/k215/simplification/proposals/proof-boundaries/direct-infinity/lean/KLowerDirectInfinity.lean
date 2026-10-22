import BusyBeaver.ZFC.KLowerTag
import DirectInfinity

/-!
Direct ordinary Infinity in the tagged domain, using the current repository's
FormSeed, raw augmented comprehension, and bounded tagged comprehension.
This module deliberately stops before the final quotient/ZF endpoint composition.
-/

namespace SetTheory.BusyBeaver.ZFC.KLowerDirectInfinity

open Form KLower KSeed222

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Output is slot 0 and input is slot 1. -/
def successorF : Form :=
  fAll (fIff (fMem 0 1) (fOr (fMem 0 2) (fEq 0 2)))

theorem sat_successorF (env : Nat → V) :
    Sat mem env successorF ↔ DirectInfinity.Succ mem (env 1) (env 0) := by
  simp only [successorF, Sat, Sat_fIff, scons, DirectInfinity.Succ]

/-- The marker is the first parameter, in slot 2 before the inner binder. -/
def taggedSuccessorF : Form := fAnd (fMem 2 1) successorF

theorem sat_taggedSuccessorF (t x y : V) :
    Sat mem (scons y (scons x (fun _ => t))) taggedSuccessorF ↔
      mem t x ∧ DirectInfinity.Succ mem x y := by
  exact and_congr Iff.rfl (sat_successorF _)

section
variable (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x)
  {t : V} (ht : ∀ z, ¬ mem z t)

include hs hirr in
theorem raw_successor (x : V) : ∃ y, DirectInfinity.Succ mem x y := by
  obtain ⟨y, hy⟩ := raw_aug hs hirr x (fEq 0 0) (fun _ => x)
  refine ⟨y, fun z => (hy z).trans ?_⟩
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr ⟨h, rfl⟩
    · exact Or.inl h

include hs in
theorem tagged_seed (e : V) :
    DirectInfinity.Seed mem (fun x y => mem t x ∧ DirectInfinity.Succ mem x y) e := by
  have h := hs taggedSuccessorF (fun _ => t) e
  have hR : (fun x y => Sat mem (scons y (scons x (fun _ => t))) taggedSuccessorF) =
      (fun x y => mem t x ∧ DirectInfinity.Succ mem x y) :=
    funext fun x => funext fun y => propext (sat_taggedSuccessorF t x y)
  rw [hR] at h
  exact h

include hs hirr ht in
/-- Bounded comprehension adjoins the chosen tagged root to the seed container.
The bound is a transitive container of the raw pair {C,e}; it is finite set
construction, with no use of Infinity or of the quotient's singleton containers. -/
theorem tagged_adjoin (e : V) (C : V) :
    ∃ I, mem t I ∧ ∀ z, mem t z → (mem z I ↔ z = e ∨ mem z C) := by
  obtain ⟨P, hP⟩ := raw_pair hs ht C e
  obtain ⟨U, hPU, hU⟩ := raw_transitive hs P
  have heU : mem e U := hU P hPU e ((hP e).mpr (Or.inr rfl))
  have hCU : mem C U := hU P hPU C ((hP C).mpr (Or.inl rfl))
  obtain ⟨I, hI⟩ := tag_of_bound hs hirr ht U
    (fun z => z.val = e ∨ mem z.val C)
    (fOr (fEq 0 1) (fMem 0 2)) (scons e (scons C (fun _ => t)))
    (fun z => by
      constructor
      · intro hz
        refine ⟨?_, hz⟩
        rcases hz with hze | hzC
        · rw [hze]; exact heU
        · exact hU C hCU z.val hzC
      · exact fun h => h.2)
  exact ⟨I.val, I.property, fun z hz => hI ⟨z, hz⟩⟩

include hs hirr in
theorem tagged_empty : ∃ e : Tag mem t, ∀ z : Tag mem t, ¬ tmem mem t z e := by
  obtain ⟨e, he⟩ := raw_singleton hs t
  refine ⟨⟨e, (he t).mpr rfl⟩, ?_⟩
  intro z hz
  have hzt : z.val = t := (he z.val).mp hz
  have hz' := z.property
  rw [hzt] at hz'
  exact hirr t hz'

include hs hirr ht in
/-- An exact empty set and an ordinary inductive set already exist in the tagged
domain. Extensionality, well-foundedness and quotient axioms are not premises. -/
theorem tagged_infinity :
    ∃ e I : Tag mem t, (∀ z, ¬ tmem mem t z e) ∧
      DirectInfinity.Inductive (tmem mem t) e I := by
  obtain ⟨e, he⟩ := tagged_empty hs hirr (t := t)
  obtain ⟨I, hIt, heI, hnext⟩ :=
    DirectInfinity.seed_tagged_container mem t e.val e.property
      (fun x _ => raw_successor hs hirr x) (tagged_seed hs (t := t) e.val)
      (tagged_adjoin hs hirr ht e.val)
  exact ⟨e, ⟨I, hIt⟩, he,
    DirectInfinity.tagged_inductive e.property hIt heI hnext⟩

end

#print axioms tagged_infinity

end SetTheory.BusyBeaver.ZFC.KLowerDirectInfinity
