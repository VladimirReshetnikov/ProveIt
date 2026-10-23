import FirstOrder.Fol

/-!
UNCOMPILED RESEARCH DRAFT. No Lean compiler was run for this packet.
One capture-aware interpretation into a definable subtype.
This is a new module, not an applied change to ProveIt.
-/

namespace SetTheory.BusyBeaver.ZFC.GuardedSubtype

open Form
universe u v

def subtypeMem {V : Type u} (mem : V → V → Prop) (P : V → Prop)
    (x y : {x // P x}) : Prop := mem x.val y.val

/-- `next` advances the binding context. The guard is already in the
ambient environment *after* its one new variable has been pushed. -/
def translate {C : Type v} (next : C → C)
    (slot : C → Nat → Nat) (guard : C → Form) : C → Form → Form
  | c, fMem i j => fMem (slot c i) (slot c j)
  | c, fEq i j => fEq (slot c i) (slot c j)
  | _, fBot => fBot
  | c, fImp a b => fImp (translate next slot guard c a) (translate next slot guard c b)
  | c, fAnd a b => fAnd (translate next slot guard c a) (translate next slot guard c b)
  | c, fOr a b => fOr (translate next slot guard c a) (translate next slot guard c b)
  | c, fAll a => fAll (fImp (guard c) (translate next slot guard (next c) a))
  | c, fEx a => fEx (fAnd (guard c) (translate next slot guard (next c) a))

def Shows {V : Type u} {C : Type v} {P : V → Prop}
    (slot : C → Nat → Nat) (c : C) (e : Nat → {x // P x}) (r : Nat → V) : Prop :=
  ∀ i, r (slot c i) = (e i).val

theorem shows_scons {V : Type u} {C : Type v} {P : V → Prop}
    (next : C → C) (slot : C → Nat → Nat)
    (hzero : ∀ c, slot (next c) 0 = 0)
    (hsucc : ∀ c i, slot (next c) (i + 1) = slot c i + 1)
    {c : C} {e : Nat → {x // P x}} {r : Nat → V}
    (h : Shows slot c e r) (x : {x // P x}) :
    Shows slot (next c) (scons x e) (scons x.val r) := by
  intro i
  cases i with
  | zero => simp only [hzero, scons]
  | succ i => simpa only [hsucc, scons] using h i

/-- All semantic content is in the two slot laws, invariant stability, and
the exact ambient guard. No set-theoretic axiom or choice is assumed. -/
theorem sat_translate {V : Type u} {C : Type v}
    (mem : V → V → Prop) (P : V → Prop)
    (next : C → C) (slot : C → Nat → Nat) (guard : C → Form)
    (Good : C → (Nat → V) → Prop)
    (hzero : ∀ c, slot (next c) 0 = 0)
    (hsucc : ∀ c i, slot (next c) (i + 1) = slot c i + 1)
    (hstep : ∀ c r x, Good c r → Good (next c) (scons x r))
    (hguard : ∀ c r x, Good c r → (Sat mem (scons x r) (guard c) ↔ P x))
    (phi : Form) :
    ∀ c (e : Nat → {x // P x}) r, Good c r → Shows slot c e r →
      (Sat mem r (translate next slot guard c phi) ↔ Sat (subtypeMem mem P) e phi) := by
  induction phi with
  | fMem i j =>
      intro c e r _ he
      change mem (r (slot c i)) (r (slot c j)) ↔ mem (e i).val (e j).val
      rw [he i, he j]
  | fEq i j =>
      intro c e r _ he
      change r (slot c i) = r (slot c j) ↔ e i = e j
      rw [he i, he j]
      exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | fBot => intro _ _ _ _ _; rfl
  | fImp a b iha ihb =>
      intro c e r hg he
      exact imp_congr (iha c e r hg he) (ihb c e r hg he)
  | fAnd a b iha ihb =>
      intro c e r hg he
      exact and_congr (iha c e r hg he) (ihb c e r hg he)
  | fOr a b iha ihb =>
      intro c e r hg he
      exact or_congr (iha c e r hg he) (ihb c e r hg he)
  | fAll a ih =>
      intro c e r hg he
      change (∀ x, Sat mem (scons x r) (guard c) →
        Sat mem (scons x r) (translate next slot guard (next c) a)) ↔
          ∀ x : {x // P x}, Sat (subtypeMem mem P) (scons x e) a
      constructor
      · intro hall x
        exact (ih (next c) (scons x e) (scons x.val r)
          (hstep c r x.val hg) (shows_scons next slot hzero hsucc he x)).mp
            (hall x.val ((hguard c r x.val hg).mpr x.property))
      · intro hall x hx
        let y : {x // P x} := ⟨x, (hguard c r x hg).mp hx⟩
        exact (ih (next c) (scons y e) (scons x r)
          (hstep c r x hg) (shows_scons next slot hzero hsucc he y)).mpr (hall y)
  | fEx a ih =>
      intro c e r hg he
      change (∃ x, Sat mem (scons x r) (guard c) ∧
        Sat mem (scons x r) (translate next slot guard (next c) a)) ↔
          ∃ x : {x // P x}, Sat (subtypeMem mem P) (scons x e) a
      constructor
      · rintro ⟨x, hx, ha⟩
        let y : {x // P x} := ⟨x, (hguard c r x hg).mp hx⟩
        exact ⟨y, (ih (next c) (scons y e) (scons x r)
          (hstep c r x hg) (shows_scons next slot hzero hsucc he y)).mp ha⟩
      · rintro ⟨x, hx⟩
        exact ⟨x.val, (hguard c r x.val hg).mpr x.property,
          (ih (next c) (scons x e) (scons x.val r)
            (hstep c r x.val hg) (shows_scons next slot hzero hsucc he x)).mpr hx⟩

end SetTheory.BusyBeaver.ZFC.GuardedSubtype
