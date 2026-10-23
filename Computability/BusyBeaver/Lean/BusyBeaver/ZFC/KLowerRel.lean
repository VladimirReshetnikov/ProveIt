import BusyBeaver.ZFC.KLowerRaw

/-!
Relativization to the tagged domain `D_t = {x | t ∈ x}` (Elliot Glazer's `KDomain`).

`relT d φ` translates a formula over the subtype `Tag mem t` into one over the raw structure: the
marker `t` sits in slot `d` below `d` binders (slot 0 at the top), the formula's own free slots
move past it, and every quantifier is guarded by `t ∈ x`. `sat_relT`: the subtype satisfies `φ`
iff the raw structure satisfies `relT 0 φ` with `t` in front of the underlying values.
-/

namespace SetTheory.BusyBeaver.ZFC.KLower

open Form

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The tagged domain. -/
def Tag (mem : V → V → Prop) (t : V) : Type u := {x : V // mem t x}

/-- Its membership: raw membership between tagged sets. -/
def tmem (mem : V → V → Prop) (t : V) (x y : Tag mem t) : Prop := mem x.1 y.1

/-- Below `d` binders: bound slots stay, free slots move past the marker. -/
def sh (d i : Nat) : Nat := if i < d then i else i + 1

def relT : Nat → Form → Form
  | d, fMem i j => fMem (sh d i) (sh d j)
  | d, fEq i j => fEq (sh d i) (sh d j)
  | _, fBot => fBot
  | d, fImp a b => fImp (relT d a) (relT d b)
  | d, fAnd a b => fAnd (relT d a) (relT d b)
  | d, fOr a b => fOr (relT d a) (relT d b)
  | d, fAll a => fAll (fImp (fMem (d + 1) 0) (relT (d + 1) a))
  | d, fEx a => fEx (fAnd (fMem (d + 1) 0) (relT (d + 1) a))

/-- The raw valuation `e'` shows the tagged valuation `e` below `d` binders. -/
def Shows (t : V) (d : Nat) (e : Nat → Tag mem t) (e' : Nat → V) : Prop :=
  ∀ i, e' (sh d i) = (e i).1

theorem shows_scons {t : V} {d : Nat} {e : Nat → Tag mem t} {e' : Nat → V}
    (h : Shows t d e e') (x : Tag mem t) : Shows t (d + 1) (scons x e) (scons x.1 e') := by
  intro i
  cases i with
  | zero => simp [sh, scons]
  | succ i =>
      rw [show sh (d + 1) (i + 1) = sh d i + 1 by unfold sh; split <;> split <;> omega]
      exact h i

theorem sat_relT {t : V} : ∀ (φ : Form) (d : Nat) (e : Nat → Tag mem t) (e' : Nat → V),
    Shows t d e e' → e' d = t →
      (Sat (tmem mem t) e φ ↔ Sat mem e' (relT d φ))
  | fMem i j, d, e, e', h, _ => by simp only [Sat, relT, tmem, h i, h j]
  | fEq i j, d, e, e', h, _ => by
      simp only [Sat, relT, h i, h j]
      exact ⟨fun hij => hij ▸ rfl, fun hij => Subtype.ext hij⟩
  | fBot, _, _, _, _, _ => Iff.rfl
  | fImp a b, d, e, e', h, ht => imp_congr (sat_relT a d e e' h ht) (sat_relT b d e e' h ht)
  | fAnd a b, d, e, e', h, ht => and_congr (sat_relT a d e e' h ht) (sat_relT b d e e' h ht)
  | fOr a b, d, e, e', h, ht => or_congr (sat_relT a d e e' h ht) (sat_relT b d e e' h ht)
  | fAll a, d, e, e', h, ht => by
      show (∀ x, Sat (tmem mem t) (scons x e) a) ↔ ∀ y, (mem (e' d) y → _)
      rw [ht]
      exact ⟨fun hx y hy => (sat_relT a (d + 1) _ _ (shows_scons h ⟨y, hy⟩) ht).mp (hx ⟨y, hy⟩),
        fun hy x => (sat_relT a (d + 1) _ _ (shows_scons h x) ht).mpr (hy x.1 x.2)⟩
  | fEx a, d, e, e', h, ht => by
      show (∃ x, Sat (tmem mem t) (scons x e) a) ↔ ∃ y, (mem (e' d) y ∧ _)
      rw [ht]
      exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, (sat_relT a (d + 1) _ _ (shows_scons h x) ht).mp hx⟩,
        fun ⟨y, hy, hr⟩ => ⟨⟨y, hy⟩, (sat_relT a (d + 1) _ _ (shows_scons h ⟨y, hy⟩) ht).mpr hr⟩⟩

/-- The top-level raw valuation: the marker, then the underlying values. -/
def topEnv (t : V) (e : Nat → Tag mem t) : Nat → V := scons t (fun i => (e i).1)

theorem shows_top (t : V) (e : Nat → Tag mem t) : Shows t 0 e (topEnv t e) := by
  intro i; simp [sh, topEnv, scons]

/-- **Relativization.** -/
theorem sat_top {t : V} (φ : Form) (e : Nat → Tag mem t) :
    Sat (tmem mem t) e φ ↔ Sat mem (topEnv t e) (relT 0 φ) :=
  sat_relT φ 0 e _ (shows_top t e) rfl

end SetTheory.BusyBeaver.ZFC.KLower
