import BusyBeaver.ZFC.NamedZF

/-!
Ordinals inside an arbitrary model of ZF with Foundation.

The model is any structure satisfying the `ZFAxioms` bundle and set
Regularity (every nonempty set has an ∈-minimal element). Nothing is assumed
about the model from outside: membership need not be well-founded
externally, and every induction below runs over a set of counterexamples cut
out by Separation with a named formula (`NamedZF`).

An ordinal is a transitive set of transitive sets. Since an ordinal is its
own transitive container, ordinal induction needs no transitive closure.
Trichotomy follows by a double ordinal induction; least elements of definable
classes of ordinals, successors and unions of sets of ordinals follow.
-/

namespace SetTheory.BusyBeaver.ZFC.InternalOrd

open NamedZF NForm

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Set Regularity: every nonempty set has an ∈-minimal element. -/
def Regular (mem : V → V → Prop) : Prop :=
  ∀ a, (∃ x, mem x a) → ∃ m, mem m a ∧ ¬ ∃ z, mem z m ∧ mem z a

def Trans (mem : V → V → Prop) (t : V) : Prop := ∀ x, mem x t → ∀ z, mem z x → mem z t

def Ord (mem : V → V → Prop) (a : V) : Prop := Trans mem a ∧ ∀ x, mem x a → Trans mem x

/-! ## Named formulas and their meaning -/

/-- `t` is transitive. -/
def transF (t : Nat) : NForm :=
  .all (t + 1) (.imp (.mem (t + 1) t) (.all (t + 2) (.imp (.mem (t + 2) (t + 1)) (.mem (t + 2) t))))

theorem nsat_transF (ρ : Nat → V) (t : Nat) : NSat mem ρ (transF t) ↔ Trans mem (ρ t) := by
  simp (disch := omega) only [transF, NSat, upd_same, upd_other]
  rfl

/-- `a` is an ordinal. -/
def ordF (a : Nat) : NForm :=
  .and (transF a) (.all (a + 1) (.imp (.mem (a + 1) a) (transF (a + 1))))

theorem nsat_ordF (ρ : Nat → V) (a : Nat) : NSat mem ρ (ordF a) ↔ Ord mem (ρ a) := by
  simp only [ordF, NSat, nsat_transF]
  simp (disch := omega) only [upd_same, upd_other]
  rfl

/-! ## Regularity and ordinal basics -/

section Basics

variable (H : ZFAxioms mem) (hR : Regular mem)
include H hR

theorem mem_irrefl (x : V) : ¬ mem x x := by
  obtain ⟨m, hm, hmin⟩ := hR (vsingle H x) ⟨x, (vsingle_spec H x x).2 rfl⟩
  have hmx : m = x := (vsingle_spec H x m).1 hm
  subst hmx
  intro hxx
  exact hmin ⟨m, hxx, hm⟩

omit H hR in
theorem ord_of_mem {a x : V} (ha : Ord mem a) (hx : mem x a) : Ord mem x := by
  refine ⟨ha.2 x hx, fun y hy => ha.2 y (ha.1 x hx y hy)⟩

omit hR in
theorem trans_succ {a : V} (ha : Trans mem a) : Trans mem (vsucc H a) := by
  intro x hx z hz
  rcases (vsucc_spec H a x).1 hx with hx | rfl
  · exact (vsucc_spec H a z).2 (Or.inl (ha x hx z hz))
  · exact (vsucc_spec H x z).2 (Or.inl hz)

omit hR in
theorem ord_succ {a : V} (ha : Ord mem a) : Ord mem (vsucc H a) := by
  refine ⟨trans_succ H ha.1, fun x hx => ?_⟩
  rcases (vsucc_spec H a x).1 hx with hx | rfl
  · exact ha.2 x hx
  · exact ha.1

omit hR in
theorem ord_vunion {A : V} (hA : ∀ x, mem x A → Ord mem x) : Ord mem (vunion H A) := by
  refine ⟨?_, ?_⟩
  · intro x hx z hz
    obtain ⟨y, hxy, hyA⟩ := (vunion_spec H A x).1 hx
    exact (vunion_spec H A z).2 ⟨y, (hA y hyA).1 x hxy z hz, hyA⟩
  · intro x hx
    obtain ⟨y, hxy, hyA⟩ := (vunion_spec H A x).1 hx
    exact (hA y hyA).2 x hxy

/-- **Ordinal induction** for a property defined by a named formula
(name `0` is the ordinal; the other names are parameters from `ρ`). -/
theorem ord_induction (P : V → Prop) (φ : NForm) (ρ : Nat → V)
    (hP : ∀ x, NSat mem (upd ρ 0 x) φ ↔ P x)
    (step : ∀ a, Ord mem a → (∀ b, mem b a → P b) → P a) :
    ∀ a, Ord mem a → P a := by
  intro a0 ha0
  apply Classical.byContradiction
  intro hna0
  obtain ⟨S, hS⟩ := sep_of H (fun x => ¬ P x) φ.neg ρ
    (fun x => by rw [nsat_neg, hP]) (vsucc H a0)
  obtain ⟨m, hm, hmin⟩ := hR S ⟨a0, (hS a0).2 ⟨vsucc_self H a0, hna0⟩⟩
  obtain ⟨hmS, hnPm⟩ := (hS m).1 hm
  have hOm : Ord mem m := by
    rcases (vsucc_spec H a0 m).1 hmS with h | rfl
    · exact ord_of_mem ha0 h
    · exact ha0
  apply hnPm
  refine step m hOm fun b hb => ?_
  apply Classical.byContradiction
  intro hnb
  exact hmin ⟨b, hb, (hS b).2 ⟨(ord_succ H ha0).1 m hmS b hb, hnb⟩⟩

/-! ## Trichotomy -/

/-- Comparability with `β`, as a property of `α` (name `0`; `β` is name `1`). -/
def cmpF : NForm := .or (.mem 0 1) (.or (.eq 0 1) (.mem 1 0))

/-- Comparability with every ordinal (name `0`). -/
def cmpAllF : NForm :=
  .all 1 (.imp (ordF 1) cmpF)

theorem trichotomy : ∀ a, Ord mem a → ∀ b, Ord mem b → mem a b ∨ a = b ∨ mem b a := by
  refine ord_induction H hR (fun a => ∀ b, Ord mem b → mem a b ∨ a = b ∨ mem b a) cmpAllF
    (fun _ => vempty H) ?_ ?_
  · intro x
    simp only [cmpAllF, cmpF, NSat, nsat_ordF]
    simp (disch := omega) only [upd_same, upd_other]
  · intro a ha IHa
    refine ord_induction H hR (fun b => mem a b ∨ a = b ∨ mem b a) (.or (.mem 1 0) (.or (.eq 1 0) (.mem 0 1)))
      (fun _ => a) ?_ ?_
    · intro x
      simp (disch := omega) only [NSat, upd_same, upd_other]
    · intro b hb IHb
      -- Some smaller ordinal already decides the comparison.
      by_cases h1 : ∃ a', mem a' a ∧ (a' = b ∨ mem b a')
      · obtain ⟨a', ha', h | h⟩ := h1
        · subst h; exact Or.inr (Or.inr ha')
        · exact Or.inr (Or.inr (ha.1 a' ha' b h))
      by_cases h2 : ∃ b', mem b' b ∧ (mem a b' ∨ a = b')
      · obtain ⟨b', hb', h | h⟩ := h2
        · exact Or.inl (hb.1 b' hb' a h)
        · subst h; exact Or.inl hb'
      -- Otherwise `a` and `b` have the same members.
      refine Or.inr (Or.inl (H.ext a b fun x => ⟨fun hx => ?_, fun hx => ?_⟩))
      · rcases IHa x hx b hb with h | h | h
        · exact h
        · exact absurd ⟨x, hx, Or.inl h⟩ h1
        · exact absurd ⟨x, hx, Or.inr h⟩ h1
      · rcases IHb x hx with h | h | h
        · exact absurd ⟨x, hx, Or.inl h⟩ h2
        · exact absurd ⟨x, hx, Or.inr h⟩ h2
        · exact h

omit H hR in
theorem sub_of_le {a b : V} (hb : Ord mem b) (h : a = b ∨ mem a b) : ∀ x, mem x a → mem x b := by
  rcases h with rfl | h
  · exact fun _ hx => hx
  · exact fun x hx => hb.1 a h x hx

/-- A transitive subset relation between ordinals is `≤`. -/
theorem le_of_sub {a b : V} (ha : Ord mem a) (hb : Ord mem b) (h : ∀ x, mem x a → mem x b) :
    a = b ∨ mem a b := by
  rcases trichotomy H hR a ha b hb with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd (h b h') (mem_irrefl H hR b)

/-- **Least elements.** A definable property holding of some ordinal holds
of an ordinal below or equal to every ordinal having it. -/
theorem least_ord (P : V → Prop) (φ : NForm) (ρ : Nat → V)
    (hP : ∀ x, NSat mem (upd ρ 0 x) φ ↔ P x) {a : V} (ha : Ord mem a) (hPa : P a) :
    ∃ m, Ord mem m ∧ P m ∧ ∀ b, Ord mem b → P b → m = b ∨ mem m b := by
  obtain ⟨S, hS⟩ := sep_of H P φ ρ hP (vsucc H a)
  obtain ⟨m, hm, hmin⟩ := hR S ⟨a, (hS a).2 ⟨vsucc_self H a, hPa⟩⟩
  obtain ⟨hmA, hPm⟩ := (hS m).1 hm
  have hOm : Ord mem m := by
    rcases (vsucc_spec H a m).1 hmA with h | rfl
    · exact ord_of_mem ha h
    · exact ha
  refine ⟨m, hOm, hPm, fun b hb hPb => ?_⟩
  rcases trichotomy H hR m hOm b hb with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact absurd ⟨b, h, (hS b).2 ⟨(ord_succ H ha).1 m hmA b h, hPb⟩⟩ hmin

end Basics

end SetTheory.BusyBeaver.ZFC.InternalOrd
