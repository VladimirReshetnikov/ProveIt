import BoundedZFCConsistency.Basic

/-!
# Coded syntax inside an arbitrary model of ZF

The object-level sentence `Con_n(ZFC)` has to talk about formulas and about
derivations, so before any of it can be written down as a `Form` the syntax
must live *inside* the model as sets.  This file is the first step: it maps
the metatheoretic type `Form` into an arbitrary first-order model
`(V, mem)` of the `ZFAxioms` bundle of `ZF.Zf`, and proves the map injective.

Everything here is relative to a semantic axiom bundle `H : ZFAxioms mem`;
nothing is asserted about which models exist.  Only Extensionality, Pairing,
Union, Separation and Infinity are actually exercised — the same fragment
`ZF.Zf` uses for its internal omega — so the coding is available in every
model of that fragment, with neither Powerset nor Regularity.

## Internal numerals

`natV H k` is the von Neumann numeral of the metatheoretic natural `k`, built
by iterating `vsucc` from `vempty`.  The index `k` is *external*: each
`natV H k` is a separate closed term, and no claim is made that the family is
internally definable as a function.  `natV_mem_omega` places every numeral in
the internal omega, which is what makes the arithmetic of `ZF.Zf` — transitivity
of naturals, irreflexivity, injectivity of successor — applicable to them, and
`natV_inj` is the resulting external injectivity.

## The coding scheme

`formCode H` is defined by external recursion on the parse tree.  Each node
becomes a Kuratowski pair whose first component is a numeral tag identifying
the constructor and whose second component packages the arguments:

| formula     | code                                                     |
| ----------- | -------------------------------------------------------- |
| `fMem i j`  | `⟨0, ⟨natV i, natV j⟩⟩`                                  |
| `fEq i j`   | `⟨1, ⟨natV i, natV j⟩⟩`                                  |
| `fBot`      | `⟨2, ∅⟩`                                                 |
| `fImp a b`  | `⟨3, ⟨code a, code b⟩⟩`                                  |
| `fAnd a b`  | `⟨4, ⟨code a, code b⟩⟩`                                  |
| `fOr a b`   | `⟨5, ⟨code a, code b⟩⟩`                                  |
| `fAll a`    | `⟨6, code a⟩`                                            |
| `fEx a`     | `⟨7, code a⟩`                                            |

Here `⟨x, y⟩` is `kpair H x y`.  The tags are what separates the eight
constructors: two codes with different tags differ because `kpair` is
injective in its first component and distinct numerals are distinct sets.
The uniform "tag paired with payload" shape is deliberate — it is the shape an
object-language predicate "`x` is a formula code" will have to case on, and it
keeps the arity of the second component the only thing that varies.

De Bruijn indices are coded by the numerals themselves rather than by a
further tag, so a variable slot and a subformula code are not distinguished by
the coding; nothing below needs them to be, because the tag already determines
which of the two a component is.

## What is deliberately absent

There is no object-language predicate for "codes a formula", no internal
satisfaction relation, and nothing about derivations.  Those need the internal
finite-recursion machinery of `ZF.Zf` (`Approx`, `Theta`, `ClosureFO_of_ZF`)
and belong in later modules.  What *is* provided beyond the coding is the
formula-macro layer this file's shapes will be read through: `fNumF` for
numerals and `fTripleF` for the nested pair, each with a satisfaction spec in
the style of `fKPairF_spec`.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section Coding

variable {V : Type u} {mem : V → V → Prop}

/-! ## Internal numerals -/

/-- The von Neumann numeral of an external natural number: `natV H 0` is the
internal empty set and `natV H (k+1)` is the internal successor of
`natV H k`.  The recursion is metatheoretic, so `natV H k` is a closed term of
the model for each fixed `k`. -/
noncomputable def natV (H : ZFAxioms mem) : Nat → V
  | 0 => vempty H
  | k+1 => vsucc H (natV H k)

theorem natV_zero (H : ZFAxioms mem) : natV H 0 = vempty H := rfl

theorem natV_succ (H : ZFAxioms mem) (k : Nat) :
    natV H (k+1) = vsucc H (natV H k) := rfl

/-- Every numeral is an internal natural number.  This is the bridge that makes
the omega arithmetic of `ZF.Zf` available for numerals. -/
theorem natV_mem_omega (H : ZFAxioms mem) (k : Nat) :
    mem (natV H k) (omegaV H) := by
  induction k with
  | zero => exact vempty_in_omega H
  | succ k ih => exact omega_succ H (natV H k) ih

/-- Successor is injective on internal naturals.  `succ_inj_nat` asks for the
comparison `mem k m ∨ k = m` as a hypothesis; it is implied by the successor
equation itself, since `k` is a member of its own successor. -/
theorem vsucc_inj_omega (H : ZFAxioms mem) (m : V) (hm : mem m (omegaV H))
    (k : V) (heq : vsucc H k = vsucc H m) : k = m := by
  refine succ_inj_nat H m hm k ?_ heq
  have hs : mem k (vsucc H k) := vsucc_self H k
  rw [heq] at hs
  exact (vsucc_spec H m k).mp hs

/-- No successor numeral is the empty set: it contains its own predecessor. -/
theorem natV_succ_ne_vempty (H : ZFAxioms mem) (k : Nat) :
    natV H (k+1) ≠ vempty H := by
  intro h
  have hs : mem (natV H k) (natV H (k+1)) := by
    rw [natV_succ]
    exact vsucc_self H (natV H k)
  rw [h] at hs
  exact vempty_spec H (natV H k) hs

/-- Distinct external naturals have distinct numerals.  This is the fact the
tag discipline of `formCode` rests on. -/
theorem natV_inj (H : ZFAxioms mem) :
    ∀ j k : Nat, natV H j = natV H k → j = k := by
  intro j
  induction j with
  | zero =>
      intro k hk
      cases k with
      | zero => rfl
      | succ k =>
          exact absurd (hk.symm.trans (natV_zero H)) (natV_succ_ne_vempty H k)
  | succ j ih =>
      intro k hk
      cases k with
      | zero =>
          exact absurd (hk.trans (natV_zero H)) (natV_succ_ne_vempty H j)
      | succ k =>
          have hk' : vsucc H (natV H j) = vsucc H (natV H k) := by
            rw [← natV_succ, ← natV_succ]; exact hk
          have := vsucc_inj_omega H (natV H k) (natV_mem_omega H k)
            (natV H j) hk'
          rw [ih k this]

/-- Contrapositive form of `natV_inj`. -/
theorem natV_ne (H : ZFAxioms mem) {j k : Nat} (h : j ≠ k) :
    natV H j ≠ natV H k := fun heq => h (natV_inj H j k heq)

/-! ## Formula codes -/

/-- The code of a formula as a hereditarily finite set of the model: a
Kuratowski pair of a constructor tag and the packaged arguments, following the
table in the module header. -/
noncomputable def formCode (H : ZFAxioms mem) : Form → V
  | fMem i j => kpair H (natV H 0) (kpair H (natV H i) (natV H j))
  | fEq i j => kpair H (natV H 1) (kpair H (natV H i) (natV H j))
  | fBot => kpair H (natV H 2) (vempty H)
  | fImp a b => kpair H (natV H 3) (kpair H (formCode H a) (formCode H b))
  | fAnd a b => kpair H (natV H 4) (kpair H (formCode H a) (formCode H b))
  | fOr a b => kpair H (natV H 5) (kpair H (formCode H a) (formCode H b))
  | fAll a => kpair H (natV H 6) (formCode H a)
  | fEx a => kpair H (natV H 7) (formCode H a)

/-! ### The coding equations, stated separately so that later modules can
rewrite with them without unfolding the recursion. -/

theorem formCode_fMem (H : ZFAxioms mem) (i j : Nat) :
    formCode H (fMem i j) = kpair H (natV H 0) (kpair H (natV H i) (natV H j)) :=
  rfl

theorem formCode_fEq (H : ZFAxioms mem) (i j : Nat) :
    formCode H (fEq i j) = kpair H (natV H 1) (kpair H (natV H i) (natV H j)) :=
  rfl

theorem formCode_fBot (H : ZFAxioms mem) :
    formCode H fBot = kpair H (natV H 2) (vempty H) := rfl

theorem formCode_fImp (H : ZFAxioms mem) (a b : Form) :
    formCode H (fImp a b)
      = kpair H (natV H 3) (kpair H (formCode H a) (formCode H b)) := rfl

theorem formCode_fAnd (H : ZFAxioms mem) (a b : Form) :
    formCode H (fAnd a b)
      = kpair H (natV H 4) (kpair H (formCode H a) (formCode H b)) := rfl

theorem formCode_fOr (H : ZFAxioms mem) (a b : Form) :
    formCode H (fOr a b)
      = kpair H (natV H 5) (kpair H (formCode H a) (formCode H b)) := rfl

theorem formCode_fAll (H : ZFAxioms mem) (a : Form) :
    formCode H (fAll a) = kpair H (natV H 6) (formCode H a) := rfl

theorem formCode_fEx (H : ZFAxioms mem) (a : Form) :
    formCode H (fEx a) = kpair H (natV H 7) (formCode H a) := rfl

/-- Codes carrying different tags are different sets.  Only the first
component of the Kuratowski pair is inspected, so the payloads are arbitrary:
this is exactly what rules out the fifty-six mismatched constructor pairs in
`formCode_inj`. -/
theorem formCode_tag_ne (H : ZFAxioms mem) {s t : Nat} (hst : s ≠ t)
    (x y : V) : kpair H (natV H s) x ≠ kpair H (natV H t) y := by
  intro h
  exact hst (natV_inj H s t (kpair_inj H _ _ _ _ h).1)

/-- **Quotation is injective.**  Distinct formulas receive distinct codes, so
the coding loses no syntactic information and the object theory can reason
about a code as a proxy for the formula itself.

The proof is by induction on the first formula and case analysis on the
second.  Matching constructors are settled by `kpair_inj` together with the
induction hypotheses (or `natV_inj` at the leaves); mismatched constructors by
`formCode_tag_ne`. -/
theorem formCode_inj (H : ZFAxioms mem) :
    ∀ a b : Form, formCode H a = formCode H b → a = b := by
  intro a
  induction a with
  | fMem i j =>
      intro b h
      cases b <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             obtain ⟨h3, h4⟩ := kpair_inj H _ _ _ _ h2
             rw [natV_inj H _ _ h3, natV_inj H _ _ h4])
  | fEq i j =>
      intro b h
      cases b <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             obtain ⟨h3, h4⟩ := kpair_inj H _ _ _ _ h2
             rw [natV_inj H _ _ h3, natV_inj H _ _ h4])
  | fBot =>
      intro b h
      cases b <;> simp only [formCode] at h <;>
        first
          | rfl
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
  | fImp a b iha ihb =>
      intro c h
      cases c <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             obtain ⟨h3, h4⟩ := kpair_inj H _ _ _ _ h2
             rw [iha _ h3, ihb _ h4])
  | fAnd a b iha ihb =>
      intro c h
      cases c <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             obtain ⟨h3, h4⟩ := kpair_inj H _ _ _ _ h2
             rw [iha _ h3, ihb _ h4])
  | fOr a b iha ihb =>
      intro c h
      cases c <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             obtain ⟨h3, h4⟩ := kpair_inj H _ _ _ _ h2
             rw [iha _ h3, ihb _ h4])
  | fAll a ih =>
      intro b h
      cases b <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             rw [ih _ h2])
  | fEx a ih =>
      intro b h
      cases b <;> simp only [formCode] at h <;>
        first
          | exact absurd h (formCode_tag_ne H (by decide) _ _)
          | (obtain ⟨-, h2⟩ := kpair_inj H _ _ _ _ h
             rw [ih _ h2])

/-- Quotation as an injective function, in the packaged form later modules
will use. -/
theorem formCode_inj_iff (H : ZFAxioms mem) (a b : Form) :
    formCode H a = formCode H b ↔ a = b :=
  ⟨formCode_inj H a b, fun h => by rw [h]⟩

/-! ## Object-language macros for the coding shapes

The macros follow the house style of `fEmptyF`, `fSingF`, `fKPairF` and
`fPairMemF` in `ZF.Zf`: each is a genuine `Form` whose arguments are ABSOLUTE
de Bruijn slots at the use site, paired with a spec lemma stating exactly what
its satisfaction means.  Together they let the two shapes appearing in
`formCode` — a numeral and a tag paired with a two-component payload — be
written inside the object language. -/

/-- "slot `i` is the numeral of the external natural `k`".

The external index `k` controls the *size of the formula*, not a quantifier
over the model: `fNumF i k` is a chain of `k` existentials, each asserting that
the next slot is the successor of the previous one, bottoming out in "slot
`i` is empty". -/
def fNumF (i : Nat) : Nat → Form
  | 0 => fEmptyF i
  | k+1 => fEx (fAnd (fNumF 0 k) (fSuccF (i+1) 0))

theorem fNumF_spec (H : ZFAxioms mem) :
    ∀ (k i : Nat) (ee : Nat → V),
      Sat mem ee (fNumF i k) ↔ ee i = natV H k := by
  intro k
  induction k with
  | zero =>
      intro i ee
      rw [natV_zero]
      exact fEmptyF_spec H ee i
  | succ k ih =>
      intro i ee
      constructor
      · rintro ⟨d, hd, hs⟩
        have hd' : d = natV H k := (ih 0 (scons d ee)).mp hd
        have hs' : ee i = vsucc H d := (fSuccF_spec H (scons d ee) (i+1) 0).mp hs
        rw [hs', hd', natV_succ]
      · intro h
        have h' : ee i = vsucc H (natV H k) := by rw [h, natV_succ]
        exact ⟨natV H k,
          (ih 0 (scons (natV H k) ee)).mpr rfl,
          (fSuccF_spec H (scons (natV H k) ee) (i+1) 0).mpr h'⟩

/-- "slot `i` = ⟨slot `j`, ⟨slot `k`, slot `l`⟩⟩" — the nested Kuratowski
shape a binary constructor's code has, with the tag in slot `j` and the two
arguments in slots `k` and `l`. -/
def fTripleF (i j k l : Nat) : Form :=
  fEx (fAnd (fKPairF 0 (k+1) (l+1)) (fKPairF (i+1) (j+1) 0))

theorem fTripleF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k l : Nat) :
    Sat mem ee (fTripleF i j k l) ↔
      ee i = kpair H (ee j) (kpair H (ee k) (ee l)) := by
  constructor
  · rintro ⟨d, hd, hi⟩
    have hd' : d = kpair H (ee k) (ee l) :=
      (fKPairF_spec H (scons d ee) 0 (k+1) (l+1)).mp hd
    have hi' : ee i = kpair H (ee j) d :=
      (fKPairF_spec H (scons d ee) (i+1) (j+1) 0).mp hi
    rw [hi', hd']
  · intro h
    refine ⟨kpair H (ee k) (ee l), ?_, ?_⟩
    · exact (fKPairF_spec H (scons (kpair H (ee k) (ee l)) ee) 0 (k+1) (l+1)).mpr
        rfl
    · exact (fKPairF_spec H (scons (kpair H (ee k) (ee l)) ee)
        (i+1) (j+1) 0).mpr h

/-- "slot `i` is the code of a nullary constructor with tag `t` and payload
`∅`" — the shape of `formCode H fBot`, written with the tag as an external
parameter rather than as a slot. -/
def fTaggedEmptyF (i t : Nat) : Form :=
  fEx (fAnd (fNumF 0 t) (fEx (fAnd (fEmptyF 0) (fKPairF (i+2) 1 0))))

theorem fTaggedEmptyF_spec (H : ZFAxioms mem) (ee : Nat → V) (i t : Nat) :
    Sat mem ee (fTaggedEmptyF i t) ↔
      ee i = kpair H (natV H t) (vempty H) := by
  constructor
  · rintro ⟨d, hd, z, hz, hi⟩
    have hd' : d = natV H t := (fNumF_spec H t 0 (scons d ee)).mp hd
    have hz' : z = vempty H :=
      (fEmptyF_spec H (scons z (scons d ee)) 0).mp hz
    have hi' : ee i = kpair H d z :=
      (fKPairF_spec H (scons z (scons d ee)) (i+2) 1 0).mp hi
    rw [hi', hd', hz']
  · intro h
    refine ⟨natV H t, (fNumF_spec H t 0 (scons (natV H t) ee)).mpr rfl,
      vempty H, ?_, ?_⟩
    · exact (fEmptyF_spec H (scons (vempty H) (scons (natV H t) ee)) 0).mpr rfl
    · exact (fKPairF_spec H (scons (vempty H) (scons (natV H t) ee))
        (i+2) 1 0).mpr h

end Coding

end BoundedZFCConsistency
end LeanProofs
