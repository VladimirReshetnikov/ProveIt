import ZF.Zf

/-!
# The axiom of choice over the language of set theory

This file adjoins a choice axiom to the first-order ZF development of
`ZF.Zf`, producing the axiom set `ZFCax`, its provability relation
`ZFCprov`, and the sentence theory `ZFCax_s`, each an extension of its ZF
counterpart by exactly one axiom.

## Which choice axiom

The language of `FirstOrder.Fol` has one binary relation symbol and equality;
it has no function symbols and no pairing operation.  Stating choice as "every
family of nonempty sets admits a choice *function*" would therefore require
first encoding functions as sets of Kuratowski pairs inside the formula, which
is possible but produces a large formula whose semantic bridge is about the
internal encoding rather than about choice.

Zermelo's original formulation avoids this entirely:

> for every `x`, if every member of `x` is nonempty and distinct members of `x`
> are disjoint, then there is a set `c` meeting every member of `x` in exactly
> one point.

The witness `c` is an ordinary set, so the formula uses nothing beyond `fMem`,
`fEq`, and quantifiers.  Over ZF this is equivalent to the choice-function
form — given an arbitrary family one disjointifies it by replacing each member
`y` by `{y} × y`, and the resulting selector is the graph of a choice function
— so nothing is lost in strength.  That equivalence is a theorem *inside* the
object theory and is not formalized here; the axiom is taken in the Zermelo
form as its official statement.

## De Bruijn layout

`Choice_form` is `fAll (fImp (fAnd Choice_nonempty Choice_disjoint)
(fEx Choice_selector))`, so under the outer binder `x` is index `0`, and under
the additional existential `c` is index `0` with `x` pushed to index `1`.  The
per-component index assignments are recorded on the three components below.

## The semantic bridge

`bridge_Choice` is an `iff`, in the style of `bridge_Pair` and `bridge_Union`
in `ZF.Zf`: satisfaction of `Choice_form` under every environment of a
structure `(V, mem)` is equivalent to the abstract principle `ChoiceSem mem`,
which mentions only `mem`.  `bridge_Choice_sealed` transports it across the
universal closure `sealF` used by the sentence theory.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

/-- Negation as a derived connective.  `Form` has no primitive negation, and
`Sat mem e fBot` is `False`, so `Sat mem e (fNot a)` is literally
`Sat mem e a → False`. -/
def fNot (a : Form) : Form := fImp a fBot

/-! ## Zermelo's choice axiom as a closed formula -/

/-- Under the outer binder of `Choice_form` (so `x` is index `0`): every member
of `x` is nonempty.

Indices: under `∀y` one has `y = 0`, `x = 1`; under the inner `∃z`, `z = 0`,
`y = 1`. -/
def Choice_nonempty : Form :=
  fAll (fImp (fMem 0 1) (fEx (fMem 0 1)))

/-- Under the outer binder of `Choice_form` (so `x` is index `0`): distinct
members of `x` are disjoint.

Indices: under `∀y ∀y'` one has `y' = 0`, `y = 1`, `x = 2`; under the inner
`∃z`, `z = 0`, `y' = 1`, `y = 2`, `x = 3`. -/
def Choice_disjoint : Form :=
  fAll (fAll (fImp (fAnd (fAnd (fMem 1 2) (fMem 0 2)) (fNot (fEq 1 0)))
                   (fNot (fEx (fAnd (fMem 0 2) (fMem 0 1))))))

/-- Under the outer binder of `Choice_form` and the existential binding the
selector (so `c = 0`, `x = 1`): `c` meets every member of `x` in exactly one
point.

Indices: under `∀y` one has `y = 0`, `c = 1`, `x = 2`; under `∃z`, `z = 0`,
`y = 1`, `c = 2`, `x = 3`; under the uniqueness binder `∀w`, `w = 0`, `z = 1`,
`y = 2`, `c = 3`, `x = 4`. -/
def Choice_selector : Form :=
  fAll (fImp (fMem 0 2)
          (fEx (fAnd (fAnd (fMem 0 1) (fMem 0 2))
                  (fAll (fImp (fAnd (fMem 0 2) (fMem 0 3)) (fEq 0 1))))))

/-- Zermelo's choice axiom: every pairwise disjoint family of nonempty sets
admits a set meeting each member in exactly one point. -/
def Choice_form : Form :=
  fAll (fImp (fAnd Choice_nonempty Choice_disjoint) (fEx Choice_selector))

/-- `Choice_form` is closed: every variable occurrence is captured by one of
its binders, so it is an axiom rather than an axiom schema instance and needs
no universal closure to be a sentence. -/
theorem Sentence_Choice_form : Sentence Choice_form := by
  intro n h
  simp only [Choice_form, Choice_nonempty, Choice_disjoint, Choice_selector,
    fNot, Free] at h
  repeat' rcases h with h | h
  all_goals first
    | exact h
    | omega

/-! ## The semantic choice principle -/

/-- The abstract choice principle for a structure `(V, mem)`: for every `x`
whose members are nonempty and pairwise disjoint there is a `c` such that every
member `y` of `x` contains exactly one element of `c`.

This is the `mem`-level reading of `Choice_form`; `bridge_Choice` proves the
two equivalent. -/
def ChoiceSem {V : Type u} (mem : V → V → Prop) : Prop :=
  ∀ x : V,
    (∀ y, mem y x → ∃ z, mem z y) →
    (∀ y y', mem y x → mem y' x → y ≠ y' → ¬ ∃ z, mem z y ∧ mem z y') →
    ∃ c, ∀ y, mem y x →
      ∃ z, mem z y ∧ mem z c ∧ ∀ w, mem w y → mem w c → w = z

/-! ## Extraction bridge -/

section Bridges

variable {V : Type u} {mem : V → V → Prop}

/-- Satisfaction of `Choice_form` in `(V, mem)` under every environment is
equivalent to the semantic choice principle.  Both directions are proved; the
environment is irrelevant because `Choice_form` is a sentence. -/
theorem bridge_Choice :
    (∀ e : Nat → V, Sat mem e Choice_form) ↔ ChoiceSem mem := by
  constructor
  · intro h x hne hdis
    have hd : Sat mem (scons x (fun _ => x)) Choice_disjoint := by
      intro y y' hy
      obtain ⟨⟨hyx, hy'x⟩, hyy'⟩ := hy
      exact hdis y y' hyx hy'x hyy'
    obtain ⟨c, hc⟩ := h (fun _ => x) x ⟨hne, hd⟩
    refine ⟨c, ?_⟩
    intro y hy
    obtain ⟨z, hz, hu⟩ := hc y hy
    refine ⟨z, hz.1, hz.2, ?_⟩
    intro w hwy hwc
    exact hu w ⟨hwy, hwc⟩
  · intro h e x hx
    obtain ⟨c, hc⟩ :=
      h x hx.1 (fun y y' hyx hy'x hyy' => hx.2 y y' ⟨⟨hyx, hy'x⟩, hyy'⟩)
    refine ⟨c, ?_⟩
    intro y hy
    obtain ⟨z, hzy, hzc, hu⟩ := hc y hy
    refine ⟨z, ⟨hzy, hzc⟩, ?_⟩
    intro w hw
    exact hu w hw.1 hw.2

theorem bridge_Choice_fwd (H : ∀ e : Nat → V, Sat mem e Choice_form) :
    ChoiceSem mem :=
  bridge_Choice.mp H

/-- The same bridge for the universally closed form used by the sentence
theory `ZFCax_s`.  Sealing a sentence changes the formula but not its class of
models. -/
theorem bridge_Choice_sealed :
    (∀ e : Nat → V, Sat mem e (sealF Choice_form)) ↔ ChoiceSem mem :=
  (seal_valid Choice_form).trans bridge_Choice

end Bridges

/-! ## The ZFC axiom set -/

/-- The axioms of ZFC: the ZF axioms of `ZFax` together with `Choice_form`.
Adjoining a single closed formula keeps every ZF-specific lemma about `ZFax`
available through `ZFCax_of_ZFax`. -/
def ZFCax (f : Form) : Prop := ZFax f ∨ f = Choice_form

/-- Provability from finitely many ZFC axioms, in the list-context calculus of
`FirstOrder.Calculus`; the ZFC counterpart of `ZFprov`. -/
def ZFCprov (phi : Form) : Prop :=
  ∃ G, (∀ x ∈ G, ZFCax x) ∧ Prov G phi

/-- ZFC as a theory of sentences: every axiom universally closed by `sealF`,
the ZFC counterpart of `ZFax_s`.  `Choice_form` is already closed, but it is
sealed anyway so that membership in `ZFCax_s` is uniform. -/
def ZFCax_s (f : Form) : Prop := ZFax_s f ∨ f = sealF Choice_form

theorem Sentences_ZFC : Sentences ZFCax_s := by
  intro f hf
  rcases hf with hf | rfl
  · exact Sentences_ZF f hf
  · exact Sentence_seal _

/-- Every ZF axiom is a ZFC axiom. -/
theorem ZFCax_of_ZFax {f : Form} (h : ZFax f) : ZFCax f := Or.inl h

/-- Every axiom of the ZF sentence theory is an axiom of the ZFC sentence
theory. -/
theorem ZFCax_s_of_ZFax_s {f : Form} (h : ZFax_s f) : ZFCax_s f := Or.inl h

theorem ZFCax_Choice : ZFCax Choice_form := Or.inr rfl

theorem ZFCax_s_Choice : ZFCax_s (sealF Choice_form) := Or.inr rfl

/-- ZFC proves everything ZF proves: a ZF derivation is already a ZFC
derivation, since its context consists of ZFC axioms. -/
theorem ZFCprov_of_ZFprov {phi : Form} (h : ZFprov phi) : ZFCprov phi := by
  obtain ⟨G, hG, hp⟩ := h
  exact ⟨G, fun x hx => ZFCax_of_ZFax (hG x hx), hp⟩

/-- The extension is not vacuous on the syntactic side: choice itself is
derivable in ZFC. -/
theorem ZFCprov_Choice : ZFCprov Choice_form := by
  refine ⟨[Choice_form], ?_, Prov.P_ass _ _ (List.Mem.head _)⟩
  intro x hx
  cases hx with
  | head => exact ZFCax_Choice
  | tail _ hx' => cases hx'

end BoundedZFCConsistency
end LeanProofs
