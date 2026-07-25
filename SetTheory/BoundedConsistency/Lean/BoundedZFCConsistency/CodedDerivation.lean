import BoundedZFCConsistency.InternalSoundness

/-!
# Coded contexts, coded derivations, and internal soundness

`BoundedZFCConsistency.InternalSoundness` completes the syntactic-operation
layer: coded formulas can be renamed inside the model, and renaming commutes
with internal satisfaction.  What is still missing between that layer and the
reflection argument is the *derivation* layer — an object-language predicate
"`d` codes a derivation of `c` from `g`" mirroring the seventeen rules of
`SetTheory.Prov`, together with the statement that such a `d` transports truth.

This file supplies both, over an arbitrary model of the `ZFAxioms` bundle.
Neither Powerset nor Regularity is used.

## Coded contexts

A context of the calculus is a `List Form`, so a coded context is an internal
list of formula codes, in the tagged-Kuratowski style of `formCode`:

| list       | code                |
| ---------- | ------------------- |
| `[]`       | `⟨0, ∅⟩`            |
| `a :: l`   | `⟨1, ⟨a, l⟩⟩`       |

The tags live in their own namespace: nothing below ever compares a context
code with a formula code, and `formCode_tag_ne` separates `ctxNil` from every
`ctxCons` exactly as it separates the eight formula constructors.

Membership is `MemCtx`, presented by certificates.  This is the same device
`RenStep`/`RenClosed`/`Renames` uses, and for the same two reasons: the
intersection presentation would need a set closed under the membership
clauses to exist before saying anything, and — more decisively — inversion is
available here without any well-foundedness, because the *shape of the list*
determines which clause applies.  `memCtx_nil` and `memCtx_cons_inv` are
therefore proved outright, from tag disjointness alone.

`IsCtx` — "`g` is a list of formula codes" — is presented the same way.  It is
not needed for soundness and is stated because the eventual `Con_n` has to
quantify over contexts.

## The context shift

`P_allI` and `P_exE` replace the context `G` by `G.map (rename Nat.succ)`.
Internally that is `ShiftsCtx`, stated *elementwise* rather than by recursion
on the list:

```text
ShiftsCtx H g g'  :=  ∀ x' ∈ g', ∃ x ∈ g, x is a code ∧ Renames H (succMap H) x x'
```

Only this direction is used, and only this direction is cheap.  Defining the
shift by recursion on the list would need a well-founded induction on coded
lists, which the certificate presentation of `MemCtx` does not supply and which
— without Regularity — is not available for a set that merely looks like a
list.  The elementwise reading is what the eigenvariable argument actually
consumes: every formula of the shifted context is a successor-renaming of a
formula of the original, so `satIn_renameV_succMap` applies to it.  Codehood of
the *source* is carried explicitly, because a member of a context is not known
to be a code: `MemCtx` has no descent principle.

## Coded derivations

The presentation is by **ranked certificates**, and the choice is forced.

The bare closure presentation used for renaming does *not* work for
derivations.  There, closure plus inversion sufficed because every clause
decreases the code, so single-valuedness could be proved by code induction.
The inference rules move in both directions: `P_andI` builds a larger
conclusion from smaller ones and `P_andE1` does the reverse, so a set can be
closed under the seventeen clauses with no well-founded justification at all.
Concretely, `{⟨g,a⟩, ⟨g,b⟩, ⟨g, a ∧ b⟩}` is closed — each element is justified
by the others through `P_andI`, `P_andE1`, `P_andE2` — while nothing in it is
derivable.  A closure presentation would prove everything.

The intersection presentation is not available either, for the reason recorded
in `InternalSoundness`: its induction principle says nothing until some closed
set exists, and a set closed under the seventeen clauses would have to record a
pair for every context, hence for every finite list over the class of codes.

What does work is to make the certificate carry a **rank** in the internal
omega and require every premise to be cited at a strictly smaller rank:

```text
DerStep H D n g c   -- ⟨n, g, c⟩ is justified by triples of D at ranks in n
DerClosed H D       -- every triple of D is a code judgement, justified by D
Derives H d g c  :=  DerClosed H d ∧ ∃ n ∈ omega, ⟨n, g, c⟩ ∈ d
```

The derivation code `d` *is* the certificate.  Well-foundedness is now the
well-foundedness of the internal omega, which the definable-induction schema
`omega_ind` supplies, and it is available for nonstandard ranks as well.
Membership `m ∈ n` of von Neumann naturals is the strict order, so the
descent needs no arithmetic beyond `nat_transitive`.

Every clause records codehood of the formulas it introduces as rule
parameters, mirroring the `Form`-valued arguments of the corresponding
constructor of `Prov`; codehood of the conclusion is carried by `DerClosed`
itself.  Codehood is *not* derivable from the code of a compound: the
intersection presentation of `IsFormCodeSem` has no inversion, which is why the
clauses state it rather than extract it.

## Internal soundness

The payoff is `derives_sound`: in an internal set structure, if `d` codes a
derivation of `c` from `g` and every member of `g` is satisfied at an
environment `e`, then `c` is satisfied at `e`.  The induction is on the rank,
by `omega_ind`, so the property has to be a `Form` — `fSoundAtF` — and the
seventeen cases are then the internal transcription of `SetTheory.soundness`.
The quantifier rules consume the substitution lemmas of `InternalSoundness`;
the two eigenvariable rules additionally consume `ShiftsCtx` together with
`satIn_renameV_succMap`.

## Quotation soundness

`derives_of_prov` maps an external derivation to a coded one, by induction on
`Prov` with the rank existentially quantified.  As everywhere in this project
the converse is not attempted and is false in nonstandard models: a nonstandard
rank carries coded derivations that are not the image of any external one.

## What is deliberately absent

No rank bound on codes, no reflection, no `V_alpha`, and no `Con_n`.  Nothing
below asserts that the coded calculus is consistent; what is proved is that it
is sound with respect to internal set structures, which is the hypothesis
reflection will discharge.

## De Bruijn bookkeeping

Every macro carries a table of the slots it introduces.  Slot arguments named
`_i` are ABSOLUTE positions at the use site; each binder shifts the caller's
slots by one and the call sites account for the shift explicitly.
-/

namespace LeanProofs
namespace BoundedZFCConsistency

open SetTheory
open SetTheory.Form

universe u

section CodedDerivation

variable {V : Type u} {mem : V → V → Prop}

/-! ## The order on numerals

Ranks of external derivations are numerals, and the descent condition of a
ranked certificate is internal membership, so the external order has to be
transported once. -/

/-- Numerals of smaller external naturals are internal members.  The step case
is `vsucc_self`; the transitive case is the internal transitivity of naturals,
which is the only arithmetic the ranked certificates need. -/
theorem natV_lt (H : ZFAxioms mem) :
    ∀ j k : Nat, j < k → mem (natV H j) (natV H k) := by
  intro j k
  induction k with
  | zero => intro h; exact absurd h (Nat.not_lt_zero j)
  | succ k ih =>
      intro h
      by_cases hjk : j < k
      · refine nat_transitive H (natV H (k+1)) (natV_mem_omega H (k+1))
          (natV H k) ?_ (natV H j) (ih hjk)
        show mem (natV H k) (vsucc H (natV H k))
        exact vsucc_self H (natV H k)
      · have hje : j = k :=
          Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.mp hjk)
        subst hje
        show mem (natV H j) (vsucc H (natV H j))
        exact vsucc_self H (natV H j)

/-! ## Coded contexts

The two shapes are the nullary and binary shapes of the coding, at tags `0`
and `1` of a namespace of their own. -/

/-- The code of the empty context. -/
noncomputable def ctxNil (H : ZFAxioms mem) : V :=
  kpair H (natV H 0) (vempty H)

/-- The code of the context `a :: l`, with `a` a formula code and `l` a
context code. -/
noncomputable def ctxCons (H : ZFAxioms mem) (a l : V) : V :=
  kpair H (natV H 1) (kpair H a l)

theorem ctxNil_ne_ctxCons (H : ZFAxioms mem) (a l : V) :
    ctxNil H ≠ ctxCons H a l :=
  formCode_tag_ne H (by decide) _ _

theorem ctxCons_inj (H : ZFAxioms mem) {a l a' l' : V}
    (h : ctxCons H a l = ctxCons H a' l') : a = a' ∧ l = l' := by
  unfold ctxCons at h
  exact kpair_inj H _ _ _ _ (kpair_inj H _ _ _ _ h).2

/-! ### Membership, by certificates

A membership certificate is a set of pairs `⟨x, g⟩`.  Both clauses require the
list to be a `ctxCons`, so a pair whose second component is `ctxNil` can never
be justified: that is `memCtx_nil`, and it is the reason the coded contexts
need no well-foundedness assumption. -/

/-- The pair `⟨x, g⟩` is justified by the membership pairs recorded in `S`:
either `x` is the head of `g`, or `x` is already known to belong to the tail. -/
def CtxMemStep (H : ZFAxioms mem) (S x g : V) : Prop :=
  (∃ l, g = ctxCons H x l) ∨
  (∃ a l, g = ctxCons H a l ∧ mem (kpair H x l) S)

theorem ctxMemStep_mono (H : ZFAxioms mem) {S S' x g : V} (hsub : Sub mem S S')
    (h : CtxMemStep H S x g) : CtxMemStep H S' x g := by
  rcases h with h | ⟨a, l, hg, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, l, hg, hsub _ hm⟩

/-- Every pair of `S` is justified by `S`. -/
def CtxMemClosed (H : ZFAxioms mem) (S : V) : Prop :=
  ∀ x g, mem (kpair H x g) S → CtxMemStep H S x g

theorem ctxMemClosed_empty (H : ZFAxioms mem) : CtxMemClosed H (vempty H) :=
  fun _ _ h => absurd h (vempty_spec H _)

theorem ctxMemClosed_insert (H : ZFAxioms mem) {S x g : V}
    (hS : CtxMemClosed H S) (hstep : CtxMemStep H S x g) :
    CtxMemClosed H (vcup H S (vsingle H (kpair H x g))) := by
  have hsub : Sub mem S (vcup H S (vsingle H (kpair H x g))) :=
    fun u hu => (vcup_spec H _ _ u).mpr (Or.inl hu)
  intro y d hmem
  rcases (vcup_spec H S (vsingle H (kpair H x g)) _).mp hmem with h | h
  · exact ctxMemStep_mono H hsub (hS y d h)
  · obtain ⟨e1, e2⟩ :=
      kpair_inj H _ _ _ _ ((vsingle_spec H (kpair H x g) _).mp h)
    rw [e1, e2]
    exact ctxMemStep_mono H hsub hstep

/-- `S` is a **membership certificate** for `⟨x, g⟩`. -/
structure CtxMemCertifies (H : ZFAxioms mem) (S x g : V) : Prop where
  /-- Every pair of the certificate is justified by the certificate. -/
  closed : CtxMemClosed H S
  /-- The pair in question is recorded. -/
  holds : mem (kpair H x g) S

/-- **`x` is a member of the coded context `g`**: some closed set records the
pair. -/
def MemCtx (H : ZFAxioms mem) (x g : V) : Prop :=
  ∃ S, CtxMemCertifies H S x g

theorem memCtx_of_step (H : ZFAxioms mem) {S x g : V} (hS : CtxMemClosed H S)
    (hstep : CtxMemStep H S x g) : MemCtx H x g :=
  ⟨vcup H S (vsingle H (kpair H x g)),
    ctxMemClosed_insert H hS hstep,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-- The head of a context is a member of it. -/
theorem memCtx_head (H : ZFAxioms mem) (x l : V) :
    MemCtx H x (ctxCons H x l) :=
  memCtx_of_step H (ctxMemClosed_empty H) (Or.inl ⟨l, rfl⟩)

/-- A member of the tail is a member of the whole. -/
theorem memCtx_tail (H : ZFAxioms mem) {x l : V} (a : V)
    (h : MemCtx H x l) : MemCtx H x (ctxCons H a l) := by
  obtain ⟨S, hS, hmem⟩ := h
  exact memCtx_of_step H hS (Or.inr ⟨a, l, rfl, hmem⟩)

/-- **The empty context has no members.**  Both clauses of the step demand a
`ctxCons`, and the two tags differ. -/
theorem memCtx_nil (H : ZFAxioms mem) (x : V) : ¬ MemCtx H x (ctxNil H) := by
  rintro ⟨S, hS, hmem⟩
  rcases hS x (ctxNil H) hmem with ⟨l, hg⟩ | ⟨a, l, hg, -⟩
  · exact ctxNil_ne_ctxCons H x l hg
  · exact ctxNil_ne_ctxCons H a l hg

/-- **Inversion at a cons.**  A member of `a :: l` is `a` or a member of `l`. -/
theorem memCtx_cons_inv (H : ZFAxioms mem) {x a l : V}
    (h : MemCtx H x (ctxCons H a l)) : x = a ∨ MemCtx H x l := by
  obtain ⟨S, hS, hmem⟩ := h
  rcases hS x (ctxCons H a l) hmem with ⟨l', hg⟩ | ⟨a', l', hg, hm⟩
  · exact Or.inl (ctxCons_inj H hg.symm).1
  · obtain ⟨-, hl⟩ := ctxCons_inj H hg.symm
    exact Or.inr ⟨S, hS, by rw [← hl]; exact hm⟩

theorem memCtx_cons_iff (H : ZFAxioms mem) (x a l : V) :
    MemCtx H x (ctxCons H a l) ↔ (x = a ∨ MemCtx H x l) := by
  constructor
  · exact memCtx_cons_inv H
  · rintro (rfl | h)
    · exact memCtx_head H x l
    · exact memCtx_tail H a h

/-! ### "Is a context", by certificates

The same device again, now over a set of context codes rather than of pairs.
Nothing below uses `IsCtx`; it is stated because the object-level sentence has
to quantify over contexts, and because it fixes what a context code is allowed
to contain. -/

/-- The context code `g` is justified by the codes recorded in `S`. -/
def CtxStep (H : ZFAxioms mem) (S g : V) : Prop :=
  g = ctxNil H ∨
  (∃ a l, g = ctxCons H a l ∧ IsFormCodeSem H a ∧ mem l S)

theorem ctxStep_mono (H : ZFAxioms mem) {S S' g : V} (hsub : Sub mem S S')
    (h : CtxStep H S g) : CtxStep H S' g := by
  rcases h with h | ⟨a, l, hg, ha, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, l, hg, ha, hsub _ hm⟩

def CtxClosed (H : ZFAxioms mem) (S : V) : Prop :=
  ∀ g, mem g S → CtxStep H S g

theorem ctxClosed_empty (H : ZFAxioms mem) : CtxClosed H (vempty H) :=
  fun _ h => absurd h (vempty_spec H _)

theorem ctxClosed_insert (H : ZFAxioms mem) {S g : V} (hS : CtxClosed H S)
    (hstep : CtxStep H S g) :
    CtxClosed H (vcup H S (vsingle H g)) := by
  have hsub : Sub mem S (vcup H S (vsingle H g)) :=
    fun u hu => (vcup_spec H _ _ u).mpr (Or.inl hu)
  intro d hmem
  rcases (vcup_spec H S (vsingle H g) _).mp hmem with h | h
  · exact ctxStep_mono H hsub (hS d h)
  · rw [(vsingle_spec H g _).mp h]
    exact ctxStep_mono H hsub hstep

/-- **`g` codes a context**: a finite list of formula codes. -/
def IsCtx (H : ZFAxioms mem) (g : V) : Prop :=
  ∃ S, CtxClosed H S ∧ mem g S

theorem isCtx_of_step (H : ZFAxioms mem) {S g : V} (hS : CtxClosed H S)
    (hstep : CtxStep H S g) : IsCtx H g :=
  ⟨vcup H S (vsingle H g), ctxClosed_insert H hS hstep,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

theorem isCtx_nil (H : ZFAxioms mem) : IsCtx H (ctxNil H) :=
  isCtx_of_step H (ctxClosed_empty H) (Or.inl rfl)

theorem isCtx_cons (H : ZFAxioms mem) {a l : V} (ha : IsFormCodeSem H a)
    (hl : IsCtx H l) : IsCtx H (ctxCons H a l) := by
  obtain ⟨S, hS, hmem⟩ := hl
  exact isCtx_of_step H hS (Or.inr ⟨a, l, rfl, ha, hmem⟩)

theorem isCtx_cons_inv (H : ZFAxioms mem) {a l : V}
    (h : IsCtx H (ctxCons H a l)) : IsFormCodeSem H a ∧ IsCtx H l := by
  obtain ⟨S, hS, hmem⟩ := h
  rcases hS _ hmem with hg | ⟨a', l', hg, ha', hm⟩
  · exact absurd hg.symm (ctxNil_ne_ctxCons H a l)
  · obtain ⟨hae, hle⟩ := ctxCons_inj H hg.symm
    exact ⟨by rw [← hae]; exact ha', ⟨S, hS, by rw [← hle]; exact hm⟩⟩

/-! ## Contexts in the object language

The two shapes are read by the tagged macros of `BoundedZFCConsistency.Coding`
and `BoundedZFCConsistency.InternalSat`, at tags `0` and `1`. -/

/-- "slot `i` is the empty context". -/
def fCtxNilF (i : Nat) : Form := fTaggedEmptyF i 0

theorem fCtxNilF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fCtxNilF i) ↔ ee i = ctxNil H :=
  fTaggedEmptyF_spec H ee i 0

/-- "slot `i` is the context with head slot `j` and tail slot `k`". -/
def fCtxConsF (i j k : Nat) : Form := fTagPairF i 1 j k

theorem fCtxConsF_spec (H : ZFAxioms mem) (ee : Nat → V) (i j k : Nat) :
    Sat mem ee (fCtxConsF i j k) ↔ ee i = ctxCons H (ee j) (ee k) :=
  fTagPairF_spec H ee i 1 j k

/-- The membership step, with the certificate in slot `s_i`.

| de Bruijn slot | contents                                   |
| -------------- | ------------------------------------------ |
| `0`            | the tail `l`                               |
| `1`            | the head `a`, in the second clause only    |
| `m+1`, `m+2`   | the caller's slot `m` under 1 or 2 binders |
-/
def fCtxMemStepF (x_i g_i s_i : Nat) : Form :=
  fOr (fEx (fCtxConsF (g_i+1) (x_i+1) 0))
    (fEx (fEx (fAnd (fCtxConsF (g_i+2) 1 0) (fPairMemF (x_i+2) 0 (s_i+2)))))

theorem fCtxMemStepF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (x_i g_i s_i : Nat) :
    Sat mem ee (fCtxMemStepF x_i g_i s_i) ↔
      CtxMemStep H (ee s_i) (ee x_i) (ee g_i) := by
  unfold CtxMemStep
  constructor
  · rintro (⟨l, hl⟩ | ⟨a, l, hg, hm⟩)
    · exact Or.inl ⟨l, (fCtxConsF_spec H (scons l ee) (g_i+1) (x_i+1) 0).mp hl⟩
    · exact Or.inr ⟨a, l,
        (fCtxConsF_spec H (scons l (scons a ee)) (g_i+2) 1 0).mp hg,
        (fPairMemF_spec H (scons l (scons a ee)) (x_i+2) 0 (s_i+2)).mp hm⟩
  · rintro (⟨l, hl⟩ | ⟨a, l, hg, hm⟩)
    · exact Or.inl ⟨l, (fCtxConsF_spec H (scons l ee) (g_i+1) (x_i+1) 0).mpr hl⟩
    · exact Or.inr ⟨a, l,
        (fCtxConsF_spec H (scons l (scons a ee)) (g_i+2) 1 0).mpr hg,
        (fPairMemF_spec H (scons l (scons a ee)) (x_i+2) 0 (s_i+2)).mpr hm⟩

/-- "slot `s_i` is a membership certificate set".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the context `g`       |
| `1`            | the member `x`        |
| `m+2`          | the caller's slot `m` |
-/
def fCtxMemClosedF (s_i : Nat) : Form :=
  fAll (fAll (fImp (fPairMemF 1 0 (s_i+2)) (fCtxMemStepF 1 0 (s_i+2))))

theorem fCtxMemClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (s_i : Nat) :
    Sat mem ee (fCtxMemClosedF s_i) ↔ CtxMemClosed H (ee s_i) := by
  unfold CtxMemClosed
  constructor
  · intro h x g hmem
    exact (fCtxMemStepF_spec H (scons g (scons x ee)) 1 0 (s_i+2)).mp
      (h x g ((fPairMemF_spec H (scons g (scons x ee)) 1 0 (s_i+2)).mpr hmem))
  · intro h x g hsat
    exact (fCtxMemStepF_spec H (scons g (scons x ee)) 1 0 (s_i+2)).mpr
      (h x g ((fPairMemF_spec H (scons g (scons x ee)) 1 0 (s_i+2)).mp hsat))

/-- "slot `x_i` is a member of the context in slot `g_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the certificate `S`   |
| `m+1`          | the caller's slot `m` |
-/
def fMemCtxF (x_i g_i : Nat) : Form :=
  fEx (fAnd (fCtxMemClosedF 0) (fPairMemF (x_i+1) (g_i+1) 0))

theorem fMemCtxF_spec (H : ZFAxioms mem) (ee : Nat → V) (x_i g_i : Nat) :
    Sat mem ee (fMemCtxF x_i g_i) ↔ MemCtx H (ee x_i) (ee g_i) := by
  constructor
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fCtxMemClosedF_spec H (scons S ee) 0).mp hS,
      (fPairMemF_spec H (scons S ee) (x_i+1) (g_i+1) 0).mp hmem⟩
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fCtxMemClosedF_spec H (scons S ee) 0).mpr hS,
      (fPairMemF_spec H (scons S ee) (x_i+1) (g_i+1) 0).mpr hmem⟩

/-- The context step, with the certificate in slot `s_i`.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the tail `l`          |
| `1`            | the head `a`          |
| `m+2`          | the caller's slot `m` |
-/
def fCtxStepF (g_i s_i : Nat) : Form :=
  fOr (fCtxNilF g_i)
    (fEx (fEx (fAnd (fCtxConsF (g_i+2) 1 0)
      (fAnd (fIsFormCodeF 1) (fMem 0 (s_i+2))))))

theorem fCtxStepF_spec (H : ZFAxioms mem) (ee : Nat → V) (g_i s_i : Nat) :
    Sat mem ee (fCtxStepF g_i s_i) ↔ CtxStep H (ee s_i) (ee g_i) := by
  unfold CtxStep
  constructor
  · rintro (h | ⟨a, l, hg, ha, hm⟩)
    · exact Or.inl ((fCtxNilF_spec H ee g_i).mp h)
    · exact Or.inr ⟨a, l,
        (fCtxConsF_spec H (scons l (scons a ee)) (g_i+2) 1 0).mp hg,
        (fIsFormCodeF_spec H (scons l (scons a ee)) 1).mp ha, hm⟩
  · rintro (h | ⟨a, l, hg, ha, hm⟩)
    · exact Or.inl ((fCtxNilF_spec H ee g_i).mpr h)
    · exact Or.inr ⟨a, l,
        (fCtxConsF_spec H (scons l (scons a ee)) (g_i+2) 1 0).mpr hg,
        (fIsFormCodeF_spec H (scons l (scons a ee)) 1).mpr ha, hm⟩

/-- "slot `s_i` is a context-certificate set".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the context `g`       |
| `m+1`          | the caller's slot `m` |
-/
def fCtxClosedF (s_i : Nat) : Form :=
  fAll (fImp (fMem 0 (s_i+1)) (fCtxStepF 0 (s_i+1)))

theorem fCtxClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (s_i : Nat) :
    Sat mem ee (fCtxClosedF s_i) ↔ CtxClosed H (ee s_i) := by
  unfold CtxClosed
  constructor
  · intro h g hmem
    exact (fCtxStepF_spec H (scons g ee) 0 (s_i+1)).mp (h g hmem)
  · intro h g hsat
    exact (fCtxStepF_spec H (scons g ee) 0 (s_i+1)).mpr (h g hsat)

/-- "slot `g_i` codes a context".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the certificate `S`   |
| `m+1`          | the caller's slot `m` |
-/
def fIsCtxF (g_i : Nat) : Form :=
  fEx (fAnd (fCtxClosedF 0) (fMem (g_i+1) 0))

theorem fIsCtxF_spec (H : ZFAxioms mem) (ee : Nat → V) (g_i : Nat) :
    Sat mem ee (fIsCtxF g_i) ↔ IsCtx H (ee g_i) := by
  constructor
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fCtxClosedF_spec H (scons S ee) 0).mp hS, hmem⟩
  · rintro ⟨S, hS, hmem⟩
    exact ⟨S, (fCtxClosedF_spec H (scons S ee) 0).mpr hS, hmem⟩

/-! ## Quotation of external contexts -/

/-- The code of an external context: the internal list of the codes of its
formulas. -/
noncomputable def ctxCode (H : ZFAxioms mem) : List Form → V
  | [] => ctxNil H
  | a :: G => ctxCons H (formCode H a) (ctxCode H G)

theorem ctxCode_nil (H : ZFAxioms mem) : ctxCode H ([] : List Form) = ctxNil H :=
  rfl

theorem ctxCode_cons (H : ZFAxioms mem) (a : Form) (G : List Form) :
    ctxCode H (a :: G) = ctxCons H (formCode H a) (ctxCode H G) := rfl

/-- **Membership of a quoted context is external membership.**  Both directions
are external inductions on the list; the forward one is where `memCtx_nil` and
`memCtx_cons_inv` are used, so it is the reason those had to be proved rather
than assumed. -/
theorem memCtx_ctxCode (H : ZFAxioms mem) (G : List Form) (x : V) :
    MemCtx H x (ctxCode H G) ↔ ∃ a, a ∈ G ∧ x = formCode H a := by
  induction G with
  | nil =>
      constructor
      · intro h; exact absurd h (memCtx_nil H x)
      · rintro ⟨a, ha, -⟩; cases ha
  | cons a G ih =>
      rw [ctxCode_cons]
      constructor
      · intro h
        rcases memCtx_cons_inv H h with h | h
        · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h⟩
        · obtain ⟨b, hb, hx⟩ := ih.mp h
          exact ⟨b, List.mem_cons.mpr (Or.inr hb), hx⟩
      · rintro ⟨b, hb, hx⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [hx]; exact memCtx_head H _ _
        · exact memCtx_tail H _ (ih.mpr ⟨b, hb, hx⟩)

theorem isCtx_ctxCode (H : ZFAxioms mem) (G : List Form) :
    IsCtx H (ctxCode H G) := by
  induction G with
  | nil => exact isCtx_nil H
  | cons a G ih =>
      exact isCtx_cons H (formCode_isFormCodeSem H a) ih

/-! ## The internal successor map in the object language

`succMap H` is a closed term, so rendering it costs one existential over the
identity map and one application of the successor image. -/

/-- "slot `i` is the internal identity map on the omega".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the index `n`         |
| `1`            | the candidate pair    |
| `m+2`          | the caller's slot `m` |
-/
def fIdMapF (i : Nat) : Form :=
  fSetByF i (fEx (fAnd (fNatF 0) (fKPairF 1 0 0)))

theorem fIdMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fIdMapF i) ↔ ee i = idMap H := by
  refine fSetByF_spec H ee i _ (idMap H) (fun p => ?_)
  rw [idMap_spec H p]
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mp hn,
      (fKPairF_spec H (scons n (scons p ee)) 1 0 0).mp hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, (fNatF_spec H (scons n (scons p ee)) 0).mpr hn,
      (fKPairF_spec H (scons n (scons p ee)) 1 0 0).mpr hp⟩

/-- "slot `i` is the internal successor map".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the identity map      |
| `m+1`          | the caller's slot `m` |
-/
def fSuccMapF (i : Nat) : Form :=
  fEx (fAnd (fIdMapF 0) (fSuccValsF (i+1) 0))

theorem fSuccMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fSuccMapF i) ↔ ee i = succMap H := by
  constructor
  · rintro ⟨v, hv, hs⟩
    have hv' : v = idMap H := (fIdMapF_spec H (scons v ee) 0).mp hv
    have hr : IsVarMap H ((scons v ee) 0) := by
      show IsVarMap H v
      rw [hv']
      exact idMap_isVarMap H
    have hval := (fSuccValsF_spec H (scons v ee) (i+1) 0 hr).mp hs
    show ee i = succVals H (idMap H)
    have : ee i = succVals H v := hval
    rw [this, hv']
  · intro h
    refine ⟨idMap H, (fIdMapF_spec H (scons (idMap H) ee) 0).mpr rfl, ?_⟩
    exact (fSuccValsF_spec H (scons (idMap H) ee) (i+1) 0
      (idMap_isVarMap H)).mpr h

/-! ## The context shift

`ShiftsCtx` is elementwise, and carries codehood of the source formula, because
membership in a coded context does not by itself entail that the member is a
code — `MemCtx` has intro and inversion rules but no descent principle. -/

/-- **`g'` is the successor shift of the context `g`**: every member of `g'` is
the successor renaming of a coded member of `g`. -/
def ShiftsCtx (H : ZFAxioms mem) (g g' : V) : Prop :=
  ∀ x', MemCtx H x' g' →
    ∃ x, IsFormCodeSem H x ∧ MemCtx H x g ∧ Renames H (succMap H) x x'

/-- "the context in slot `g'_i` is the successor shift of the one in slot
`g_i`".

| de Bruijn slot | contents                             |
| -------------- | ------------------------------------ |
| `0`            | the member `x'` of the shift         |
| `1`            | under one further binder, the source |
| `2`, `3`       | the source `x`, then the successor map |
| `m+1` … `m+3`  | the caller's slot `m`                |
-/
def fShiftsCtxF (g_i g'_i : Nat) : Form :=
  fAll (fImp (fMemCtxF 0 (g'_i+1))
    (fEx (fAnd (fIsFormCodeF 0)
      (fAnd (fMemCtxF 0 (g_i+2))
        (fEx (fAnd (fSuccMapF 0) (fRenamesF 0 1 2)))))))

theorem fShiftsCtxF_spec (H : ZFAxioms mem) (ee : Nat → V) (g_i g'_i : Nat) :
    Sat mem ee (fShiftsCtxF g_i g'_i) ↔ ShiftsCtx H (ee g_i) (ee g'_i) := by
  unfold ShiftsCtx
  constructor
  · intro h x' hx'
    obtain ⟨x, hcode, hmem, sm, hsm, hren⟩ :=
      h x' ((fMemCtxF_spec H (scons x' ee) 0 (g'_i+1)).mpr hx')
    refine ⟨x, (fIsFormCodeF_spec H (scons x (scons x' ee)) 0).mp hcode,
      (fMemCtxF_spec H (scons x (scons x' ee)) 0 (g_i+2)).mp hmem, ?_⟩
    have hsm' : sm = succMap H :=
      (fSuccMapF_spec H (scons sm (scons x (scons x' ee))) 0).mp hsm
    have hren' :=
      (fRenamesF_spec H (scons sm (scons x (scons x' ee))) 0 1 2).mp hren
    rw [hsm'] at hren'
    exact hren'
  · intro h x' hx'
    obtain ⟨x, hcode, hmem, hren⟩ :=
      h x' ((fMemCtxF_spec H (scons x' ee) 0 (g'_i+1)).mp hx')
    refine ⟨x, (fIsFormCodeF_spec H (scons x (scons x' ee)) 0).mpr hcode,
      (fMemCtxF_spec H (scons x (scons x' ee)) 0 (g_i+2)).mpr hmem,
      succMap H,
      (fSuccMapF_spec H (scons (succMap H) (scons x (scons x' ee))) 0).mpr rfl,
      ?_⟩
    exact (fRenamesF_spec H (scons (succMap H) (scons x (scons x' ee)))
      0 1 2).mpr hren

/-- **Quotation soundness for the context shift.**  The code of
`G.map (rename Nat.succ)` is the successor shift of the code of `G`. -/
theorem shiftsCtx_ctxCode (H : ZFAxioms mem) (G : List Form) :
    ShiftsCtx H (ctxCode H G) (ctxCode H (G.map (rename Nat.succ))) := by
  intro x' hx'
  obtain ⟨b, hb, hx⟩ := (memCtx_ctxCode H _ x').mp hx'
  rw [List.mem_map] at hb
  obtain ⟨a, ha, rfl⟩ := hb
  refine ⟨formCode H a, formCode_isFormCodeSem H a,
    (memCtx_ctxCode H G _).mpr ⟨a, ha, rfl⟩, ?_⟩
  rw [hx]
  exact renames_formCode H a (succMap H) Nat.succ (succMap_isVarMap H)
    (succMap_agreesWith H)

/-! ## Coded derivations

A derivation triple is `⟨n, ⟨g, c⟩⟩`: a rank, a context code and a conclusion
code.  That is the shape of `satTriple`, so the triple is written with
`satTriple H n g c` and the macro `fTripleMemF` reads it unchanged.  The shape
is shared with the evaluation triples of `InternalSat` and the renaming triples
of `InternalSoundness`; the meanings are not, and nothing below mixes them.

The rank is what makes the presentation well founded.  A premise is *cited* at
a rank strictly below the rank of the conclusion, and `∈` between von Neumann
naturals is that strict order. -/

/-- The judgement `⟨g, c⟩` is recorded in `D` at some rank below `n`. -/
def DerCite (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ m, mem m n ∧ mem (satTriple H m g c) D

theorem derCite_mono (H : ZFAxioms mem) {D D' n g c : V} (hsub : Sub mem D D')
    (h : DerCite H D n g c) : DerCite H D' n g c := by
  obtain ⟨m, hm, hmem⟩ := h
  exact ⟨m, hm, hsub _ hmem⟩

/-- A judgement recorded at the numeral rank `j` is cited at every larger
numeral rank. -/
theorem derCite_of_natV (H : ZFAxioms mem) {D g c : V} {j k : Nat}
    (hjk : j < k) (h : mem (satTriple H (natV H j) g c) D) :
    DerCite H D (natV H k) g c :=
  ⟨natV H j, natV_lt H j k hjk, h⟩

/-! ### The seventeen clauses

Each clause is the internal transcription of one constructor of
`SetTheory.Prov`.  A clause states codehood of every formula it introduces as a
rule parameter — that is, of every `Form`-valued argument of the corresponding
constructor which is not the conclusion of a cited premise.  Codehood of the
conclusion is carried by `DerClosed`, and codehood is never *extracted* from a
compound code, because the intersection presentation of `IsFormCodeSem` has no
inversion rule. -/

/-- Assumption. -/
def DAss (H : ZFAxioms mem) (g c : V) : Prop := MemCtx H c g

/-- Implication introduction. -/
def DImpI (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a b, IsFormCodeSem H a ∧ c = kpair H (natV H 3) (kpair H a b) ∧
    DerCite H D n (ctxCons H a g) b

/-- Implication elimination. -/
def DImpE (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a, IsFormCodeSem H a ∧
    DerCite H D n g (kpair H (natV H 3) (kpair H a c)) ∧ DerCite H D n g a

/-- Ex falso. -/
def DBotE (H : ZFAxioms mem) (D n g : V) : Prop :=
  DerCite H D n g (kpair H (natV H 2) (vempty H))

/-- Excluded middle. -/
def DLem (H : ZFAxioms mem) (c : V) : Prop :=
  ∃ a, IsFormCodeSem H a ∧
    c = kpair H (natV H 5) (kpair H a
      (kpair H (natV H 3) (kpair H a (kpair H (natV H 2) (vempty H)))))

/-- Conjunction introduction. -/
def DAndI (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a b, c = kpair H (natV H 4) (kpair H a b) ∧
    DerCite H D n g a ∧ DerCite H D n g b

/-- First conjunction elimination. -/
def DAndE1 (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ b, IsFormCodeSem H b ∧
    DerCite H D n g (kpair H (natV H 4) (kpair H c b))

/-- Second conjunction elimination. -/
def DAndE2 (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a, IsFormCodeSem H a ∧
    DerCite H D n g (kpair H (natV H 4) (kpair H a c))

/-- First disjunction introduction. -/
def DOrI1 (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a b, IsFormCodeSem H a ∧ IsFormCodeSem H b ∧
    c = kpair H (natV H 5) (kpair H a b) ∧ DerCite H D n g a

/-- Second disjunction introduction. -/
def DOrI2 (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a b, IsFormCodeSem H a ∧ IsFormCodeSem H b ∧
    c = kpair H (natV H 5) (kpair H a b) ∧ DerCite H D n g b

/-- Disjunction elimination. -/
def DOrE (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a b, IsFormCodeSem H a ∧ IsFormCodeSem H b ∧
    DerCite H D n g (kpair H (natV H 5) (kpair H a b)) ∧
    DerCite H D n (ctxCons H a g) c ∧ DerCite H D n (ctxCons H b g) c

/-- Universal introduction, over a successor shift of the context. -/
def DAllI (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a g', IsFormCodeSem H a ∧ c = kpair H (natV H 6) a ∧
    ShiftsCtx H g g' ∧ DerCite H D n g' a

/-- Universal elimination, at an internal variable index. -/
def DAllE (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a k, IsFormCodeSem H a ∧ mem k (omegaV H) ∧
    Renames H (instMap H k) a c ∧
    DerCite H D n g (kpair H (natV H 6) a)

/-- Existential introduction, at an internal variable index. -/
def DExI (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a k a', IsFormCodeSem H a ∧ mem k (omegaV H) ∧
    c = kpair H (natV H 7) a ∧ Renames H (instMap H k) a a' ∧
    DerCite H D n g a'

/-- Existential elimination, over a successor shift of the context. -/
def DExE (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ a g' c', IsFormCodeSem H a ∧ ShiftsCtx H g g' ∧
    Renames H (succMap H) c c' ∧
    DerCite H D n g (kpair H (natV H 7) a) ∧
    DerCite H D n (ctxCons H a g') c'

/-- Reflexivity of equality. -/
def DEqRefl (H : ZFAxioms mem) (c : V) : Prop :=
  ∃ k, mem k (omegaV H) ∧ c = kpair H (natV H 1) (kpair H k k)

/-- The Leibniz rule. -/
def DEqElim (H : ZFAxioms mem) (D n g c : V) : Prop :=
  ∃ i j a ci, mem i (omegaV H) ∧ mem j (omegaV H) ∧ IsFormCodeSem H a ∧
    Renames H (instMap H i) a ci ∧ Renames H (instMap H j) a c ∧
    DerCite H D n g (kpair H (natV H 1) (kpair H i j)) ∧
    DerCite H D n g ci

/-- The triple `⟨n, g, c⟩` is justified by the judgements recorded in `D` at
ranks below `n`, by one of the seventeen rules. -/
def DerStep (H : ZFAxioms mem) (D n g c : V) : Prop :=
  DAss H g c ∨ DImpI H D n g c ∨ DImpE H D n g c ∨ DBotE H D n g ∨
  DLem H c ∨ DAndI H D n g c ∨ DAndE1 H D n g c ∨ DAndE2 H D n g c ∨
  DOrI1 H D n g c ∨ DOrI2 H D n g c ∨ DOrE H D n g c ∨ DAllI H D n g c ∨
  DAllE H D n g c ∨ DExI H D n g c ∨ DExE H D n g c ∨ DEqRefl H c ∨
  DEqElim H D n g c

/-! ### The seventeen introduction forms

Written once, so that every later construction names its rule instead of
counting disjuncts. -/

theorem derStep_ass (H : ZFAxioms mem) {D n g c : V} (h : DAss H g c) :
    DerStep H D n g c := Or.inl h

theorem derStep_impI (H : ZFAxioms mem) {D n g c : V} (h : DImpI H D n g c) :
    DerStep H D n g c := Or.inr (Or.inl h)

theorem derStep_impE (H : ZFAxioms mem) {D n g c : V} (h : DImpE H D n g c) :
    DerStep H D n g c := Or.inr (Or.inr (Or.inl h))

theorem derStep_botE (H : ZFAxioms mem) {D n g c : V} (h : DBotE H D n g) :
    DerStep H D n g c := Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem derStep_lem (H : ZFAxioms mem) {D n g c : V} (h : DLem H c) :
    DerStep H D n g c := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem derStep_andI (H : ZFAxioms mem) {D n g c : V} (h : DAndI H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem derStep_andE1 (H : ZFAxioms mem) {D n g c : V} (h : DAndE1 H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem derStep_andE2 (H : ZFAxioms mem) {D n g c : V} (h : DAndE2 H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

theorem derStep_orI1 (H : ZFAxioms mem) {D n g c : V} (h : DOrI1 H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h))))))))

theorem derStep_orI2 (H : ZFAxioms mem) {D n g c : V} (h : DOrI2 H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl h)))))))))

theorem derStep_orE (H : ZFAxioms mem) {D n g c : V} (h : DOrE H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl h))))))))))

theorem derStep_allI (H : ZFAxioms mem) {D n g c : V} (h : DAllI H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl h)))))))))))

theorem derStep_allE (H : ZFAxioms mem) {D n g c : V} (h : DAllE H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))

theorem derStep_exI (H : ZFAxioms mem) {D n g c : V} (h : DExI H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))

theorem derStep_exE (H : ZFAxioms mem) {D n g c : V} (h : DExE H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))

theorem derStep_eqRefl (H : ZFAxioms mem) {D n g c : V} (h : DEqRefl H c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))

theorem derStep_eqElim (H : ZFAxioms mem) {D n g c : V} (h : DEqElim H D n g c) :
    DerStep H D n g c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))

/-- Every clause is positive in the set of established judgements, so the step
is monotone.  This is what lets certificates be combined by union. -/
theorem derStep_mono (H : ZFAxioms mem) {D D' n g c : V} (hsub : Sub mem D D')
    (h : DerStep H D n g c) : DerStep H D' n g c := by
  have hc : ∀ m a b, DerCite H D m a b → DerCite H D' m a b :=
    fun _ _ _ => derCite_mono H hsub
  rcases h with h | ⟨a, b, h1, h2, h3⟩ | ⟨a, h1, h2, h3⟩ | h | h |
    ⟨a, b, h1, h2, h3⟩ | ⟨b, h1, h2⟩ | ⟨a, h1, h2⟩ |
    ⟨a, b, h1, h2, h3, h4⟩ | ⟨a, b, h1, h2, h3, h4⟩ |
    ⟨a, b, h1, h2, h3, h4, h5⟩ | ⟨a, g', h1, h2, h3, h4⟩ |
    ⟨a, k, h1, h2, h3, h4⟩ | ⟨a, k, a', h1, h2, h3, h4, h5⟩ |
    ⟨a, g', c', h1, h2, h3, h4, h5⟩ | h |
    ⟨i, j, a, ci, h1, h2, h3, h4, h5, h6, h7⟩
  · exact derStep_ass H h
  · exact derStep_impI H ⟨a, b, h1, h2, hc _ _ _ h3⟩
  · exact derStep_impE H ⟨a, h1, hc _ _ _ h2, hc _ _ _ h3⟩
  · exact derStep_botE H (hc _ _ _ h)
  · exact derStep_lem H h
  · exact derStep_andI H ⟨a, b, h1, hc _ _ _ h2, hc _ _ _ h3⟩
  · exact derStep_andE1 H ⟨b, h1, hc _ _ _ h2⟩
  · exact derStep_andE2 H ⟨a, h1, hc _ _ _ h2⟩
  · exact derStep_orI1 H ⟨a, b, h1, h2, h3, hc _ _ _ h4⟩
  · exact derStep_orI2 H ⟨a, b, h1, h2, h3, hc _ _ _ h4⟩
  · exact derStep_orE H
      ⟨a, b, h1, h2, hc _ _ _ h3, hc _ _ _ h4, hc _ _ _ h5⟩
  · exact derStep_allI H ⟨a, g', h1, h2, h3, hc _ _ _ h4⟩
  · exact derStep_allE H ⟨a, k, h1, h2, h3, hc _ _ _ h4⟩
  · exact derStep_exI H ⟨a, k, a', h1, h2, h3, h4, hc _ _ _ h5⟩
  · exact derStep_exE H ⟨a, g', c', h1, h2, h3, hc _ _ _ h4, hc _ _ _ h5⟩
  · exact derStep_eqRefl H h
  · exact derStep_eqElim H
      ⟨i, j, a, ci, h1, h2, h3, h4, h5, hc _ _ _ h6, hc _ _ _ h7⟩

/-! ### Certificates -/

/-- Every triple of `D` is a code judgement at an internal rank, justified by
`D` at strictly smaller ranks. -/
def DerClosed (H : ZFAxioms mem) (D : V) : Prop :=
  ∀ n g c, mem (satTriple H n g c) D →
    (mem n (omegaV H) ∧ IsFormCodeSem H c ∧ DerStep H D n g c)

theorem derClosed_empty (H : ZFAxioms mem) : DerClosed H (vempty H) :=
  fun _ _ _ h => absurd h (vempty_spec H _)

theorem derClosed_cup (H : ZFAxioms mem) {D1 D2 : V} (h1 : DerClosed H D1)
    (h2 : DerClosed H D2) : DerClosed H (vcup H D1 D2) := by
  intro n g c hmem
  rcases (vcup_spec H D1 D2 _).mp hmem with h | h
  · obtain ⟨hn, hc, hstep⟩ := h1 n g c h
    exact ⟨hn, hc, derStep_mono H
      (fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inl hx)) hstep⟩
  · obtain ⟨hn, hc, hstep⟩ := h2 n g c h
    exact ⟨hn, hc, derStep_mono H
      (fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inr hx)) hstep⟩

/-- Adjoining a single justified judgement keeps a set closed. -/
theorem derClosed_insert (H : ZFAxioms mem) {D n g c : V} (hD : DerClosed H D)
    (hn : mem n (omegaV H)) (hc : IsFormCodeSem H c)
    (hstep : DerStep H D n g c) :
    DerClosed H (vcup H D (vsingle H (satTriple H n g c))) := by
  have hsub : Sub mem D (vcup H D (vsingle H (satTriple H n g c))) :=
    fun x hx => (vcup_spec H _ _ x).mpr (Or.inl hx)
  intro m d e hmem
  rcases (vcup_spec H D (vsingle H (satTriple H n g c)) _).mp hmem with h | h
  · obtain ⟨hm, he, hs⟩ := hD m d e h
    exact ⟨hm, he, derStep_mono H hsub hs⟩
  · obtain ⟨e1, e2, e3⟩ :=
      satTriple_inj H ((vsingle_spec H (satTriple H n g c) _).mp h)
    rw [e1, e2, e3]
    exact ⟨hn, hc, derStep_mono H hsub hstep⟩

/-- **`d` codes a derivation of `c` from `g`**: `d` is a ranked certificate
recording the judgement at some internal rank. -/
def Derives (H : ZFAxioms mem) (d g c : V) : Prop :=
  DerClosed H d ∧ ∃ n, mem n (omegaV H) ∧ mem (satTriple H n g c) d

theorem Derives.isFormCodeSem (H : ZFAxioms mem) {d g c : V}
    (h : Derives H d g c) : IsFormCodeSem H c := by
  obtain ⟨hD, n, -, hmem⟩ := h
  exact (hD n g c hmem).2.1

/-- A justified judgement over a closed set can always be adjoined. -/
theorem derives_of_step (H : ZFAxioms mem) {D n g c : V} (hD : DerClosed H D)
    (hn : mem n (omegaV H)) (hc : IsFormCodeSem H c)
    (hstep : DerStep H D n g c) :
    ∃ D', DerClosed H D' ∧ mem (satTriple H n g c) D' :=
  ⟨vcup H D (vsingle H (satTriple H n g c)),
    derClosed_insert H hD hn hc hstep,
    (vcup_spec H _ _ _).mpr (Or.inr ((vsingle_spec H _ _).mpr rfl))⟩

/-! ## The derivation predicate as a `Form`

One macro per rule, each with an exact satisfaction spec, then the seventeen
disjuncts and the two outer layers.  Nothing here unfolds a macro: every proof
goes through the spec of its constituents, which is what keeps the formulas —
several of which are large, `fShiftsCtxF` and `fRenamesF` in particular — out
of the elaborator's way. -/

/-- "slot `i` is the internal instantiation map at slot `k_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the identity map      |
| `m+1`          | the caller's slot `m` |
-/
def fInstMapF (i k_i : Nat) : Form :=
  fEx (fAnd (fIdMapF 0) (fEconsF (i+1) (k_i+1) 0))

theorem fInstMapF_spec (H : ZFAxioms mem) (ee : Nat → V) (i k_i : Nat) :
    Sat mem ee (fInstMapF i k_i) ↔ ee i = instMap H (ee k_i) := by
  constructor
  · rintro ⟨v, hv, hs⟩
    have hv' : v = idMap H := (fIdMapF_spec H (scons v ee) 0).mp hv
    have hfun : ∀ x y y', mem (kpair H x y) ((scons v ee) 0) →
        mem (kpair H x y') ((scons v ee) 0) → y = y' := by
      show ∀ x y y', mem (kpair H x y) v → mem (kpair H x y') v → y = y'
      rw [hv']
      exact (idMap_isVarMap H).1.1
    have hval := (fEconsF_spec H (scons v ee) (i+1) (k_i+1) 0 hfun).mp hs
    show ee i = econs H (ee k_i) (idMap H)
    have hv2 : ee i = econs H (ee k_i) v := hval
    rw [hv2, hv']
  · intro h
    refine ⟨idMap H, (fIdMapF_spec H (scons (idMap H) ee) 0).mpr rfl, ?_⟩
    exact (fEconsF_spec H (scons (idMap H) ee) (i+1) (k_i+1) 0
      (idMap_isVarMap H).1.1).mpr h

/-- "the judgement ⟨slot `g_i`, slot `c_i`⟩ is recorded in slot `d_i` at a rank
below slot `n_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the smaller rank `m`  |
| `m+1`          | the caller's slot `m` |
-/
def fDerCiteF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fAnd (fMem 0 (n_i+1)) (fTripleMemF 0 (g_i+1) (c_i+1) (d_i+1)))

theorem fDerCiteF_spec (H : ZFAxioms mem) (ee : Nat → V) (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDerCiteF d_i n_i g_i c_i) ↔
      DerCite H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DerCite
  constructor
  · rintro ⟨m, hm, hmem⟩
    exact ⟨m, hm,
      (fTripleMemF_spec H (scons m ee) 0 (g_i+1) (c_i+1) (d_i+1)).mp hmem⟩
  · rintro ⟨m, hm, hmem⟩
    exact ⟨m, hm,
      (fTripleMemF_spec H (scons m ee) 0 (g_i+1) (c_i+1) (d_i+1)).mpr hmem⟩

/-! ### The seventeen clauses in the object language -/

def fDAssF (g_i c_i : Nat) : Form := fMemCtxF c_i g_i

theorem fDAssF_spec (H : ZFAxioms mem) (ee : Nat → V) (g_i c_i : Nat) :
    Sat mem ee (fDAssF g_i c_i) ↔ DAss H (ee g_i) (ee c_i) :=
  fMemCtxF_spec H ee c_i g_i

def fDImpIF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fIsFormCodeF 1)
    (fAnd (fTagPairF (c_i+2) 3 1 0)
      (fEx (fAnd (fCtxConsF 0 2 (g_i+3))
        (fDerCiteF (d_i+3) (n_i+3) 0 1))))))

theorem fDImpIF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDImpIF d_i n_i g_i c_i) ↔
      DImpI H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DImpI
  constructor
  · rintro ⟨a, b, ha, hce, w, hw, hcite⟩
    refine ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mp ha,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 3 1 0).mp hce, ?_⟩
    have hw' :=
      (fCtxConsF_spec H (scons w (scons b (scons a ee))) 0 2 (g_i+3)).mp hw
    have hcite' :=
      (fDerCiteF_spec H (scons w (scons b (scons a ee)))
        (d_i+3) (n_i+3) 0 1).mp hcite
    rw [hw'] at hcite'
    exact hcite'
  · rintro ⟨a, b, ha, hce, hcite⟩
    exact ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mpr ha,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 3 1 0).mpr hce,
      ctxCons H a (ee g_i),
      (fCtxConsF_spec H (scons (ctxCons H a (ee g_i)) (scons b (scons a ee)))
        0 2 (g_i+3)).mpr rfl,
      (fDerCiteF_spec H (scons (ctxCons H a (ee g_i)) (scons b (scons a ee)))
        (d_i+3) (n_i+3) 0 1).mpr hcite⟩

def fDImpEF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fAnd (fIsFormCodeF 0)
    (fAnd (fEx (fAnd (fTagPairF 0 3 1 (c_i+2))
              (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 0)))
          (fDerCiteF (d_i+1) (n_i+1) (g_i+1) 0)))

theorem fDImpEF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDImpEF d_i n_i g_i c_i) ↔
      DImpE H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DImpE
  constructor
  · rintro ⟨a, ha, ⟨w, hw, h1⟩, h2⟩
    refine ⟨a, (fIsFormCodeF_spec H (scons a ee) 0).mp ha, ?_,
      (fDerCiteF_spec H (scons a ee) (d_i+1) (n_i+1) (g_i+1) 0).mp h2⟩
    have hw' := (fTagPairF_spec H (scons w (scons a ee)) 0 3 1 (c_i+2)).mp hw
    have h1' := (fDerCiteF_spec H (scons w (scons a ee))
      (d_i+2) (n_i+2) (g_i+2) 0).mp h1
    rw [hw'] at h1'
    exact h1'
  · rintro ⟨a, ha, h1, h2⟩
    refine ⟨a, (fIsFormCodeF_spec H (scons a ee) 0).mpr ha, ⟨
      kpair H (natV H 3) (kpair H a (ee c_i)), ?_, ?_⟩,
      (fDerCiteF_spec H (scons a ee) (d_i+1) (n_i+1) (g_i+1) 0).mpr h2⟩
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 3) (kpair H a (ee c_i))) (scons a ee))
        0 3 1 (c_i+2)).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 3) (kpair H a (ee c_i))) (scons a ee))
        (d_i+2) (n_i+2) (g_i+2) 0).mpr h1

def fDBotEF (d_i n_i g_i : Nat) : Form :=
  fEx (fAnd (fTaggedEmptyF 0 2) (fDerCiteF (d_i+1) (n_i+1) (g_i+1) 0))

theorem fDBotEF_spec (H : ZFAxioms mem) (ee : Nat → V) (d_i n_i g_i : Nat) :
    Sat mem ee (fDBotEF d_i n_i g_i) ↔
      DBotE H (ee d_i) (ee n_i) (ee g_i) := by
  unfold DBotE
  constructor
  · rintro ⟨w, hw, h⟩
    have hw' := (fTaggedEmptyF_spec H (scons w ee) 0 2).mp hw
    have h' := (fDerCiteF_spec H (scons w ee) (d_i+1) (n_i+1) (g_i+1) 0).mp h
    rw [hw'] at h'
    exact h'
  · intro h
    refine ⟨kpair H (natV H 2) (vempty H), ?_, ?_⟩
    · exact (fTaggedEmptyF_spec H
        (scons (kpair H (natV H 2) (vempty H)) ee) 0 2).mpr rfl
    · exact (fDerCiteF_spec H (scons (kpair H (natV H 2) (vempty H)) ee)
        (d_i+1) (n_i+1) (g_i+1) 0).mpr h

def fDLemF (c_i : Nat) : Form :=
  fEx (fAnd (fIsFormCodeF 0)
    (fEx (fAnd (fTaggedEmptyF 0 2)
      (fEx (fAnd (fTagPairF 0 3 2 1) (fTagPairF (c_i+3) 5 2 0))))))

theorem fDLemF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i : Nat) :
    Sat mem ee (fDLemF c_i) ↔ DLem H (ee c_i) := by
  unfold DLem
  constructor
  · rintro ⟨a, ha, z, hz, w, hw, hc⟩
    refine ⟨a, (fIsFormCodeF_spec H (scons a ee) 0).mp ha, ?_⟩
    have hz' : z = kpair H (natV H 2) (vempty H) :=
      (fTaggedEmptyF_spec H (scons z (scons a ee)) 0 2).mp hz
    have hw' : w = kpair H (natV H 3) (kpair H a z) :=
      (fTagPairF_spec H (scons w (scons z (scons a ee))) 0 3 2 1).mp hw
    have hc' : ee c_i = kpair H (natV H 5) (kpair H a w) :=
      (fTagPairF_spec H (scons w (scons z (scons a ee))) (c_i+3) 5 2 0).mp hc
    rw [hc', hw', hz']
  · rintro ⟨a, ha, hc⟩
    refine ⟨a, (fIsFormCodeF_spec H (scons a ee) 0).mpr ha,
      kpair H (natV H 2) (vempty H), ?_,
      kpair H (natV H 3) (kpair H a (kpair H (natV H 2) (vempty H))), ?_, ?_⟩
    · exact (fTaggedEmptyF_spec H
        (scons (kpair H (natV H 2) (vempty H)) (scons a ee)) 0 2).mpr rfl
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 3) (kpair H a (kpair H (natV H 2) (vempty H))))
          (scons (kpair H (natV H 2) (vempty H)) (scons a ee)))
        0 3 2 1).mpr rfl
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 3) (kpair H a (kpair H (natV H 2) (vempty H))))
          (scons (kpair H (natV H 2) (vempty H)) (scons a ee)))
        (c_i+3) 5 2 0).mpr hc

def fDAndIF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fTagPairF (c_i+2) 4 1 0)
    (fAnd (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 1)
          (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 0))))

theorem fDAndIF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDAndIF d_i n_i g_i c_i) ↔
      DAndI H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DAndI
  constructor
  · rintro ⟨a, b, hce, h1, h2⟩
    exact ⟨a, b,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 4 1 0).mp hce,
      (fDerCiteF_spec H (scons b (scons a ee)) (d_i+2) (n_i+2) (g_i+2) 1).mp h1,
      (fDerCiteF_spec H (scons b (scons a ee)) (d_i+2) (n_i+2) (g_i+2) 0).mp h2⟩
  · rintro ⟨a, b, hce, h1, h2⟩
    exact ⟨a, b,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 4 1 0).mpr hce,
      (fDerCiteF_spec H (scons b (scons a ee))
        (d_i+2) (n_i+2) (g_i+2) 1).mpr h1,
      (fDerCiteF_spec H (scons b (scons a ee))
        (d_i+2) (n_i+2) (g_i+2) 0).mpr h2⟩

def fDAndE1F (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fAnd (fIsFormCodeF 0)
    (fEx (fAnd (fTagPairF 0 4 (c_i+2) 1)
      (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 0))))

theorem fDAndE1F_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDAndE1F d_i n_i g_i c_i) ↔
      DAndE1 H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DAndE1
  constructor
  · rintro ⟨b, hb, w, hw, h⟩
    refine ⟨b, (fIsFormCodeF_spec H (scons b ee) 0).mp hb, ?_⟩
    have hw' := (fTagPairF_spec H (scons w (scons b ee)) 0 4 (c_i+2) 1).mp hw
    have h' := (fDerCiteF_spec H (scons w (scons b ee))
      (d_i+2) (n_i+2) (g_i+2) 0).mp h
    rw [hw'] at h'
    exact h'
  · rintro ⟨b, hb, h⟩
    refine ⟨b, (fIsFormCodeF_spec H (scons b ee) 0).mpr hb,
      kpair H (natV H 4) (kpair H (ee c_i) b), ?_, ?_⟩
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 4) (kpair H (ee c_i) b)) (scons b ee))
        0 4 (c_i+2) 1).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 4) (kpair H (ee c_i) b)) (scons b ee))
        (d_i+2) (n_i+2) (g_i+2) 0).mpr h

def fDAndE2F (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fAnd (fIsFormCodeF 0)
    (fEx (fAnd (fTagPairF 0 4 1 (c_i+2))
      (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 0))))

theorem fDAndE2F_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDAndE2F d_i n_i g_i c_i) ↔
      DAndE2 H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DAndE2
  constructor
  · rintro ⟨a, ha, w, hw, h⟩
    refine ⟨a, (fIsFormCodeF_spec H (scons a ee) 0).mp ha, ?_⟩
    have hw' := (fTagPairF_spec H (scons w (scons a ee)) 0 4 1 (c_i+2)).mp hw
    have h' := (fDerCiteF_spec H (scons w (scons a ee))
      (d_i+2) (n_i+2) (g_i+2) 0).mp h
    rw [hw'] at h'
    exact h'
  · rintro ⟨a, ha, h⟩
    refine ⟨a, (fIsFormCodeF_spec H (scons a ee) 0).mpr ha,
      kpair H (natV H 4) (kpair H a (ee c_i)), ?_, ?_⟩
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 4) (kpair H a (ee c_i))) (scons a ee))
        0 4 1 (c_i+2)).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 4) (kpair H a (ee c_i))) (scons a ee))
        (d_i+2) (n_i+2) (g_i+2) 0).mpr h

def fDOrI1F (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fIsFormCodeF 1) (fAnd (fIsFormCodeF 0)
    (fAnd (fTagPairF (c_i+2) 5 1 0)
          (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 1)))))

theorem fDOrI1F_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDOrI1F d_i n_i g_i c_i) ↔
      DOrI1 H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DOrI1
  constructor
  · rintro ⟨a, b, ha, hb, hce, h⟩
    exact ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mp ha,
      (fIsFormCodeF_spec H (scons b (scons a ee)) 0).mp hb,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 5 1 0).mp hce,
      (fDerCiteF_spec H (scons b (scons a ee)) (d_i+2) (n_i+2) (g_i+2) 1).mp h⟩
  · rintro ⟨a, b, ha, hb, hce, h⟩
    exact ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mpr ha,
      (fIsFormCodeF_spec H (scons b (scons a ee)) 0).mpr hb,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 5 1 0).mpr hce,
      (fDerCiteF_spec H (scons b (scons a ee))
        (d_i+2) (n_i+2) (g_i+2) 1).mpr h⟩

def fDOrI2F (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fIsFormCodeF 1) (fAnd (fIsFormCodeF 0)
    (fAnd (fTagPairF (c_i+2) 5 1 0)
          (fDerCiteF (d_i+2) (n_i+2) (g_i+2) 0)))))

theorem fDOrI2F_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDOrI2F d_i n_i g_i c_i) ↔
      DOrI2 H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DOrI2
  constructor
  · rintro ⟨a, b, ha, hb, hce, h⟩
    exact ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mp ha,
      (fIsFormCodeF_spec H (scons b (scons a ee)) 0).mp hb,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 5 1 0).mp hce,
      (fDerCiteF_spec H (scons b (scons a ee)) (d_i+2) (n_i+2) (g_i+2) 0).mp h⟩
  · rintro ⟨a, b, ha, hb, hce, h⟩
    exact ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mpr ha,
      (fIsFormCodeF_spec H (scons b (scons a ee)) 0).mpr hb,
      (fTagPairF_spec H (scons b (scons a ee)) (c_i+2) 5 1 0).mpr hce,
      (fDerCiteF_spec H (scons b (scons a ee))
        (d_i+2) (n_i+2) (g_i+2) 0).mpr h⟩

def fDOrEF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fIsFormCodeF 1) (fAnd (fIsFormCodeF 0)
    (fAnd (fEx (fAnd (fTagPairF 0 5 2 1)
                (fDerCiteF (d_i+3) (n_i+3) (g_i+3) 0)))
      (fAnd (fEx (fAnd (fCtxConsF 0 2 (g_i+3))
                  (fDerCiteF (d_i+3) (n_i+3) 0 (c_i+3))))
            (fEx (fAnd (fCtxConsF 0 1 (g_i+3))
                  (fDerCiteF (d_i+3) (n_i+3) 0 (c_i+3)))))))))

theorem fDOrEF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDOrEF d_i n_i g_i c_i) ↔
      DOrE H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DOrE
  constructor
  · rintro ⟨a, b, ha, hb, ⟨w, hw, h1⟩, ⟨u, hu, h2⟩, ⟨v, hv, h3⟩⟩
    refine ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mp ha,
      (fIsFormCodeF_spec H (scons b (scons a ee)) 0).mp hb, ?_, ?_, ?_⟩
    · have hw' :=
        (fTagPairF_spec H (scons w (scons b (scons a ee))) 0 5 2 1).mp hw
      have h1' := (fDerCiteF_spec H (scons w (scons b (scons a ee)))
        (d_i+3) (n_i+3) (g_i+3) 0).mp h1
      rw [hw'] at h1'
      exact h1'
    · have hu' :=
        (fCtxConsF_spec H (scons u (scons b (scons a ee))) 0 2 (g_i+3)).mp hu
      have h2' := (fDerCiteF_spec H (scons u (scons b (scons a ee)))
        (d_i+3) (n_i+3) 0 (c_i+3)).mp h2
      rw [hu'] at h2'
      exact h2'
    · have hv' :=
        (fCtxConsF_spec H (scons v (scons b (scons a ee))) 0 1 (g_i+3)).mp hv
      have h3' := (fDerCiteF_spec H (scons v (scons b (scons a ee)))
        (d_i+3) (n_i+3) 0 (c_i+3)).mp h3
      rw [hv'] at h3'
      exact h3'
  · rintro ⟨a, b, ha, hb, h1, h2, h3⟩
    refine ⟨a, b, (fIsFormCodeF_spec H (scons b (scons a ee)) 1).mpr ha,
      (fIsFormCodeF_spec H (scons b (scons a ee)) 0).mpr hb,
      ⟨kpair H (natV H 5) (kpair H a b), ?_, ?_⟩,
      ⟨ctxCons H a (ee g_i), ?_, ?_⟩,
      ⟨ctxCons H b (ee g_i), ?_, ?_⟩⟩
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 5) (kpair H a b)) (scons b (scons a ee)))
        0 5 2 1).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 5) (kpair H a b)) (scons b (scons a ee)))
        (d_i+3) (n_i+3) (g_i+3) 0).mpr h1
    · exact (fCtxConsF_spec H
        (scons (ctxCons H a (ee g_i)) (scons b (scons a ee)))
        0 2 (g_i+3)).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (ctxCons H a (ee g_i)) (scons b (scons a ee)))
        (d_i+3) (n_i+3) 0 (c_i+3)).mpr h2
    · exact (fCtxConsF_spec H
        (scons (ctxCons H b (ee g_i)) (scons b (scons a ee)))
        0 1 (g_i+3)).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (ctxCons H b (ee g_i)) (scons b (scons a ee)))
        (d_i+3) (n_i+3) 0 (c_i+3)).mpr h3

def fDAllIF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fIsFormCodeF 1)
    (fAnd (fTagUnF (c_i+2) 6 1)
      (fAnd (fShiftsCtxF (g_i+2) 0) (fDerCiteF (d_i+2) (n_i+2) 0 1)))))

theorem fDAllIF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDAllIF d_i n_i g_i c_i) ↔
      DAllI H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DAllI
  constructor
  · rintro ⟨a, g', ha, hce, hsh, h⟩
    exact ⟨a, g', (fIsFormCodeF_spec H (scons g' (scons a ee)) 1).mp ha,
      (fTagUnF_spec H (scons g' (scons a ee)) (c_i+2) 6 1).mp hce,
      (fShiftsCtxF_spec H (scons g' (scons a ee)) (g_i+2) 0).mp hsh,
      (fDerCiteF_spec H (scons g' (scons a ee)) (d_i+2) (n_i+2) 0 1).mp h⟩
  · rintro ⟨a, g', ha, hce, hsh, h⟩
    exact ⟨a, g', (fIsFormCodeF_spec H (scons g' (scons a ee)) 1).mpr ha,
      (fTagUnF_spec H (scons g' (scons a ee)) (c_i+2) 6 1).mpr hce,
      (fShiftsCtxF_spec H (scons g' (scons a ee)) (g_i+2) 0).mpr hsh,
      (fDerCiteF_spec H (scons g' (scons a ee)) (d_i+2) (n_i+2) 0 1).mpr h⟩

def fDAllEF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fAnd (fIsFormCodeF 1) (fAnd (fNatF 0)
    (fAnd (fEx (fAnd (fInstMapF 0 1) (fRenamesF 0 2 (c_i+3))))
          (fEx (fAnd (fTagUnF 0 6 2)
                (fDerCiteF (d_i+3) (n_i+3) (g_i+3) 0)))))))

theorem fDAllEF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDAllEF d_i n_i g_i c_i) ↔
      DAllE H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DAllE
  constructor
  · rintro ⟨a, k, ha, hk, ⟨r, hr, hren⟩, ⟨w, hw, h⟩⟩
    refine ⟨a, k, (fIsFormCodeF_spec H (scons k (scons a ee)) 1).mp ha,
      (fNatF_spec H (scons k (scons a ee)) 0).mp hk, ?_, ?_⟩
    · have hr' :=
        (fInstMapF_spec H (scons r (scons k (scons a ee))) 0 1).mp hr
      have hren' :=
        (fRenamesF_spec H (scons r (scons k (scons a ee))) 0 2 (c_i+3)).mp hren
      rw [hr'] at hren'
      exact hren'
    · have hw' :=
        (fTagUnF_spec H (scons w (scons k (scons a ee))) 0 6 2).mp hw
      have h' := (fDerCiteF_spec H (scons w (scons k (scons a ee)))
        (d_i+3) (n_i+3) (g_i+3) 0).mp h
      rw [hw'] at h'
      exact h'
  · rintro ⟨a, k, ha, hk, hren, h⟩
    refine ⟨a, k, (fIsFormCodeF_spec H (scons k (scons a ee)) 1).mpr ha,
      (fNatF_spec H (scons k (scons a ee)) 0).mpr hk,
      ⟨instMap H k, ?_, ?_⟩, ⟨kpair H (natV H 6) a, ?_, ?_⟩⟩
    · exact (fInstMapF_spec H
        (scons (instMap H k) (scons k (scons a ee))) 0 1).mpr rfl
    · exact (fRenamesF_spec H
        (scons (instMap H k) (scons k (scons a ee))) 0 2 (c_i+3)).mpr hren
    · exact (fTagUnF_spec H
        (scons (kpair H (natV H 6) a) (scons k (scons a ee))) 0 6 2).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 6) a) (scons k (scons a ee)))
        (d_i+3) (n_i+3) (g_i+3) 0).mpr h

def fDExIF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fEx (fAnd (fIsFormCodeF 2) (fAnd (fNatF 1)
    (fAnd (fTagUnF (c_i+3) 7 2)
      (fAnd (fEx (fAnd (fInstMapF 0 2) (fRenamesF 0 3 1)))
            (fDerCiteF (d_i+3) (n_i+3) (g_i+3) 0)))))))

theorem fDExIF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDExIF d_i n_i g_i c_i) ↔
      DExI H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DExI
  constructor
  · rintro ⟨a, k, a', ha, hk, hce, ⟨r, hr, hren⟩, h⟩
    refine ⟨a, k, a',
      (fIsFormCodeF_spec H (scons a' (scons k (scons a ee))) 2).mp ha,
      (fNatF_spec H (scons a' (scons k (scons a ee))) 1).mp hk,
      (fTagUnF_spec H (scons a' (scons k (scons a ee))) (c_i+3) 7 2).mp hce,
      ?_,
      (fDerCiteF_spec H (scons a' (scons k (scons a ee)))
        (d_i+3) (n_i+3) (g_i+3) 0).mp h⟩
    have hr' :=
      (fInstMapF_spec H (scons r (scons a' (scons k (scons a ee)))) 0 2).mp hr
    have hren' :=
      (fRenamesF_spec H (scons r (scons a' (scons k (scons a ee))))
        0 3 1).mp hren
    rw [hr'] at hren'
    exact hren'
  · rintro ⟨a, k, a', ha, hk, hce, hren, h⟩
    refine ⟨a, k, a',
      (fIsFormCodeF_spec H (scons a' (scons k (scons a ee))) 2).mpr ha,
      (fNatF_spec H (scons a' (scons k (scons a ee))) 1).mpr hk,
      (fTagUnF_spec H (scons a' (scons k (scons a ee))) (c_i+3) 7 2).mpr hce,
      ⟨instMap H k, ?_, ?_⟩,
      (fDerCiteF_spec H (scons a' (scons k (scons a ee)))
        (d_i+3) (n_i+3) (g_i+3) 0).mpr h⟩
    · exact (fInstMapF_spec H
        (scons (instMap H k) (scons a' (scons k (scons a ee)))) 0 2).mpr rfl
    · exact (fRenamesF_spec H
        (scons (instMap H k) (scons a' (scons k (scons a ee))))
        0 3 1).mpr hren

def fDExEF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fEx (fAnd (fIsFormCodeF 2)
    (fAnd (fShiftsCtxF (g_i+3) 1)
      (fAnd (fEx (fAnd (fSuccMapF 0) (fRenamesF 0 (c_i+4) 1)))
        (fAnd (fEx (fAnd (fTagUnF 0 7 3)
                    (fDerCiteF (d_i+4) (n_i+4) (g_i+4) 0)))
              (fEx (fAnd (fCtxConsF 0 3 2)
                    (fDerCiteF (d_i+4) (n_i+4) 0 1)))))))))

theorem fDExEF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDExEF d_i n_i g_i c_i) ↔
      DExE H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DExE
  constructor
  · rintro ⟨a, g', c', ha, hsh, ⟨sm, hsm, hren⟩, ⟨w, hw, h1⟩, ⟨u, hu, h2⟩⟩
    refine ⟨a, g', c',
      (fIsFormCodeF_spec H (scons c' (scons g' (scons a ee))) 2).mp ha,
      (fShiftsCtxF_spec H (scons c' (scons g' (scons a ee))) (g_i+3) 1).mp hsh,
      ?_, ?_, ?_⟩
    · have hsm' :=
        (fSuccMapF_spec H (scons sm (scons c' (scons g' (scons a ee)))) 0).mp hsm
      have hren' :=
        (fRenamesF_spec H (scons sm (scons c' (scons g' (scons a ee))))
          0 (c_i+4) 1).mp hren
      rw [hsm'] at hren'
      exact hren'
    · have hw' :=
        (fTagUnF_spec H (scons w (scons c' (scons g' (scons a ee)))) 0 7 3).mp hw
      have h1' := (fDerCiteF_spec H (scons w (scons c' (scons g' (scons a ee))))
        (d_i+4) (n_i+4) (g_i+4) 0).mp h1
      rw [hw'] at h1'
      exact h1'
    · have hu' :=
        (fCtxConsF_spec H (scons u (scons c' (scons g' (scons a ee))))
          0 3 2).mp hu
      have h2' := (fDerCiteF_spec H (scons u (scons c' (scons g' (scons a ee))))
        (d_i+4) (n_i+4) 0 1).mp h2
      rw [hu'] at h2'
      exact h2'
  · rintro ⟨a, g', c', ha, hsh, hren, h1, h2⟩
    refine ⟨a, g', c',
      (fIsFormCodeF_spec H (scons c' (scons g' (scons a ee))) 2).mpr ha,
      (fShiftsCtxF_spec H (scons c' (scons g' (scons a ee))) (g_i+3) 1).mpr hsh,
      ⟨succMap H, ?_, ?_⟩, ⟨kpair H (natV H 7) a, ?_, ?_⟩,
      ⟨ctxCons H a g', ?_, ?_⟩⟩
    · exact (fSuccMapF_spec H
        (scons (succMap H) (scons c' (scons g' (scons a ee)))) 0).mpr rfl
    · exact (fRenamesF_spec H
        (scons (succMap H) (scons c' (scons g' (scons a ee))))
        0 (c_i+4) 1).mpr hren
    · exact (fTagUnF_spec H
        (scons (kpair H (natV H 7) a) (scons c' (scons g' (scons a ee))))
        0 7 3).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 7) a) (scons c' (scons g' (scons a ee))))
        (d_i+4) (n_i+4) (g_i+4) 0).mpr h1
    · exact (fCtxConsF_spec H
        (scons (ctxCons H a g') (scons c' (scons g' (scons a ee))))
        0 3 2).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (ctxCons H a g') (scons c' (scons g' (scons a ee))))
        (d_i+4) (n_i+4) 0 1).mpr h2

def fDEqReflF (c_i : Nat) : Form :=
  fEx (fAnd (fNatF 0) (fTagPairF (c_i+1) 1 0 0))

theorem fDEqReflF_spec (H : ZFAxioms mem) (ee : Nat → V) (c_i : Nat) :
    Sat mem ee (fDEqReflF c_i) ↔ DEqRefl H (ee c_i) := by
  unfold DEqRefl
  constructor
  · rintro ⟨k, hk, hce⟩
    exact ⟨k, (fNatF_spec H (scons k ee) 0).mp hk,
      (fTagPairF_spec H (scons k ee) (c_i+1) 1 0 0).mp hce⟩
  · rintro ⟨k, hk, hce⟩
    exact ⟨k, (fNatF_spec H (scons k ee) 0).mpr hk,
      (fTagPairF_spec H (scons k ee) (c_i+1) 1 0 0).mpr hce⟩

def fDEqElimF (d_i n_i g_i c_i : Nat) : Form :=
  fEx (fEx (fEx (fEx (fAnd (fNatF 3) (fAnd (fNatF 2) (fAnd (fIsFormCodeF 1)
    (fAnd (fEx (fAnd (fInstMapF 0 4) (fRenamesF 0 2 1)))
      (fAnd (fEx (fAnd (fInstMapF 0 3) (fRenamesF 0 2 (c_i+5))))
        (fAnd (fEx (fAnd (fTagPairF 0 1 4 3)
                    (fDerCiteF (d_i+5) (n_i+5) (g_i+5) 0)))
              (fDerCiteF (d_i+4) (n_i+4) (g_i+4) 0))))))))))

theorem fDEqElimF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDEqElimF d_i n_i g_i c_i) ↔
      DEqElim H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DEqElim
  constructor
  · rintro ⟨i, j, a, ci, hi, hj, ha, ⟨r1, hr1, hren1⟩, ⟨r2, hr2, hren2⟩,
      ⟨w, hw, h1⟩, h2⟩
    refine ⟨i, j, a, ci,
      (fNatF_spec H (scons ci (scons a (scons j (scons i ee)))) 3).mp hi,
      (fNatF_spec H (scons ci (scons a (scons j (scons i ee)))) 2).mp hj,
      (fIsFormCodeF_spec H (scons ci (scons a (scons j (scons i ee)))) 1).mp ha,
      ?_, ?_, ?_,
      (fDerCiteF_spec H (scons ci (scons a (scons j (scons i ee))))
        (d_i+4) (n_i+4) (g_i+4) 0).mp h2⟩
    · have hr1' := (fInstMapF_spec H
        (scons r1 (scons ci (scons a (scons j (scons i ee))))) 0 4).mp hr1
      have hren1' := (fRenamesF_spec H
        (scons r1 (scons ci (scons a (scons j (scons i ee))))) 0 2 1).mp hren1
      rw [hr1'] at hren1'
      exact hren1'
    · have hr2' := (fInstMapF_spec H
        (scons r2 (scons ci (scons a (scons j (scons i ee))))) 0 3).mp hr2
      have hren2' := (fRenamesF_spec H
        (scons r2 (scons ci (scons a (scons j (scons i ee)))))
        0 2 (c_i+5)).mp hren2
      rw [hr2'] at hren2'
      exact hren2'
    · have hw' := (fTagPairF_spec H
        (scons w (scons ci (scons a (scons j (scons i ee))))) 0 1 4 3).mp hw
      have h1' := (fDerCiteF_spec H
        (scons w (scons ci (scons a (scons j (scons i ee)))))
        (d_i+5) (n_i+5) (g_i+5) 0).mp h1
      rw [hw'] at h1'
      exact h1'
  · rintro ⟨i, j, a, ci, hi, hj, ha, hren1, hren2, h1, h2⟩
    refine ⟨i, j, a, ci,
      (fNatF_spec H (scons ci (scons a (scons j (scons i ee)))) 3).mpr hi,
      (fNatF_spec H (scons ci (scons a (scons j (scons i ee)))) 2).mpr hj,
      (fIsFormCodeF_spec H (scons ci (scons a (scons j (scons i ee)))) 1).mpr ha,
      ⟨instMap H i, ?_, ?_⟩, ⟨instMap H j, ?_, ?_⟩,
      ⟨kpair H (natV H 1) (kpair H i j), ?_, ?_⟩,
      (fDerCiteF_spec H (scons ci (scons a (scons j (scons i ee))))
        (d_i+4) (n_i+4) (g_i+4) 0).mpr h2⟩
    · exact (fInstMapF_spec H
        (scons (instMap H i) (scons ci (scons a (scons j (scons i ee)))))
        0 4).mpr rfl
    · exact (fRenamesF_spec H
        (scons (instMap H i) (scons ci (scons a (scons j (scons i ee)))))
        0 2 1).mpr hren1
    · exact (fInstMapF_spec H
        (scons (instMap H j) (scons ci (scons a (scons j (scons i ee)))))
        0 3).mpr rfl
    · exact (fRenamesF_spec H
        (scons (instMap H j) (scons ci (scons a (scons j (scons i ee)))))
        0 2 (c_i+5)).mpr hren2
    · exact (fTagPairF_spec H
        (scons (kpair H (natV H 1) (kpair H i j))
          (scons ci (scons a (scons j (scons i ee))))) 0 1 4 3).mpr rfl
    · exact (fDerCiteF_spec H
        (scons (kpair H (natV H 1) (kpair H i j))
          (scons ci (scons a (scons j (scons i ee)))))
        (d_i+5) (n_i+5) (g_i+5) 0).mpr h1

/-! ### The step, the certificate condition, and the predicate -/

/-- "the triple ⟨slot `n_i`, slot `g_i`, slot `c_i`⟩ is justified by the
certificate in slot `d_i`" — the seventeen clauses, in the order of `Prov`. -/
def fDerStepF (d_i n_i g_i c_i : Nat) : Form :=
  fOr (fDAssF g_i c_i)
   (fOr (fDImpIF d_i n_i g_i c_i)
    (fOr (fDImpEF d_i n_i g_i c_i)
     (fOr (fDBotEF d_i n_i g_i)
      (fOr (fDLemF c_i)
       (fOr (fDAndIF d_i n_i g_i c_i)
        (fOr (fDAndE1F d_i n_i g_i c_i)
         (fOr (fDAndE2F d_i n_i g_i c_i)
          (fOr (fDOrI1F d_i n_i g_i c_i)
           (fOr (fDOrI2F d_i n_i g_i c_i)
            (fOr (fDOrEF d_i n_i g_i c_i)
             (fOr (fDAllIF d_i n_i g_i c_i)
              (fOr (fDAllEF d_i n_i g_i c_i)
               (fOr (fDExIF d_i n_i g_i c_i)
                (fOr (fDExEF d_i n_i g_i c_i)
                 (fOr (fDEqReflF c_i)
                      (fDEqElimF d_i n_i g_i c_i))))))))))))))))

theorem fDerStepF_spec (H : ZFAxioms mem) (ee : Nat → V)
    (d_i n_i g_i c_i : Nat) :
    Sat mem ee (fDerStepF d_i n_i g_i c_i) ↔
      DerStep H (ee d_i) (ee n_i) (ee g_i) (ee c_i) := by
  unfold DerStep
  constructor
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
    · exact Or.inl ((fDAssF_spec H ee g_i c_i).mp h)
    · exact derStep_impI H ((fDImpIF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_impE H ((fDImpEF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_botE H ((fDBotEF_spec H ee d_i n_i g_i).mp h)
    · exact derStep_lem H ((fDLemF_spec H ee c_i).mp h)
    · exact derStep_andI H ((fDAndIF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_andE1 H ((fDAndE1F_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_andE2 H ((fDAndE2F_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_orI1 H ((fDOrI1F_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_orI2 H ((fDOrI2F_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_orE H ((fDOrEF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_allI H ((fDAllIF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_allE H ((fDAllEF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_exI H ((fDExIF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_exE H ((fDExEF_spec H ee d_i n_i g_i c_i).mp h)
    · exact derStep_eqRefl H ((fDEqReflF_spec H ee c_i).mp h)
    · exact derStep_eqElim H ((fDEqElimF_spec H ee d_i n_i g_i c_i).mp h)
  · rintro (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)
    · exact Or.inl ((fDAssF_spec H ee g_i c_i).mpr h)
    · exact Or.inr (Or.inl ((fDImpIF_spec H ee d_i n_i g_i c_i).mpr h))
    · exact Or.inr (Or.inr (Or.inl
        ((fDImpEF_spec H ee d_i n_i g_i c_i).mpr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((fDBotEF_spec H ee d_i n_i g_i).mpr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((fDLemF_spec H ee c_i).mpr h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((fDAndIF_spec H ee d_i n_i g_i c_i).mpr h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((fDAndE1F_spec H ee d_i n_i g_i c_i).mpr h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((fDAndE2F_spec H ee d_i n_i g_i c_i).mpr h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ((fDOrI1F_spec H ee d_i n_i g_i c_i).mpr h)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ((fDOrI2F_spec H ee d_i n_i g_i c_i).mpr h))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl
          ((fDOrEF_spec H ee d_i n_i g_i c_i).mpr h)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl
          ((fDAllIF_spec H ee d_i n_i g_i c_i).mpr h))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((fDAllEF_spec H ee d_i n_i g_i c_i).mpr h)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((fDExIF_spec H ee d_i n_i g_i c_i).mpr h))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((fDExEF_spec H ee d_i n_i g_i c_i).mpr h)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ((fDEqReflF_spec H ee c_i).mpr h))))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ((fDEqElimF_spec H ee d_i n_i g_i c_i).mpr h))))))))))))))))

/-- "slot `d_i` is a ranked derivation certificate".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the conclusion `c`    |
| `1`            | the context `g`       |
| `2`            | the rank `n`          |
| `m+3`          | the caller's slot `m` |
-/
def fDerClosedF (d_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF 2 1 0 (d_i+3))
    (fAnd (fNatF 2) (fAnd (fIsFormCodeF 0) (fDerStepF (d_i+3) 2 1 0))))))

theorem fDerClosedF_spec (H : ZFAxioms mem) (ee : Nat → V) (d_i : Nat) :
    Sat mem ee (fDerClosedF d_i) ↔ DerClosed H (ee d_i) := by
  unfold DerClosed
  constructor
  · intro h n g c hmem
    obtain ⟨h1, h2, h3⟩ := h n g c
      ((fTripleMemF_spec H (scons c (scons g (scons n ee)))
        2 1 0 (d_i+3)).mpr hmem)
    exact ⟨(fNatF_spec H (scons c (scons g (scons n ee))) 2).mp h1,
      (fIsFormCodeF_spec H (scons c (scons g (scons n ee))) 0).mp h2,
      (fDerStepF_spec H (scons c (scons g (scons n ee)))
        (d_i+3) 2 1 0).mp h3⟩
  · intro h n g c hsat
    obtain ⟨h1, h2, h3⟩ := h n g c
      ((fTripleMemF_spec H (scons c (scons g (scons n ee)))
        2 1 0 (d_i+3)).mp hsat)
    exact ⟨(fNatF_spec H (scons c (scons g (scons n ee))) 2).mpr h1,
      (fIsFormCodeF_spec H (scons c (scons g (scons n ee))) 0).mpr h2,
      (fDerStepF_spec H (scons c (scons g (scons n ee)))
        (d_i+3) 2 1 0).mpr h3⟩

/-- **"slot `d_i` codes a derivation of slot `c_i` from slot `g_i`", as a
`Form`.**

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the rank `n`          |
| `m+1`          | the caller's slot `m` |
-/
def fDerivesF (d_i g_i c_i : Nat) : Form :=
  fAnd (fDerClosedF d_i)
    (fEx (fAnd (fNatF 0) (fTripleMemF 0 (g_i+1) (c_i+1) (d_i+1))))

/-- The object-language predicate means exactly the semantic one.  This is what
lets the eventual `Con_n(ZFC)` quantify over coded derivations while the
surrounding reasoning stays on the semantic side. -/
theorem fDerivesF_spec (H : ZFAxioms mem) (ee : Nat → V) (d_i g_i c_i : Nat) :
    Sat mem ee (fDerivesF d_i g_i c_i) ↔
      Derives H (ee d_i) (ee g_i) (ee c_i) := by
  unfold Derives
  constructor
  · rintro ⟨hD, n, hn, hmem⟩
    exact ⟨(fDerClosedF_spec H ee d_i).mp hD, n,
      (fNatF_spec H (scons n ee) 0).mp hn,
      (fTripleMemF_spec H (scons n ee) 0 (g_i+1) (c_i+1) (d_i+1)).mp hmem⟩
  · rintro ⟨hD, n, hn, hmem⟩
    exact ⟨(fDerClosedF_spec H ee d_i).mpr hD, n,
      (fNatF_spec H (scons n ee) 0).mpr hn,
      (fTripleMemF_spec H (scons n ee) 0 (g_i+1) (c_i+1) (d_i+1)).mpr hmem⟩

/-! ## Quotation soundness for derivations

An external derivation becomes a coded one, with the rank existentially
quantified: the induction is on `Prov` itself, which is legitimate because the
conclusion is a `Prop`.  A rule with several premises unions their certificates
and takes a rank above all of theirs, so `natV_lt` is what makes the premises
citable.

The converse is false in nonstandard models — a nonstandard rank carries coded
derivations that are the image of no external one — and is not attempted. -/

/-- The rank-explicit form of quotation soundness. -/
theorem provCode_of_prov (H : ZFAxioms mem) {G : List Form} {a : Form}
    (h : Prov G a) :
    ∃ (k : Nat) (D : V), DerClosed H D ∧
      mem (satTriple H (natV H k) (ctxCode H G) (formCode H a)) D := by
  induction h with
  | P_ass G a hin =>
      obtain ⟨D, hD, hmem⟩ :=
        derives_of_step H (derClosed_empty H) (natV_mem_omega H 0)
          (formCode_isFormCodeSem H a)
          (derStep_ass H ((memCtx_ctxCode H G _).mpr ⟨a, hin, rfl⟩))
      exact ⟨0, D, hD, hmem⟩
  | P_impI G a b _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H (fImp a b))
          (derStep_impI H ⟨formCode H a, formCode H b,
            formCode_isFormCodeSem H a, rfl,
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨k+1, D', hD', hmem'⟩
  | P_impE G a b _ _ ihab iha =>
      obtain ⟨k1, D1, hD1, hm1⟩ := ihab
      obtain ⟨k2, D2, hD2, hm2⟩ := iha
      have hs1 : Sub mem D1 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inl hx)
      have hs2 : Sub mem D2 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inr hx)
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H (derClosed_cup H hD1 hD2)
          (natV_mem_omega H (k1 + k2 + 1))
          (formCode_isFormCodeSem H b)
          (derStep_impE H ⟨formCode H a, formCode_isFormCodeSem H a,
            derCite_of_natV H (by omega) (hs1 _ hm1),
            derCite_of_natV H (by omega) (hs2 _ hm2)⟩)
      exact ⟨k1 + k2 + 1, D', hD', hmem'⟩
  | P_botE G a _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H a)
          (derStep_botE H (derCite_of_natV H (by omega) hmem))
      exact ⟨k+1, D', hD', hmem'⟩
  | P_lem G a =>
      obtain ⟨D, hD, hmem⟩ :=
        derives_of_step H (derClosed_empty H) (natV_mem_omega H 0)
          (formCode_isFormCodeSem H (fOr a (fImp a fBot)))
          (derStep_lem H ⟨formCode H a, formCode_isFormCodeSem H a, rfl⟩)
      exact ⟨0, D, hD, hmem⟩
  | P_andI G a b _ _ iha ihb =>
      obtain ⟨k1, D1, hD1, hm1⟩ := iha
      obtain ⟨k2, D2, hD2, hm2⟩ := ihb
      have hs1 : Sub mem D1 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inl hx)
      have hs2 : Sub mem D2 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inr hx)
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H (derClosed_cup H hD1 hD2)
          (natV_mem_omega H (k1 + k2 + 1))
          (formCode_isFormCodeSem H (fAnd a b))
          (derStep_andI H ⟨formCode H a, formCode H b, rfl,
            derCite_of_natV H (by omega) (hs1 _ hm1),
            derCite_of_natV H (by omega) (hs2 _ hm2)⟩)
      exact ⟨k1 + k2 + 1, D', hD', hmem'⟩
  | P_andE1 G a b _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H a)
          (derStep_andE1 H ⟨formCode H b, formCode_isFormCodeSem H b,
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨k+1, D', hD', hmem'⟩
  | P_andE2 G a b _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H b)
          (derStep_andE2 H ⟨formCode H a, formCode_isFormCodeSem H a,
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨k+1, D', hD', hmem'⟩
  | P_orI1 G a b _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H (fOr a b))
          (derStep_orI1 H ⟨formCode H a, formCode H b,
            formCode_isFormCodeSem H a, formCode_isFormCodeSem H b, rfl,
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨k+1, D', hD', hmem'⟩
  | P_orI2 G a b _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H (fOr a b))
          (derStep_orI2 H ⟨formCode H a, formCode H b,
            formCode_isFormCodeSem H a, formCode_isFormCodeSem H b, rfl,
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨k+1, D', hD', hmem'⟩
  | P_orE G a b c _ _ _ ihor iha ihb =>
      obtain ⟨k1, D1, hD1, hm1⟩ := ihor
      obtain ⟨k2, D2, hD2, hm2⟩ := iha
      obtain ⟨k3, D3, hD3, hm3⟩ := ihb
      have hs1 : Sub mem D1 (vcup H (vcup H D1 D2) D3) := fun x hx =>
        (vcup_spec H _ D3 x).mpr (Or.inl ((vcup_spec H D1 D2 x).mpr (Or.inl hx)))
      have hs2 : Sub mem D2 (vcup H (vcup H D1 D2) D3) := fun x hx =>
        (vcup_spec H _ D3 x).mpr (Or.inl ((vcup_spec H D1 D2 x).mpr (Or.inr hx)))
      have hs3 : Sub mem D3 (vcup H (vcup H D1 D2) D3) := fun x hx =>
        (vcup_spec H _ D3 x).mpr (Or.inr hx)
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H (derClosed_cup H (derClosed_cup H hD1 hD2) hD3)
          (natV_mem_omega H (k1 + k2 + k3 + 1))
          (formCode_isFormCodeSem H c)
          (derStep_orE H ⟨formCode H a, formCode H b,
            formCode_isFormCodeSem H a, formCode_isFormCodeSem H b,
            derCite_of_natV H (by omega) (hs1 _ hm1),
            derCite_of_natV H (by omega) (hs2 _ hm2),
            derCite_of_natV H (by omega) (hs3 _ hm3)⟩)
      exact ⟨k1 + k2 + k3 + 1, D', hD', hmem'⟩
  | P_allI G a _ ih =>
      obtain ⟨k, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (k+1))
          (formCode_isFormCodeSem H (fAll a))
          (derStep_allI H ⟨formCode H a, ctxCode H (G.map (rename Nat.succ)),
            formCode_isFormCodeSem H a, rfl, shiftsCtx_ctxCode H G,
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨k+1, D', hD', hmem'⟩
  | P_allE G a k _ ih =>
      obtain ⟨r, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (r+1))
          (formCode_isFormCodeSem H (rename (inst k) a))
          (derStep_allE H ⟨formCode H a, natV H k,
            formCode_isFormCodeSem H a, natV_mem_omega H k,
            renames_formCode H a (instMap H (natV H k)) (inst k)
              (instMap_isVarMap H (natV_mem_omega H k))
              (instMap_agreesWith H k),
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨r+1, D', hD', hmem'⟩
  | P_exI G a k _ ih =>
      obtain ⟨r, D, hD, hmem⟩ := ih
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H hD (natV_mem_omega H (r+1))
          (formCode_isFormCodeSem H (fEx a))
          (derStep_exI H ⟨formCode H a, natV H k,
            formCode H (rename (inst k) a),
            formCode_isFormCodeSem H a, natV_mem_omega H k, rfl,
            renames_formCode H a (instMap H (natV H k)) (inst k)
              (instMap_isVarMap H (natV_mem_omega H k))
              (instMap_agreesWith H k),
            derCite_of_natV H (by omega) hmem⟩)
      exact ⟨r+1, D', hD', hmem'⟩
  | P_exE G a c _ _ ihex ihbody =>
      obtain ⟨k1, D1, hD1, hm1⟩ := ihex
      obtain ⟨k2, D2, hD2, hm2⟩ := ihbody
      have hs1 : Sub mem D1 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inl hx)
      have hs2 : Sub mem D2 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inr hx)
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H (derClosed_cup H hD1 hD2)
          (natV_mem_omega H (k1 + k2 + 1))
          (formCode_isFormCodeSem H c)
          (derStep_exE H ⟨formCode H a, ctxCode H (G.map (rename Nat.succ)),
            formCode H (rename Nat.succ c),
            formCode_isFormCodeSem H a, shiftsCtx_ctxCode H G,
            renames_formCode H c (succMap H) Nat.succ (succMap_isVarMap H)
              (succMap_agreesWith H),
            derCite_of_natV H (by omega) (hs1 _ hm1),
            derCite_of_natV H (by omega) (hs2 _ hm2)⟩)
      exact ⟨k1 + k2 + 1, D', hD', hmem'⟩
  | P_eqRefl G k =>
      obtain ⟨D, hD, hmem⟩ :=
        derives_of_step H (derClosed_empty H) (natV_mem_omega H 0)
          (formCode_isFormCodeSem H (fEq k k))
          (derStep_eqRefl H ⟨natV H k, natV_mem_omega H k, rfl⟩)
      exact ⟨0, D, hD, hmem⟩
  | P_eqElim G i j a _ _ iheq iha =>
      obtain ⟨k1, D1, hD1, hm1⟩ := iheq
      obtain ⟨k2, D2, hD2, hm2⟩ := iha
      have hs1 : Sub mem D1 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inl hx)
      have hs2 : Sub mem D2 (vcup H D1 D2) :=
        fun x hx => (vcup_spec H D1 D2 x).mpr (Or.inr hx)
      obtain ⟨D', hD', hmem'⟩ :=
        derives_of_step H (derClosed_cup H hD1 hD2)
          (natV_mem_omega H (k1 + k2 + 1))
          (formCode_isFormCodeSem H (rename (inst j) a))
          (derStep_eqElim H ⟨natV H i, natV H j, formCode H a,
            formCode H (rename (inst i) a),
            natV_mem_omega H i, natV_mem_omega H j,
            formCode_isFormCodeSem H a,
            renames_formCode H a (instMap H (natV H i)) (inst i)
              (instMap_isVarMap H (natV_mem_omega H i))
              (instMap_agreesWith H i),
            renames_formCode H a (instMap H (natV H j)) (inst j)
              (instMap_isVarMap H (natV_mem_omega H j))
              (instMap_agreesWith H j),
            derCite_of_natV H (by omega) (hs1 _ hm1),
            derCite_of_natV H (by omega) (hs2 _ hm2)⟩)
      exact ⟨k1 + k2 + 1, D', hD', hmem'⟩

/-- **Quotation soundness.**  Every external derivation is coded by some
internal certificate. -/
theorem derives_of_prov (H : ZFAxioms mem) {G : List Form} {a : Form}
    (h : Prov G a) : ∃ d, Derives H d (ctxCode H G) (formCode H a) := by
  obtain ⟨k, D, hD, hmem⟩ := provCode_of_prov H h
  exact ⟨D, hD, natV H k, natV_mem_omega H k, hmem⟩

/-! ## Internal soundness

Soundness is proved by induction on the rank of the certificate, so the
property has to be a `Form` with parameters: `omega_ind` separates by a formula
and nothing weaker is available.  Every ingredient is already rendered —
membership in a coded context by `fMemCtxF`, satisfaction by `fSatInF`, being
an environment by `fEnvOnF`, and the triple by `fTripleMemF` — so the property
is assembled rather than built.

The induction is the strong one: the property carried through `omega_ind` is
"every rank *below* `n` is sound", whose successor step is exactly one
application of the seventeen-case argument.  That is what a citation at a
strictly smaller rank needs, and it is the whole content of the ranking. -/

/-- Every member of the coded context is satisfied at the environment. -/
def CtxSat (H : ZFAxioms mem) (A R g e : V) : Prop :=
  ∀ x, MemCtx H x g → SatIn H A R x e

/-- Extending a satisfied context by a satisfied formula. -/
theorem ctxSat_cons (H : ZFAxioms mem) {A R g e a : V}
    (hg : CtxSat H A R g e) (ha : SatIn H A R a e) :
    CtxSat H A R (ctxCons H a g) e := by
  intro x hx
  rcases memCtx_cons_inv H hx with rfl | hx
  · exact ha
  · exact hg x hx

/-- **The eigenvariable transfer.**  A successor shift of a satisfied context is
satisfied at the shifted environment: each of its members is the successor
renaming of a coded member of the original, and `satIn_renames` turns that into
satisfaction at `econs H d e` through `compV_succMap`. -/
theorem ctxSat_shift (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {g g' e d : V} (hsh : ShiftsCtx H g g') (he : IsEnvOn H A e)
    (hd : mem d A) (hg : CtxSat H A R g e) :
    CtxSat H A R g' (econs H d e) := by
  intro x' hx'
  obtain ⟨x, hxc, hxm, hren⟩ := hsh x' hx'
  have hiff := satIn_renames H hS hxc (succMap_isVarMap H)
    (econs_isEnvOn H he hd) hren
  rw [compV_succMap H he hd] at hiff
  exact hiff.mpr (hg x hxm)

/-- Soundness of a certificate at a single rank. -/
def SoundAt (H : ZFAxioms mem) (A R D n : V) : Prop :=
  ∀ g c e, mem (satTriple H n g c) D → IsEnvOn H A e →
    CtxSat H A R g e → SatIn H A R c e

/-- "every member of the context in slot `g_i` is satisfied at slot `e_i`".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the member `x`        |
| `m+1`          | the caller's slot `m` |
-/
def fCtxSatF (g_i e_i a_i r_i : Nat) : Form :=
  fAll (fImp (fMemCtxF 0 (g_i+1)) (fSatInF 0 (e_i+1) (a_i+1) (r_i+1)))

theorem fCtxSatF_spec (H : ZFAxioms mem) (ee : Nat → V) (g_i e_i a_i r_i : Nat) :
    Sat mem ee (fCtxSatF g_i e_i a_i r_i) ↔
      CtxSat H (ee a_i) (ee r_i) (ee g_i) (ee e_i) := by
  unfold CtxSat
  constructor
  · intro h x hx
    exact (fSatInF_spec H (scons x ee) 0 (e_i+1) (a_i+1) (r_i+1)).mp
      (h x ((fMemCtxF_spec H (scons x ee) 0 (g_i+1)).mpr hx))
  · intro h x hx
    exact (fSatInF_spec H (scons x ee) 0 (e_i+1) (a_i+1) (r_i+1)).mpr
      (h x ((fMemCtxF_spec H (scons x ee) 0 (g_i+1)).mp hx))

/-- "the certificate in slot `d_i` is sound at the rank in slot `n_i`, over the
structure ⟨slot `a_i`, slot `r_i`⟩".

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the environment `e`   |
| `1`            | the conclusion `c`    |
| `2`            | the context `g`       |
| `m+3`          | the caller's slot `m` |
-/
def fSoundAtF (n_i d_i a_i r_i : Nat) : Form :=
  fAll (fAll (fAll (fImp (fTripleMemF (n_i+3) 2 1 (d_i+3))
    (fImp (fEnvOnF 0 (a_i+3))
      (fImp (fCtxSatF 2 0 (a_i+3) (r_i+3)) (fSatInF 1 0 (a_i+3) (r_i+3)))))))

theorem fSoundAtF_spec (H : ZFAxioms mem) (ee : Nat → V) (n_i d_i a_i r_i : Nat) :
    Sat mem ee (fSoundAtF n_i d_i a_i r_i) ↔
      SoundAt H (ee a_i) (ee r_i) (ee d_i) (ee n_i) := by
  unfold SoundAt
  constructor
  · intro h g c e hmem he hg
    exact (fSatInF_spec H (scons e (scons c (scons g ee)))
        1 0 (a_i+3) (r_i+3)).mp
      (h g c e
        ((fTripleMemF_spec H (scons e (scons c (scons g ee)))
          (n_i+3) 2 1 (d_i+3)).mpr hmem)
        ((fEnvOnF_spec H (scons e (scons c (scons g ee))) 0 (a_i+3)).mpr he)
        ((fCtxSatF_spec H (scons e (scons c (scons g ee)))
          2 0 (a_i+3) (r_i+3)).mpr hg))
  · intro h g c e hmem he hg
    exact (fSatInF_spec H (scons e (scons c (scons g ee)))
        1 0 (a_i+3) (r_i+3)).mpr
      (h g c e
        ((fTripleMemF_spec H (scons e (scons c (scons g ee)))
          (n_i+3) 2 1 (d_i+3)).mp hmem)
        ((fEnvOnF_spec H (scons e (scons c (scons g ee))) 0 (a_i+3)).mp he)
        ((fCtxSatF_spec H (scons e (scons c (scons g ee)))
          2 0 (a_i+3) (r_i+3)).mp hg))

/-- **The seventeen cases.**  Given soundness at every rank below `n`, the
certificate is sound at `n`.  This is the internal transcription of
`SetTheory.soundness`: each case reads a Tarski clause of `SatIn`, and the five
rules that move a formula across a binder read a substitution lemma of
`BoundedZFCConsistency.InternalSoundness` instead. -/
theorem soundAt_step (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {D : V} (hD : DerClosed H D) {n : V}
    (ih : ∀ m, mem m n → SoundAt H A R D m) : SoundAt H A R D n := by
  intro g c e hmem he hg
  obtain ⟨-, hc, hstep⟩ := hD n g c hmem
  have use : ∀ g' c' e', DerCite H D n g' c' → IsEnvOn H A e' →
      CtxSat H A R g' e' → SatIn H A R c' e' := by
    rintro g' c' e' ⟨m, hm, hmm⟩ he' hg'
    exact ih m hm g' c' e' hmm he' hg'
  have code : ∀ g' c', DerCite H D n g' c' → IsFormCodeSem H c' := by
    rintro g' c' ⟨m, hm, hmm⟩
    exact (hD m g' c' hmm).2.1
  rcases hstep with h | ⟨a, b, ha, hce, h1⟩ | ⟨a, ha, h1, h2⟩ | h |
    ⟨a, ha, hce⟩ | ⟨a, b, hce, h1, h2⟩ | ⟨b, hb, h1⟩ | ⟨a, ha, h1⟩ |
    ⟨a, b, ha, hb, hce, h1⟩ | ⟨a, b, ha, hb, hce, h1⟩ |
    ⟨a, b, ha, hb, h1, h2, h3⟩ | ⟨a, g', ha, hce, hsh, h1⟩ |
    ⟨a, k, ha, hk, hren, h1⟩ | ⟨a, k, a', ha, hk, hce, hren, h1⟩ |
    ⟨a, g', c', ha, hsh, hren, h1, h2⟩ | ⟨k, hk, hce⟩ |
    ⟨i, j, a, ci, hi, hj, ha, hren1, hren2, h1, h2⟩
  · -- assumption
    exact hg c h
  · -- implication introduction
    subst hce
    rw [satIn_imp H hS ha (code _ _ h1) he]
    intro hsa
    exact use _ _ e h1 he (ctxSat_cons H hg hsa)
  · -- implication elimination
    have s1 := use g _ e h1 he hg
    rw [satIn_imp H hS ha hc he] at s1
    exact s1 (use g a e h2 he hg)
  · -- ex falso
    exact absurd (use g _ e h he hg) (satIn_bot H)
  · -- excluded middle
    subst hce
    have hbot : IsFormCodeSem H (kpair H (natV H 2) (vempty H)) :=
      isFormCodeSem_bot H
    rw [satIn_or H hS ha (isFormCodeSem_imp H ha hbot) he]
    by_cases hsa : SatIn H A R a e
    · exact Or.inl hsa
    · refine Or.inr ?_
      rw [satIn_imp H hS ha hbot he]
      intro hx
      exact absurd hx hsa
  · -- conjunction introduction
    subst hce
    rw [satIn_and H hS (code _ _ h1) (code _ _ h2) he]
    exact ⟨use g a e h1 he hg, use g b e h2 he hg⟩
  · -- first conjunction elimination
    have s := use g _ e h1 he hg
    rw [satIn_and H hS hc hb he] at s
    exact s.1
  · -- second conjunction elimination
    have s := use g _ e h1 he hg
    rw [satIn_and H hS ha hc he] at s
    exact s.2
  · -- first disjunction introduction
    subst hce
    rw [satIn_or H hS ha hb he]
    exact Or.inl (use g a e h1 he hg)
  · -- second disjunction introduction
    subst hce
    rw [satIn_or H hS ha hb he]
    exact Or.inr (use g b e h1 he hg)
  · -- disjunction elimination
    have s := use g _ e h1 he hg
    rw [satIn_or H hS ha hb he] at s
    rcases s with s | s
    · exact use _ _ e h2 he (ctxSat_cons H hg s)
    · exact use _ _ e h3 he (ctxSat_cons H hg s)
  · -- universal introduction
    subst hce
    rw [satIn_all H hS ha he]
    intro d hd
    exact use g' a (econs H d e) h1 (econs_isEnvOn H he hd)
      (ctxSat_shift H hS hsh he hd hg)
  · -- universal elimination
    have s := use g _ e h1 he hg
    rw [satIn_all H hS ha he] at s
    have hiff := satIn_renames H hS ha (instMap_isVarMap H hk) he hren
    rw [compV_instMap H he hk] at hiff
    exact hiff.mpr (s (applyV H e k) (isEnvOn_apply H he hk))
  · -- existential introduction
    subst hce
    have s := use g a' e h1 he hg
    have hiff := satIn_renames H hS ha (instMap_isVarMap H hk) he hren
    rw [compV_instMap H he hk] at hiff
    rw [satIn_ex H hS ha he]
    exact ⟨applyV H e k, isEnvOn_apply H he hk, hiff.mp s⟩
  · -- existential elimination
    have s := use g _ e h1 he hg
    rw [satIn_ex H hS ha he] at s
    obtain ⟨d, hd, hsa⟩ := s
    have hec : IsEnvOn H A (econs H d e) := econs_isEnvOn H he hd
    have hbody := use _ c' (econs H d e) h2 hec
      (ctxSat_cons H (ctxSat_shift H hS hsh he hd hg) hsa)
    have hiff := satIn_renames H hS hc (succMap_isVarMap H) hec hren
    rw [compV_succMap H he hd] at hiff
    exact hiff.mp hbody
  · -- reflexivity of equality
    subst hce
    exact (satIn_eqAtom H hS hk hk he).mpr rfl
  · -- the Leibniz rule
    have seq := use g _ e h1 he hg
    rw [satIn_eqAtom H hS hi hj he] at seq
    have sci := use g ci e h2 he hg
    have hiff1 := satIn_renames H hS ha (instMap_isVarMap H hi) he hren1
    rw [compV_instMap H he hi] at hiff1
    have hiff2 := satIn_renames H hS ha (instMap_isVarMap H hj) he hren2
    rw [compV_instMap H he hj] at hiff2
    refine hiff2.mpr ?_
    rw [← seq]
    exact hiff1.mp sci

/-- The parameter block of `fSoundAtF`: the certificate, the carrier, then the
relation. -/
def envSound (D A R : V) : Nat → V
  | 0 => D
  | 1 => A
  | _ => R

/-- The property the definable-induction schema carries: soundness at every
rank strictly below the induction variable.

| de Bruijn slot | contents              |
| -------------- | --------------------- |
| `0`            | the smaller rank `m`  |
| `1`            | the induction variable |
| `2`, `3`, `4`  | the certificate, the carrier, the relation |
-/
def fSoundBelowF : Form :=
  fAll (fImp (fMem 0 1) (fSoundAtF 0 2 3 4))

theorem fSoundBelowF_spec (H : ZFAxioms mem) (D A R n : V) :
    Sat mem (scons n (envSound D A R)) fSoundBelowF ↔
      ∀ m, mem m n → SoundAt H A R D m := by
  constructor
  · intro h m hm
    exact (fSoundAtF_spec H (scons m (scons n (envSound D A R)))
      0 2 3 4).mp (h m hm)
  · intro h m hm
    exact (fSoundAtF_spec H (scons m (scons n (envSound D A R)))
      0 2 3 4).mpr (h m hm)

/-- **Soundness at every rank below a given internal natural.**  This is the
form the definable-induction schema proves; the successor step is a single
application of `soundAt_step`. -/
theorem soundBelow (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {D : V} (hD : DerClosed H D) :
    ∀ n, mem n (omegaV H) → ∀ m, mem m n → SoundAt H A R D m := by
  intro n hn
  refine (fSoundBelowF_spec H D A R n).mp ?_
  refine omega_ind H fSoundBelowF (envSound D A R) ?_ ?_ n hn
  · refine (fSoundBelowF_spec H D A R (vempty H)).mpr (fun m hm => ?_)
    exact absurd hm (vempty_spec H m)
  · intro k hk hbelow
    have hb := (fSoundBelowF_spec H D A R k).mp hbelow
    refine (fSoundBelowF_spec H D A R (vsucc H k)).mpr (fun m hm => ?_)
    rcases (vsucc_spec H k m).mp hm with hm | rfl
    · exact hb m hm
    · exact soundAt_step H hS hD hb

theorem soundAt_all (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {D : V} (hD : DerClosed H D) :
    ∀ n, mem n (omegaV H) → SoundAt H A R D n :=
  fun n hn =>
    soundBelow H hS hD (vsucc H n) (omega_succ H n hn) n (vsucc_self H n)

/-- **Internal soundness of the coded calculus.**  A coded derivation of `c`
from `g` transports satisfaction of every member of `g` to satisfaction of
`c`. -/
theorem derives_sound (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {d g c e : V} (hd : Derives H d g c) (he : IsEnvOn H A e)
    (hg : CtxSat H A R g e) : SatIn H A R c e := by
  obtain ⟨hD, n, hn, hmem⟩ := hd
  exact soundAt_all H hS hD n hn g c e hmem he hg

/-- **No coded derivation of falsity from the empty context.**  The hypothesis
is the existence of an internal set structure, which is exactly what the
reflection step is meant to supply; nothing here asserts that one exists. -/
theorem not_derives_bot (H : ZFAxioms mem) {A R : V}
    (hS : IsSetStructure H A R) {d : V}
    (hd : Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H))) : False := by
  obtain ⟨e, he⟩ := exists_isEnvOn H hS.nonempty
  exact satIn_bot H
    (derives_sound H hS hd he (fun x hx => absurd hx (memCtx_nil H x)))

/-- Soundness of an external derivation, read inside the model: if `Prov G a`
then the code of `a` is satisfied wherever the codes of `G` are.  This is
`derives_of_prov` composed with `derives_sound`, and it is the shape the
reflection argument consumes at the quotation level. -/
theorem prov_satIn (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {G : List Form} {a : Form} (h : Prov G a) {e : V} (he : IsEnvOn H A e)
    (hg : ∀ b ∈ G, SatIn H A R (formCode H b) e) :
    SatIn H A R (formCode H a) e := by
  obtain ⟨d, hd⟩ := derives_of_prov H h
  refine derives_sound H hS hd he (fun x hx => ?_)
  obtain ⟨b, hb, rfl⟩ := (memCtx_ctxCode H G x).mp hx
  exact hg b hb

end CodedDerivation

end BoundedZFCConsistency
end LeanProofs
