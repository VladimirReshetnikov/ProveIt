(** * [-impredicative-set]: one of Hurkens' two sorts, and what supplies the other

    Requires [-impredicative-set].  Rocq's manual: "Change the logical theory of
    Rocq by declaring the sort [Set] impredicative. Warning: This is known to be
    inconsistent with some standard axioms of classical mathematics such as the
    functional axiom of choice or the principle of description."

    Category (see ../../README.md): ESCAPE HATCH.  Unlike ../TypingFlags.v this
    flag is *not* inconsistent on its own -- impredicative [Set] was Coq's
    default until 2004 and has a model.  It becomes fatal only in combination.
    This file pins down exactly what the flag does and does not grant.

    Toolchain: The Rocq Prover 9.2, compiled with [-impredicative-set].
    Verified by ../verify.ps1. *)

From Stdlib Require Import Hurkens.
From Stdlib Require Import ClassicalUniqueChoice.

(** ** 1. What the flag grants: [Set] closed under [Set]-indexed products

    Without the flag this definition is rejected with
    [universe inconsistency: Cannot enforce Set+1 <= Set]. *)

Definition ForallSet (F : Set -> Set) : Set := forall A : Set, F A.

(** [Theory: Set is impredicative] *)
Print Assumptions ForallSet.

(** ** 2. Why that alone is not Girard

    It is tempting to conclude that [Set] is now a universe containing a code
    for every [Set]-indexed product, i.e. [Set : Set], i.e. Girard.  It is not,
    and the stdlib's own statement of the paradox says why.

    [Hurkens.Generic.paradox] axiomatises System U-, which has *two*
    impredicative sorts.  Its argument list demands, besides the outer universe
    [U1] with [ForallU1 : (U1 -> U1) -> U1], an inner one: [u0 : U1] together
    with [El0], [Forall0], and crucially

      [ForallU0 : forall u : U1, (El1 u -> El1 u0) -> El1 u0]

    -- a universe *inside* [Set] that is itself closed under [Set]-indexed
    products.  The flag gives the outer sort and nothing else, which is exactly
    why impredicative [Set] has a model. *)

Check Hurkens.Generic.paradox.

(** ** 3. What supplies the missing sort: decidability in [Set]

    [{A} + {~A}] is a *small computational* type that decides an arbitrary
    proposition, so it builds a retract of [Prop] into a two-element member of
    the impredicative [Set].  That is the second sort, and the paradox fires.

    This is Chicli-Pottier-Simpson (TYPES 2002, LNCS 2646).  The derivation of
    the first hypothesis below lives in [rocq-archive/paradoxes/Hurkens_Set.v]
    as [not_EM_set], dated 2002 and authored by Barras, Coquand, Herbelin and
    Werner; it is not in the stdlib, so it is taken as a hypothesis here rather
    than reproduced.  The second is a stdlib theorem. *)

Check not_not_classic_set.
(** [not_not_classic_set : ((forall P : Prop, {P} + {~ P}) -> False) -> False] *)

(** It is not axiom-free: it rests on [classic] and [dependent_unique_choice],
    which is the "standard axioms of classical mathematics" half of the manual's
    warning.  [Print Assumptions] names both. *)
Print Assumptions not_not_classic_set.

Definition chicli_pottier_simpson
    (not_EM_set : (forall A : Prop, {A} + {~A}) -> False) : False :=
  not_not_classic_set not_EM_set.

Print Assumptions chicli_pottier_simpson.

(** ** 4. Why this was a shipped bug, not just a theoretical risk

    Rocq's own [dev/doc/critical-bugs.md] records that the axiom of description
    together with decidability of equality on the reals -- both in the [Reals]
    library -- were inconsistent with impredicative [Set].  Introduced
    2002-06-20, shipped in **7.3.1 and 7.4**, found by Herbelin and Werner, and
    fixed on 2004-10-28 by making [Set] predicative.  That is why the flag
    exists at all and why it is off by default.

    ** The Lean comparison

    Lean has exactly one impredicative sort, [Prop], and no flag to add another.
    [Prop]'s safety rests on the *other* half of the pattern: it is
    proof-irrelevant, and data cannot be eliminated out of it.  The
    machine-checked version of that claim is
    ../../Paradoxes/Lean/TypeTheoryParadoxes/LargeElimination.lean.

    The unifying statement across both systems: **impredicativity is safe
    exactly when it is paired with proof irrelevance, and fatal when paired with
    proof relevance.**  [{A}+{~A}] in an impredicative [Set] is the
    proof-relevant pairing; Lean's [Prop] is the irrelevant one. *)
