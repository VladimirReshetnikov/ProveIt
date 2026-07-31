(** * The route no assumption tracker defends against: a statement that lies

    Every other file in this directory obtains [False] by weakening the logic,
    and every one of them is named in [Print Assumptions].  This file obtains
    something that *reads* as a proof of [False] while the logic stays
    completely intact -- and [Print Assumptions] reports "Closed under the
    global context", correctly, because the proof really is closed.

    Category (see ../../README.md): ESCAPE HATCH, but the one that escapes the
    audit rather than the kernel.  Nothing here is a bug in Rocq.  The point is
    that "the proof was machine-checked and depends on no axioms" is a claim
    about a *term*, and a reader who has not also checked the *statement* has
    verified nothing.

    This is the Rocq counterpart of ../../Audits/Lean/StringIdentity/, which
    asks the same question of Lean's identifiers and answers it lexically.

    Toolchain: The Rocq Prover 9.2.  Verified by ../verify.ps1. *)

(** ** 1. Redefining the name

    The bluntest form.  Inside the module, [False] is a different constant. *)

Module Redefined.
  Definition False := True.
  Lemma looks_absurd : False.
  Proof. exact I. Qed.
  Print Assumptions looks_absurd.
End Redefined.

(** ** 2. Redefining the notation

    Sharper, because no identifier was shadowed: [False] still means what it
    always did, and the *notation* is what changed.  [Check] prints the
    statement back exactly as written. *)

Module Notated.
  Notation "'False'" := True.
  Lemma looks_absurd : False.
  Proof. exact I. Qed.
  Check looks_absurd.
  Print Assumptions looks_absurd.
End Notated.

(** ** 3. Redefining the relation inside the statement

    The most dangerous variant, because the lie is in an infix operator rather
    than in the headline noun.  A reader scanning for the *shape* of a theorem
    sees [0 = 1]; the [=] is not Rocq's.

    Note the [: type_scope] annotation -- without it the stdlib [=] wins and the
    trick silently fails, which is itself worth knowing. *)

Module Relation.
  Definition myeq (x y : nat) : Prop := True.
  Notation "x = y" := (myeq x y) (at level 70, no associativity) : type_scope.
  Lemma zero_is_one : 0 = 1.
  Proof. exact I. Qed.
  Check zero_is_one.
  Print Assumptions zero_is_one.
End Relation.

(** ** 4. Homoglyphs

    No shadowing and no notation: [Fаlse] below contains U+0430 CYRILLIC SMALL
    LETTER A in place of the Latin [a].  It is a different identifier that no
    amount of reading will distinguish at typical font sizes. *)

Module Homoglyph.
  Definition Fаlse := True.
  Lemma looks_absurd : Fаlse.
  Proof. exact I. Qed.
  Check looks_absurd.
  Print Assumptions looks_absurd.
End Homoglyph.

(** ** 5. What actually defends against this

    - [Set Printing All] disables notations and prints fully qualified constants.
    - [Locate] and [About] resolve a name to the constant it denotes.
    - Rocq emits [notation-overridden] warnings for sections 2 and 3 -- which
      [-w none] suppresses, and which is the reason that flag belongs on an
      audit checklist rather than in a build script. *)

Set Printing All.
Check Redefined.looks_absurd.
Check Notated.looks_absurd.
Check Relation.zero_is_one.
Check Homoglyph.looks_absurd.
Unset Printing All.

Locate "=".

(** ** The honest summary

    None of the five is a soundness defect, and none of them would survive
    [coqchk] telling you anything different -- [coqchk] would also report these
    developments as fine, because they *are* fine.  The failure is entirely in
    the human step of reading a statement, and it is the failure mode that both
    Rocq's and Lean's assumption-tracking machinery is structurally unable to
    catch.  A [False] obtained this way is a fact about a reader, not about a
    kernel. *)
