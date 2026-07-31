(** * Girard/Hurkens paradoxes in Coq, and the loophole that used to reach them

    This is the Coq counterpart of [Shenanigans/Hurkens/] (Lean 4).  Nothing
    here is a defect in Coq.  Every [False] below is derived from a hypothesis
    Coq deliberately withholds, and is stated as an *implication*: granting the
    hypothesis is fatal, so the rule cannot be added.

    Category (per ../../README.md): PARADOX -- a negative result about type
    theory, not a bug.  Contrast with ../GuardChecker/, which holds genuine
    implementation defects.

    Toolchain: The Rocq Prover 9.2 (OCaml 4.14.2).  Compile with [coqc].
    Every claim carries a [Print Assumptions] audit; all report
    "Closed under the global context".
*)

From Stdlib Require Import Hurkens.

(** ** 1. There is no [Type : Type]

    The stdlib states this as: no small type is equal to [Type].  If [Type]
    were an element of itself -- the rule a naive "type in type" system adds --
    the equation would be inhabited and the system inconsistent. *)

Theorem no_type_in_type : forall A : Type, Type = A -> False.
Proof. exact Hurkens.TypeNeqSmallType.paradox. Qed.

Print Assumptions no_type_in_type.

(** [Prop] and [Type] are distinct for the same reason. *)

Theorem prop_neq_type : Prop <> Type.
Proof. exact Hurkens.PropNeqType.paradox. Qed.

Print Assumptions prop_neq_type.

(** ** 2. A retract of [Type] into [Prop] collapses the logic

    [Prop] is impredicative.  If it could also *encode* [Type] -- i.e. if there
    were [down]/[up] with [up (down A) = A] -- then Hurkens' paradox applies and
    every proposition becomes provable.  This is the precise sense in which
    impredicativity is safe only because [Prop] cannot store arbitrary types. *)

Section RetractTypeIntoProp.

  Variable down : Hurkens.NoRetractFromTypeToProp.Type1 -> Prop.
  Variable up   : Prop -> Hurkens.NoRetractFromTypeToProp.Type1.
  Hypothesis up_down : forall A, up (down A) = A.

  Theorem retract_type_prop_absurd : False.
  Proof. exact (Hurkens.NoRetractFromTypeToProp.paradox down up up_down False). Qed.

End RetractTypeIntoProp.

Print Assumptions retract_type_prop_absurd.

(** ** 3. The historical loophole: reaching the paradox without a hypothesis

    A submission to <https://github.com/codyroux/name-the-biggest-number>
    ([Shenannigans.v], by jakobbotsh, annotated "Works in 8.9.1") reached
    section 1's hypothesis *for real*, with no [Variable] and no axiom, by
    using universe handling for this inductive: *)

Inductive foo (A : Type) := bar X : foo X -> foo A | nonempty.
Arguments nonempty {_}.

(** The constructor [bar] quantifies over [X : Type] in the same universe as the
    parameter [A], so a value of the *small* type [foo nat] can store an
    arbitrary [X : Type].  Projecting it back out is unproblematic: *)

Definition A : Type := foo nat.

Definition up' : A -> Type :=
  fun a => match a with bar _ u _ => u | nonempty => nat end.

(** The injection is the half Rocq 9.2 refuses.  Uncommenting

      Definition down' : Type -> A := fun u => bar nat u nonempty.

    yields, verbatim on Rocq 9.2:

      The term "u" has type "U" while it is expected to have type "Type"
      (universe inconsistency: Cannot enforce U.u0 <= foo.u0
       because foo.u0 < U.u0).

    In 8.9.1 the analogous definition was accepted, [up' (down' X) = X] held by
    [reflexivity], and feeding that retract to [Hurkens] produced a closed,
    axiom-free [False] -- which the submission used to "prove"
    [forall n, n < 7].

    So this file's sections 1 and 2 are permanent facts about type theory, while
    section 3 is a fixed implementation defect: the universe constraint
    [foo.u0 < U.u0] is exactly the guard that closes it.  This is the CONTROL
    for the whole file -- it shows the paradox is unreachable in current Coq
    precisely because the retract cannot be built. *)

(** A weaker, harmless projection survives, confirming that only the injection
    is blocked and the inductive itself is fine. *)

Definition roundtrip_nonempty : up' (@nonempty nat) = nat := eq_refl.

Print Assumptions roundtrip_nonempty.
