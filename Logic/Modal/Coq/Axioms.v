(**
  Standard modal axiom schemata.

  These definitions port the central schemata from
  FormalizedFormalLogic/Foundation's [Foundation.Modal.Axioms] module at the
  repository's pinned upstream revision.  They are deliberately only syntax:
  semantic validity and frame correspondences belong in later modules.
*)

From FoundationModal Require Import Syntax.

Set Implicit Arguments.
Unset Strict Implicit.

(** Distribution, the characteristic axiom of normal modal logic. *)
Definition K {AtomType} (p q : formula AtomType) : formula AtomType :=
  Imp (Box (Imp p q)) (Imp (Box p) (Box q)).

(** Reflexivity. *)
Definition T {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box p) p.

(** Seriality. *)
Definition D {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box p) (Dia p).

(** Symmetry. *)
Definition B {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p (Box (Dia p)).

(** Transitivity. *)
Definition Four {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box p) (Box (Box p)).

(** Right-Euclideanness. *)
Definition Five {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia p) (Box (Dia p)).

(** Local strong confluence. *)
Definition Point2 {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia (Box p)) (Box (Dia p)).

(** Coreflexivity. *)
Definition Tc {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p (Box p).

(** Piecewise strong connectedness. *)
Definition Point3 {AtomType} (p q : formula AtomType) : formula AtomType :=
  Or (Box (Imp (Box p) q)) (Box (Imp (Box q) p)).

(** Loeb's axiom. *)
Definition Loeb {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Imp (Box p) p)) (Box p).

(** Foundation calls Loeb's axiom [L]. *)
Definition L {AtomType} (p : formula AtomType) : formula AtomType :=
  Loeb p.

(** The Grzegorczyk axiom. *)
Definition Grz {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Imp (Box (Imp p (Box p))) p)) p.

(** Parameters for a Geach confluence schema.

    The tuple [(i,j,m,n)] describes the frame condition saying that an
    [i]-step successor and a [j]-step successor have a common future reached
    in [m] and [n] steps, respectively.
*)
Record geach_tuple : Type := {
  geach_i : nat;
  geach_j : nat;
  geach_m : nat;
  geach_n : nat
}.

(** The generic Geach schema

      diamond^i box^m p -> box^j diamond^n p.
*)
Definition Geach {AtomType} (g : geach_tuple) (p : formula AtomType)
    : formula AtomType :=
  Imp (dia_iter (geach_i g) (box_iter (geach_m g) p))
      (box_iter (geach_j g) (dia_iter (geach_n g) p)).
