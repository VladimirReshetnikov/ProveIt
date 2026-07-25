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

(** Diamond/box duality, stated as an axiom schema for systems in which
    diamond may be primitive.  It is definitionally canonical in this port. *)
Definition DiaDuality {AtomType} (p : formula AtomType) : formula AtomType :=
  Iff (Dia p) (Neg (Box (Neg p))).

(** Distribution, the characteristic axiom of normal modal logic. *)
Definition K {AtomType} (p q : formula AtomType) : formula AtomType :=
  Imp (Box (Imp p q)) (Imp (Box p) (Box q)).

(** Distribution of box over conjunction, in both directions. *)
Definition M {AtomType} (p q : formula AtomType) : formula AtomType :=
  Imp (Box (And p q)) (And (Box p) (Box q)).

Definition C {AtomType} (p q : formula AtomType) : formula AtomType :=
  Imp (And (Box p) (Box q)) (Box (And p q)).

(** Necessity of truth. *)
Definition N {AtomType} : formula AtomType := Box Top.

(** Reflexivity. *)
Definition T {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box p) p.

(** Diamond-form alternative to T. *)
Definition DiaTc {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p (Dia p).

(** Seriality. *)
Definition D {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box p) (Dia p).

(** Formula-free seriality schema. *)
Definition P {AtomType} : formula AtomType := Neg (Box Bottom).

(** Symmetry. *)
Definition B {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p (Box (Dia p)).

(** Transitivity. *)
Definition Four {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box p) (Box (Box p)).

Definition FourN {AtomType} (n : nat) (p : formula AtomType)
    : formula AtomType :=
  Imp (box_iter n p) (box_iter (n + 1) p).

(** Right-Euclideanness. *)
Definition Five {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia p) (Box (Dia p)).

(** Local strong confluence. *)
Definition Point2 {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia (Box p)) (Box (Dia p)).

(** Weak confluence. *)
Definition WeakPoint2 {AtomType} (p q : formula AtomType)
    : formula AtomType :=
  Imp (Dia (And (Box p) q)) (Box (Or (Dia p) q)).

(** Density and functionality. *)
Definition C4 {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Box p)) (Box p).

Definition CD {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia p) (Box p).

(** Coreflexivity. *)
Definition Tc {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p (Box p).

(** Diamond-form alternative to coreflexivity. *)
Definition DiaT {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia p) p.

(** Validity on frames with no successors. *)
Definition Ver {AtomType} (p : formula AtomType) : formula AtomType := Box p.

(** Piecewise strong connectedness. *)
Definition Point3 {AtomType} (p q : formula AtomType) : formula AtomType :=
  Or (Box (Imp (Box p) q)) (Box (Imp (Box q) p)).

Definition WeakPoint3 {AtomType} (p q : formula AtomType)
    : formula AtomType :=
  Or (Box (Imp (Boxdot p) q)) (Box (Imp (Boxdot q) p)).

Definition Point4 {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Dia (Box p)) (Imp p (Box p)).

(** Loeb's axiom. *)
Definition Loeb {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Imp (Box p) p)) (Box p).

(** Foundation calls Loeb's axiom [L]. *)
Definition L {AtomType} (p : formula AtomType) : formula AtomType :=
  Loeb p.

(** The Grzegorczyk axiom. *)
Definition Grz {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Imp (Box (Imp p (Box p))) p)) p.

Definition Dum {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Imp (Box (Imp p (Box p))) p))
      (Imp (Dia (Box p)) p).

(** McKinsey's axiom. *)
Definition McK {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Dia p)) (Dia (Box p)).

Definition Z {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Imp (Box p) p)) (Imp (Dia (Box p)) (Box p)).

Definition Hen {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp (Box (Iff (Box p) p)) (Box p).

Definition Mk {AtomType} (p q : formula AtomType) : formula AtomType :=
  Imp (And (Box p) q) (Dia (And (Box (Box p)) (Dia q))).

Definition H {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p (Box (Imp (Dia p) p)).

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

(** Boolos's axiom I. *)
Definition I {AtomType} (p q : formula AtomType) : formula AtomType :=
  Or (Box (Imp (Box p) (Box q)))
     (Box (Imp (Box q) (Boxdot p))).
