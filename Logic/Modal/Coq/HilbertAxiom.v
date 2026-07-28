(**
  Raw modal-axiom templates and their substitution instances.

  This file independently ports the complete active declaration surface of
  the pinned Foundation module [Modal/Hilbert/Axiom.lean].  A raw axiom set
  fixes one atom type and contains formula templates.  Its instances use
  substitutions over that same atom type, exactly as in the source.

  Records that retain an atom live in [Type].  This is mathematically
  significant in Coq: clients must be able to eliminate the witness in order
  to construct a substitution.  The two atom-free records can remain in
  [Prop].
*)

From FoundationModal Require Import Syntax Axioms LogicInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition raw_modal_axiom (AtomType : Type) : Type :=
  formula AtomType -> Prop.

Definition raw_axiom_instances {AtomType : Type}
    (Ax : raw_modal_axiom AtomType) : modal_logic_set AtomType :=
  fun phi =>
    exists psi, Ax psi /\
      exists sigma : AtomType -> formula AtomType,
        phi = substitute sigma psi.

(** Membership in a raw template set constructively yields every one of its
    substitution instances.  The equality has Foundation's orientation. *)
Lemma raw_axiom_instance_of_mem :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (phi : formula AtomType) (sigma : AtomType -> formula AtomType),
    Ax phi -> raw_axiom_instances Ax (substitute sigma phi).
Proof.
  intros AtomType Ax phi sigma Hphi.
  exists phi; split; [exact Hphi |].
  exists sigma; reflexivity.
Qed.

(** * Witness-carrying schema capabilities *)

Record raw_axioms_has_M {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_M_p : AtomType;
  raw_M_q : AtomType;
  raw_M_ne : raw_M_p <> raw_M_q;
  raw_M_mem : Ax (M (Atom raw_M_p) (Atom raw_M_q))
}.

Record raw_axioms_has_C {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_C_p : AtomType;
  raw_C_q : AtomType;
  raw_C_ne : raw_C_p <> raw_C_q;
  raw_C_mem : Ax (C (Atom raw_C_p) (Atom raw_C_q))
}.

Record raw_axioms_has_N {AtomType}
    (Ax : raw_modal_axiom AtomType) : Prop := {
  raw_N_mem : Ax N
}.

Record raw_axioms_has_K {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_K_p : AtomType;
  raw_K_q : AtomType;
  raw_K_ne : raw_K_p <> raw_K_q;
  raw_K_mem : Ax (K (Atom raw_K_p) (Atom raw_K_q))
}.

Record raw_axioms_has_T {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_T_p : AtomType;
  raw_T_mem : Ax (T (Atom raw_T_p))
}.

Record raw_axioms_has_D {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_D_p : AtomType;
  raw_D_mem : Ax (D (Atom raw_D_p))
}.

Record raw_axioms_has_P {AtomType}
    (Ax : raw_modal_axiom AtomType) : Prop := {
  raw_P_mem : Ax P
}.

Record raw_axioms_has_B {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_B_p : AtomType;
  raw_B_mem : Ax (B (Atom raw_B_p))
}.

Record raw_axioms_has_Four {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Four_p : AtomType;
  raw_Four_mem : Ax (Four (Atom raw_Four_p))
}.

Record raw_axioms_has_FourN {AtomType} (n : nat)
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_FourN_p : AtomType;
  raw_FourN_mem : Ax (FourN n (Atom raw_FourN_p))
}.

Record raw_axioms_has_Five {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Five_p : AtomType;
  raw_Five_mem : Ax (Five (Atom raw_Five_p))
}.

Record raw_axioms_has_Point2 {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Point2_p : AtomType;
  raw_Point2_mem : Ax (Point2 (Atom raw_Point2_p))
}.

Record raw_axioms_has_WeakPoint2 {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_WeakPoint2_p : AtomType;
  raw_WeakPoint2_q : AtomType;
  raw_WeakPoint2_ne : raw_WeakPoint2_p <> raw_WeakPoint2_q;
  raw_WeakPoint2_mem :
    Ax (WeakPoint2 (Atom raw_WeakPoint2_p) (Atom raw_WeakPoint2_q))
}.

Record raw_axioms_has_Point3 {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Point3_p : AtomType;
  raw_Point3_q : AtomType;
  raw_Point3_ne : raw_Point3_p <> raw_Point3_q;
  raw_Point3_mem :
    Ax (Point3 (Atom raw_Point3_p) (Atom raw_Point3_q))
}.

Record raw_axioms_has_WeakPoint3 {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_WeakPoint3_p : AtomType;
  raw_WeakPoint3_q : AtomType;
  raw_WeakPoint3_ne : raw_WeakPoint3_p <> raw_WeakPoint3_q;
  raw_WeakPoint3_mem :
    Ax (WeakPoint3 (Atom raw_WeakPoint3_p) (Atom raw_WeakPoint3_q))
}.

Record raw_axioms_has_Point4 {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Point4_p : AtomType;
  raw_Point4_mem : Ax (Point4 (Atom raw_Point4_p))
}.

Record raw_axioms_has_L {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_L_p : AtomType;
  raw_L_mem : Ax (L (Atom raw_L_p))
}.

Record raw_axioms_has_Z {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Z_p : AtomType;
  raw_Z_mem : Ax (Z (Atom raw_Z_p))
}.

Record raw_axioms_has_Grz {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Grz_p : AtomType;
  raw_Grz_mem : Ax (Grz (Atom raw_Grz_p))
}.

Record raw_axioms_has_Dum {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Dum_p : AtomType;
  raw_Dum_mem : Ax (Dum (Atom raw_Dum_p))
}.

Record raw_axioms_has_Tc {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Tc_p : AtomType;
  raw_Tc_mem : Ax (Tc (Atom raw_Tc_p))
}.

Record raw_axioms_has_Ver {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Ver_p : AtomType;
  raw_Ver_mem : Ax (Ver (Atom raw_Ver_p))
}.

Record raw_axioms_has_Hen {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Hen_p : AtomType;
  raw_Hen_mem : Ax (Hen (Atom raw_Hen_p))
}.

Record raw_axioms_has_McK {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_McK_p : AtomType;
  raw_McK_mem : Ax (McK (Atom raw_McK_p))
}.

Record raw_axioms_has_Mk {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Mk_p : AtomType;
  raw_Mk_q : AtomType;
  raw_Mk_ne : raw_Mk_p <> raw_Mk_q;
  raw_Mk_mem : Ax (Mk (Atom raw_Mk_p) (Atom raw_Mk_q))
}.

Record raw_axioms_has_H1 {AtomType}
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_H1_p : AtomType;
  raw_H1_mem : Ax (H (Atom raw_H1_p))
}.

Record raw_axioms_has_Geach {AtomType} (g : geach_tuple)
    (Ax : raw_modal_axiom AtomType) : Type := {
  raw_Geach_p : AtomType;
  raw_Geach_mem : Ax (Geach g (Atom raw_Geach_p))
}.
