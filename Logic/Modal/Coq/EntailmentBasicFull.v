(**
  The remaining generic rule and named-axiom layer of
  Foundation/Modal/Entailment/Basic.lean.

  Foundation presents theoremhood twice, through proof objects and through
  their mere existence.  A modal logic set is already Prop-valued here, so
  those two APIs coincide.  Likewise, the source repeats every axiom
  capability for finite contexts and arbitrary contexts.  The generic
  schema-transport theorems below are stronger: every inclusion of theorem
  predicates transports nullary, unary, and binary axiom families at once.
*)

From FoundationModal Require Import
  Syntax Axioms LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Rules *)

Definition unnecessitation {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L (Box p) -> L p.

Definition loeb_rule {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L (Imp (Box p) p) -> L p.

Definition henkin_rule {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p, L (Iff (Box p) p) -> L p.

Definition modus_ponens_rule {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p q, L (Imp p q) -> L p -> L q.

Lemma multinecessitation :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    necessitation L -> forall n p, L p -> L (box_iter n p).
Proof.
  intros AtomType L Hnec n; induction n as [|n IH]; intros p Hp; simpl.
  - exact Hp.
  - now apply Hnec, IH.
Qed.

Lemma multiunnecessitation :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    unnecessitation L -> forall n p, L (box_iter n p) -> L p.
Proof.
  intros AtomType L Hunnec n; induction n as [|n IH]; intros p Hp; simpl in *.
  - exact Hp.
  - apply IH. now apply Hunnec.
Qed.

Lemma unnecessitation_of_T :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_T L -> unnecessitation L.
Proof.
  intros AtomType L Hmp HT p Hbox.
  exact (Hmp _ _ (has_T_axiom HT p) Hbox).
Qed.

(** These application lemmas collect all source declarations whose primed
    name merely applies an axiom once or twice by modus ponens. *)

Lemma axiom_K_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_K L -> forall p q,
    L (Box (Imp p q)) -> L (Imp (Box p) (Box q)).
Proof.
  intros AtomType L Hmp HK p q H.
  exact (Hmp _ _ (has_K_axiom HK p q) H).
Qed.

Lemma axiom_K_apply2 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_K L -> forall p q,
    L (Box (Imp p q)) -> L (Box p) -> L (Box q).
Proof.
  intros AtomType L Hmp HK p q Himp Hp.
  exact (Hmp _ _ (axiom_K_apply Hmp HK Himp) Hp).
Qed.

Lemma axiom_M_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_M L -> forall p q,
    L (Box (And p q)) -> L (And (Box p) (Box q)).
Proof.
  intros AtomType L Hmp HM p q H.
  exact (Hmp _ _ (has_M_axiom HM p q) H).
Qed.

Lemma axiom_C_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_C L -> forall p q,
    L (And (Box p) (Box q)) -> L (Box (And p q)).
Proof.
  intros AtomType L Hmp HC p q H.
  exact (Hmp _ _ (has_C_axiom HC p q) H).
Qed.

Lemma axiom_T_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_T L -> forall p, L (Box p) -> L p.
Proof. exact unnecessitation_of_T. Qed.

Lemma axiom_DiaTc_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_DiaTc L -> forall p, L p -> L (Dia p).
Proof.
  intros AtomType L Hmp HD p H.
  exact (Hmp _ _ (has_DiaTc_axiom HD p) H).
Qed.

Lemma axiom_D_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_D L -> forall p, L (Box p) -> L (Dia p).
Proof.
  intros AtomType L Hmp HD p H.
  exact (Hmp _ _ (has_D_axiom HD p) H).
Qed.

Lemma axiom_B_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_B L -> forall p, L p -> L (Box (Dia p)).
Proof.
  intros AtomType L Hmp HB p H.
  exact (Hmp _ _ (has_B_axiom HB p) H).
Qed.

Lemma axiom_Four_apply :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    modus_ponens_rule L -> has_Four L -> forall p,
    L (Box p) -> L (Box (Box p)).
Proof.
  intros AtomType L Hmp HFour p H.
  exact (Hmp _ _ (has_Four_axiom HFour p) H).
Qed.

(** * Generic schema transport

    These three lemmas subsume every [FiniteContext.of] and [Context.of]
    instance in the source file.  No property of contexts is used there
    beyond inclusion of base theorems. *)

Definition nullary_schema {AtomType}
    (L : modal_logic_set AtomType) (a : formula AtomType) : Prop := L a.

Definition unary_schema {AtomType}
    (L : modal_logic_set AtomType)
    (a : formula AtomType -> formula AtomType) : Prop :=
  forall p, L (a p).

Definition binary_schema {AtomType}
    (L : modal_logic_set AtomType)
    (a : formula AtomType -> formula AtomType -> formula AtomType) : Prop :=
  forall p q, L (a p q).

Lemma lift_nullary_schema :
  forall (AtomType : Type) (L C : modal_logic_set AtomType) a,
    logic_subset L C -> nullary_schema L a -> nullary_schema C a.
Proof. firstorder. Qed.

Lemma lift_unary_schema :
  forall (AtomType : Type) (L C : modal_logic_set AtomType) a,
    logic_subset L C -> unary_schema L a -> unary_schema C a.
Proof. firstorder. Qed.

Lemma lift_binary_schema :
  forall (AtomType : Type) (L C : modal_logic_set AtomType) a,
    logic_subset L C -> binary_schema L a -> binary_schema C a.
Proof. firstorder. Qed.

(** * Remaining named axiom capabilities *)

Record has_FourN {AtomType} (n : nat)
    (L : modal_logic_set AtomType) : Prop := {
  has_FourN_axiom : forall p, L (FourN n p)
}.

Record has_L {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_L_axiom : forall p, L (Axioms.L p)
}.

Record has_WeakPoint2 {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  has_WeakPoint2_axiom : forall p q, L (WeakPoint2 p q)
}.

Record has_Point3 {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Point3_axiom : forall p q, L (Point3 p q)
}.

Record has_WeakPoint3 {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  has_WeakPoint3_axiom : forall p q, L (WeakPoint3 p q)
}.

Record has_Grz {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Grz_axiom : forall p, L (Grz p)
}.

Record has_Dum {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Dum_axiom : forall p, L (Dum p)
}.

Record has_Tc {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Tc_axiom : forall p, L (Tc p)
}.

Record has_DiaT {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_DiaT_axiom : forall p, L (DiaT p)
}.

Record has_Ver {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Ver_axiom : forall p, L (Ver p)
}.

Record has_Hen {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Hen_axiom : forall p, L (Hen p)
}.

Record has_Z {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Z_axiom : forall p, L (Z p)
}.

Record has_McK {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_McK_axiom : forall p, L (McK p)
}.

Record has_Mk {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Mk_axiom : forall p q, L (Mk p q)
}.

Record has_Point4 {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_Point4_axiom : forall p, L (Point4 p)
}.

Record has_H {AtomType} (L : modal_logic_set AtomType) : Prop := {
  has_H_axiom : forall p, L (Axioms.H p)
}.

(** Because diamond is definitionally [not (box (not p))] in this syntax,
    classical propositional closure proves the source duality schema without
    any separate modal or involution hypothesis. *)
Lemma has_DiaDuality_of_classical :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> has_DiaDuality L.
Proof.
  intros AtomType L Hclass; constructor; intro p; unfold DiaDuality, Dia.
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Iff, And, Neg; simpl; tauto.
Qed.

(** The eight source instances identifying familiar axioms as special Geach
    schemata are definitional computations of the iteration operators. *)

Definition geach_T : geach_tuple :=
  {| geach_i := 0; geach_j := 0; geach_m := 1; geach_n := 0 |}.

Definition geach_B : geach_tuple :=
  {| geach_i := 0; geach_j := 1; geach_m := 0; geach_n := 1 |}.

Definition geach_D : geach_tuple :=
  {| geach_i := 0; geach_j := 0; geach_m := 1; geach_n := 1 |}.

Definition geach_Four : geach_tuple :=
  {| geach_i := 0; geach_j := 2; geach_m := 1; geach_n := 0 |}.

Definition geach_FourN (n : nat) : geach_tuple :=
  {| geach_i := 0; geach_j := n + 1; geach_m := n; geach_n := 0 |}.

Definition geach_Five : geach_tuple :=
  {| geach_i := 1; geach_j := 1; geach_m := 0; geach_n := 1 |}.

Definition geach_Tc : geach_tuple :=
  {| geach_i := 0; geach_j := 1; geach_m := 0; geach_n := 0 |}.

Definition geach_Point2 : geach_tuple :=
  {| geach_i := 1; geach_j := 1; geach_m := 1; geach_n := 1 |}.

Lemma has_Geach_of_T :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_T L -> has_Geach geach_T L.
Proof.
  intros AtomType L HT; constructor; intro p.
  exact (has_T_axiom HT p).
Qed.

Lemma has_Geach_of_B :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_B L -> has_Geach geach_B L.
Proof.
  intros AtomType L HB; constructor; intro p.
  exact (has_B_axiom HB p).
Qed.

Lemma has_Geach_of_D :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_D L -> has_Geach geach_D L.
Proof.
  intros AtomType L HD; constructor; intro p.
  exact (has_D_axiom HD p).
Qed.

Lemma has_Geach_of_Four :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_Four L -> has_Geach geach_Four L.
Proof.
  intros AtomType L HFour; constructor; intro p.
  exact (has_Four_axiom HFour p).
Qed.

Lemma has_Geach_of_FourN :
  forall (AtomType : Type) n (L : modal_logic_set AtomType),
    has_FourN n L -> has_Geach (geach_FourN n) L.
Proof.
  intros AtomType n L HFourN; constructor; intro p.
  exact (has_FourN_axiom HFourN p).
Qed.

Lemma has_Geach_of_Five :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_Five L -> has_Geach geach_Five L.
Proof.
  intros AtomType L HFive; constructor; intro p.
  exact (has_Five_axiom HFive p).
Qed.

Lemma has_Geach_of_Tc :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_Tc L -> has_Geach geach_Tc L.
Proof.
  intros AtomType L HTc; constructor; intro p.
  exact (has_Tc_axiom HTc p).
Qed.

Lemma has_Geach_of_Point2 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    has_Point2 L -> has_Geach geach_Point2 L.
Proof.
  intros AtomType L HPoint2; constructor; intro p.
  exact (has_Point2_axiom HPoint2 p).
Qed.

(** Explicit transport wrappers retain the source-facing capability names;
    their proofs all factor through the three generic schema lemmas. *)

Lemma lift_has_FourN :
  forall (AtomType : Type) n (L C : modal_logic_set AtomType),
    logic_subset L C -> has_FourN n L -> has_FourN n C.
Proof.
  intros AtomType n L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_FourN_axiom H)).
Qed.

Lemma lift_has_L :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_L L -> has_L C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_L_axiom H)).
Qed.

Lemma lift_has_WeakPoint2 :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_WeakPoint2 L -> has_WeakPoint2 C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_binary_schema Hsub (has_WeakPoint2_axiom H)).
Qed.

Lemma lift_has_Point3 :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Point3 L -> has_Point3 C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_binary_schema Hsub (has_Point3_axiom H)).
Qed.

Lemma lift_has_WeakPoint3 :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_WeakPoint3 L -> has_WeakPoint3 C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_binary_schema Hsub (has_WeakPoint3_axiom H)).
Qed.

Lemma lift_has_Grz :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Grz L -> has_Grz C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Grz_axiom H)).
Qed.

Lemma lift_has_Dum :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Dum L -> has_Dum C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Dum_axiom H)).
Qed.

Lemma lift_has_Tc :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Tc L -> has_Tc C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Tc_axiom H)).
Qed.

Lemma lift_has_DiaT :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_DiaT L -> has_DiaT C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_DiaT_axiom H)).
Qed.

Lemma lift_has_Ver :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Ver L -> has_Ver C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Ver_axiom H)).
Qed.

Lemma lift_has_Hen :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Hen L -> has_Hen C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Hen_axiom H)).
Qed.

Lemma lift_has_Z :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Z L -> has_Z C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Z_axiom H)).
Qed.

Lemma lift_has_McK :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_McK L -> has_McK C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_McK_axiom H)).
Qed.

Lemma lift_has_Mk :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Mk L -> has_Mk C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_binary_schema Hsub (has_Mk_axiom H)).
Qed.

Lemma lift_has_Point4 :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_Point4 L -> has_Point4 C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_Point4_axiom H)).
Qed.

Lemma lift_has_H :
  forall (AtomType : Type) (L C : modal_logic_set AtomType),
    logic_subset L C -> has_H L -> has_H C.
Proof.
  intros AtomType L C Hsub H; constructor.
  exact (lift_unary_schema Hsub (has_H_axiom H)).
Qed.

(** * Modal disjunction and inverse necessitation *)

Definition disjunctive {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p q, L (Or p q) -> L p \/ L q.

Definition modal_disjunctive {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p q, L (Or (Box p) (Box q)) -> L p \/ L q.

Definition disjunction_introduction_left {AtomType}
    (L : modal_logic_set AtomType) : Prop :=
  forall p q, L p -> L (Or p q).

Lemma modal_disjunctive_of_disjunctive_unnecessitation :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    disjunctive L -> unnecessitation L -> modal_disjunctive L.
Proof.
  intros AtomType L Hdisj Hunnec p q H.
  destruct (Hdisj _ _ H) as [Hp | Hq].
  - left; now apply Hunnec.
  - right; now apply Hunnec.
Qed.

Lemma unnecessitation_of_modal_disjunctive_from_or_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    disjunction_introduction_left L ->
    modal_disjunctive L -> unnecessitation L.
Proof.
  intros AtomType L Hor_intro Hmodal p Hp.
  pose proof (Hor_intro (Box p) (Box p) Hp) as Hor.
  destruct (Hmodal p p Hor); assumption.
Qed.

Lemma disjunction_introduction_left_of_classical :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> disjunction_introduction_left L.
Proof.
  intros AtomType L Hclass p q Hp.
  eapply (logic_modus_ponens Hclass); [|exact Hp].
  apply (logic_classical_tautology Hclass).
  intro rho; unfold Or, Neg; simpl; tauto.
Qed.

Lemma unnecessitation_of_modal_disjunctive :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> modal_disjunctive L -> unnecessitation L.
Proof.
  intros AtomType L Hclass Hmodal.
  apply (unnecessitation_of_modal_disjunctive_from_or_intro
    (disjunction_introduction_left_of_classical Hclass) Hmodal).
Qed.

(** Foundation's construction is noncomputable only because it repackages
    proof objects.  The Prop-valued Coq proof is fully constructive once the
    classical entailment capability supplies disjunction introduction. *)
Definition modal_disjunctive_iff_unnecessitation_under_disjunction
    {AtomType} (L : modal_logic_set AtomType)
    (Hclass : classical_logic L) (Hdisj : disjunctive L)
    : modal_disjunctive L <-> unnecessitation L.
Proof.
  split.
  - now apply unnecessitation_of_modal_disjunctive.
  - now apply modal_disjunctive_of_disjunctive_unnecessitation.
Qed.
