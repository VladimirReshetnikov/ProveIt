(**
  The generic Hilbert calculus with replacement of equivalents.

  This is an independent Rocq port of the reusable core of the pinned
  Foundation module [Modal/Hilbert/WithRE/Basic.lean].  The axiom predicate
  and atom type are fixed, just as they are for Foundation's [WithRE Ax].
  The named-system catalogue from the second half of that file is kept out
  of this module.

  There is one deliberate interface boundary.  Foundation's class [Cl]
  records a Lukasiewicz basis plus derived DNE, whereas this repository's
  [classical_logic] asks for every semantically classical tautology.  The raw
  calculus below therefore remains faithful to K/S/EC; its extensional
  [classical_logic] and [e_entailment] adapters take an explicit completeness
  hypothesis rather than silently adding a tautology constructor.
*)

From FoundationModal Require Import
  Syntax Axioms HilbertK LogicInfrastructure EntailmentExtensions
  EntailmentNamedExtensions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition with_re_axiom (AtomType : Type) : Type :=
  formula AtomType -> Prop.

(** Foundation's six constructors: substituted raw axioms, modus ponens,
    replacement of equivalents, and the classical Lukasiewicz K/S/EC
    basis.  In particular there is no necessitation, modal K, or generic
    tautology constructor. *)
Inductive with_re_proves {AtomType : Type}
    (Ax : with_re_axiom AtomType) : formula AtomType -> Prop :=
| WRE_axm : forall p (sigma : AtomType -> formula AtomType),
    Ax p -> with_re_proves Ax (substitute sigma p)
| WRE_mp : forall p q,
    with_re_proves Ax (Imp p q) ->
    with_re_proves Ax p ->
    with_re_proves Ax q
| WRE_re : forall p q,
    with_re_proves Ax (Iff p q) ->
    with_re_proves Ax (Iff (Box p) (Box q))
| WRE_imply_K : forall p q,
    with_re_proves Ax (Hilbert_imply_K p q)
| WRE_imply_S : forall p q r,
    with_re_proves Ax (Hilbert_imply_S p q r)
| WRE_elim_contra : forall p q,
    with_re_proves Ax (Hilbert_elim_contra p q).

Arguments WRE_axm {AtomType Ax p} sigma _.
Arguments WRE_mp {AtomType Ax p q} _ _.
Arguments WRE_re {AtomType Ax p q} _.
Arguments WRE_imply_K {AtomType Ax} p q.
Arguments WRE_imply_S {AtomType Ax} p q r.
Arguments WRE_elim_contra {AtomType Ax} p q.

(** Source-facing wrappers for an arbitrary substitution and for the
    identity substitution. *)
Lemma with_re_axm_substituted :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType) p
         (sigma : AtomType -> formula AtomType),
    Ax p -> with_re_proves Ax (substitute sigma p).
Proof. intros; now apply WRE_axm. Qed.

Lemma with_re_axm :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType) p,
    Ax p -> with_re_proves Ax p.
Proof.
  intros AtomType Ax p Hp.
  replace p with (substitute (@Atom AtomType) p).
  - now apply WRE_axm.
  - apply substitute_id.
Qed.

(** A direct record for Foundation's [Entailment.Lukasiewicz] instance. *)
Record lukasiewicz_entailment {AtomType}
    (L : modal_logic_set AtomType) : Prop := {
  lukasiewicz_imply_K : forall p q, L (Hilbert_imply_K p q);
  lukasiewicz_imply_S : forall p q r, L (Hilbert_imply_S p q r);
  lukasiewicz_elim_contra : forall p q, L (Hilbert_elim_contra p q);
  lukasiewicz_mp : forall p q, L (Imp p q) -> L p -> L q
}.

Lemma with_re_lukasiewicz :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    lukasiewicz_entailment (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax; constructor.
  - apply WRE_imply_K.
  - apply WRE_imply_S.
  - apply WRE_elim_contra.
  - intros p q Hpq Hp. exact (WRE_mp Hpq Hp).
Qed.

(** Structural substitution, with the same fixed source and target atom type
    as Foundation's logic-level substitution instance. *)
Lemma with_re_proves_substitute :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType)
         (sigma : AtomType -> formula AtomType) p,
    with_re_proves Ax p ->
    with_re_proves Ax (substitute sigma p).
Proof.
  intros AtomType Ax sigma p Hp; induction Hp.
  - rewrite substitute_comp.
    now apply WRE_axm.
  - simpl. exact (WRE_mp IHHp1 IHHp2).
  - change (with_re_proves Ax
      (Iff (Box (substitute sigma p)) (Box (substitute sigma q)))).
    apply WRE_re.
    change (with_re_proves Ax
      (Iff (substitute sigma p) (substitute sigma q))) in IHHp.
    exact IHHp.
  - change (with_re_proves Ax
      (Hilbert_imply_K (substitute sigma p) (substitute sigma q))).
    apply WRE_imply_K.
  - change (with_re_proves Ax
      (Hilbert_imply_S (substitute sigma p) (substitute sigma q)
        (substitute sigma r))).
    apply WRE_imply_S.
  - change (with_re_proves Ax
      (Hilbert_elim_contra (substitute sigma p) (substitute sigma q))).
    apply WRE_elim_contra.
Qed.

Definition with_re_substitution_closed {AtomType}
    (Ax : with_re_axiom AtomType) :
    logic_substitution_closed (@with_re_proves AtomType Ax) :=
  @with_re_proves_substitute AtomType Ax.

(** A compact fold API corresponding to Foundation's dependent [rec!]. *)
Lemma with_re_proves_fold :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType)
         (P : formula AtomType -> Prop),
    (forall p sigma, Ax p -> P (substitute sigma p)) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    (forall p q, P (Iff p q) -> P (Iff (Box p) (Box q))) ->
    (forall p q, P (Hilbert_imply_K p q)) ->
    (forall p q r, P (Hilbert_imply_S p q r)) ->
    (forall p q, P (Hilbert_elim_contra p q)) ->
    forall p, with_re_proves Ax p -> P p.
Proof.
  intros AtomType Ax P Hax Hmp Hre HK HS HEC p Hp.
  induction Hp; eauto.
Qed.

(** Weakening where each source axiom is already provable in the target.
    Substitution closure supplies the substituted instance used by [WRE_axm]. *)
Lemma with_re_weaker_of_provable_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : with_re_axiom AtomType),
    (forall p, Ax1 p -> with_re_proves Ax2 p) ->
    logic_subset (@with_re_proves AtomType Ax1)
                 (@with_re_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Hax p Hp; induction Hp.
  - now apply with_re_proves_substitute, Hax.
  - exact (WRE_mp IHHp1 IHHp2).
  - exact (WRE_re IHHp).
  - apply WRE_imply_K.
  - apply WRE_imply_S.
  - apply WRE_elim_contra.
Qed.

Lemma with_re_weaker_of_subset_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : with_re_axiom AtomType),
    (forall p, Ax1 p -> Ax2 p) ->
    logic_subset (@with_re_proves AtomType Ax1)
                 (@with_re_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Hsub.
  apply with_re_weaker_of_provable_axioms.
  intros p Hp. apply with_re_axm. now apply Hsub.
Qed.

(** The extensional capability required by [classical_logic].  Keeping this
    as a named premise documents the exact completeness fact absent from the
    raw six-constructor source calculus. *)
Definition with_re_classical_complete {AtomType}
    (Ax : with_re_axiom AtomType) : Prop :=
  forall p, classical_tautology p -> with_re_proves Ax p.

Lemma with_re_classical_logic :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    with_re_classical_complete Ax ->
    classical_logic (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax Hcomplete; constructor.
  - exact Hcomplete.
  - intros p q Hpq Hp. exact (WRE_mp Hpq Hp).
Qed.

Lemma with_re_e_entailment :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    with_re_classical_complete Ax ->
    e_entailment (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax Hcomplete; constructor.
  - now apply with_re_classical_logic.
  - intro p. apply Hcomplete.
    intro rho; unfold DiaDuality, Iff, And, Dia, Neg; simpl; tauto.
  - intros p q Hiff. now apply WRE_re.
Qed.

(** * Generic raw-axiom capabilities

    These ten records are the relevant fragment of Foundation's imported
    [Modal.Hilbert.Axiom] API.  They remember the schematic atom or atoms and
    membership of that raw formula in [Ax].  Binary schemata retain the
    source's distinctness condition. *)

Record with_re_axioms_has_M {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_M_p : AtomType;
  with_re_M_q : AtomType;
  with_re_M_ne : with_re_M_p <> with_re_M_q;
  with_re_M_mem : Ax (M (Atom with_re_M_p) (Atom with_re_M_q))
}.

Record with_re_axioms_has_C {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_C_p : AtomType;
  with_re_C_q : AtomType;
  with_re_C_ne : with_re_C_p <> with_re_C_q;
  with_re_C_mem : Ax (C (Atom with_re_C_p) (Atom with_re_C_q))
}.

Record with_re_axioms_has_N {AtomType}
    (Ax : with_re_axiom AtomType) : Prop := {
  with_re_N_mem : Ax N
}.

Record with_re_axioms_has_K {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_K_p : AtomType;
  with_re_K_q : AtomType;
  with_re_K_ne : with_re_K_p <> with_re_K_q;
  with_re_K_mem : Ax (K (Atom with_re_K_p) (Atom with_re_K_q))
}.

Record with_re_axioms_has_T {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_T_p : AtomType;
  with_re_T_mem : Ax (T (Atom with_re_T_p))
}.

Record with_re_axioms_has_D {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_D_p : AtomType;
  with_re_D_mem : Ax (D (Atom with_re_D_p))
}.

Record with_re_axioms_has_P {AtomType}
    (Ax : with_re_axiom AtomType) : Prop := {
  with_re_P_mem : Ax P
}.

Record with_re_axioms_has_Four {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_Four_p : AtomType;
  with_re_Four_mem : Ax (Four (Atom with_re_Four_p))
}.

Record with_re_axioms_has_B {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_B_p : AtomType;
  with_re_B_mem : Ax (B (Atom with_re_B_p))
}.

Record with_re_axioms_has_Five {AtomType}
    (Ax : with_re_axiom AtomType) : Type := {
  with_re_Five_p : AtomType;
  with_re_Five_mem : Ax (Five (Atom with_re_Five_p))
}.

Definition atom_decidable_equality (AtomType : Type) : Type :=
  forall x y : AtomType, {x = y} + {x <> y}.

Definition with_re_single_substitution {AtomType}
    (eq_dec : atom_decidable_equality AtomType)
    (a : AtomType) (p : formula AtomType)
    : AtomType -> formula AtomType :=
  fun b => if eq_dec a b then p else Atom b.

Definition with_re_double_substitution {AtomType}
    (eq_dec : atom_decidable_equality AtomType)
    (a b : AtomType) (p q : formula AtomType)
    : AtomType -> formula AtomType :=
  fun c =>
    if eq_dec a c then p
    else if eq_dec b c then q
    else Atom c.

Lemma with_re_single_substitution_at :
  forall (AtomType : Type) (eq_dec : atom_decidable_equality AtomType)
         a p,
    with_re_single_substitution eq_dec a p a = p.
Proof.
  intros AtomType eq_dec a p; unfold with_re_single_substitution.
  destruct (eq_dec a a); [reflexivity | contradiction].
Qed.

Lemma with_re_double_substitution_left :
  forall (AtomType : Type) (eq_dec : atom_decidable_equality AtomType)
         a b p q,
    with_re_double_substitution eq_dec a b p q a = p.
Proof.
  intros AtomType eq_dec a b p q; unfold with_re_double_substitution.
  destruct (eq_dec a a); [reflexivity | contradiction].
Qed.

Lemma with_re_double_substitution_right :
  forall (AtomType : Type) (eq_dec : atom_decidable_equality AtomType)
         a b p q,
    a <> b ->
    with_re_double_substitution eq_dec a b p q b = q.
Proof.
  intros AtomType eq_dec a b p q Hab; unfold with_re_double_substitution.
  destruct (eq_dec a b) as [Heq | _]; [contradiction |].
  destruct (eq_dec b b); [reflexivity | contradiction].
Qed.

Lemma with_re_instantiate_unary :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType)
         (eq_dec : atom_decidable_equality AtomType)
         (Schema : formula AtomType -> formula AtomType) a,
    (forall sigma x,
      substitute sigma (Schema x) = Schema (substitute sigma x)) ->
    Ax (Schema (Atom a)) ->
    forall p, with_re_proves Ax (Schema p).
Proof.
  intros AtomType Ax eq_dec Schema a Hschema Hmem p.
  pose proof
    (@WRE_axm AtomType Ax (Schema (Atom a))
      (with_re_single_substitution eq_dec a p) Hmem) as H.
  rewrite Hschema in H; simpl in H.
  rewrite with_re_single_substitution_at in H.
  exact H.
Qed.

Lemma with_re_instantiate_binary :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType)
         (eq_dec : atom_decidable_equality AtomType)
         (Schema : formula AtomType -> formula AtomType -> formula AtomType)
         a b,
    a <> b ->
    (forall sigma x y,
      substitute sigma (Schema x y) =
      Schema (substitute sigma x) (substitute sigma y)) ->
    Ax (Schema (Atom a) (Atom b)) ->
    forall p q, with_re_proves Ax (Schema p q).
Proof.
  intros AtomType Ax eq_dec Schema a b Hab Hschema Hmem p q.
  pose proof
    (@WRE_axm AtomType Ax (Schema (Atom a) (Atom b))
      (with_re_double_substitution eq_dec a b p q) Hmem) as H.
  rewrite Hschema in H; simpl in H.
  rewrite with_re_double_substitution_left in H.
  rewrite with_re_double_substitution_right in H by exact Hab.
  exact H.
Qed.

(** * The ten generic adapters from WithRE/Basic.lean *)

Lemma with_re_has_M :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_M Ax ->
    has_M (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intros p q.
  eapply (@with_re_instantiate_binary AtomType Ax eq_dec (@M AtomType)
    (with_re_M_p Hraw) (with_re_M_q Hraw)).
  - exact (@with_re_M_ne AtomType Ax Hraw).
  - reflexivity.
  - exact (@with_re_M_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_C :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_C Ax ->
    has_C (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intros p q.
  eapply (@with_re_instantiate_binary AtomType Ax eq_dec (@C AtomType)
    (with_re_C_p Hraw) (with_re_C_q Hraw)).
  - exact (@with_re_C_ne AtomType Ax Hraw).
  - reflexivity.
  - exact (@with_re_C_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_N :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    with_re_axioms_has_N Ax ->
    has_N (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax Hraw; constructor.
  apply with_re_axm. exact (@with_re_N_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_K :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_K Ax ->
    has_K (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intros p q.
  eapply (@with_re_instantiate_binary AtomType Ax eq_dec (@K AtomType)
    (with_re_K_p Hraw) (with_re_K_q Hraw)).
  - exact (@with_re_K_ne AtomType Ax Hraw).
  - reflexivity.
  - exact (@with_re_K_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_T :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_T Ax ->
    has_T (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_re_instantiate_unary AtomType Ax eq_dec (@T AtomType)
    (with_re_T_p Hraw)).
  - reflexivity.
  - exact (@with_re_T_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_D :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_D Ax ->
    has_D (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_re_instantiate_unary AtomType Ax eq_dec (@D AtomType)
    (with_re_D_p Hraw)).
  - reflexivity.
  - exact (@with_re_D_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_P :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    with_re_axioms_has_P Ax ->
    has_P (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax Hraw; constructor.
  apply with_re_axm. exact (@with_re_P_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_Four :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_Four Ax ->
    has_Four (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_re_instantiate_unary AtomType Ax eq_dec (@Four AtomType)
    (with_re_Four_p Hraw)).
  - reflexivity.
  - exact (@with_re_Four_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_B :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_B Ax ->
    has_B (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_re_instantiate_unary AtomType Ax eq_dec (@B AtomType)
    (with_re_B_p Hraw)).
  - reflexivity.
  - exact (@with_re_B_mem AtomType Ax Hraw).
Qed.

Lemma with_re_has_Five :
  forall (AtomType : Type) (Ax : with_re_axiom AtomType),
    atom_decidable_equality AtomType ->
    with_re_axioms_has_Five Ax ->
    has_Five (@with_re_proves AtomType Ax).
Proof.
  intros AtomType Ax eq_dec Hraw; constructor; intro p.
  eapply (@with_re_instantiate_unary AtomType Ax eq_dec (@Five AtomType)
    (with_re_Five_p Hraw)).
  - reflexivity.
  - exact (@with_re_Five_mem AtomType Ax Hraw).
Qed.
