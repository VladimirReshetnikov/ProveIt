(**
  The raw axiom-parametric normal Hilbert calculus.

  This file independently ports the ten-declaration generic core of the
  pinned Foundation module [Modal/Hilbert/Normal/Basic.lean], through
  [weakerThan_of_subset_axioms].  The later raw-axiom capability adapters and
  concrete named-system catalogue remain outside this tranche.

  The calculus is deliberately not [normal_proves] from [NormalHilbert]: its
  axiom predicate fixes an atom type, each raw axiom enters only through an
  endosubstitution, and modal K is not hardwired.  It is available precisely
  when the chosen [raw_modal_axiom] contains a K template, as in Foundation.

  Foundation distinguishes a raw proof from proposition-valued theoremhood.
  Here the raw calculus itself lives in Prop, so [axm'] and [axm'!] have the
  same Coq proposition and are exposed by separate public names.  Likewise,
  Foundation's dependent [rec!] writes its motive into bare [Sort], which
  Lean elaborates as [Sort 0] ([Prop]).  Therefore
  [normal_hilbert_proves_fold] retains both the dependent proof index and the
  exact source codomain.
*)

From FoundationModal Require Import
  Syntax HilbertK LogicInfrastructure EntailmentExtensions HilbertAxiom
  HilbertWithRE.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The six raw constructors of [Hilbert.Normal] *)

Inductive normal_hilbert_proves {AtomType : Type}
    (Ax : raw_modal_axiom AtomType) : formula AtomType -> Prop :=
| NH_axm : forall p (sigma : AtomType -> formula AtomType),
    Ax p -> normal_hilbert_proves Ax (substitute sigma p)
| NH_mp : forall p q,
    normal_hilbert_proves Ax (Imp p q) ->
    normal_hilbert_proves Ax p ->
    normal_hilbert_proves Ax q
| NH_nec : forall p,
    normal_hilbert_proves Ax p ->
    normal_hilbert_proves Ax (Box p)
| NH_imply_K : forall p q,
    normal_hilbert_proves Ax (Hilbert_imply_K p q)
| NH_imply_S : forall p q r,
    normal_hilbert_proves Ax (Hilbert_imply_S p q r)
| NH_elim_contra : forall p q,
    normal_hilbert_proves Ax (Hilbert_elim_contra p q).

Arguments NH_axm {AtomType Ax p} sigma _.
Arguments NH_mp {AtomType Ax p q} _ _.
Arguments NH_nec {AtomType Ax p} _.
Arguments NH_imply_K {AtomType Ax} p q.
Arguments NH_imply_S {AtomType Ax} p q r.
Arguments NH_elim_contra {AtomType Ax} p q.

(** [axm'] in the source: inject a raw axiom through the identity
    substitution. *)
Lemma normal_hilbert_axm :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p,
    Ax p -> normal_hilbert_proves Ax p.
Proof.
  intros AtomType Ax p Hp.
  replace p with (substitute (@Atom AtomType) p).
  - now apply NH_axm.
  - apply substitute_id.
Qed.

(** [axm!] in the source: inject an arbitrary substitution instance. *)
Lemma normal_hilbert_axm_substituted :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType) p
         (sigma : AtomType -> formula AtomType),
    Ax p -> normal_hilbert_proves Ax (substitute sigma p).
Proof. intros; now apply NH_axm. Qed.

(** [axm'!] collapses extensionally to [axm'] because theoremhood is
    already Prop-valued. *)
Definition normal_hilbert_axm_bang := @normal_hilbert_axm.

(** * The three structural instances *)

Lemma normal_hilbert_lukasiewicz :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    lukasiewicz_entailment (@normal_hilbert_proves AtomType Ax).
Proof.
  intros AtomType Ax; constructor.
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
  - intros p q Hpq Hp. exact (NH_mp Hpq Hp).
Qed.

Lemma normal_hilbert_necessitation :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType),
    necessitation (@normal_hilbert_proves AtomType Ax).
Proof.
  intros AtomType Ax p Hp. exact (NH_nec Hp).
Qed.

Lemma normal_hilbert_proves_substitute :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (sigma : AtomType -> formula AtomType) p,
    normal_hilbert_proves Ax p ->
    normal_hilbert_proves Ax (substitute sigma p).
Proof.
  intros AtomType Ax sigma p Hp; induction Hp; simpl.
  - rewrite substitute_comp. now apply NH_axm.
  - exact (NH_mp IHHp1 IHHp2).
  - exact (NH_nec IHHp).
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
Qed.

(** * Exact Prop-valued dependent fold corresponding to [Normal.rec!] *)

Lemma normal_hilbert_proves_fold :
  forall (AtomType : Type) (Ax : raw_modal_axiom AtomType)
         (P : forall p, normal_hilbert_proves Ax p -> Prop),
    (forall p sigma (h : Ax p),
      P (substitute sigma p) (@NH_axm AtomType Ax p sigma h)) ->
    (forall p q
       (hpq : normal_hilbert_proves Ax (Imp p q))
       (hp : normal_hilbert_proves Ax p),
      P (Imp p q) hpq -> P p hp -> P q (@NH_mp AtomType Ax p q hpq hp)) ->
    (forall p (hp : normal_hilbert_proves Ax p),
      P p hp -> P (Box p) (@NH_nec AtomType Ax p hp)) ->
    (forall p q,
      P (Hilbert_imply_K p q) (@NH_imply_K AtomType Ax p q)) ->
    (forall p q r,
      P (Hilbert_imply_S p q r) (@NH_imply_S AtomType Ax p q r)) ->
    (forall p q,
      P (Hilbert_elim_contra p q) (@NH_elim_contra AtomType Ax p q)) ->
    forall p (d : normal_hilbert_proves Ax p), P p d.
Proof.
  intros AtomType Ax P Hax Hmp Hnec HK HS HEC p d.
  exact ((fix fold p0 (d0 : normal_hilbert_proves Ax p0) {struct d0}
      : P p0 d0 :=
    match d0 as d1 in normal_hilbert_proves _ p1 return P p1 d1 with
    | @NH_axm _ _ q sigma h => Hax q sigma h
    | @NH_mp _ _ q r hqr hq =>
        Hmp q r hqr hq (fold (Imp q r) hqr) (fold q hq)
    | @NH_nec _ _ q hq => Hnec q hq (fold q hq)
    | @NH_imply_K _ _ q r => HK q r
    | @NH_imply_S _ _ q r s => HS q r s
    | @NH_elim_contra _ _ q r => HEC q r
    end) p d).
Qed.

(** * Exact axiom weakening principles *)

Lemma normal_hilbert_weaker_of_provable_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : raw_modal_axiom AtomType),
    (forall p, Ax1 p -> normal_hilbert_proves Ax2 p) ->
    logic_subset (@normal_hilbert_proves AtomType Ax1)
                 (@normal_hilbert_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Haxioms p Hp; induction Hp.
  - now apply normal_hilbert_proves_substitute, Haxioms.
  - exact (NH_mp IHHp1 IHHp2).
  - exact (NH_nec IHHp).
  - apply NH_imply_K.
  - apply NH_imply_S.
  - apply NH_elim_contra.
Qed.

Lemma normal_hilbert_weaker_of_subset_axioms :
  forall (AtomType : Type)
         (Ax1 Ax2 : raw_modal_axiom AtomType),
    (forall p, Ax1 p -> Ax2 p) ->
    logic_subset (@normal_hilbert_proves AtomType Ax1)
                 (@normal_hilbert_proves AtomType Ax2).
Proof.
  intros AtomType Ax1 Ax2 Hsubset.
  apply normal_hilbert_weaker_of_provable_axioms.
  intros p Hp. apply normal_hilbert_axm. now apply Hsubset.
Qed.
