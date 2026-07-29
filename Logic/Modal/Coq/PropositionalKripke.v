(** Generalized intuitionistic propositional Kripke semantics.

    This ports the semantic core of Foundation's Propositional/Kripke
    [Basic], [Hilbert/Basic], [AxiomWLEM], and [AxiomDummett] modules.
    Arbitrary, possibly empty preorders replace nonempty partial orders, and
    atoms are polymorphic rather than fixed to naturals. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  GenericSemantics GenericForcingRelation
  PropositionalFormula PropositionalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record pkripke_frame : Type := {
  pkripke_world : Type;
  pkripke_access : pkripke_world -> pkripke_world -> Prop;
  pkripke_access_refl : forall w, pkripke_access w w;
  pkripke_access_trans : forall x y z,
    pkripke_access x y -> pkripke_access y z -> pkripke_access x z
}.

Arguments pkripke_world _ : clear implicits.
Arguments pkripke_access _ _ _ : clear implicits.
Arguments pkripke_access_refl _ _ : clear implicits.
Arguments pkripke_access_trans _ _ _ _ _ _ : clear implicits.

Record pkripke_valuation (Atom : Type) (F : pkripke_frame) : Type := {
  pkripke_atom_value : Atom -> pkripke_world F -> Prop;
  pkripke_atom_persistent : forall a x y,
    pkripke_access F x y ->
    pkripke_atom_value a x -> pkripke_atom_value a y
}.

Arguments pkripke_atom_value {Atom F} _ _ _.

Record pkripke_model (Atom : Type) : Type := {
  pkripke_model_frame : pkripke_frame;
  pkripke_model_valuation : pkripke_valuation Atom pkripke_model_frame
}.

Arguments pkripke_model_frame {Atom} _.
Arguments pkripke_model_valuation {Atom} _.

Fixpoint pkripke_forces {Atom : Type} (M : pkripke_model Atom)
    (w : pkripke_world (pkripke_model_frame M))
    (p : pformula Atom) : Prop :=
  match p with
  | PAtom a => pkripke_atom_value (pkripke_model_valuation M) a w
  | PFalsum => False
  | PAnd q r => @pkripke_forces Atom M w q /\
                @pkripke_forces Atom M w r
  | POr q r => @pkripke_forces Atom M w q \/
               @pkripke_forces Atom M w r
  | PImp q r => forall v,
      pkripke_access (pkripke_model_frame M) w v ->
      @pkripke_forces Atom M v q -> @pkripke_forces Atom M v r
  end.

Arguments pkripke_forces {Atom} M w p.

Lemma pkripke_forces_atom :
  forall (Atom : Type) (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M)) a,
    pkripke_forces M w (PAtom a) =
    pkripke_atom_value (pkripke_model_valuation M) a w.
Proof. reflexivity. Qed.

Lemma pkripke_forces_bottom :
  forall (Atom : Type) (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M)),
    ~ pkripke_forces M w (@PFalsum Atom).
Proof. intros; exact (fun H => H). Qed.

Lemma pkripke_forces_and :
  forall (Atom : Type) (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M)) p q,
    pkripke_forces M w (PAnd p q) <->
    pkripke_forces M w p /\ pkripke_forces M w q.
Proof. reflexivity. Qed.

Lemma pkripke_forces_or :
  forall (Atom : Type) (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M)) p q,
    pkripke_forces M w (POr p q) <->
    pkripke_forces M w p \/ pkripke_forces M w q.
Proof. reflexivity. Qed.

Lemma pkripke_forces_imp :
  forall (Atom : Type) (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M)) p q,
    pkripke_forces M w (PImp p q) <->
    (forall v, pkripke_access (pkripke_model_frame M) w v ->
      pkripke_forces M v p -> pkripke_forces M v q).
Proof. reflexivity. Qed.

Lemma pkripke_forces_neg :
  forall (Atom : Type) (M : pkripke_model Atom)
      (w : pkripke_world (pkripke_model_frame M)) p,
    pkripke_forces M w (pneg p) <->
    (forall v, pkripke_access (pkripke_model_frame M) w v ->
      ~ pkripke_forces M v p).
Proof. reflexivity. Qed.

(** Heredity is factored once for every formula. *)
Lemma pkripke_forces_persistent :
  forall (Atom : Type) (M : pkripke_model Atom) (p : pformula Atom)
      (x y : pkripke_world (pkripke_model_frame M)),
    pkripke_access (pkripke_model_frame M) x y ->
    pkripke_forces M x p -> pkripke_forces M y p.
Proof.
  intros Atom M p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros x y Rxy Hx; cbn in *.
  - eapply pkripke_atom_persistent; eauto.
  - contradiction.
  - destruct Hx as [Hp Hq]. split.
    + exact (IHp x y Rxy Hp).
    + exact (IHq x y Rxy Hq).
  - destruct Hx as [Hp | Hq].
    + left; eapply IHp; eauto.
    + right; eapply IHq; eauto.
  - intros z Ryz Hzp. apply (Hx z).
    + eapply pkripke_access_trans; eauto.
    + exact Hzp.
Qed.

(** Package the concrete semantics once for generic forcing arguments.  This
    adapter lets every theorem stated through [generic_int_kripke] consume a
    propositional Kripke model without restating its forcing clauses. *)
Definition pkripke_forcing_relation {Atom : Type}
    (M : pkripke_model Atom) :
    generic_forcing_relation
      (pkripke_world (pkripke_model_frame M)) (pformula Atom) :=
  @Build_generic_semantics
    (pkripke_world (pkripke_model_frame M)) (pformula Atom)
    (pkripke_forces M).

Definition pkripke_generic_int_forcing {Atom : Type}
    (M : pkripke_model Atom) :
    generic_int_kripke (pformula_connectives Atom)
      (pkripke_forcing_relation M)
      (pkripke_access (pkripke_model_frame M)).
Proof.
  constructor.
  - constructor.
    + constructor. intros w v Rwv Hfalse. exact Hfalse.
    + constructor. intros w p q. reflexivity.
    + constructor. intros w p q. reflexivity.
  - constructor. intros w p Hw v Rwv.
    exact (pkripke_forces_persistent Rwv Hw).
  - constructor. intros w p q. reflexivity.
  - constructor. apply pkripke_forces_bottom.
  - constructor. intros w p. apply pkripke_forces_neg.
Defined.

Definition pkripke_substitution_model {A B : Type}
    (M : pkripke_model B) (sigma : psubstitution A B) :
    pkripke_model A.
Proof.
  refine {| pkripke_model_frame := pkripke_model_frame M;
            pkripke_model_valuation :=
              {| pkripke_atom_value := fun a w =>
                   pkripke_forces M w (sigma a) |} |}.
  intros a x y Rxy Hx.
  exact (@pkripke_forces_persistent B M (sigma a) x y Rxy Hx).
Defined.

(** Heterogeneous substitution strictly generalizes the source theorem. *)
Lemma pkripke_forces_substitute :
  forall (A B : Type) (M : pkripke_model B) (sigma : psubstitution A B)
      (p : pformula A) (w : pkripke_world (pkripke_model_frame M)),
    pkripke_forces (pkripke_substitution_model M sigma) w p <->
    pkripke_forces M w (pformula_substitute sigma p).
Proof.
  intros A B M sigma p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro w; cbn.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - split; intros H v Rwv Hv.
    + apply (proj1 (IHq v)), H with (v := v); [exact Rwv |].
      now apply (proj2 (IHp v)).
    + apply (proj2 (IHq v)), H with (v := v); [exact Rwv |].
      now apply (proj1 (IHp v)).
Qed.

Definition pkripke_model_valid {Atom : Type}
    (M : pkripke_model Atom) (p : pformula Atom) : Prop :=
  forall w, pkripke_forces M w p.

Definition pkripke_frame_valid {Atom : Type}
    (F : pkripke_frame) (p : pformula Atom) : Prop :=
  forall V : pkripke_valuation Atom F,
    pkripke_model_valid
      {| pkripke_model_frame := F; pkripke_model_valuation := V |} p.

Definition pkripke_frame_class_valid {Atom : Type}
    (C : pkripke_frame -> Prop) (p : pformula Atom) : Prop :=
  forall F, C F -> pkripke_frame_valid F p.

Definition pkripke_sound {Atom : Type} (H : ph_hilbert Atom)
    (C : pkripke_frame -> Prop) : Prop :=
  forall p, ph_hilbert_provable H p -> pkripke_frame_class_valid C p.

Definition pkripke_complete {Atom : Type} (H : ph_hilbert Atom)
    (C : pkripke_frame -> Prop) : Prop :=
  forall p, pkripke_frame_class_valid C p -> ph_hilbert_provable H p.

Definition ph_hilbert_logic_included {Atom : Type}
    (H1 H2 : ph_hilbert Atom) : Prop :=
  forall p, ph_hilbert_provable H1 p -> ph_hilbert_provable H2 p.

Definition pkripke_false_valuation (Atom : Type) (F : pkripke_frame) :
    pkripke_valuation Atom F :=
  {| pkripke_atom_value := fun _ _ => False;
     pkripke_atom_persistent := fun _ _ _ _ H => H |}.

Lemma pkripke_frame_valid_substitute :
  forall (A B : Type) (F : pkripke_frame) (p : pformula A),
    pkripke_frame_valid F p -> forall sigma : psubstitution A B,
    pkripke_frame_valid F (pformula_substitute sigma p).
Proof.
  intros A B F p Hp sigma V w.
  apply (proj1 (@pkripke_forces_substitute A B
    {| pkripke_model_frame := F; pkripke_model_valuation := V |}
    sigma p w)).
  apply Hp.
Qed.

(** * Hilbert soundness *)

Lemma pkripke_model_valid_modus_ponens :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (PImp p q) ->
    pkripke_model_valid M p -> pkripke_model_valid M q.
Proof.
  intros Atom M p q Hpq Hp w.
  apply (Hpq w w (pkripke_access_refl _ w)), Hp.
Qed.

Lemma pkripke_minimal_axiom_K_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (ph_axiom_K p q).
Proof.
  intros Atom M p q x y Rxy Hp z Ryz _.
  exact (@pkripke_forces_persistent Atom M p y z Ryz Hp).
Qed.

Lemma pkripke_minimal_axiom_S_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q r,
    pkripke_model_valid M (ph_axiom_S p q r).
Proof.
  intros Atom M p q r x y Rxy H1 z Ryz H2 u Rzu Hp.
  apply (H1 u).
  - eapply pkripke_access_trans; eauto.
  - exact Hp.
  - apply pkripke_access_refl.
  - apply (H2 u Rzu Hp).
Qed.

Lemma pkripke_minimal_axiom_and1_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (ph_axiom_and1 p q).
Proof. intros Atom M p q x y _ [Hp _]; exact Hp. Qed.

Lemma pkripke_minimal_axiom_and2_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (ph_axiom_and2 p q).
Proof. intros Atom M p q x y _ [_ Hq]; exact Hq. Qed.

Lemma pkripke_minimal_axiom_and3_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (ph_axiom_and3 p q).
Proof.
  intros Atom M p q x y Rxy Hp z Ryz Hq; split.
  - eapply pkripke_forces_persistent; eauto.
  - exact Hq.
Qed.

Lemma pkripke_minimal_axiom_or1_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (ph_axiom_or1 p q).
Proof. intros Atom M p q x y _ Hp; now left. Qed.

Lemma pkripke_minimal_axiom_or2_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q,
    pkripke_model_valid M (ph_axiom_or2 p q).
Proof. intros Atom M p q x y _ Hq; now right. Qed.

Lemma pkripke_minimal_axiom_or3_valid :
  forall (Atom : Type) (M : pkripke_model Atom) p q r,
    pkripke_model_valid M (ph_axiom_or3 p q r).
Proof.
  intros Atom M p q r x y Rxy Hpr z Ryz Hqr u Rzu [Hp | Hq].
  - apply (Hpr u); [eapply pkripke_access_trans; eauto | exact Hp].
  - apply (Hqr u Rzu Hq).
Qed.

Lemma pkripke_model_valid_efq :
  forall (Atom : Type) (M : pkripke_model Atom) p,
    pkripke_model_valid M (ph_axiom_efq p).
Proof. intros Atom M p x y _ H; contradiction. Qed.

Theorem ph_hilbert_proof_pkripke_sound :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (C : pkripke_frame -> Prop),
    (forall p, ph_hilbert_schema H p ->
      pkripke_frame_class_valid C p) ->
    forall p, ph_hilbert_proof H p ->
      pkripke_frame_class_valid C p.
Proof.
  intros Atom H C Hschema p d; induction d; intros F HF V.
  - exact (Hschema p p0 F HF V).
  - eapply pkripke_model_valid_modus_ponens.
    + exact (IHd1 F HF V).
    + exact (IHd2 F HF V).
  - intros w y _ Hfalse; contradiction.
  - apply pkripke_minimal_axiom_S_valid.
  - apply pkripke_minimal_axiom_K_valid.
  - apply pkripke_minimal_axiom_and1_valid.
  - apply pkripke_minimal_axiom_and2_valid.
  - apply pkripke_minimal_axiom_and3_valid.
  - apply pkripke_minimal_axiom_or1_valid.
  - apply pkripke_minimal_axiom_or2_valid.
  - apply pkripke_minimal_axiom_or3_valid.
Qed.

Corollary ph_hilbert_pkripke_sound :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (C : pkripke_frame -> Prop),
    (forall p, ph_hilbert_schema H p ->
      pkripke_frame_class_valid C p) ->
    forall p, ph_hilbert_provable H p ->
      pkripke_frame_class_valid C p.
Proof.
  intros Atom H C Hschema p [d].
  exact (ph_hilbert_proof_pkripke_sound Hschema d).
Qed.

Theorem ph_hilbert_consistent_of_nonempty_pkripke_class :
  forall (Atom : Type) (H : ph_hilbert Atom)
      (C : pkripke_frame -> Prop),
    pkripke_sound H C ->
    (exists F, C F /\ inhabited (pkripke_world F)) ->
    ~ ph_hilbert_provable H PFalsum.
Proof.
  intros Atom H C Hsound [F [HF [w]]] Hbottom.
  exact (Hsound PFalsum Hbottom F HF
    (pkripke_false_valuation Atom F) w).
Qed.

Theorem ph_hilbert_included_of_pkripke_class_subset :
  forall (Atom : Type) (H1 H2 : ph_hilbert Atom)
      (C1 C2 : pkripke_frame -> Prop),
    (forall F, C2 F -> C1 F) ->
    pkripke_sound H1 C1 -> pkripke_complete H2 C2 ->
    ph_hilbert_logic_included H1 H2.
Proof.
  intros Atom H1 H2 C1 C2 Hsubset Hsound Hcomplete p Hp.
  apply Hcomplete. intros F HF.
  exact (Hsound p Hp F (Hsubset F HF)).
Qed.

Theorem ph_hilbert_int_pkripke_sound :
  forall (Atom : Type) p,
    ph_hilbert_provable (ph_hilbert_int Atom) p ->
    pkripke_frame_class_valid (fun _ => True) p.
Proof.
  intros Atom p Hp.
  eapply ph_hilbert_pkripke_sound; [|exact Hp].
  intros q Hq; destruct Hq. intros F _ V.
  apply pkripke_model_valid_efq.
Qed.

Definition pkripke_singleton_frame : pkripke_frame :=
  {| pkripke_world := unit;
     pkripke_access := fun _ _ => True;
     pkripke_access_refl := fun _ => I;
     pkripke_access_trans := fun _ _ _ _ _ => I |}.

Definition pkripke_singleton_valuation (Atom : Type) :
    pkripke_valuation Atom pkripke_singleton_frame :=
  {| pkripke_atom_value := fun _ _ => False;
     pkripke_atom_persistent := fun _ _ _ _ H => H |}.

Theorem ph_hilbert_int_consistent_via_pkripke :
  forall Atom : Type,
    ~ ph_hilbert_provable (ph_hilbert_int Atom) PFalsum.
Proof.
  intro Atom.
  eapply ph_hilbert_consistent_of_nonempty_pkripke_class.
  - exact (@ph_hilbert_int_pkripke_sound Atom).
  - exists pkripke_singleton_frame. split; [exact I |].
    now constructor; exact tt.
Qed.

(** * Intermediate axioms and exact frame conditions *)

Definition pkripke_frame_strongly_convergent (F : pkripke_frame) : Prop :=
  forall x y z,
    pkripke_access F x y -> pkripke_access F x z ->
    exists u, pkripke_access F y u /\ pkripke_access F z u.

Definition pkripke_frame_strongly_connected (F : pkripke_frame) : Prop :=
  forall x y z,
    pkripke_access F x y -> pkripke_access F x z ->
    pkripke_access F y z \/ pkripke_access F z y.

Theorem pkripke_WLEM_valid_of_strongly_convergent :
  forall (Atom : Type) (F : pkripke_frame),
    pkripke_frame_strongly_convergent F ->
    forall p : pformula Atom, pkripke_frame_valid F (ph_axiom_wlem p).
Proof.
  intros Atom F Hconv p V x; cbn [ph_axiom_wlem pneg].
  destruct (classic (forall y, pkripke_access F x y ->
      ~ pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |}
        y p)) as [Hneg | Hneg].
  - now left.
  - right. intros y Rxy Hyneg.
    assert (Hex : exists z, pkripke_access F x z /\
        pkripke_forces
          {| pkripke_model_frame := F; pkripke_model_valuation := V |}
          z p).
    { apply NNPP. intro Hnone. apply Hneg. intros z Rxz Hzp.
      apply Hnone. now exists z. }
    destruct Hex as [z [Rxz Hzp]].
    destruct (Hconv x y z Rxy Rxz) as [u [Ryu Rzu]].
    apply (Hyneg u Ryu).
    eapply pkripke_forces_persistent; eauto.
Qed.

Theorem pkripke_strongly_convergent_of_WLEM_valid :
  forall (F : pkripke_frame),
    pkripke_frame_valid F (ph_axiom_wlem (PAtom 0)) ->
    pkripke_frame_strongly_convergent F.
Proof.
  intros F Hvalid x y z Rxy Rxz.
  pose (V :=
    {| pkripke_atom_value := fun _ v => pkripke_access F y v;
       pkripke_atom_persistent := fun _ a b Rab Rya =>
         pkripke_access_trans F y a b Rya Rab |} :
      pkripke_valuation nat F).
  specialize (Hvalid V x). cbn [ph_axiom_wlem pneg] in Hvalid.
  destruct Hvalid as [Hneg | Hdneg].
  - exfalso. apply (Hneg y Rxy). apply pkripke_access_refl.
  - apply NNPP. intro Hnone.
    apply (Hdneg z Rxz). intros u Rzu Ryu.
    apply Hnone. now exists u.
Qed.

Theorem pkripke_Dummett_valid_of_strongly_connected :
  forall (Atom : Type) (F : pkripke_frame),
    pkripke_frame_strongly_connected F ->
    forall p q : pformula Atom,
      pkripke_frame_valid F (ph_axiom_dummett p q).
Proof.
  intros Atom F Hconn p q V x; cbn [ph_axiom_dummett].
  apply NNPP. intro Hneither.
  apply Decidable.not_or in Hneither as [Hpq Hqp].
  assert (Hy : exists y, pkripke_access F x y /\
      pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} y p /\
      ~ pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} y q).
  { apply NNPP. intro Hnone. apply Hpq. intros y Rxy Hyp.
    apply NNPP. intro Hynq. apply Hnone. exists y. repeat split; assumption. }
  assert (Hz : exists z, pkripke_access F x z /\
      pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} z q /\
      ~ pkripke_forces
        {| pkripke_model_frame := F; pkripke_model_valuation := V |} z p).
  { apply NNPP. intro Hnone. apply Hqp. intros z Rxz Hzq.
    apply NNPP. intro Hznp. apply Hnone. exists z. repeat split; assumption. }
  destruct Hy as [y [Rxy [Hyp Hynq]]].
  destruct Hz as [z [Rxz [Hzq Hznp]]].
  destruct (Hconn x y z Rxy Rxz) as [Ryz | Rzy].
  - apply Hznp. eapply pkripke_forces_persistent; eauto.
  - apply Hynq. eapply pkripke_forces_persistent; eauto.
Qed.

Theorem pkripke_strongly_connected_of_Dummett_valid :
  forall (F : pkripke_frame),
    pkripke_frame_valid F
      (ph_axiom_dummett (PAtom 0) (PAtom 1)) ->
    pkripke_frame_strongly_connected F.
Proof.
  intros F Hvalid x y z Rxy Rxz.
  assert (HV : forall (a : nat) u v,
      pkripke_access F u v ->
      match a with
      | 0 => pkripke_access F y u
      | 1 => pkripke_access F z u
      | _ => True
      end ->
      match a with
      | 0 => pkripke_access F y v
      | 1 => pkripke_access F z v
      | _ => True
      end).
  { intros [|[|a]] u v Ruv H; cbn in *.
    - eapply pkripke_access_trans; eauto.
    - eapply pkripke_access_trans; eauto.
    - exact I. }
  pose (V :=
    {| pkripke_atom_value := fun a v =>
         match a with
         | 0 => pkripke_access F y v
         | 1 => pkripke_access F z v
         | _ => True
         end;
       pkripke_atom_persistent := HV |} : pkripke_valuation nat F).
  specialize (Hvalid V x). cbn [ph_axiom_dummett] in Hvalid.
  destruct Hvalid as [Hyz | Hzy].
  - right. apply (Hyz y Rxy). apply pkripke_access_refl.
  - left. apply (Hzy z Rxz). apply pkripke_access_refl.
Qed.

Theorem ph_hilbert_kc_pkripke_sound :
  forall (Atom : Type) p,
    ph_hilbert_provable (ph_hilbert_kc Atom) p ->
    pkripke_frame_class_valid pkripke_frame_strongly_convergent p.
Proof.
  intros Atom p Hp.
  eapply ph_hilbert_pkripke_sound; [|exact Hp].
  intros q Hq; destruct Hq; intros F HF.
  - intros V. apply pkripke_model_valid_efq.
  - now apply pkripke_WLEM_valid_of_strongly_convergent.
Qed.

Theorem ph_hilbert_lc_pkripke_sound :
  forall (Atom : Type) p,
    ph_hilbert_provable (ph_hilbert_lc Atom) p ->
    pkripke_frame_class_valid pkripke_frame_strongly_connected p.
Proof.
  intros Atom p Hp.
  eapply ph_hilbert_pkripke_sound; [|exact Hp].
  intros q Hq; destruct Hq; intros F HF.
  - intros V. apply pkripke_model_valid_efq.
  - now apply pkripke_Dummett_valid_of_strongly_connected.
Qed.

Theorem ph_hilbert_lc_consistent_via_pkripke :
  ~ ph_hilbert_provable (ph_hilbert_lc nat) PFalsum.
Proof.
  eapply ph_hilbert_consistent_of_nonempty_pkripke_class.
  - exact (@ph_hilbert_lc_pkripke_sound nat).
  - exists pkripke_singleton_frame. split.
    + intros x y z _ _. left. constructor.
    + constructor. exact tt.
Qed.
