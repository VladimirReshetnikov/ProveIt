(** The Gödel translation underlying standard modal companions.

    This begins the port of Foundation's
    [Modal/ModalCompanion/Standard/Basic.lean].  The structural results are
    atom-polymorphic, and the proof-theoretic results require only the
    substitution-free S4 capability rather than a concrete Hilbert system. *)

From FoundationModal Require Import
  Syntax Kripke LogicInfrastructure EntailmentExtensions EntailmentS4
  PropositionalFormula PropositionalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint godel_translate {AtomType : Type}
    (p : pformula AtomType) : formula AtomType :=
  match p with
  | PAtom a => Box (Atom a)
  | PFalsum => Bottom
  | PAnd q r => And (godel_translate q) (godel_translate r)
  | POr q r => Or (godel_translate q) (godel_translate r)
  | PImp q r => Box (Imp (godel_translate q) (godel_translate r))
  end.

Lemma godel_translate_rename :
  forall (A B : Type) (f : A -> B) p,
    godel_translate (pformula_substitute (fun a => PAtom (f a)) p) =
    substitute (fun a => Atom (f a)) (godel_translate p).
Proof.
  intros A B f p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; simpl.
  - reflexivity.
  - reflexivity.
  - unfold And, Neg; simpl. now rewrite IHp, IHq.
  - unfold Or, Neg; simpl. now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
Qed.

(** Every translated formula is stable in substitution-free S4. *)
Lemma godel_translate_stable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p : pformula AtomType,
    L (Imp (godel_translate p) (Box (godel_translate p))).
Proof.
  intros AtomType L HS4 p; induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    simpl.
  - exact (has_Four_axiom (s4_Four HS4) (Atom a)).
  - apply (logic_classical_tautology (k_classical (s4_K HS4))).
    intro rho; simpl; tauto.
  - pose proof (s4_K HS4) as HK.
    pose proof (k_classical HK) as Hclass.
    assert (Hpair :
        L (Imp (And (godel_translate p) (godel_translate q))
          (And (Box (godel_translate p)) (Box (godel_translate q))))).
    { apply logic_imp_and_intro; [exact Hclass | |].
      + eapply logic_imp_trans; [exact Hclass | |exact IHp].
        exact (logic_and_elim_left_imp Hclass _ _).
      + eapply logic_imp_trans; [exact Hclass | |exact IHq].
        exact (logic_and_elim_right_imp Hclass _ _). }
    exact (logic_imp_trans Hclass Hpair
      (k_box_iter_and_collect HK 1
        (godel_translate p) (godel_translate q))).
  - pose proof (s4_K HS4) as HK.
    pose proof (k_classical HK) as Hclass.
    assert (Hpointwise :
        L (Imp (Or (godel_translate p) (godel_translate q))
          (Or (Box (godel_translate p)) (Box (godel_translate q))))).
    { eapply (logic_modus_ponens Hclass); [|exact IHq].
      eapply (logic_modus_ponens Hclass); [|exact IHp].
      apply (logic_classical_tautology Hclass).
      intro rho; unfold Or, Neg; simpl; tauto. }
    exact (logic_imp_trans Hclass Hpointwise
      (k_box_iter_or_collect HK 1
        (godel_translate p) (godel_translate q))).
  - exact (has_Four_axiom (s4_Four HS4)
      (Imp (godel_translate p) (godel_translate q))).
Qed.

(** Reusable modal lifting: a stable antecedent turns any consequence into
    a boxed consequence. *)
Lemma s4_stable_consequence :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall a b,
    L (Imp a (Box a)) -> L (Imp a b) -> L (Imp a (Box b)).
Proof.
  intros AtomType L HS4 a b Hstable Hab.
  exact (logic_imp_trans (k_classical (s4_K HS4)) Hstable
    (box_regularity_of_k (s4_K HS4) Hab)).
Qed.

Lemma s4_box_nested_one :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall a b,
    L (Imp a (Box a)) -> L (Imp a b) ->
    L (Box (Imp a (Box b))).
Proof.
  intros AtomType L HS4 a b Hstable Hab.
  apply k_necessitation; [exact (s4_K HS4) |].
  exact (s4_stable_consequence HS4 Hstable Hab).
Qed.

Lemma s4_box_nested_two :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall a b c,
    L (Imp a (Box a)) -> L (Imp b (Box b)) ->
    L (Imp a (Imp b c)) ->
    L (Box (Imp a (Box (Imp b (Box c))))).
Proof.
  intros AtomType L HS4 a b c Hsa Hsb Habc.
  pose proof (s4_K HS4) as HK.
  pose proof (k_classical HK) as Hclass.
  assert (Hab_c : L (Imp (And a b) c)).
  { eapply (logic_modus_ponens Hclass); [|exact Habc].
    apply (logic_classical_tautology Hclass).
    intro rho; unfold And, Neg; simpl; tauto. }
  assert (Hab_stable : L (Imp (And a b) (Box (And a b)))).
  { assert (Hboxes : L (Imp (And a b) (And (Box a) (Box b)))).
    { apply logic_imp_and_intro; [exact Hclass | |].
      - eapply logic_imp_trans; [exact Hclass | |exact Hsa].
        exact (logic_and_elim_left_imp Hclass _ _).
      - eapply logic_imp_trans; [exact Hclass | |exact Hsb].
        exact (logic_and_elim_right_imp Hclass _ _). }
    exact (logic_imp_trans Hclass Hboxes
      (k_box_iter_and_collect HK 1 a b)). }
  pose proof (s4_stable_consequence HS4 Hab_stable Hab_c) as Hab_boxc.
  pose proof (logic_curry Hclass Hab_boxc) as Ha_b_boxc.
  pose proof
    (s4_stable_consequence HS4 Hsa Ha_b_boxc) as Ha_box_b_boxc.
  exact (k_necessitation HK Ha_box_b_boxc).
Qed.

Lemma godel_translated_axiom_K :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (ph_axiom_K p q)).
Proof.
  intros AtomType L HS4 p q; simpl.
  eapply (@s4_box_nested_one AtomType L HS4 _ _).
  - apply godel_translate_stable; exact HS4.
  - apply (logic_classical_tautology (k_classical (s4_K HS4))).
    intro rho; simpl; tauto.
Qed.

Lemma godel_translated_axiom_and1 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (ph_axiom_and1 p q)).
Proof.
  intros AtomType L HS4 p q; simpl.
  apply k_necessitation; [exact (s4_K HS4) |].
  exact (logic_and_elim_left_imp (k_classical (s4_K HS4)) _ _).
Qed.

Lemma godel_translated_axiom_and2 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (ph_axiom_and2 p q)).
Proof.
  intros AtomType L HS4 p q; simpl.
  apply k_necessitation; [exact (s4_K HS4) |].
  exact (logic_and_elim_right_imp (k_classical (s4_K HS4)) _ _).
Qed.

Lemma godel_translated_axiom_and3 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (ph_axiom_and3 p q)).
Proof.
  intros AtomType L HS4 p q; simpl.
  eapply (@s4_box_nested_one AtomType L HS4 _ _).
  - apply godel_translate_stable; exact HS4.
  - apply (logic_classical_tautology (k_classical (s4_K HS4))).
    intro rho; unfold And, Neg; simpl; tauto.
Qed.

Lemma godel_translated_axiom_or1 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (ph_axiom_or1 p q)).
Proof.
  intros AtomType L HS4 p q; simpl.
  apply k_necessitation; [exact (s4_K HS4) |].
  apply (logic_classical_tautology (k_classical (s4_K HS4))).
  intro rho; unfold Or, Neg; simpl; tauto.
Qed.

Lemma godel_translated_axiom_or2 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (ph_axiom_or2 p q)).
Proof.
  intros AtomType L HS4 p q; simpl.
  apply k_necessitation; [exact (s4_K HS4) |].
  apply (logic_classical_tautology (k_classical (s4_K HS4))).
  intro rho; unfold Or, Neg; simpl; tauto.
Qed.

Lemma godel_translated_axiom_S :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q r : pformula AtomType,
    L (godel_translate (ph_axiom_S p q r)).
Proof.
  intros AtomType L HS4 p q r; simpl.
  set (P := godel_translate p); set (Q := godel_translate q);
    set (R := godel_translate r).
  set (a := Box (Imp P (Box (Imp Q R)))).
  set (b := Box (Imp P Q)).
  assert (Hbase : L (Imp a (Imp b (Imp P R)))).
  { pose proof (k_classical (s4_K HS4)) as Hclass.
    eapply (logic_modus_ponens Hclass); [|exact (has_T_axiom (s4_T HS4) (Imp Q R))].
    eapply (logic_modus_ponens Hclass); [|exact (has_T_axiom (s4_T HS4) (Imp P Q))].
    eapply (logic_modus_ponens Hclass); [|exact (has_T_axiom (s4_T HS4) (Imp P (Box (Imp Q R))))].
    apply (logic_classical_tautology Hclass).
    intro rho; simpl; tauto. }
  eapply (@s4_box_nested_two AtomType L HS4 _ _ _); [| |exact Hbase].
  - change (L (Imp (godel_translate (PImp p (PImp q r)))
      (Box (godel_translate (PImp p (PImp q r)))))).
    apply godel_translate_stable; exact HS4.
  - change (L (Imp (godel_translate (PImp p q))
      (Box (godel_translate (PImp p q))))).
    apply godel_translate_stable; exact HS4.
Qed.

Lemma godel_translated_axiom_or3 :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q r : pformula AtomType,
    L (godel_translate (ph_axiom_or3 p q r)).
Proof.
  intros AtomType L HS4 p q r; simpl.
  set (P := godel_translate p); set (Q := godel_translate q);
    set (R := godel_translate r).
  set (a := Box (Imp P R)); set (b := Box (Imp Q R)).
  assert (Hbase : L (Imp a (Imp b (Imp (Or P Q) R)))).
  { pose proof (k_classical (s4_K HS4)) as Hclass.
    eapply (logic_modus_ponens Hclass); [|exact (has_T_axiom (s4_T HS4) (Imp Q R))].
    eapply (logic_modus_ponens Hclass); [|exact (has_T_axiom (s4_T HS4) (Imp P R))].
    apply (logic_classical_tautology Hclass).
    intro rho; unfold Or, Neg; simpl; tauto. }
  eapply (@s4_box_nested_two AtomType L HS4 _ _ _); [| |exact Hbase].
  - change (L (Imp (godel_translate (PImp p r))
      (Box (godel_translate (PImp p r))))).
    apply godel_translate_stable; exact HS4.
  - change (L (Imp (godel_translate (PImp q r))
      (Box (godel_translate (PImp q r))))).
    apply godel_translate_stable; exact HS4.
Qed.

(** The translated implication is boxed.  T therefore yields a shorter
    translated modus-ponens proof than the source's necessitation/K/T chain. *)
Lemma godel_translate_modus_ponens :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p q : pformula AtomType,
    L (godel_translate (PImp p q)) ->
    L (godel_translate p) -> L (godel_translate q).
Proof.
  intros AtomType L HS4 p q Himp Hp; simpl in Himp.
  pose proof (s4_K HS4) as HK.
  pose proof (logic_modus_ponens (k_classical HK)
    (has_T_axiom (s4_T HS4)
      (Imp (godel_translate p) (godel_translate q))) Himp) as Hpq.
  exact (logic_modus_ponens (k_classical HK) Hpq Hp).
Qed.

Lemma godel_translate_efq :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p : pformula AtomType,
    L (godel_translate (ph_axiom_efq p)).
Proof.
  intros AtomType L HS4 p; simpl.
  apply k_necessitation; [exact (s4_K HS4) |].
  apply (logic_classical_tautology (k_classical (s4_K HS4))).
  intro rho; simpl; tauto.
Qed.

Lemma godel_translate_verum :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L ->
    L (godel_translate (@ptop AtomType)).
Proof.
  intros AtomType L HS4; simpl.
  apply k_necessitation; [exact (s4_K HS4) |].
  apply (logic_classical_tautology (k_classical (s4_K HS4))).
  intro rho; simpl; tauto.
Qed.

(** One recursor transports every schema-generated propositional Hilbert
    proof once its optional schemata have translated proofs. *)
Lemma godel_translate_hilbert_proof :
  forall (AtomType : Type) (H : ph_hilbert AtomType)
      (L : modal_logic_set AtomType),
    s4_entailment L ->
    (forall p, ph_hilbert_schema H p -> L (godel_translate p)) ->
    forall p, ph_hilbert_proof H p -> L (godel_translate p).
Proof.
  intros AtomType H L HS4 Hschema p d; induction d.
  - now apply Hschema.
  - exact (godel_translate_modus_ponens HS4 IHd1 IHd2).
  - exact (godel_translate_verum HS4).
  - exact (godel_translated_axiom_S HS4 p q r).
  - exact (godel_translated_axiom_K HS4 p q).
  - exact (godel_translated_axiom_and1 HS4 p q).
  - exact (godel_translated_axiom_and2 HS4 p q).
  - exact (godel_translated_axiom_and3 HS4 p q).
  - exact (godel_translated_axiom_or1 HS4 p q).
  - exact (godel_translated_axiom_or2 HS4 p q).
  - exact (godel_translated_axiom_or3 HS4 p q r).
Qed.

Lemma godel_translate_hilbert_provable :
  forall (AtomType : Type) (H : ph_hilbert AtomType)
      (L : modal_logic_set AtomType),
    s4_entailment L ->
    (forall p, ph_hilbert_schema H p -> L (godel_translate p)) ->
    forall p, ph_hilbert_provable H p -> L (godel_translate p).
Proof.
  intros AtomType H L HS4 Hschema p [d].
  exact (godel_translate_hilbert_proof HS4 Hschema d).
Qed.

Lemma godel_translate_int_provable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    s4_entailment L -> forall p,
    ph_hilbert_provable (ph_hilbert_int AtomType) p ->
    L (godel_translate p).
Proof.
  intros AtomType L HS4 p Hp.
  eapply godel_translate_hilbert_provable; [exact HS4 | |exact Hp].
  intros q Hq; destruct Hq.
  exact (godel_translate_efq HS4 p0).
Qed.

(** Gödel translations are persistent on every transitive modal frame.  No
    hereditary hypothesis on the valuation is needed because atoms are boxed. *)
Lemma godel_translate_persistent :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F),
    (forall x y z, Rel F x y -> Rel F y z -> Rel F x z) ->
    forall (p : pformula AtomType) x y,
    satisfies F V x (godel_translate p) -> Rel F x y ->
    satisfies F V y (godel_translate p).
Proof.
  intros AtomType F V Htrans p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros x y Hsat Rxy; simpl in *.
  - intros z Ryz. exact (Hsat z (Htrans x y z Rxy Ryz)).
  - exact Hsat.
  - apply satisfies_and in Hsat; apply satisfies_and; split.
    + exact (IHp x y (proj1 Hsat) Rxy).
    + exact (IHq x y (proj2 Hsat) Rxy).
  - apply satisfies_or in Hsat; apply satisfies_or.
    destruct Hsat as [Hp | Hq].
    + left. exact (IHp x y Hp Rxy).
    + right. exact (IHq x y Hq Rxy).
  - intros z Ryz.
    exact (Hsat z (Htrans x y z Rxy Ryz)).
Qed.
