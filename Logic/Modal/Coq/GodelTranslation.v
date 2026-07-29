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
