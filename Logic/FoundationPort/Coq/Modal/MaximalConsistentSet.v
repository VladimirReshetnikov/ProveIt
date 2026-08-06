(** Zorn-style Lindenbaum extensions over arbitrary modal atom types.

    The modal project constructs canonical theories by enumerating formulas
    over [nat].  Foundation's abstract maximal-consistency theorem is more
    general: compact contextual derivability and Zorn's lemma suffice, so no
    atom enumeration or equality decision is required.  This module proves
    that theorem over the minimal [classical_logic] interface and packages
    the result as the atom-polymorphic algebraic core consumed by
    [MaximalTheoryLaws]. *)

From Stdlib Require Import Logic.Classical_Prop Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality Logic.ProofIrrelevance.
From Foundation.Vorspiel.Set Require Import Basic.
From Foundation.Vorspiel.Order Require Import Zorn.
From FoundationModal Require Import
  Syntax LogicInfrastructure ComplementEntailment MaximalTheoryLaws.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition abstract_formula_theory (AtomType : Type) : Type :=
  formula AtomType -> Prop.

Definition abstract_theory_included {AtomType}
    (Gamma Delta : abstract_formula_theory AtomType) : Prop :=
  forall p, Gamma p -> Delta p.

Definition abstract_theory_insert {AtomType}
    (Gamma : abstract_formula_theory AtomType) (p : formula AtomType)
    : abstract_formula_theory AtomType :=
  fun q => q = p \/ Gamma q.

Inductive abstract_context_derives {AtomType}
    (L : modal_logic_set AtomType)
    (Gamma : abstract_formula_theory AtomType) : formula AtomType -> Prop :=
| ACD_assumption : forall p, Gamma p -> abstract_context_derives L Gamma p
| ACD_theorem : forall p, L p -> abstract_context_derives L Gamma p
| ACD_mp : forall p q,
    abstract_context_derives L Gamma (Imp p q) ->
    abstract_context_derives L Gamma p ->
    abstract_context_derives L Gamma q.

Arguments ACD_assumption {AtomType L Gamma p} _.
Arguments ACD_theorem {AtomType L Gamma p} _.
Arguments ACD_mp {AtomType L Gamma p q} _ _.

Definition abstract_context_consistent {AtomType}
    (L : modal_logic_set AtomType)
    (Gamma : abstract_formula_theory AtomType) : Prop :=
  ~ abstract_context_derives L Gamma Bottom.

Lemma abstract_context_derives_weaken :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma Delta p,
    abstract_theory_included Gamma Delta ->
    abstract_context_derives L Gamma p ->
    abstract_context_derives L Delta p.
Proof.
  intros AtomType L Gamma Delta p Hinc Hp; induction Hp.
  - apply ACD_assumption. now apply Hinc.
  - now apply ACD_theorem.
  - eapply ACD_mp; eauto.
Qed.

Lemma abstract_context_derives_imply_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p q,
    abstract_context_derives L Gamma q ->
    abstract_context_derives L Gamma (Imp p q).
Proof.
  intros AtomType L Hclass Gamma p q Hq.
  eapply ACD_mp; [|exact Hq]. apply ACD_theorem.
  apply (logic_classical_tautology Hclass).
  intro rho. simpl. tauto.
Qed.

Lemma abstract_context_derives_under_mp :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p q r,
    abstract_context_derives L Gamma (Imp p (Imp q r)) ->
    abstract_context_derives L Gamma (Imp p q) ->
    abstract_context_derives L Gamma (Imp p r).
Proof.
  intros AtomType L Hclass Gamma p q r Hqr Hq.
  eapply ACD_mp; [|exact Hq]. eapply ACD_mp; [|exact Hqr].
  apply ACD_theorem, (logic_classical_tautology Hclass).
  intro rho. simpl. tauto.
Qed.

Theorem abstract_context_deduction :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p q,
    abstract_context_derives L (abstract_theory_insert Gamma p) q ->
    abstract_context_derives L Gamma (Imp p q).
Proof.
  intros AtomType L Hclass Gamma p q Hq.
  induction Hq as [r Hr | r Hr | r s Hrs IHrs Hr IHr].
  - destruct Hr as [-> | Hr].
    + apply ACD_theorem, (logic_classical_tautology Hclass).
      intro rho. simpl. tauto.
    + apply abstract_context_derives_imply_intro; [exact Hclass |].
      now apply ACD_assumption.
  - apply abstract_context_derives_imply_intro; [exact Hclass |].
    now apply ACD_theorem.
  - exact (abstract_context_derives_under_mp Hclass IHrs IHr).
Qed.

Lemma abstract_context_undeduction :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma p q,
    abstract_context_derives L Gamma (Imp p q) ->
    abstract_context_derives L (abstract_theory_insert Gamma p) q.
Proof.
  intros AtomType L Gamma p q Himp. eapply ACD_mp.
  - eapply abstract_context_derives_weaken; [|exact Himp].
    intros r Hr. now right.
  - apply ACD_assumption. now left.
Qed.

Lemma abstract_context_dne :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_derives L Gamma (Neg (Neg p)) ->
    abstract_context_derives L Gamma p.
Proof.
  intros AtomType L Hclass Gamma p Hnn. eapply ACD_mp; [|exact Hnn].
  apply ACD_theorem. exact (classical_logic_double_neg_elim Hclass p).
Qed.

Theorem abstract_insert_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_consistent L (abstract_theory_insert Gamma p) <->
    ~ abstract_context_derives L Gamma (Neg p).
Proof.
  intros AtomType L Hclass Gamma p; split.
  - intros Hconsistent Hneg. apply Hconsistent.
    now apply abstract_context_undeduction.
  - intros Hnot Hbottom. apply Hnot.
    now apply abstract_context_deduction.
Qed.

Theorem abstract_insert_neg_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_consistent L
      (abstract_theory_insert Gamma (Neg p)) <->
    ~ abstract_context_derives L Gamma p.
Proof.
  intros AtomType L Hclass Gamma p; split.
  - intros Hconsistent Hp. apply Hconsistent. eapply ACD_mp.
    + apply ACD_assumption. now left.
    + eapply abstract_context_derives_weaken; [|exact Hp].
      intros r Hr. now right.
  - intros Hnot Hbottom. apply Hnot, (abstract_context_dne Hclass).
    now apply abstract_context_deduction.
Qed.

Lemma abstract_either_insert_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma,
    abstract_context_consistent L Gamma -> forall p,
    abstract_context_consistent L (abstract_theory_insert Gamma p) \/
    abstract_context_consistent L (abstract_theory_insert Gamma (Neg p)).
Proof.
  intros AtomType L Hclass Gamma Hconsistent p.
  destruct (classic (abstract_context_consistent L
    (abstract_theory_insert Gamma p))) as [Hp | Hnp]; [now left |].
  destruct (classic (abstract_context_consistent L
    (abstract_theory_insert Gamma (Neg p)))) as [Hneg | Hnneg];
    [now right |].
  exfalso. apply Hconsistent.
  assert (Hderive_neg : abstract_context_derives L Gamma (Neg p)).
  { apply NNPP. intro Hnot. apply Hnp.
    now apply (proj2 (abstract_insert_consistent_iff Hclass Gamma p)). }
  assert (Hderive_p : abstract_context_derives L Gamma p).
  { apply NNPP. intro Hnot. apply Hnneg.
    now apply (proj2 (abstract_insert_neg_consistent_iff Hclass Gamma p)). }
  exact (ACD_mp Hderive_neg Hderive_p).
Qed.

Section ZornLindenbaum.

  Context {AtomType : Type}.
  Variable L : modal_logic_set AtomType.
  Variable Hclass : classical_logic L.
  Variable Gamma : abstract_formula_theory AtomType.
  Variable Hgamma : abstract_context_consistent L Gamma.

  Definition abstract_consistent_extension : Type :=
    { Delta : abstract_formula_theory AtomType |
      abstract_context_consistent L Delta /\
      abstract_theory_included Gamma Delta }.

  Definition abstract_extension_carrier
      (E : abstract_consistent_extension) : abstract_formula_theory AtomType :=
    proj1_sig E.

  Definition abstract_extension_included
      (E D : abstract_consistent_extension) : Prop :=
    abstract_theory_included (abstract_extension_carrier E)
      (abstract_extension_carrier D).

  Lemma abstract_extension_included_order :
    partial_order_laws abstract_extension_included.
  Proof.
    constructor.
    - intros E p Hp. exact Hp.
    - intros E D K HED HDK p Hp. now apply HDK, HED.
    - intros [E HE] [D HD] HED HDE. cbn in *.
      assert (E = D).
      { apply functional_extensionality. intro p.
        apply propositional_extensionality. split; [apply HED | apply HDE]. }
      subst D. f_equal. apply proof_irrelevance.
  Qed.

  Definition abstract_base_extension : abstract_consistent_extension :=
    exist _ Gamma (conj Hgamma (fun p Hp => Hp)).

  Definition abstract_chain_with_base
      (C : pred_set abstract_consistent_extension)
      (E : abstract_consistent_extension) : Prop :=
    E = abstract_base_extension \/ C E.

  Lemma abstract_chain_with_base_ordered :
    forall C, order_chain abstract_extension_included C ->
      order_chain abstract_extension_included (abstract_chain_with_base C).
  Proof.
    intros C HC E D [-> | HE] [-> | HD].
    - left. intros p Hp. exact Hp.
    - left. exact (proj2 (proj2_sig D)).
    - right. exact (proj2 (proj2_sig E)).
    - exact (HC E D HE HD).
  Qed.

  Definition abstract_chain_union
      (C : pred_set abstract_consistent_extension)
      : abstract_formula_theory AtomType :=
    fun p => exists E,
      abstract_chain_with_base C E /\ abstract_extension_carrier E p.

  Lemma abstract_chain_union_derivation_stage :
    forall C, order_chain abstract_extension_included C ->
    forall p, abstract_context_derives L (abstract_chain_union C) p ->
    exists E, abstract_chain_with_base C E /\
      abstract_context_derives L (abstract_extension_carrier E) p.
  Proof.
    intros C HC p Hp. induction Hp as
      [p [E [HE Hp]] | p Hp | p q Hpq IHpq Hp IHp].
    - exists E. split; [exact HE | now apply ACD_assumption].
    - exists abstract_base_extension. split; [now left |].
      now apply ACD_theorem.
    - destruct IHpq as [E [HE HpqE]]. destruct IHp as [D [HD HpD]].
      destruct (abstract_chain_with_base_ordered HC HE HD)
        as [HED | HDE].
      + exists D. split; [exact HD |]. eapply ACD_mp.
        * eapply abstract_context_derives_weaken; [exact HED | exact HpqE].
        * exact HpD.
      + exists E. split; [exact HE |]. eapply ACD_mp.
        * exact HpqE.
        * eapply abstract_context_derives_weaken; [exact HDE | exact HpD].
  Qed.

  Lemma abstract_chain_union_consistent :
    forall C, order_chain abstract_extension_included C ->
      abstract_context_consistent L (abstract_chain_union C).
  Proof.
    intros C HC Hbottom.
    destruct (abstract_chain_union_derivation_stage HC Hbottom)
      as [E [_ HEbottom]].
    exact (proj1 (proj2_sig E) HEbottom).
  Qed.

  Definition abstract_chain_union_extension C
      (HC : order_chain abstract_extension_included C)
      : abstract_consistent_extension :=
    exist _ (abstract_chain_union C)
      (conj (abstract_chain_union_consistent HC)
        (fun p Hp => ex_intro _ abstract_base_extension
          (conj (or_introl eq_refl) Hp))).

  Lemma abstract_extension_chain_upper_bound :
    forall C, order_chain abstract_extension_included C ->
      exists E, order_upper_bound abstract_extension_included C E.
  Proof.
    intros C HC. exists (abstract_chain_union_extension HC).
    intros E HE p Hp. exists E. split; [now right | exact Hp].
  Qed.

  Lemma abstract_maximal_extension_complete :
    forall X : abstract_consistent_extension,
      order_maximal abstract_extension_included X ->
      forall p,
        abstract_extension_carrier X p \/
        abstract_extension_carrier X (Neg p).
  Proof.
    intros X Hmax p.
    destruct (abstract_either_insert_consistent Hclass
      (proj1 (proj2_sig X)) p) as [Hp | Hneg].
    - set (Y := exist (fun Delta =>
        abstract_context_consistent L Delta /\
        abstract_theory_included Gamma Delta)
        (abstract_theory_insert (abstract_extension_carrier X) p)
        (conj Hp (fun q Hq => or_intror
          ((proj2 (proj2_sig X)) q Hq)))).
      assert (HXY : abstract_extension_included X Y).
      { intros q Hq. now right. }
      pose proof (Hmax Y HXY) as Heq. left.
      change (abstract_extension_carrier X p).
      rewrite Heq. simpl. now left.
    - set (Y := exist (fun Delta =>
        abstract_context_consistent L Delta /\
        abstract_theory_included Gamma Delta)
        (abstract_theory_insert (abstract_extension_carrier X) (Neg p))
        (conj Hneg (fun q Hq => or_intror
          ((proj2 (proj2_sig X)) q Hq)))).
      assert (HXY : abstract_extension_included X Y).
      { intros q Hq. now right. }
      pose proof (Hmax Y HXY) as Heq. right.
      change (abstract_extension_carrier X (Neg p)).
      rewrite Heq. simpl. now left.
  Qed.

  Lemma abstract_maximal_extension_derivable_mem :
    forall (X : abstract_consistent_extension)
      (Hmax : order_maximal abstract_extension_included X),
    forall p,
      abstract_context_derives L (abstract_extension_carrier X) p ->
      abstract_extension_carrier X p.
  Proof.
    intros X Hmax p Hp.
    destruct (abstract_maximal_extension_complete Hmax p)
      as [Hmem | Hneg]; [exact Hmem |].
    exfalso. apply (proj1 (proj2_sig X)).
    exact (ACD_mp (ACD_assumption Hneg) Hp).
  Qed.

  Definition abstract_maximal_extension_classical
      (X : abstract_consistent_extension)
      (Hmax : order_maximal abstract_extension_included X)
      : classical_logic (abstract_extension_carrier X).
  Proof.
    constructor.
    - intros p Htaut. apply (abstract_maximal_extension_derivable_mem Hmax).
      apply ACD_theorem.
      exact (logic_classical_tautology Hclass Htaut).
    - intros p q Himp Hp.
      apply (abstract_maximal_extension_derivable_mem Hmax).
      exact (ACD_mp (ACD_assumption Himp) (ACD_assumption Hp)).
  Defined.

  Definition abstract_maximal_extension_as_generic
      (X : abstract_consistent_extension)
      (Hmax : order_maximal abstract_extension_included X)
    : generic_maximal_classical_theory AtomType :=
    {| gmct_mem := abstract_extension_carrier X;
       gmct_classical := abstract_maximal_extension_classical Hmax;
       gmct_bottom_absent_field := fun Hbottom =>
         proj1 (proj2_sig X) (ACD_assumption Hbottom);
       gmct_complete := abstract_maximal_extension_complete Hmax |}.

  (** This theorem is the arbitrary-atom Lindenbaum extension.  Its final
      clause is the original strict-maximality conclusion, stated
      extensionally for predicate theories. *)
  Theorem abstract_lindenbaum_extension :
    exists M : generic_maximal_classical_theory AtomType,
      abstract_theory_included Gamma (gmct_mem M) /\
      abstract_context_consistent L (gmct_mem M) /\
      (forall p,
        abstract_context_derives L (gmct_mem M) p <-> gmct_mem M p) /\
      forall Delta,
        abstract_context_consistent L Delta ->
        abstract_theory_included (gmct_mem M) Delta ->
        forall p, Delta p <-> gmct_mem M p.
  Proof.
    destruct (zorn_maximal_element abstract_extension_included_order
      abstract_extension_chain_upper_bound) as [X Hmax].
    exists (abstract_maximal_extension_as_generic Hmax). split.
    - exact (proj2 (proj2_sig X)).
    - split.
      + exact (proj1 (proj2_sig X)).
      + split.
        * intro phi; split.
          -- apply abstract_maximal_extension_derivable_mem. exact Hmax.
          -- now apply ACD_assumption.
        * intros Delta Hconsistent Hinc phi.
          set (Y := exist (fun D =>
            abstract_context_consistent L D /\
            abstract_theory_included Gamma D) Delta
            (conj Hconsistent (fun q Hq => Hinc q
              ((proj2 (proj2_sig X)) q Hq)))).
          assert (HXY : abstract_extension_included X Y) by exact Hinc.
          pose proof (Hmax Y HXY) as Heq. split; intro Hp.
          -- change (abstract_extension_carrier X phi).
             rewrite Heq. exact Hp.
          -- change (abstract_extension_carrier X phi) in Hp.
             rewrite Heq in Hp. exact Hp.
  Qed.

End ZornLindenbaum.

Arguments abstract_lindenbaum_extension
  {AtomType L} Hclass Gamma Hgamma.
