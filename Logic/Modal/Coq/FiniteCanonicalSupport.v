(**
  Shared finite mini-canonical-model support.

  The finite GL and Grz constructions in Foundation repeatedly use the
  preimage of a finite context under [Box], its pointwise boxed image, and
  the boxed formulas of a complement-closed maximal context which are
  relevant to a fixed finite closure.  This module gives those operations
  executable list presentations and proves their extensional interfaces.

  The last two sections collect only proof-theoretic and closure facts used
  by both mini-canonical arguments: contextual weakening, necessitation and
  substitution for finite contexts; extensional equality of finite maximal
  contexts from their decisions on the base closure; and the small Grz
  enrichment of the ordinary subformula list.
*)

From Stdlib Require Import Lists.List Bool.Bool.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Complement HilbertK NormalHilbert CanonicalExtensions
  FiniteMaximalContext.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Finite prebox and box images *)

Fixpoint formula_list_unbox {AtomType : Type}
    (Gamma : list (formula AtomType)) : list (formula AtomType) :=
  match Gamma with
  | [] => []
  | Box p :: rest => p :: formula_list_unbox rest
  | _ :: rest => formula_list_unbox rest
  end.

Definition formula_list_box {AtomType : Type}
    (Gamma : list (formula AtomType)) : list (formula AtomType) :=
  map Box Gamma.

Lemma formula_list_unbox_spec :
  forall (AtomType : Type) (Gamma : list (formula AtomType)) p,
    In p (formula_list_unbox Gamma) <-> In (Box p) Gamma.
Proof.
  intros AtomType Gamma; induction Gamma as [|q Gamma IH]; intro p.
  - simpl. tauto.
  - destruct q as [a | | q r | q].
    + simpl. rewrite IH. split.
      * intro H. now right.
      * intros [H | H]; [discriminate | exact H].
    + simpl. rewrite IH. split.
      * intro H. now right.
      * intros [H | H]; [discriminate | exact H].
    + simpl. rewrite IH. split.
      * intro H. now right.
      * intros [H | H]; [discriminate | exact H].
    + simpl. rewrite IH. split.
      * intros [H | H].
        -- subst q. now left.
        -- now right.
      * intros [H | H].
        -- inversion H. subst q. now left.
        -- now right.
Qed.

Lemma formula_list_box_spec :
  forall (AtomType : Type) (Gamma : list (formula AtomType)) p,
    In (Box p) (formula_list_box Gamma) <-> In p Gamma.
Proof.
  intros AtomType Gamma p. unfold formula_list_box.
  rewrite in_map_iff. split.
  - intros [q [Hq Hmem]]. inversion Hq. now subst q.
  - intro Hp. exists p. now split.
Qed.

Lemma formula_list_box_member :
  forall (AtomType : Type) (Gamma : list (formula AtomType)) p,
    In p Gamma -> In (Box p) (formula_list_box Gamma).
Proof.
  intros AtomType Gamma p Hp.
  now apply (proj2 (formula_list_box_spec Gamma p)).
Qed.

Lemma formula_list_unbox_box :
  forall (AtomType : Type) (Gamma : list (formula AtomType)),
    formula_list_unbox (formula_list_box Gamma) = Gamma.
Proof.
  intros AtomType Gamma; induction Gamma as [|p Gamma IH]; simpl; auto.
  now rewrite IH.
Qed.

Lemma finite_theory_unbox_iff :
  forall Gamma p,
    finite_theory (formula_list_unbox Gamma) p <->
    finite_theory Gamma (Box p).
Proof.
  intros Gamma p. unfold finite_theory.
  apply formula_list_unbox_spec.
Qed.

Lemma finite_theory_box_iff :
  forall Gamma p,
    finite_theory (formula_list_box Gamma) (Box p) <->
    finite_theory Gamma p.
Proof.
  intros Gamma p. unfold finite_theory.
  apply formula_list_box_spec.
Qed.

Lemma finite_theory_boxed_extensional :
  forall Gamma p,
    finite_theory (formula_list_box Gamma) p <->
    boxed_theory (finite_theory Gamma) p.
Proof.
  intros Gamma p. unfold finite_theory, formula_list_box, boxed_theory.
  rewrite in_map_iff. split.
  - intros [q [Hqeq Hq]]. exists q. split; [exact Hq |].
    now symmetry.
  - intros [q [Hq Hqeq]]. exists q. split; [|exact Hq].
    now symmetry.
Qed.

(** * Context lifting for finite lists *)

Lemma normal_derives_finite_weaken :
  forall Ax Gamma Delta p,
    list_subset Gamma Delta ->
    normal_derives Ax (finite_theory Gamma) p ->
    normal_derives Ax (finite_theory Delta) p.
Proof.
  intros Ax Gamma Delta p Hsub Hp.
  eapply normal_derives_weaken; [|exact Hp].
  intros q Hq. now apply Hsub.
Qed.

(** Contextual cut, or simultaneous replacement of assumptions.  Unlike
    mere weakening, each source assumption may be replaced by an arbitrary
    derivation in the target context. *)
Lemma normal_derives_context_cut :
  forall Ax (Gamma Delta : theory nat) p,
    (forall q, Gamma q -> normal_derives Ax Delta q) ->
    normal_derives Ax Gamma p ->
    normal_derives Ax Delta p.
Proof.
  intros Ax Gamma Delta p Hreplace Hp. induction Hp.
  - now apply Hreplace.
  - now apply ND_theorem.
  - eapply ND_mp; eauto.
Qed.

Lemma normal_derives_finite_context_cut :
  forall Ax Gamma Delta p,
    (forall q, In q Gamma ->
      normal_derives Ax (finite_theory Delta) q) ->
    normal_derives Ax (finite_theory Gamma) p ->
    normal_derives Ax (finite_theory Delta) p.
Proof.
  intros Ax Gamma Delta p Hreplace Hp.
  eapply normal_derives_context_cut; [|exact Hp].
  intros q Hq. now apply Hreplace.
Qed.

Lemma normal_derives_finite_box :
  forall Ax Gamma p,
    normal_derives Ax (finite_theory Gamma) p ->
    normal_derives Ax (finite_theory (formula_list_box Gamma)) (Box p).
Proof.
  intros Ax Gamma p Hp.
  eapply normal_derives_weaken.
  - intros q Hq.
    apply (proj2 (finite_theory_boxed_extensional Gamma q)). exact Hq.
  - now apply normal_derives_boxed.
Qed.

Lemma normal_derives_finite_box_into :
  forall Ax Gamma Delta p,
    list_subset (formula_list_box Gamma) Delta ->
    normal_derives Ax (finite_theory Gamma) p ->
    normal_derives Ax (finite_theory Delta) (Box p).
Proof.
  intros Ax Gamma Delta p Hsub Hp.
  eapply normal_derives_finite_weaken; [exact Hsub |].
  now apply normal_derives_finite_box.
Qed.

Lemma normal_derives_finite_unbox_to_box :
  forall Ax Gamma p,
    normal_derives Ax (finite_theory (formula_list_unbox Gamma)) p ->
    normal_derives Ax (finite_theory Gamma) (Box p).
Proof.
  intros Ax Gamma p Hp. apply normal_derives_box_from_unboxed.
  eapply normal_derives_weaken; [|exact Hp].
  intros q Hq. now apply (proj1 (finite_theory_unbox_iff Gamma q)).
Qed.

Definition substituted_theory (sigma : nat -> formula nat)
    (Gamma : theory nat) : theory nat :=
  fun q => exists p, Gamma p /\ q = substitute sigma p.

Lemma normal_derives_substitute_context :
  forall Ax,
    schema_substitution_closed Ax ->
    forall (sigma : nat -> formula nat) Gamma p,
      normal_derives Ax Gamma p ->
      normal_derives Ax (substituted_theory sigma Gamma)
        (substitute sigma p).
Proof.
  intros Ax Hclosed sigma Gamma p Hp. induction Hp.
  - apply ND_assumption. exists p. now split.
  - apply ND_theorem. now apply normal_proves_substitute.
  - simpl. eapply ND_mp; eauto.
Qed.

Lemma normal_derives_finite_substitute :
  forall Ax,
    schema_substitution_closed Ax ->
    forall (sigma : nat -> formula nat) Gamma p,
      normal_derives Ax (finite_theory Gamma) p ->
      normal_derives Ax
        (finite_theory (map (substitute sigma) Gamma))
        (substitute sigma p).
Proof.
  intros Ax Hclosed sigma Gamma p Hp.
  pose proof (@normal_derives_substitute_context Ax Hclosed sigma
    (finite_theory Gamma) p Hp) as Hsubstitute.
  refine (@normal_derives_weaken Ax
    (substituted_theory sigma (finite_theory Gamma))
    (finite_theory (map (substitute sigma) Gamma))
    (substitute sigma p) _ Hsubstitute).
  intros q Hq. unfold substituted_theory in Hq.
  destruct Hq as [r [Hr ->]]. unfold finite_theory in *.
  now apply in_map.
Qed.

(** * Closure predicates needed by the finite frames *)

Definition formula_context_antecedent_closed {AtomType : Type}
    (Psi : list (formula AtomType)) : Prop :=
  forall p q, In (Imp p q) Psi -> In p Psi.

Definition formula_context_implication_closed {AtomType : Type}
    (Psi : list (formula AtomType)) : Prop :=
  forall p q, In (Imp p q) Psi -> In p Psi /\ In q Psi.

Definition formula_context_box_body_closed {AtomType : Type}
    (Psi : list (formula AtomType)) : Prop :=
  forall p, In (Box p) Psi -> In p Psi.

Lemma subformulas_implication_closed :
  forall (AtomType : Type) (target : formula AtomType),
    formula_context_implication_closed (subformulas target).
Proof.
  intros AtomType target p q Himp. split.
  - eapply subformulas_trans; [exact Himp |].
    apply subformulas_imp_left. apply subformulas_self.
  - eapply subformulas_trans; [exact Himp |].
    apply subformulas_imp_right. apply subformulas_self.
Qed.

Lemma subformulas_antecedent_closed :
  forall (AtomType : Type) (target : formula AtomType),
    formula_context_antecedent_closed (subformulas target).
Proof.
  intros AtomType target p q Himp.
  exact (proj1
    (@subformulas_implication_closed AtomType target p q Himp)).
Qed.

Lemma subformulas_box_body_closed :
  forall (AtomType : Type) (target : formula AtomType),
    formula_context_box_body_closed (subformulas target).
Proof.
  intros AtomType target p Hbox.
  eapply subformulas_trans; [exact Hbox |].
  apply subformulas_box. apply subformulas_self.
Qed.

(** * Relevant boxed members of a finite maximal context *)

Definition fmc_relevant_unboxed Ax Psi
    (X : finite_maximal_context Ax Psi) : list (formula nat) :=
  filter (fun p => fmc_selector X (Box p)) (formula_list_unbox Psi).

Definition fmc_relevant_boxed Ax Psi
    (X : finite_maximal_context Ax Psi) : list (formula nat) :=
  formula_list_box (fmc_relevant_unboxed X).

Lemma fmc_relevant_unboxed_spec :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p (fmc_relevant_unboxed X) <->
    In (Box p) Psi /\ fmc_mem X (Box p).
Proof.
  intros Ax Psi X p. unfold fmc_relevant_unboxed.
  rewrite filter_In, formula_list_unbox_spec. unfold fmc_selector.
  destruct (fmc_mem_dec X (Box p)) as [Hmem | Hnot]; simpl.
  - tauto.
  - split.
    + intros [_ Hfalse]. discriminate.
    + intros [_ Hmem]. contradiction.
Qed.

Lemma fmc_relevant_boxed_spec :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In (Box p) (fmc_relevant_boxed X) <->
    In (Box p) Psi /\ fmc_mem X (Box p).
Proof.
  intros Ax Psi X p. unfold fmc_relevant_boxed.
  rewrite formula_list_box_spec. apply fmc_relevant_unboxed_spec.
Qed.

Lemma fmc_mem_in_complementary :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    fmc_mem X p -> In p (complementary Psi).
Proof.
  intros Ax Psi X p Hp.
  exact (@predicate_closed_subset (fmc_mem X) Psi
    (@fmc_closed Ax Psi X) p Hp).
Qed.

Lemma fmc_mem_box_in_base :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    formula_context_antecedent_closed Psi ->
    fmc_mem X (Box p) -> In (Box p) Psi.
Proof.
  intros Ax Psi X p Hclosed Hbox.
  eapply complementary_mem_box; [exact Hclosed |].
  exact (@fmc_mem_in_complementary Ax Psi X (Box p) Hbox).
Qed.

Lemma fmc_relevant_unboxed_spec_closed :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    formula_context_antecedent_closed Psi ->
    (In p (fmc_relevant_unboxed X) <-> fmc_mem X (Box p)).
Proof.
  intros Ax Psi X p Hclosed. rewrite fmc_relevant_unboxed_spec.
  split.
  - tauto.
  - intro Hbox. split; [|exact Hbox].
    exact (@fmc_mem_box_in_base Ax Psi X p Hclosed Hbox).
Qed.

Lemma fmc_relevant_boxed_spec_closed :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    formula_context_antecedent_closed Psi ->
    (In (Box p) (fmc_relevant_boxed X) <-> fmc_mem X (Box p)).
Proof.
  intros Ax Psi X p Hclosed. rewrite fmc_relevant_boxed_spec.
  split.
  - tauto.
  - intro Hbox. split; [|exact Hbox].
    exact (@fmc_mem_box_in_base Ax Psi X p Hclosed Hbox).
Qed.

Lemma fmc_relevant_unboxed_subset_base :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    formula_context_box_body_closed Psi ->
    list_subset (fmc_relevant_unboxed X) Psi.
Proof.
  intros Ax Psi X Hclosed p Hp.
  apply (proj1 (fmc_relevant_unboxed_spec X p)) in Hp.
  now apply Hclosed.
Qed.

Lemma fmc_relevant_unboxed_subset_complementary :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    formula_context_box_body_closed Psi ->
    list_subset (fmc_relevant_unboxed X) (complementary Psi).
Proof.
  intros Ax Psi X Hclosed p Hp. apply complementary_mem.
  now apply (@fmc_relevant_unboxed_subset_base Ax Psi X Hclosed p).
Qed.

Lemma fmc_relevant_boxed_subset_complementary :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    list_subset (fmc_relevant_boxed X) (complementary Psi).
Proof.
  intros Ax Psi X q Hq. unfold fmc_relevant_boxed in Hq.
  apply in_map_iff in Hq. destruct Hq as [p [Heq Hp]]. subst q.
  apply (@fmc_mem_in_complementary Ax Psi X (Box p)).
  apply (proj1 (fmc_relevant_unboxed_spec X p)) in Hp. tauto.
Qed.

Lemma fmc_mem_box_in_subformulas :
  forall Ax target
    (X : finite_maximal_context Ax (subformulas target)) p,
    fmc_mem X (Box p) -> In (Box p) (subformulas target).
Proof.
  intros Ax target X p Hbox. eapply fmc_mem_box_in_base; [|exact Hbox].
  apply subformulas_antecedent_closed.
Qed.

(** Agreement on the base closure determines a finite maximal context.
    Formulae outside the complementary closure occur in neither carrier;
    membership of a complement inside the closure is determined by the
    decision on its base formula. *)
Lemma fmc_equality_on_base :
  forall Ax Psi (X Y : finite_maximal_context Ax Psi),
    X = Y <->
    forall p, In p Psi -> (fmc_mem X p <-> fmc_mem Y p).
Proof.
  intros Ax Psi X Y; split.
  - intros -> p Hp. tauto.
  - intro Hbase. apply (proj2 (@fmc_equality_def Ax Psi X Y)). intro p.
    destruct (in_dec formula_nat_eq_dec p (complementary Psi)) as [Hp | Hp].
    + destruct (complementary_member_cases Hp)
        as [Hdirect | [q [Hq Hcomp]]].
      * now apply Hbase.
      * subst p.
        rewrite <- (@fmc_not_mem_iff_mem_complement Ax Psi X q Hq).
        rewrite <- (@fmc_not_mem_iff_mem_complement Ax Psi Y q Hq).
        now rewrite (Hbase q Hq).
    + split; intro Hmem; exfalso; apply Hp.
      * exact (@fmc_mem_in_complementary Ax Psi X p Hmem).
      * exact (@fmc_mem_in_complementary Ax Psi Y p Hmem).
Qed.

(** * The finite Grz enrichment *)

Definition grz_enrichment {AtomType : Type}
    (Psi : list (formula AtomType)) : list (formula AtomType) :=
  Psi ++
    map (fun p => Box (Imp p (Box p))) (formula_list_unbox Psi).

Lemma grz_enrichment_base :
  forall (AtomType : Type) (Psi : list (formula AtomType)) p,
    In p Psi -> In p (grz_enrichment Psi).
Proof.
  intros AtomType Psi p Hp. unfold grz_enrichment.
  apply in_or_app. now left.
Qed.

Lemma grz_enrichment_generated :
  forall (AtomType : Type) (Psi : list (formula AtomType)) p,
    In (Box p) Psi ->
    In (Box (Imp p (Box p))) (grz_enrichment Psi).
Proof.
  intros AtomType Psi p Hp. unfold grz_enrichment.
  apply in_or_app. right. apply in_map_iff. exists p. split.
  - reflexivity.
  - now apply (proj2 (formula_list_unbox_spec Psi p)).
Qed.

Lemma grz_enrichment_member_cases :
  forall (AtomType : Type) (Psi : list (formula AtomType)) p,
    In p (grz_enrichment Psi) ->
    In p Psi \/
    exists q, In (Box q) Psi /\ p = Box (Imp q (Box q)).
Proof.
  intros AtomType Psi p Hp. unfold grz_enrichment in Hp.
  apply in_app_iff in Hp. destruct Hp as [Hp | Hp]; [now left |].
  right. apply in_map_iff in Hp. destruct Hp as [q [Hq Hmem]].
  exists q. split.
  - now apply (proj1 (formula_list_unbox_spec Psi q)).
  - now symmetry.
Qed.

Lemma grz_enrichment_implication_closed :
  forall (AtomType : Type) (Psi : list (formula AtomType)),
    formula_context_implication_closed Psi ->
    formula_context_implication_closed (grz_enrichment Psi).
Proof.
  intros AtomType Psi Hclosed p q Himp.
  destruct (grz_enrichment_member_cases Himp)
    as [Hbase | [r [Hr Heq]]].
  - destruct (Hclosed p q Hbase) as [Hp Hq]. split;
      now apply grz_enrichment_base.
  - discriminate Heq.
Qed.

Lemma grz_enrichment_antecedent_closed :
  forall (AtomType : Type) (Psi : list (formula AtomType)),
    formula_context_implication_closed Psi ->
    formula_context_antecedent_closed (grz_enrichment Psi).
Proof.
  intros AtomType Psi Hclosed p q Himp.
  exact (proj1 (@grz_enrichment_implication_closed
    AtomType Psi Hclosed p q Himp)).
Qed.

Definition grz_subformulas {AtomType : Type} (target : formula AtomType)
    : list (formula AtomType) :=
  grz_enrichment (subformulas target).

Lemma grz_subformulas_base :
  forall (AtomType : Type) (target p : formula AtomType),
    In p (subformulas target) -> In p (grz_subformulas target).
Proof. intros; now apply grz_enrichment_base. Qed.

Lemma grz_subformulas_self :
  forall (AtomType : Type) (target : formula AtomType),
    In target (grz_subformulas target).
Proof. intros; apply grz_subformulas_base, subformulas_self. Qed.

Lemma grz_subformulas_generated :
  forall (AtomType : Type) (target p : formula AtomType),
    In (Box p) (subformulas target) ->
    In (Box (Imp p (Box p))) (grz_subformulas target).
Proof. intros; now apply grz_enrichment_generated. Qed.

Lemma grz_subformulas_implication_closed :
  forall (AtomType : Type) (target : formula AtomType),
    formula_context_implication_closed (grz_subformulas target).
Proof.
  intros AtomType target. apply grz_enrichment_implication_closed.
  apply subformulas_implication_closed.
Qed.

Lemma grz_subformulas_antecedent_closed :
  forall (AtomType : Type) (target : formula AtomType),
    formula_context_antecedent_closed (grz_subformulas target).
Proof.
  intros AtomType target p q Himp.
  exact (proj1 (@grz_subformulas_implication_closed
    AtomType target p q Himp)).
Qed.

Lemma grz_subformulas_original_box_body :
  forall (AtomType : Type) (target p : formula AtomType),
    In (Box p) (subformulas target) -> In p (grz_subformulas target).
Proof.
  intros AtomType target p Hbox. apply grz_subformulas_base.
  exact (@subformulas_box_body_closed AtomType target p Hbox).
Qed.

Lemma fmc_mem_box_in_grz_subformulas :
  forall Ax target
    (X : finite_maximal_context Ax (grz_subformulas target)) p,
    fmc_mem X (Box p) -> In (Box p) (grz_subformulas target).
Proof.
  intros Ax target X p Hbox. eapply fmc_mem_box_in_base; [|exact Hbox].
  apply grz_subformulas_antecedent_closed.
Qed.
