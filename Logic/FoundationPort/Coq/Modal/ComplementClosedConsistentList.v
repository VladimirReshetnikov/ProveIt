(** Complement-closed consistent finite contexts over arbitrary atom types.

    Foundation states this API with finsets and decidable atom equality.  An
    extensional list presentation needs neither: duplicates and order are
    ignored by [In], while finite support still permits an explicit powerset
    cover of all bounded maximal contexts. *)

From Stdlib Require Import Lists.List Bool.Bool.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality Logic.ProofIrrelevance.
From FoundationModal Require Import
  Syntax Complement LogicInfrastructure ComplementEntailment.
From Foundation.Modal Require Import MaximalConsistentSet.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition abstract_list_subset {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Definition abstract_finite_theory {AtomType}
    (Gamma : list (formula AtomType)) : abstract_formula_theory AtomType :=
  fun p => In p Gamma.

Definition abstract_finite_consistent {AtomType}
    (L : modal_logic_set AtomType) (Gamma : list (formula AtomType)) : Prop :=
  abstract_context_consistent L (abstract_finite_theory Gamma).

Definition abstract_finite_inconsistent {AtomType}
    (L : modal_logic_set AtomType) (Gamma : list (formula AtomType)) : Prop :=
  ~ abstract_finite_consistent L Gamma.

Lemma abstract_context_derives_extensional :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma Delta p,
    (forall q, Gamma q <-> Delta q) ->
    (abstract_context_derives L Gamma p <->
     abstract_context_derives L Delta p).
Proof.
  intros AtomType L Gamma Delta p Heq; split; intro Hp.
  - eapply abstract_context_derives_weaken; [|exact Hp].
    intros q Hq. now apply (proj1 (Heq q)).
  - eapply abstract_context_derives_weaken; [|exact Hp].
    intros q Hq. now apply (proj2 (Heq q)).
Qed.

Lemma abstract_context_consistent_extensional :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma Delta,
    (forall q, Gamma q <-> Delta q) ->
    (abstract_context_consistent L Gamma <->
     abstract_context_consistent L Delta).
Proof.
  intros AtomType L Gamma Delta Heq. unfold abstract_context_consistent.
  rewrite (@abstract_context_derives_extensional
    AtomType L Gamma Delta Bottom Heq).
  reflexivity.
Qed.

Lemma abstract_finite_theory_cons_insert :
  forall (AtomType : Type) (p : formula AtomType)
    (Gamma : list (formula AtomType)) (q : formula AtomType),
    abstract_finite_theory (p :: Gamma) q <->
    abstract_theory_insert (abstract_finite_theory Gamma) p q.
Proof.
  intros AtomType p Gamma q. unfold abstract_finite_theory,
    abstract_theory_insert. simpl. split; intros [H | H].
  - left. now symmetry.
  - now right.
  - left. now symmetry.
  - now right.
Qed.

Lemma abstract_finite_derives_empty_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_context_derives L (fun _ => False) p <-> L p.
Proof.
  intros AtomType L Hclass p; split.
  - intro Hp. induction Hp.
    + contradiction.
    + assumption.
    + eapply (logic_modus_ponens Hclass); eauto.
  - now apply ACD_theorem.
Qed.

Lemma abstract_finite_empty_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> ~ L Bottom -> abstract_finite_consistent L [].
Proof.
  intros AtomType L Hclass Hsystem.
  unfold abstract_finite_consistent, abstract_context_consistent.
  intro Hbottom. apply Hsystem.
  apply (proj1 (abstract_finite_derives_empty_iff Hclass Bottom)).
  exact Hbottom.
Qed.

Lemma abstract_finite_consistent_insert_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_finite_consistent L (p :: Gamma) <->
    ~ abstract_context_derives L (abstract_finite_theory Gamma) (Neg p).
Proof.
  intros AtomType L Hclass Gamma p.
  transitivity (abstract_context_consistent L
    (abstract_theory_insert (abstract_finite_theory Gamma) p)).
  - apply abstract_context_consistent_extensional.
    intro q. apply abstract_finite_theory_cons_insert.
  - apply abstract_insert_consistent_iff, Hclass.
Qed.

Lemma abstract_finite_consistent_insert_neg_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_finite_consistent L (Neg p :: Gamma) <->
    ~ abstract_context_derives L (abstract_finite_theory Gamma) p.
Proof.
  intros AtomType L Hclass Gamma p.
  transitivity (abstract_context_consistent L
    (abstract_theory_insert (abstract_finite_theory Gamma) (Neg p))).
  - apply abstract_context_consistent_extensional.
    intro q. apply abstract_finite_theory_cons_insert.
  - apply abstract_insert_neg_consistent_iff, Hclass.
Qed.

Lemma abstract_finite_provable_iff_insert_neg_inconsistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_finite_inconsistent L (Neg p :: Gamma) <->
    abstract_context_derives L (abstract_finite_theory Gamma) p.
Proof.
  intros AtomType L Hclass Gamma p. unfold abstract_finite_inconsistent.
  rewrite abstract_finite_consistent_insert_neg_iff by exact Hclass.
  split; [apply NNPP | tauto].
Qed.

Lemma abstract_finite_neg_provable_iff_insert_inconsistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_finite_inconsistent L (p :: Gamma) <->
    abstract_context_derives L (abstract_finite_theory Gamma) (Neg p).
Proof.
  intros AtomType L Hclass Gamma p. unfold abstract_finite_inconsistent.
  rewrite abstract_finite_consistent_insert_iff by exact Hclass.
  split; [apply NNPP | tauto].
Qed.

Lemma abstract_finite_singleton_neg_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_finite_consistent L [Neg p] <-> ~ L p.
Proof.
  intros AtomType L Hclass p.
  rewrite abstract_finite_consistent_insert_neg_iff by exact Hclass.
  now rewrite abstract_finite_derives_empty_iff by exact Hclass.
Qed.

Lemma abstract_finite_singleton_consistent_iff_neg_unprovable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_finite_consistent L [p] <-> ~ L (Neg p).
Proof.
  intros AtomType L Hclass p.
  rewrite abstract_finite_consistent_insert_iff by exact Hclass.
  now rewrite abstract_finite_derives_empty_iff by exact Hclass.
Qed.

Lemma abstract_finite_singleton_complement_consistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_finite_consistent L [complement p] <-> ~ L p.
Proof.
  intros AtomType L Hclass p.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg. apply abstract_finite_singleton_neg_consistent_iff, Hclass.
  - rewrite <- Hq. rewrite complement_neg.
    apply abstract_finite_singleton_consistent_iff_neg_unprovable, Hclass.
Qed.

Lemma abstract_finite_singleton_complement_inconsistent_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    abstract_finite_inconsistent L [complement p] <-> L p.
Proof.
  intros AtomType L Hclass p. unfold abstract_finite_inconsistent.
  rewrite abstract_finite_singleton_complement_consistent_iff
    by exact Hclass. split; [apply NNPP | tauto].
Qed.

Lemma abstract_finite_union_consistent_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType) P1 P2,
    (forall Gamma1 Gamma2,
      abstract_list_subset Gamma1 P1 ->
      abstract_list_subset Gamma2 P2 ->
      ~ abstract_context_derives L
          (abstract_finite_theory (Gamma1 ++ Gamma2)) Bottom) ->
    abstract_finite_consistent L (P1 ++ P2).
Proof.
  intros AtomType L P1 P2 Hall.
  apply Hall; unfold abstract_list_subset; auto.
Qed.

(** Contextual forms of the complement proof theory. *)
Lemma abstract_derives_complement_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_derives L Gamma p ->
    abstract_context_derives L Gamma (complement p) ->
    abstract_context_derives L Gamma Bottom.
Proof.
  intros AtomType L Hclass Gamma p Hp Hcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg in Hcomp. exact (ACD_mp Hcomp Hp).
  - rewrite <- Hq in *. rewrite complement_neg in Hcomp.
    exact (ACD_mp Hp Hcomp).
Qed.

Lemma abstract_derives_neg_complement_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_derives L Gamma (Neg p) ->
    abstract_context_derives L Gamma (Neg (complement p)) ->
    abstract_context_derives L Gamma Bottom.
Proof.
  intros AtomType L Hclass Gamma p Hneg Hnegcomp.
  destruct (complement_cases p) as [Hcomp | [q Hq]].
  - rewrite Hcomp in Hnegcomp. exact (ACD_mp Hnegcomp Hneg).
  - rewrite <- Hq in *. rewrite complement_neg in Hnegcomp.
    exact (ACD_mp Hneg Hnegcomp).
Qed.

Lemma abstract_derives_of_neg_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_derives L Gamma (Neg (complement p)) ->
    abstract_context_derives L Gamma p.
Proof.
  intros AtomType L Hclass Gamma p Hnegcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg in Hnegcomp. now apply abstract_context_dne in Hnegcomp.
  - rewrite <- Hq in *. now rewrite complement_neg in Hnegcomp.
Qed.

Lemma abstract_derives_neg_of_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_context_derives L Gamma (complement p) ->
    abstract_context_derives L Gamma (Neg p).
Proof.
  intros AtomType L Hclass Gamma p Hcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - now rewrite Hneg in Hcomp.
  - rewrite <- Hq in *. rewrite complement_neg in Hcomp.
    eapply ACD_mp; [apply ACD_theorem | exact Hcomp].
    exact (classical_logic_double_neg_intro Hclass q).
Qed.

(** * Deterministic finite complementary closure *)

Definition abstract_finite_next {AtomType}
    (L : modal_logic_set AtomType) (p : formula AtomType)
    (Gamma : list (formula AtomType)) : list (formula AtomType) :=
  if excluded_middle_informative
       (abstract_finite_consistent L (p :: Gamma))
  then p :: Gamma
  else complement p :: Gamma.

Fixpoint abstract_finite_enumerate {AtomType}
    (L : modal_logic_set AtomType) (Gamma items : list (formula AtomType))
    : list (formula AtomType) :=
  match items with
  | [] => Gamma
  | p :: rest => abstract_finite_next L p
      (abstract_finite_enumerate L Gamma rest)
  end.

Lemma abstract_finite_next_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma p,
    abstract_finite_consistent L Gamma ->
    abstract_finite_consistent L (abstract_finite_next L p Gamma).
Proof.
  intros AtomType L Hclass Gamma p Hconsistent.
  unfold abstract_finite_next.
  destruct (excluded_middle_informative
    (abstract_finite_consistent L (p :: Gamma))) as [Hpos | Hpos].
  - exact Hpos.
  - apply (proj2 (abstract_finite_consistent_insert_iff
      Hclass Gamma (complement p))). intro Hnegcomp.
    apply Hconsistent.
    eapply abstract_derives_neg_complement_bottom; [exact Hclass | |].
    + apply (proj1 (abstract_finite_neg_provable_iff_insert_inconsistent
        Hclass Gamma p)). exact Hpos.
    + exact Hnegcomp.
Qed.

Lemma abstract_finite_enumerate_consistent :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Gamma items,
    abstract_finite_consistent L Gamma ->
    abstract_finite_consistent L
      (abstract_finite_enumerate L Gamma items).
Proof.
  intros AtomType L Hclass Gamma items Hconsistent.
  induction items as [|p items IH]; simpl.
  - exact Hconsistent.
  - apply abstract_finite_next_consistent; [exact Hclass | exact IH].
Qed.

Lemma abstract_finite_next_includes :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma p,
    abstract_list_subset Gamma (abstract_finite_next L p Gamma).
Proof.
  intros AtomType L Gamma p. unfold abstract_finite_next,
    abstract_list_subset.
  destruct (excluded_middle_informative
    (abstract_finite_consistent L (p :: Gamma))); simpl; auto.
Qed.

Lemma abstract_finite_enumerate_includes :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma items,
    abstract_list_subset Gamma (abstract_finite_enumerate L Gamma items).
Proof.
  intros AtomType L Gamma items. induction items as [|p items IH]; simpl.
  - intros q Hq. exact Hq.
  - intros q Hq. apply abstract_finite_next_includes. now apply IH.
Qed.

Lemma abstract_finite_enumerate_either :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma items p,
    In p items ->
    In p (abstract_finite_enumerate L Gamma items) \/
    In (complement p) (abstract_finite_enumerate L Gamma items).
Proof.
  intros AtomType L Gamma items. induction items as [|q items IH];
    intros p Hp; [contradiction |].
  simpl in Hp |- *. destruct Hp as [-> | Hp].
  - unfold abstract_finite_next.
    destruct (excluded_middle_informative
      (abstract_finite_consistent L
        (p :: abstract_finite_enumerate L Gamma items))); simpl; auto.
  - destruct (IH p Hp) as [H | H]; unfold abstract_finite_next;
      destruct (excluded_middle_informative
        (abstract_finite_consistent L
          (q :: abstract_finite_enumerate L Gamma items))); simpl; auto.
Qed.

Lemma abstract_finite_enumerate_origin :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Gamma items p,
    In p (abstract_finite_enumerate L Gamma items) ->
    In p Gamma \/ In p items \/
      exists q, In q items /\ complement q = p.
Proof.
  intros AtomType L Gamma items. induction items as [|q items IH];
    intros p Hp.
  - simpl in Hp. now left.
  - simpl in Hp |- *. unfold abstract_finite_next in Hp.
    destruct (excluded_middle_informative
      (abstract_finite_consistent L
        (q :: abstract_finite_enumerate L Gamma items)));
      simpl in Hp; destruct Hp as [Heq | Hp].
    + subst p. right; left; now left.
    + destruct (IH p Hp) as [H | [H | [r [Hr Heq]]]].
      * now left.
      * right; left; now right.
      * right; right. exists r. split; [now right | exact Heq].
    + subst p. right; right. exists q. split; [now left | reflexivity].
    + destruct (IH p Hp) as [H | [H | [r [Hr Heq]]]].
      * now left.
      * right; left; now right.
      * right; right. exists r. split; [now right | exact Heq].
Qed.

Theorem abstract_exists_consistent_complementary_closed :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall P S,
    abstract_list_subset P (complementary S) ->
    abstract_finite_consistent L P ->
    exists P',
      abstract_list_subset P P' /\
      abstract_finite_consistent L P' /\
      complementary_closed P' S.
Proof.
  intros AtomType L Hclass P S Hsub Hconsistent.
  exists (abstract_finite_enumerate L P S). split.
  - apply abstract_finite_enumerate_includes.
  - split.
    + now apply abstract_finite_enumerate_consistent.
    + constructor.
      * intros p Hp.
        destruct (@abstract_finite_enumerate_origin AtomType L P S p Hp)
          as [HinP | [HinS | [q [Hq Heq]]]].
        -- exact (Hsub p HinP).
        -- now apply complementary_mem.
        -- rewrite <- Heq. now apply complementary_comp.
      * intros p Hp.
        exact (@abstract_finite_enumerate_either AtomType L P S p Hp).
Qed.

(** * Bounded complement-closed context subtype *)

Record abstract_predicate_complementary_closed {AtomType}
    (X : abstract_formula_theory AtomType)
    (Psi : list (formula AtomType)) : Prop := {
  apcc_subset : forall p, X p -> In p (complementary Psi);
  apcc_either : forall p, In p Psi -> X p \/ X (complement p)
}.

Record abstract_finite_maximal_context (AtomType : Type)
    (L : modal_logic_set AtomType) (Psi : list (formula AtomType)) : Type := {
  afmc_carrier : abstract_formula_theory AtomType;
  afmc_finite : exists support : list (formula AtomType),
    forall p, afmc_carrier p <-> In p support;
  afmc_consistent : abstract_context_consistent L afmc_carrier;
  afmc_closed : abstract_predicate_complementary_closed afmc_carrier Psi
}.

Arguments abstract_finite_maximal_context (AtomType) L Psi : clear implicits.
Arguments afmc_carrier {AtomType L Psi} _ _.
Arguments afmc_finite {AtomType L Psi} _.
Arguments afmc_consistent {AtomType L Psi} _.
Arguments afmc_closed {AtomType L Psi} _.

Definition afmc_mem {AtomType L Psi}
    (X : abstract_finite_maximal_context AtomType L Psi) := afmc_carrier X.

Lemma afmc_mem_complement_of_not_mem :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p,
    In p Psi -> ~ afmc_mem X p -> afmc_mem X (complement p).
Proof.
  intros AtomType L Psi X p Hp Hnot.
  destruct (apcc_either (afmc_closed X) Hp); tauto.
Qed.

Lemma afmc_mem_of_not_mem_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p,
    In p Psi -> ~ afmc_mem X (complement p) -> afmc_mem X p.
Proof.
  intros AtomType L Psi X p Hp Hnot.
  destruct (apcc_either (afmc_closed X) Hp); tauto.
Qed.

Lemma afmc_equality_def :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi
    (X Y : abstract_finite_maximal_context AtomType L Psi),
    X = Y <-> forall p, afmc_mem X p <-> afmc_mem Y p.
Proof.
  intros AtomType L Psi X Y; split.
  - intros -> p. reflexivity.
  - destruct X as [X Xfinite Xconsistent Xclosed].
    destruct Y as [Y Yfinite Yconsistent Yclosed]. simpl.
    intro Hext. assert (Hcarrier : X = Y).
    { apply functional_extensionality; intro p.
      apply propositional_extensionality, Hext. }
    subst Y.
    assert (Xfinite = Yfinite) by apply proof_irrelevance. subst Yfinite.
    assert (Xconsistent = Yconsistent) by apply proof_irrelevance.
    subst Yconsistent.
    assert (Xclosed = Yclosed) by apply proof_irrelevance. now subst Yclosed.
Qed.

Theorem abstract_finite_context_lindenbaum :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Phi Psi,
    abstract_list_subset Phi (complementary Psi) ->
    abstract_finite_consistent L Phi ->
    exists X : abstract_finite_maximal_context AtomType L Psi,
      forall p, In p Phi -> afmc_mem X p.
Proof.
  intros AtomType L Hclass Phi Psi Hsub Hconsistent.
  destruct (abstract_exists_consistent_complementary_closed
    Hclass Hsub Hconsistent) as [P [HP [Hcons Hclosed]]].
  exists {| afmc_carrier := abstract_finite_theory P;
            afmc_finite := ex_intro _ P
              (fun p => @iff_refl (In p P));
            afmc_consistent := Hcons;
            afmc_closed :=
              {| apcc_subset := complementary_closed_subset Hclosed;
                 apcc_either := complementary_closed_either Hclosed |} |}.
  exact HP.
Qed.

Theorem abstract_finite_maximal_context_inhabited :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> ~ L Bottom -> forall Psi,
    exists X : abstract_finite_maximal_context AtomType L Psi, True.
Proof.
  intros AtomType L Hclass Hsystem Psi.
  destruct (abstract_finite_context_lindenbaum Hclass
    (Phi:=[]) (Psi:=Psi)) as [X HX].
  - intros p Hp. contradiction.
  - now apply abstract_finite_empty_consistent.
  - now exists X.
Qed.

Lemma afmc_membership_iff_derivable :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p,
    In p Psi ->
    (afmc_mem X p <-> abstract_context_derives L (afmc_mem X) p).
Proof.
  intros AtomType L Hclass Psi X p Hp; split.
  - intro Hmem. now apply ACD_assumption.
  - intro Hder. destruct (apcc_either (afmc_closed X) Hp)
      as [Hmem | Hcomp]; [exact Hmem |].
    exfalso. apply (afmc_consistent X).
    eapply abstract_derives_complement_bottom; [exact Hclass | exact Hder |].
    now apply ACD_assumption.
Qed.

Lemma afmc_mem_top :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Psi
    (X : abstract_finite_maximal_context AtomType L Psi),
    In Top Psi -> afmc_mem X Top.
Proof.
  intros AtomType L Hclass Psi X Htop.
  apply (proj2 (@afmc_membership_iff_derivable
    AtomType L Hclass Psi X Top Htop)).
  apply ACD_theorem. exact (logic_mem_top Hclass).
Qed.

Lemma afmc_bottom_absent :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi
    (X : abstract_finite_maximal_context AtomType L Psi),
    ~ afmc_mem X Bottom.
Proof.
  intros AtomType L Psi X Hbottom. apply (afmc_consistent X).
  now apply ACD_assumption.
Qed.

Lemma afmc_mem_iff_not_mem_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p,
    In p Psi -> (afmc_mem X p <-> ~ afmc_mem X (complement p)).
Proof.
  intros AtomType L Hclass Psi X p Hp; split.
  - intros Hmem Hcomp. apply (afmc_consistent X).
    eapply abstract_derives_complement_bottom; [exact Hclass | |].
    + exact (@ACD_assumption AtomType L (afmc_mem X) p Hmem).
    + exact (@ACD_assumption AtomType L (afmc_mem X)
        (complement p) Hcomp).
  - now apply afmc_mem_of_not_mem_complement.
Qed.

Lemma afmc_not_mem_iff_mem_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p,
    In p Psi -> (~ afmc_mem X p <-> afmc_mem X (complement p)).
Proof.
  intros AtomType L Hclass Psi X p Hp; split.
  - now apply afmc_mem_complement_of_not_mem.
  - intros Hcomp Hmem. apply (afmc_consistent X).
    eapply abstract_derives_complement_bottom; [exact Hclass | |].
    + exact (@ACD_assumption AtomType L (afmc_mem X) p Hmem).
    + exact (@ACD_assumption AtomType L (afmc_mem X)
        (complement p) Hcomp).
Qed.

Lemma afmc_mem_imp_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p q,
    In (Imp p q) Psi -> In p Psi -> In q Psi ->
    (afmc_mem X (Imp p q) <->
      (afmc_mem X p -> ~ afmc_mem X (complement q))).
Proof.
  intros AtomType L Hclass Psi X p q Himp Hp Hq; split.
  - intros Hmemimp Hmemp Hcompq. apply (afmc_consistent X).
    eapply abstract_derives_complement_bottom; [exact Hclass | |].
    + eapply ACD_mp; apply ACD_assumption; eassumption.
    + now apply ACD_assumption.
  - intro Hsemantic.
    apply (proj2 (@afmc_membership_iff_derivable
      AtomType L Hclass Psi X (Imp p q) Himp)).
    destruct (apcc_either (afmc_closed X) Hp)
      as [Hmemp | Hcompp].
    + apply abstract_context_derives_imply_intro; [exact Hclass |].
      apply ACD_assumption.
      apply afmc_mem_of_not_mem_complement; [exact Hq |].
      exact (Hsemantic Hmemp).
    + eapply (@ACD_mp AtomType L (afmc_mem X)
        (Neg p) (Imp p q)).
      * apply ACD_theorem, (logic_classical_tautology Hclass).
        intro rho. unfold Neg. simpl. tauto.
      * apply (abstract_derives_neg_of_complement Hclass).
        exact (@ACD_assumption AtomType L (afmc_mem X)
          (complement p) Hcompp).
Qed.

Lemma afmc_not_mem_imp_iff :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p q,
    In (Imp p q) Psi -> In p Psi -> In q Psi ->
    (~ afmc_mem X (Imp p q) <->
      afmc_mem X p /\ afmc_mem X (complement q)).
Proof.
  intros AtomType L Hclass Psi X p q Himp Hp Hq; split.
  - intro Hnot.
    assert (Hmemp : afmc_mem X p).
    { destruct (apcc_either (afmc_closed X) Hp)
        as [Hmemp | Hcompp]; [exact Hmemp |].
      exfalso. apply Hnot, (proj2
        (@afmc_membership_iff_derivable
          AtomType L Hclass Psi X (Imp p q) Himp)).
      eapply (@ACD_mp AtomType L (afmc_mem X)
        (Neg p) (Imp p q)).
      - apply ACD_theorem, (logic_classical_tautology Hclass).
        intro rho. unfold Neg. simpl. tauto.
      - apply (abstract_derives_neg_of_complement Hclass).
        exact (@ACD_assumption AtomType L (afmc_mem X)
          (complement p) Hcompp). }
    split; [exact Hmemp |].
    destruct (apcc_either (afmc_closed X) Hq)
      as [Hmemq | Hcompq]; [|exact Hcompq].
    exfalso. apply Hnot, (proj2
      (@afmc_membership_iff_derivable
        AtomType L Hclass Psi X (Imp p q) Himp)).
    apply abstract_context_derives_imply_intro; [exact Hclass |].
    now apply ACD_assumption.
  - intros [Hmemp Hcompq] Hmemimp.
    exact (proj1 (@afmc_mem_imp_iff
      AtomType L Hclass Psi X p q Himp Hp Hq)
      Hmemimp Hmemp Hcompq).
Qed.

(** * An explicit finite cover of the bounded context space *)

Fixpoint abstract_finite_powerset {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: rest =>
      let ps := abstract_finite_powerset rest in ps ++ map (cons x) ps
  end.

Lemma abstract_finite_powerset_contains_filter :
  forall (A : Type) (select : A -> bool) xs,
    In (filter select xs) (abstract_finite_powerset xs).
Proof.
  intros A select xs. induction xs as [|x xs IH]; simpl.
  - now left.
  - destruct (select x); simpl.
    + apply in_or_app. right. now apply in_map.
    + apply in_or_app. now left.
Qed.

Definition afmc_mem_dec {AtomType L Psi}
    (X : abstract_finite_maximal_context AtomType L Psi)
    (p : formula AtomType) : {afmc_mem X p} + {~ afmc_mem X p} :=
  excluded_middle_informative (afmc_mem X p).

Definition afmc_selector {AtomType L Psi}
    (X : abstract_finite_maximal_context AtomType L Psi)
    (p : formula AtomType) : bool :=
  if afmc_mem_dec X p then true else false.

Definition afmc_representative {AtomType L Psi}
    (X : abstract_finite_maximal_context AtomType L Psi) :
    list (formula AtomType) :=
  filter (afmc_selector X) (complementary Psi).

Lemma afmc_representative_spec :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi
    (X : abstract_finite_maximal_context AtomType L Psi) p,
    In p (afmc_representative X) <-> afmc_mem X p.
Proof.
  intros AtomType L Psi X p. unfold afmc_representative.
  rewrite filter_In. unfold afmc_selector.
  destruct (afmc_mem_dec X p) as [Hmem | Hnot]; simpl.
  - split.
    + intros Hselected. exact Hmem.
    + intro Hselected. split.
      * exact (apcc_subset (afmc_closed X) Hmem).
      * reflexivity.
  - split.
    + intros [Hselected Hfalse]. discriminate.
    + contradiction.
Qed.

Definition abstract_option_list {A : Type} (x : option A) : list A :=
  match x with Some y => [y] | None => [] end.

Definition afmc_candidate {AtomType} (L : modal_logic_set AtomType)
    (Psi carrier : list (formula AtomType)) :
    option (abstract_finite_maximal_context AtomType L Psi).
Proof.
  destruct (excluded_middle_informative
    (abstract_context_consistent L (abstract_finite_theory carrier) /\
     abstract_predicate_complementary_closed
       (abstract_finite_theory carrier) Psi)) as [[Hcons Hclosed] | Hbad].
  - exact (Some
      {| afmc_carrier := abstract_finite_theory carrier;
         afmc_finite := ex_intro _ carrier
           (fun p => @iff_refl (In p carrier));
         afmc_consistent := Hcons;
         afmc_closed := Hclosed |}).
  - exact None.
Defined.

Definition afmc_explicit_cover {AtomType}
    (L : modal_logic_set AtomType) (Psi : list (formula AtomType)) :
    list (abstract_finite_maximal_context AtomType L Psi) :=
  flat_map (fun carrier => abstract_option_list (afmc_candidate L Psi carrier))
    (abstract_finite_powerset (complementary Psi)).

Lemma afmc_candidate_complete :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi carrier,
    abstract_context_consistent L (abstract_finite_theory carrier) ->
    abstract_predicate_complementary_closed
      (abstract_finite_theory carrier) Psi ->
    exists X,
      afmc_candidate L Psi carrier = Some X /\
      forall p, afmc_mem X p <-> In p carrier.
Proof.
  intros AtomType L Psi carrier Hconsistent Hclosed.
  unfold afmc_candidate.
  destruct (excluded_middle_informative
    (abstract_context_consistent L (abstract_finite_theory carrier) /\
     abstract_predicate_complementary_closed
       (abstract_finite_theory carrier) Psi)) as [Hgood | Hbad].
  - destruct Hgood as [Hgood_consistent Hgood_closed].
    eexists. split; [reflexivity |]. intro p. reflexivity.
  - exfalso. apply Hbad. now split.
Qed.

Theorem afmc_explicit_cover_complete :
  forall (AtomType : Type) (L : modal_logic_set AtomType) Psi
    (X : abstract_finite_maximal_context AtomType L Psi),
    In X (afmc_explicit_cover L Psi).
Proof.
  intros AtomType L Psi X.
  set (carrier := afmc_representative X).
  assert (Hcarrier : forall p,
      abstract_finite_theory carrier p <-> afmc_mem X p).
  { intro p. unfold abstract_finite_theory, carrier.
    apply afmc_representative_spec. }
  assert (Hconsistent :
      abstract_context_consistent L (abstract_finite_theory carrier)).
  { apply (proj2 (@abstract_context_consistent_extensional
      AtomType L (abstract_finite_theory carrier) (afmc_mem X) Hcarrier)).
    exact (afmc_consistent X). }
  assert (Hclosed : abstract_predicate_complementary_closed
      (abstract_finite_theory carrier) Psi).
  { constructor.
    - intros p Hp. apply (apcc_subset (afmc_closed X)).
      now apply (proj1 (Hcarrier p)).
    - intros p Hp. destruct (apcc_either (afmc_closed X) Hp) as [H | H].
      + left. now apply (proj2 (Hcarrier p)).
      + right. now apply (proj2 (Hcarrier (complement p))). }
  destruct (@afmc_candidate_complete
    AtomType L Psi carrier Hconsistent Hclosed)
    as [Y [Hcandidate HY]].
  assert (HYX : Y = X).
  { apply (proj2 (@afmc_equality_def AtomType L Psi Y X)). intro p.
    rewrite HY. apply Hcarrier. }
  subst Y. unfold afmc_explicit_cover.
  apply in_flat_map. exists carrier. split.
  - unfold carrier, afmc_representative.
    apply abstract_finite_powerset_contains_filter.
  - unfold abstract_option_list. now rewrite Hcandidate; simpl; auto.
Qed.
