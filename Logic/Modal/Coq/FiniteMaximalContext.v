(**
  Complement-closed consistent finite contexts.

  This ports the complete mathematical surface of Foundation's
  [Modal/ComplementClosedConsistentFinset.lean].  Lean's [Finset] layer is
  represented in two idiomatic Coq forms:

  - the executable extension construction uses lists, interpreted
    extensionally through [In] (so order and duplicate entries are inert);
  - the resulting context type stores a predicate together with a finite
    support.  Thus equality of contexts is extensional equality of carriers,
    exactly as it is for Lean finsets.

  The calculus is parameterized by an arbitrary normal axiom schema, so one
  construction serves all named normal extensions in this port.  This is not
  the source's full atom-polymorphic abstract-entailment interface: formula
  atoms are [nat], as required by the schema-generic contextual calculus in
  [CanonicalExtensions].

  The final section gives an explicit finite list covering the entire context
  space.  It is stronger than merely asserting a [Finite] instance: every
  context is proved equal to an element of the displayed list.
*)

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.
From Stdlib Require Import Logic.ClassicalDescription Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.PropExtensionality Logic.ProofIrrelevance.
From FoundationModal Require Import
  Syntax Complement HilbertK NormalHilbert CanonicalExtensions.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Extensional finite-list theories *)

Definition finite_theory (Gamma : list (formula nat)) : theory nat :=
  fun p => In p Gamma.

Definition list_subset {A : Type} (xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Definition finite_consistent (Ax : modal_axiom_schema)
    (Gamma : list (formula nat)) : Prop :=
  normal_theory_consistent Ax (finite_theory Gamma).

Definition finite_inconsistent (Ax : modal_axiom_schema)
    (Gamma : list (formula nat)) : Prop :=
  ~ finite_consistent Ax Gamma.

Lemma normal_derives_extensional :
  forall Ax (Gamma Delta : theory nat) p,
    (forall q, Gamma q <-> Delta q) ->
    (normal_derives Ax Gamma p <-> normal_derives Ax Delta p).
Proof.
  intros Ax Gamma Delta p Heq; split; intro Hp.
  - eapply normal_derives_weaken; [|exact Hp].
    intros q Hq. now apply (proj1 (Heq q)).
  - eapply normal_derives_weaken; [|exact Hp].
    intros q Hq. now apply (proj2 (Heq q)).
Qed.

Lemma normal_theory_consistent_extensional :
  forall Ax (Gamma Delta : theory nat),
    (forall q, Gamma q <-> Delta q) ->
    (normal_theory_consistent Ax Gamma <->
     normal_theory_consistent Ax Delta).
Proof.
  intros Ax Gamma Delta Heq. unfold normal_theory_consistent.
  rewrite (@normal_derives_extensional Ax Gamma Delta Bottom Heq).
  tauto.
Qed.

Lemma finite_theory_nil :
  forall p, finite_theory [] p <-> empty_theory p.
Proof. intros p; simpl; tauto. Qed.

Lemma finite_theory_cons_iff_insert :
  forall p Gamma q,
    finite_theory (p :: Gamma) q <->
    theory_insert (finite_theory Gamma) p q.
Proof.
  intros p Gamma q. unfold finite_theory, theory_insert. simpl.
  split; intros [H | H].
  - now left.
  - now right.
  - left. symmetry. exact H.
  - now right.
Qed.

Lemma finite_consistent_theory_iff :
  forall Ax Gamma,
    normal_theory_consistent Ax (finite_theory Gamma) <->
    finite_consistent Ax Gamma.
Proof. reflexivity. Qed.

Lemma finite_inconsistent_theory_iff :
  forall Ax Gamma,
    (~ normal_theory_consistent Ax (finite_theory Gamma)) <->
    finite_inconsistent Ax Gamma.
Proof. reflexivity. Qed.

Lemma finite_empty_consistent :
  forall Ax,
    normal_system_consistent Ax -> finite_consistent Ax [].
Proof.
  intros Ax Hsystem.
  apply (proj2 (@normal_theory_consistent_extensional Ax
    (finite_theory []) empty_theory finite_theory_nil)).
  now apply (proj2 (normal_empty_theory_consistent_iff Ax)).
Qed.

Lemma finite_consistent_insert_iff :
  forall Ax Gamma p,
    finite_consistent Ax (p :: Gamma) <->
    ~ normal_derives Ax (finite_theory Gamma) (Neg p).
Proof.
  intros Ax Gamma p.
  transitivity
    (normal_theory_consistent Ax
      (theory_insert (finite_theory Gamma) p)).
  - apply normal_theory_consistent_extensional.
    intro q. apply finite_theory_cons_iff_insert.
  - apply normal_theory_consistent_insert_iff.
Qed.

Lemma finite_consistent_insert_neg_iff :
  forall Ax Gamma p,
    finite_consistent Ax (Neg p :: Gamma) <->
    ~ normal_derives Ax (finite_theory Gamma) p.
Proof.
  intros Ax Gamma p.
  transitivity
    (normal_theory_consistent Ax
      (theory_insert (finite_theory Gamma) (Neg p))).
  - apply normal_theory_consistent_extensional.
    intro q. apply finite_theory_cons_iff_insert.
  - apply normal_theory_consistent_insert_neg_iff.
Qed.

(** These are the two insertion equivalences used throughout the source.
    [finite_inconsistent] intentionally retains the source definition as the
    negation of consistency, hence the reverse implications use classical
    double-negation elimination. *)
Lemma finite_provable_iff_insert_neg_inconsistent :
  forall Ax Gamma p,
    finite_inconsistent Ax (Neg p :: Gamma) <->
    normal_derives Ax (finite_theory Gamma) p.
Proof.
  intros Ax Gamma p. unfold finite_inconsistent.
  rewrite finite_consistent_insert_neg_iff. split.
  - apply NNPP.
  - tauto.
Qed.

Lemma finite_neg_provable_iff_insert_inconsistent :
  forall Ax Gamma p,
    finite_inconsistent Ax (p :: Gamma) <->
    normal_derives Ax (finite_theory Gamma) (Neg p).
Proof.
  intros Ax Gamma p. unfold finite_inconsistent.
  rewrite finite_consistent_insert_iff. split.
  - apply NNPP.
  - tauto.
Qed.

Lemma finite_singleton_neg_consistent_iff_unprovable :
  forall Ax p,
    finite_consistent Ax [Neg p] <->
    ~ normal_proves Ax p.
Proof.
  intros Ax p. rewrite finite_consistent_insert_neg_iff.
  now rewrite normal_derives_empty_iff.
Qed.

Lemma finite_singleton_consistent_iff_neg_unprovable :
  forall Ax p,
    finite_consistent Ax [p] <->
    ~ normal_proves Ax (Neg p).
Proof.
  intros Ax p. rewrite finite_consistent_insert_iff.
  now rewrite normal_derives_empty_iff.
Qed.

Lemma finite_singleton_complement_consistent_iff_unprovable :
  forall Ax p,
    finite_consistent Ax [complement p] <->
    ~ normal_proves Ax p.
Proof.
  intros Ax p.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg. apply finite_singleton_neg_consistent_iff_unprovable.
  - rewrite <- Hq. rewrite complement_neg.
    apply finite_singleton_consistent_iff_neg_unprovable.
Qed.

Lemma finite_singleton_complement_inconsistent_iff_provable :
  forall Ax p,
    finite_inconsistent Ax [complement p] <-> normal_proves Ax p.
Proof.
  intros Ax p. unfold finite_inconsistent.
  rewrite finite_singleton_complement_consistent_iff_unprovable.
  split; [apply NNPP | tauto].
Qed.

Lemma finite_union_consistent_intro :
  forall Ax P1 P2,
    (forall Gamma1 Gamma2,
      list_subset Gamma1 P1 ->
      list_subset Gamma2 P2 ->
      ~ normal_derives Ax (finite_theory (Gamma1 ++ Gamma2)) Bottom) ->
    finite_consistent Ax (P1 ++ P2).
Proof.
  intros Ax P1 P2 Hall.
  apply Hall; unfold list_subset; auto.
Qed.

(** * Syntactic complements in the generic contextual calculus *)

Lemma normal_derives_complement_bottom :
  forall Ax Gamma p,
    normal_derives Ax Gamma p ->
    normal_derives Ax Gamma (complement p) ->
    normal_derives Ax Gamma Bottom.
Proof.
  intros Ax Gamma p Hp Hcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg in Hcomp. exact (ND_mp Hcomp Hp).
  - rewrite <- Hq in *. rewrite complement_neg in Hcomp.
    exact (ND_mp Hp Hcomp).
Qed.

Lemma normal_derives_neg_complement_bottom :
  forall Ax Gamma p,
    normal_derives Ax Gamma (Neg p) ->
    normal_derives Ax Gamma (Neg (complement p)) ->
    normal_derives Ax Gamma Bottom.
Proof.
  intros Ax Gamma p Hneg Hnegcomp.
  destruct (complement_cases p) as [Hcomp | [q Hq]].
  - rewrite Hcomp in Hnegcomp. exact (ND_mp Hnegcomp Hneg).
  - rewrite <- Hq in *. rewrite complement_neg in Hnegcomp.
    exact (ND_mp Hneg Hnegcomp).
Qed.

(** Foundation names this theorem [of_imply_complement_bot]: refuting the
    syntactic complement proves the original formula. *)
Lemma normal_derives_of_neg_complement :
  forall Ax Gamma p,
    normal_derives Ax Gamma (Neg (complement p)) ->
    normal_derives Ax Gamma p.
Proof.
  intros Ax Gamma p Hnegcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg in Hnegcomp. now apply normal_derives_dne in Hnegcomp.
  - rewrite <- Hq in *. rewrite complement_neg in Hnegcomp.
    exact Hnegcomp.
Qed.

Lemma normal_derives_neg_of_complement :
  forall Ax Gamma p,
    normal_derives Ax Gamma (complement p) ->
    normal_derives Ax Gamma (Neg p).
Proof.
  intros Ax Gamma p Hcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - now rewrite Hneg in Hcomp.
  - rewrite <- Hq in *. rewrite complement_neg in Hcomp.
    eapply ND_mp; [apply ND_theorem; apply normal_proves_dni | exact Hcomp].
Qed.

(** * Deterministic classical finite extension *)

Definition finite_next (Ax : modal_axiom_schema) (p : formula nat)
    (Gamma : list (formula nat)) : list (formula nat) :=
  if excluded_middle_informative (finite_consistent Ax (p :: Gamma))
  then p :: Gamma
  else complement p :: Gamma.

Fixpoint finite_enumerate (Ax : modal_axiom_schema)
    (Gamma : list (formula nat)) (items : list (formula nat))
    : list (formula nat) :=
  match items with
  | [] => Gamma
  | p :: rest => finite_next Ax p (finite_enumerate Ax Gamma rest)
  end.

Lemma finite_next_consistent :
  forall Ax Gamma p,
    finite_consistent Ax Gamma ->
    finite_consistent Ax (finite_next Ax p Gamma).
Proof.
  intros Ax Gamma p Hconsistent. unfold finite_next.
  destruct (excluded_middle_informative
    (finite_consistent Ax (p :: Gamma))) as [Hpos | Hpos].
  - exact Hpos.
  - apply (proj2 (finite_consistent_insert_iff Ax Gamma (complement p))).
    intro Hnegcomp.
    apply Hconsistent.
    eapply normal_derives_neg_complement_bottom.
    + apply (proj1
        (finite_neg_provable_iff_insert_inconsistent Ax Gamma p)).
      exact Hpos.
    + exact Hnegcomp.
Qed.

Lemma finite_enumerate_consistent :
  forall Ax Gamma items,
    finite_consistent Ax Gamma ->
    finite_consistent Ax (finite_enumerate Ax Gamma items).
Proof.
  intros Ax Gamma items Hconsistent. induction items as [|p items IH].
  - exact Hconsistent.
  - simpl. apply finite_next_consistent. exact IH.
Qed.

Lemma finite_enumerate_nil :
  forall Ax Gamma, finite_enumerate Ax Gamma [] = Gamma.
Proof. reflexivity. Qed.

Lemma finite_next_includes :
  forall Ax Gamma p,
    list_subset Gamma (finite_next Ax p Gamma).
Proof.
  intros Ax Gamma p. unfold finite_next, list_subset.
  destruct (excluded_middle_informative
    (finite_consistent Ax (p :: Gamma))); simpl; auto.
Qed.

Lemma finite_enumerate_subset_step :
  forall Ax Gamma items p,
    list_subset (finite_enumerate Ax Gamma items)
      (finite_enumerate Ax Gamma (p :: items)).
Proof. intros; simpl; apply finite_next_includes. Qed.

Lemma finite_enumerate_includes :
  forall Ax Gamma items,
    list_subset Gamma (finite_enumerate Ax Gamma items).
Proof.
  intros Ax Gamma items. induction items as [|p items IH].
  - unfold list_subset; simpl; auto.
  - unfold list_subset in *. intros x Hx.
    apply (@finite_enumerate_subset_step Ax Gamma items p).
    now apply IH.
Qed.

Lemma finite_enumerate_either :
  forall Ax Gamma items p,
    In p items ->
    In p (finite_enumerate Ax Gamma items) \/
    In (complement p) (finite_enumerate Ax Gamma items).
Proof.
  intros Ax Gamma items. induction items as [|q items IH]; intros p Hp.
  - contradiction.
  - simpl in Hp |- *. destruct Hp as [Hp | Hp].
    + subst q. unfold finite_next.
      destruct (excluded_middle_informative
        (finite_consistent Ax (p :: finite_enumerate Ax Gamma items)));
        simpl; auto.
    + destruct (IH p Hp) as [H | H]; unfold finite_next;
        destruct (excluded_middle_informative
          (finite_consistent Ax (q :: finite_enumerate Ax Gamma items)));
        simpl; auto.
Qed.

Lemma finite_enumerate_origin :
  forall Ax Gamma items p,
    In p (finite_enumerate Ax Gamma items) ->
    In p Gamma \/ In p items \/
      exists q, In q items /\ complement q = p.
Proof.
  intros Ax Gamma items. induction items as [|q items IH]; intros p Hp.
  - simpl in Hp. now left.
  - simpl in Hp |- *. unfold finite_next in Hp.
    destruct (excluded_middle_informative
      (finite_consistent Ax
        (q :: finite_enumerate Ax Gamma items))) as [Hpos | Hpos];
      simpl in Hp; destruct Hp as [Hp | Hp].
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

Theorem finite_exists_consistent_complementary_closed :
  forall Ax P S,
    list_subset P (complementary S) ->
    finite_consistent Ax P ->
    exists P',
      list_subset P P' /\
      finite_consistent Ax P' /\
      complementary_closed P' S.
Proof.
  intros Ax P S Hsub Hconsistent.
  exists (finite_enumerate Ax P S). split.
  - apply finite_enumerate_includes.
  - split.
    + now apply finite_enumerate_consistent.
    + constructor.
      * intros p Hp.
      destruct (@finite_enumerate_origin Ax P S p Hp)
        as [HinP | [HinS | [q [Hq Heq]]]].
        -- exact (Hsub p HinP).
        -- now apply complementary_mem.
        -- rewrite <- Heq. now apply complementary_comp.
      * intros p Hp. exact (@finite_enumerate_either Ax P S p Hp).
Qed.

(** * Complement-closed consistent finite context subtype *)

Record predicate_complementary_closed
    (X : theory nat) (Psi : list (formula nat)) : Prop := {
  predicate_closed_subset :
    forall p, X p -> In p (complementary Psi);
  predicate_closed_either :
    forall p, In p Psi -> X p \/ X (complement p)
}.

Record finite_maximal_context
    (Ax : modal_axiom_schema) (Psi : list (formula nat)) : Type := {
  fmc_carrier : theory nat;
  fmc_finite :
    exists support : list (formula nat),
      forall p, fmc_carrier p <-> In p support;
  fmc_consistent : normal_theory_consistent Ax fmc_carrier;
  fmc_closed : predicate_complementary_closed fmc_carrier Psi
}.

Definition fmc_mem {Ax Psi}
    (X : finite_maximal_context Ax Psi) (p : formula nat) : Prop :=
  fmc_carrier X p.

Lemma fmc_unprovable_falsum :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    ~ normal_derives Ax (fmc_mem X) Bottom.
Proof. intros Ax Psi X. exact (@fmc_consistent Ax Psi X). Qed.

Lemma fmc_mem_complement_of_not_mem :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p Psi -> ~ fmc_mem X p -> fmc_mem X (complement p).
Proof.
  intros Ax Psi X p Hp Hnot.
  destruct (@predicate_closed_either (fmc_mem X) Psi
    (@fmc_closed Ax Psi X) p Hp); tauto.
Qed.

Lemma fmc_mem_of_not_mem_complement :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p Psi -> ~ fmc_mem X (complement p) -> fmc_mem X p.
Proof.
  intros Ax Psi X p Hp Hnot.
  destruct (@predicate_closed_either (fmc_mem X) Psi
    (@fmc_closed Ax Psi X) p Hp); tauto.
Qed.

Lemma fmc_equality_def :
  forall Ax Psi (X Y : finite_maximal_context Ax Psi),
    X = Y <-> forall p, fmc_mem X p <-> fmc_mem Y p.
Proof.
  intros Ax Psi X Y; split.
  - intros -> p. tauto.
  - destruct X as [X Xfinite Xconsistent Xclosed].
    destruct Y as [Y Yfinite Yconsistent Yclosed]. simpl.
    intro Hext.
    assert (Hcarrier : X = Y).
    { apply functional_extensionality. intro p.
      apply propositional_extensionality. apply Hext. }
    subst Y.
    assert (Hfinite : Xfinite = Yfinite) by apply proof_irrelevance.
    subst Yfinite.
    assert (Hconsistent : Xconsistent = Yconsistent) by apply proof_irrelevance.
    subst Yconsistent.
    assert (Hclosed : Xclosed = Yclosed) by apply proof_irrelevance.
    now subst Yclosed.
Qed.

Theorem finite_context_lindenbaum :
  forall Ax Phi Psi,
    list_subset Phi (complementary Psi) ->
    finite_consistent Ax Phi ->
    exists X : finite_maximal_context Ax Psi,
      forall p, In p Phi -> fmc_mem X p.
Proof.
  intros Ax Phi Psi Hsub Hconsistent.
  destruct (@finite_exists_consistent_complementary_closed
    Ax Phi Psi Hsub Hconsistent) as [P [HP [Hcons Hclosed]]].
  exists {| fmc_carrier := finite_theory P;
            fmc_finite :=
              ex_intro _ P (fun p => @iff_refl (In p P));
            fmc_consistent := Hcons;
            fmc_closed :=
              {| predicate_closed_subset :=
                   complementary_closed_subset Hclosed;
                 predicate_closed_either :=
                   complementary_closed_either Hclosed |} |}.
  exact HP.
Qed.

Theorem finite_maximal_context_inhabited :
  forall Ax Psi,
    normal_system_consistent Ax ->
    exists X : finite_maximal_context Ax Psi, True.
Proof.
  intros Ax Psi Hsystem.
  destruct (@finite_context_lindenbaum Ax [] Psi) as [X HX].
  - unfold list_subset. simpl. tauto.
  - now apply finite_empty_consistent.
  - now exists X.
Qed.

Lemma fmc_membership_iff_derivable :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p Psi ->
    (fmc_mem X p <-> normal_derives Ax (fmc_mem X) p).
Proof.
  intros Ax Psi X p Hp; split.
  - intro Hmem. now apply ND_assumption.
  - intro Hder.
    destruct (@predicate_closed_either (fmc_mem X) Psi
      (@fmc_closed Ax Psi X) p Hp)
      as [Hmem | Hcomp]; [exact Hmem |].
    exfalso. apply (@fmc_consistent Ax Psi X).
    eapply normal_derives_complement_bottom.
    + exact Hder.
    + now apply ND_assumption.
Qed.

Lemma fmc_mem_top :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    In Top Psi -> fmc_mem X Top.
Proof.
  intros Ax Psi X Htop.
  apply (proj2 (@fmc_membership_iff_derivable Ax Psi X Top Htop)).
  apply ND_theorem. unfold Top, Neg. apply normal_proves_identity.
Qed.

Lemma fmc_bottom_absent :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    ~ fmc_mem X Bottom.
Proof.
  intros Ax Psi X Hbottom. apply (@fmc_consistent Ax Psi X).
  now apply ND_assumption.
Qed.

Lemma fmc_mem_iff_not_mem_complement :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p Psi ->
    (fmc_mem X p <-> ~ fmc_mem X (complement p)).
Proof.
  intros Ax Psi X p Hp; split.
  - intros Hmem Hcomp. apply (@fmc_consistent Ax Psi X).
    eapply normal_derives_complement_bottom.
    + exact (@ND_assumption Ax (fmc_mem X) p Hmem).
    + exact (@ND_assumption Ax (fmc_mem X) (complement p) Hcomp).
  - now apply fmc_mem_of_not_mem_complement.
Qed.

Lemma fmc_not_mem_iff_mem_complement :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p Psi ->
    (~ fmc_mem X p <-> fmc_mem X (complement p)).
Proof.
  intros Ax Psi X p Hp; split.
  - now apply fmc_mem_complement_of_not_mem.
  - intros Hcomp Hmem. apply (@fmc_consistent Ax Psi X).
    eapply normal_derives_complement_bottom.
    + exact (@ND_assumption Ax (fmc_mem X) p Hmem).
    + exact (@ND_assumption Ax (fmc_mem X) (complement p) Hcomp).
Qed.

Lemma fmc_mem_imp_iff :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p q,
    In (Imp p q) Psi -> In p Psi -> In q Psi ->
    (fmc_mem X (Imp p q) <->
      (fmc_mem X p -> ~ fmc_mem X (complement q))).
Proof.
  intros Ax Psi X p q Himp Hp Hq; split.
  - intros Hmemimp Hmemp Hcompq.
    apply (@fmc_consistent Ax Psi X).
    eapply normal_derives_complement_bottom.
    + eapply ND_mp; apply ND_assumption; eassumption.
    + now apply ND_assumption.
  - intro Hsemantic.
    apply (proj2 (@fmc_membership_iff_derivable Ax Psi X
      (Imp p q) Himp)).
    destruct (@predicate_closed_either (fmc_mem X) Psi
      (@fmc_closed Ax Psi X) p Hp)
      as [Hmemp | Hcompp].
    + apply normal_derives_imply_intro.
      apply ND_assumption.
      apply fmc_mem_of_not_mem_complement; [exact Hq |].
      exact (Hsemantic Hmemp).
    + eapply ND_mp.
      * apply ND_theorem. apply normal_proves_neg_imply.
      * now apply normal_derives_neg_of_complement, ND_assumption.
Qed.

Lemma fmc_not_mem_imp_iff :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p q,
    In (Imp p q) Psi -> In p Psi -> In q Psi ->
    (~ fmc_mem X (Imp p q) <->
      fmc_mem X p /\ fmc_mem X (complement q)).
Proof.
  intros Ax Psi X p q Himp Hp Hq; split.
  - intro Hnot.
    assert (Hmemp : fmc_mem X p).
    { destruct (@predicate_closed_either (fmc_mem X) Psi
        (@fmc_closed Ax Psi X) p Hp)
        as [Hmemp | Hcompp]; [exact Hmemp |].
      exfalso. apply Hnot.
      apply (proj2 (@fmc_membership_iff_derivable Ax Psi X
        (Imp p q) Himp)).
      eapply ND_mp.
      - apply ND_theorem. apply normal_proves_neg_imply.
      - now apply normal_derives_neg_of_complement, ND_assumption. }
    split; [exact Hmemp |].
    destruct (@predicate_closed_either (fmc_mem X) Psi
      (@fmc_closed Ax Psi X) q Hq)
      as [Hmemq | Hcompq]; [|exact Hcompq].
    exfalso. apply Hnot.
    apply (proj2 (@fmc_membership_iff_derivable Ax Psi X
      (Imp p q) Himp)).
    apply normal_derives_imply_intro. now apply ND_assumption.
  - intros [Hmemp Hcompq] Hmemimp.
    apply (proj1 (@fmc_mem_imp_iff Ax Psi X p q Himp Hp Hq)
      Hmemimp Hmemp Hcompq).
Qed.

(** * An explicit finite cover of the context space *)

Fixpoint finite_powerset {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: rest =>
      let ps := finite_powerset rest in ps ++ map (cons x) ps
  end.

Lemma finite_powerset_contains_filter :
  forall (A : Type) (select : A -> bool) xs,
    In (filter select xs) (finite_powerset xs).
Proof.
  intros A select xs. induction xs as [|x xs IH]; simpl.
  - now left.
  - destruct (select x) eqn:Hx; simpl.
    + apply in_or_app. right. now apply in_map.
    + apply in_or_app. now left.
Qed.

Definition formula_nat_eq_dec :
  forall p q : formula nat, {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition fmc_mem_dec Ax Psi (X : finite_maximal_context Ax Psi)
    (p : formula nat) : {fmc_mem X p} + {~ fmc_mem X p}.
Proof.
  exact (excluded_middle_informative (fmc_mem X p)).
Defined.

Definition fmc_selector Ax Psi (X : finite_maximal_context Ax Psi)
    (p : formula nat) : bool :=
  if fmc_mem_dec X p then true else false.

Definition fmc_representative Ax Psi
    (X : finite_maximal_context Ax Psi) : list (formula nat) :=
  filter (fmc_selector X) (complementary Psi).

Lemma fmc_representative_spec :
  forall Ax Psi (X : finite_maximal_context Ax Psi) p,
    In p (fmc_representative X) <-> fmc_mem X p.
Proof.
  intros Ax Psi X p. unfold fmc_representative.
  rewrite filter_In. unfold fmc_selector.
  destruct (fmc_mem_dec X p) as [Hmem | Hnot]; simpl.
  - split.
    + intros Hselected. exact Hmem.
    + intros Hselected. split.
      * exact (@predicate_closed_subset (fmc_mem X) Psi
          (@fmc_closed Ax Psi X) p Hmem).
      * reflexivity.
  - split.
    + intros [_ Hfalse]. discriminate.
    + contradiction.
Qed.

Definition finite_context_candidate Ax Psi (carrier : list (formula nat))
    : option (finite_maximal_context Ax Psi).
Proof.
  destruct (excluded_middle_informative
    (normal_theory_consistent Ax (finite_theory carrier) /\
     predicate_complementary_closed (finite_theory carrier) Psi))
    as [[Hconsistent Hclosed] | Hbad].
  - exact (Some
      {| fmc_carrier := finite_theory carrier;
         fmc_finite :=
           ex_intro _ carrier (fun p => @iff_refl (In p carrier));
         fmc_consistent := Hconsistent;
         fmc_closed := Hclosed |}).
  - exact None.
Defined.

Definition option_list {A : Type} (x : option A) : list A :=
  match x with Some y => [y] | None => [] end.

Definition finite_maximal_context_cover Ax Psi
    : list (finite_maximal_context Ax Psi) :=
  flat_map
    (fun carrier => option_list (finite_context_candidate Ax Psi carrier))
    (finite_powerset (complementary Psi)).

Lemma finite_context_candidate_complete :
  forall Ax Psi carrier,
    normal_theory_consistent Ax (finite_theory carrier) ->
    predicate_complementary_closed (finite_theory carrier) Psi ->
    exists X,
      finite_context_candidate Ax Psi carrier = Some X /\
      forall p, fmc_mem X p <-> In p carrier.
Proof.
  intros Ax Psi carrier Hconsistent Hclosed.
  unfold finite_context_candidate.
  destruct (excluded_middle_informative
    (normal_theory_consistent Ax (finite_theory carrier) /\
     predicate_complementary_closed (finite_theory carrier) Psi))
    as [Hgood | Hbad].
  - destruct Hgood as [Hgood_consistent Hgood_closed].
    eexists. split; [reflexivity |]. intro p. reflexivity.
  - exfalso. apply Hbad. now split.
Qed.

Theorem finite_maximal_context_explicit_cover :
  forall Ax Psi (X : finite_maximal_context Ax Psi),
    In X (finite_maximal_context_cover Ax Psi).
Proof.
  intros Ax Psi X.
  set (carrier := fmc_representative X).
  assert (Hcarrier : forall p, finite_theory carrier p <-> fmc_mem X p).
  { intro p. unfold finite_theory, carrier.
    apply fmc_representative_spec. }
  assert (Hconsistent :
      normal_theory_consistent Ax (finite_theory carrier)).
  { apply (proj2 (@normal_theory_consistent_extensional Ax
      (finite_theory carrier) (fmc_mem X) Hcarrier)).
    exact (@fmc_consistent Ax Psi X). }
  assert (Hclosed :
      predicate_complementary_closed (finite_theory carrier) Psi).
  { constructor.
    - intros p Hp. apply (@predicate_closed_subset (fmc_mem X) Psi
        (@fmc_closed Ax Psi X) p).
      now apply (proj1 (Hcarrier p)).
    - intros p Hp.
      destruct (@predicate_closed_either (fmc_mem X) Psi
        (@fmc_closed Ax Psi X) p Hp)
        as [H | H].
      + left. now apply (proj2 (Hcarrier p)).
      + right. now apply (proj2 (Hcarrier (complement p))). }
  destruct (@finite_context_candidate_complete Ax Psi carrier
    Hconsistent Hclosed) as [Y [Hcandidate HY]].
  assert (HYX : Y = X).
  { apply (proj2 (@fmc_equality_def Ax Psi Y X)). intro p.
    rewrite HY. apply Hcarrier. }
  subst Y.
  unfold finite_maximal_context_cover.
  apply in_flat_map. exists carrier. split.
  - unfold carrier, fmc_representative.
    apply finite_powerset_contains_filter.
  - unfold option_list. now rewrite Hcandidate; simpl; auto.
Qed.
