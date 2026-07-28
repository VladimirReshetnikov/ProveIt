(**
  The quasinormal modal logic D: its proof-theoretic core and finite
  reduction context.

  This module ports the principal results of Foundation's pinned
  [Modal/Logic/D/Basic.lean].  Foundation defines D as the least
  quasinormal sum of GL and two distinguished formulas:

    - [~ box bottom], and
    - [box (box p \/ box q) -> box p \/ box q] at atoms 0 and 1.

  Substitution generates every instance of the second formula.  As in the
  source, a substitution-free presentation then gives a compact recursor
  with just GL, P, Dz, and modus-ponens cases.

  Finite sets are represented by lists.  The list of all subsets needed by
  [dzSubformula] is [finite_powerset]; repetitions in the source subformula
  list are harmless because every theorem below is extensional in list
  membership.  The second half constructs Foundation's infinite tail model,
  proves its semantic properties, and derives the exact finite reduction of
  D to GL, including the strict hierarchy GL < D < S.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence Loeb Preservation NormalHilbert
  HilbertKSoundness LogicInfrastructure GLGrzDerivations GLIndependence
  Filtration FrameProperties Root
  FrameTransformations FiniteMaximalContext FiniteCanonicalSupport
  CanonicalGL QuasiNormalS.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Definition and primitive generators *)

(** Foundation's binary axiom [Dz]. *)
Definition Dz {AtomType : Type} (p q : formula AtomType)
    : formula AtomType :=
  Imp (Box (Or (Box p) (Box q))) (Or (Box p) (Box q)).

(** The exact two-element right summand used by Foundation's definition.
    Closure under substitution belongs to the generated quasinormal sum,
    rather than to this atomic predicate. *)
Definition D_atomic_axiom : modal_logic_set nat :=
  fun p =>
    p = P \/
    p = Dz (Atom 0) (Atom 1).

(** Foundation [Modal.D].  This is unrelated to the normal serial logic
    [KD_proves]; the short name D here follows the pinned quasinormal source. *)
Definition D_proves : modal_logic_set nat :=
  logic_sum_quasi_normal (@GL_proves nat) D_atomic_axiom.

(** Foundation's [Modal.D.IsQuasiNormal] instance. *)
Theorem D_quasi_normal : quasi_normal_logic D_proves.
Proof.
  unfold D_proves.
  apply logic_sum_quasi_normal_quasi_left.
  exact (normal_quasi GL_normal_logic).
Qed.

Definition D_classical_logic : classical_logic D_proves :=
  quasi_classical D_quasi_normal.

(** The canonical inclusion [GL <= D]. *)
Theorem GL_weaker_than_D : logic_subset (@GL_proves nat) D_proves.
Proof.
  intros p Hp. now apply LSQ_mem_left.
Qed.

(** Foundation's P instance. *)
Theorem D_proves_P : D_proves (@P nat).
Proof.
  apply LSQ_mem_right. unfold D_atomic_axiom. now left.
Qed.

(** The distinguished atomic Dz generator. *)
Theorem D_proves_atomic_Dz :
  D_proves (Dz (Atom 0) (Atom 1)).
Proof.
  apply LSQ_mem_right. unfold D_atomic_axiom. now right.
Qed.

(** Foundation [D.mem_axiomDz].  Every Dz instance is obtained by one
    substitution from the distinguished atoms. *)
Theorem D_proves_Dz :
  forall p q : formula nat, D_proves (Dz p q).
Proof.
  intros p q.
  pose proof
    (LSQ_substitute
      (fun n : nat => match n with 0 => p | _ => q end)
      D_proves_atomic_Dz) as Hsub.
  change (D_proves (Dz p q)) in Hsub.
  exact Hsub.
Qed.

(** A named form of D's structural substitution rule. *)
Theorem D_proves_substitute :
  forall (sigma : nat -> formula nat) p,
    D_proves p -> D_proves (substitute sigma p).
Proof.
  intros sigma p Hp. now apply LSQ_substitute.
Qed.

(** The first strict inclusion in Foundation's hierarchy. *)
Theorem GL_strictly_weaker_D :
  logic_strictly_weaker (@GL_proves nat) D_proves.
Proof.
  split.
  - exact GL_weaker_than_D.
  - exists (@P nat); split.
    + exact D_proves_P.
    + exact (GL_unprovable_notbox (p := @Bottom nat)).
Qed.

(** * A substitution-free presentation and recursor *)

Module DDerivationInternal.

Inductive derives : formula nat -> Prop :=
| derives_GL : forall p, GL_proves p -> derives p
| derives_P : derives P
| derives_Dz : forall p q, derives (Dz p q)
| derives_mp : forall p q,
    derives (Imp p q) -> derives p -> derives q.

Lemma derives_substitute :
  forall p, derives p ->
  forall sigma : nat -> formula nat, derives (substitute sigma p).
Proof.
  intros p Hp; induction Hp; intro sigma.
  - apply derives_GL.
    eapply (@normal_proves_substitute schema_L
      schema_L_substitution_closed nat nat sigma p).
    exact H.
  - change (derives P). apply derives_P.
  - change (derives (Dz (substitute sigma p) (substitute sigma q))).
    apply derives_Dz.
  - simpl. eapply derives_mp; eauto.
Qed.

Lemma derives_to_D : forall p, derives p -> D_proves p.
Proof.
  intros p Hp; induction Hp.
  - now apply GL_weaker_than_D.
  - exact D_proves_P.
  - now apply D_proves_Dz.
  - eapply LSQ_mp; eassumption.
Qed.

Lemma D_to_derives : forall p, D_proves p -> derives p.
Proof.
  intros p Hp; induction Hp.
  - now apply derives_GL.
  - unfold D_atomic_axiom in H. destruct H as [-> | ->].
    + apply derives_P.
    + apply derives_Dz.
  - eapply derives_mp; eassumption.
  - now apply derives_substitute.
Qed.

End DDerivationInternal.

(** The source-equivalent derivation characterization. *)
Theorem D_derivation_iff :
  forall p, D_proves p <-> DDerivationInternal.derives p.
Proof.
  intro p; split.
  - apply DDerivationInternal.D_to_derives.
  - apply DDerivationInternal.derives_to_D.
Qed.

(** Foundation [Modal.D.rec'].  Substitution has been normalized into the
    GL and arbitrary-Dz cases. *)
Theorem D_proves_induction :
  forall (Q : formula nat -> Prop),
    (forall p, GL_proves p -> Q p) ->
    Q P ->
    (forall p q, Q (Dz p q)) ->
    (forall p q, Q (Imp p q) -> Q p -> Q q) ->
    forall p, D_proves p -> Q p.
Proof.
  intros Q HGL HP HDz Hmp p Hp.
  apply DDerivationInternal.D_to_derives in Hp.
  induction Hp.
  - now apply HGL.
  - exact HP.
  - now apply HDz.
  - eapply Hmp; eassumption.
Qed.

Definition D_rec := D_proves_induction.

(** * Finite disjunction support *)

(** The standard right-associated finite disjunction, with falsity at the
    empty list.  It is the list presentation of Foundation's [List.disj]. *)
Fixpoint D_list_disj (Gamma : list (formula nat)) : formula nat :=
  match Gamma with
  | [] => Bottom
  | p :: rest => Or p (D_list_disj rest)
  end.

Definition D_boxed_list_disj (Gamma : list (formula nat)) : formula nat :=
  D_list_disj (map Box Gamma).

(** The finite/list instance of Dz used throughout the reduction. *)
Definition D_list_Dz (Gamma : list (formula nat)) : formula nat :=
  Imp (Box (D_boxed_list_disj Gamma)) (D_boxed_list_disj Gamma).

(** Two elementary classical rules kept local to this development. *)
Lemma D_logic_or_mono :
  forall (L : modal_logic_set nat), classical_logic L ->
  forall p p' q q',
    L (Imp p p') -> L (Imp q q') ->
    L (Imp (Or p q) (Or p' q')).
Proof.
  intros L Hclass p p' q q' Hpp Hqq.
  eapply (logic_modus_ponens Hclass); [|exact Hqq].
  eapply (logic_modus_ponens Hclass); [|exact Hpp].
  apply (logic_classical_tautology Hclass).
  intro rho. unfold Or, Neg; simpl; tauto.
Qed.

Lemma D_logic_or_cases :
  forall (L : modal_logic_set nat), classical_logic L ->
  forall p q r,
    L (Imp p r) -> L (Imp q r) -> L (Imp (Or p q) r).
Proof.
  intros L Hclass p q r Hpr Hqr.
  eapply (logic_modus_ponens Hclass); [|exact Hqr].
  eapply (logic_modus_ponens Hclass); [|exact Hpr].
  apply (logic_classical_tautology Hclass).
  intro rho. unfold Or, Neg; simpl; tauto.
Qed.

(** Normal box collects a disjunction of boxes into the box of a
    disjunction. *)
Lemma D_logic_box_or_collect :
  forall (L : modal_logic_set nat), normal_logic L ->
  forall p q,
    L (Imp (Or (Box p) (Box q)) (Box (Or p q))).
Proof.
  intros L Hnormal p q.
  pose proof (quasi_classical (normal_quasi Hnormal)) as Hclass.
  apply D_logic_or_cases; [exact Hclass | |].
  - apply logic_box_regularity; [exact Hnormal |].
    apply (logic_classical_tautology Hclass).
    intro rho. unfold Or, Neg; simpl; tauto.
  - apply logic_box_regularity; [exact Hnormal |].
    apply (logic_classical_tautology Hclass).
    intro rho. unfold Or, Neg; simpl; tauto.
Qed.

(** Foundation [GL.box_disj_Tc].  Transitivity turns every boxed disjunct
    into its doubly boxed form, after which normality collects the finite
    disjunction. *)
Theorem GL_proves_boxed_list_disj_Four :
  forall Gamma,
    GL_proves
      (Imp (D_boxed_list_disj Gamma)
           (Box (D_boxed_list_disj Gamma))).
Proof.
  intro Gamma; induction Gamma as [|p Gamma IH].
  - cbn [D_boxed_list_disj D_list_disj].
    apply (logic_classical_tautology GL_classical_logic).
    intro rho; simpl; tauto.
  - cbn [D_boxed_list_disj D_list_disj] in IH |- *.
    set (A := D_list_disj (map Box Gamma)) in IH |- *.
    assert (Hmono :
      GL_proves
        (Imp (Or (Box p) A) (Or (Box (Box p)) (Box A)))).
    { apply D_logic_or_mono; [exact GL_classical_logic | |].
      - apply GL_proves_Four.
      - exact IH. }
    exact
      (logic_imp_trans GL_classical_logic Hmono
        (D_logic_box_or_collect GL_normal_logic (Box p) A)).
Qed.

(** Foundation [D.ldisj_axiomDz], with lists serving for both the source's
    list and finite-set variants.  The proof uses GL only for the step that
    must be necessitated; the induction hypothesis is used propositionally
    inside quasinormal D. *)
Theorem D_proves_list_Dz :
  forall Gamma, D_proves (D_list_Dz Gamma).
Proof.
  intro Gamma; induction Gamma as [|p Gamma IH].
  - cbn [D_list_Dz D_boxed_list_disj D_list_disj].
    exact D_proves_P.
  - cbn [D_list_Dz D_boxed_list_disj D_list_disj] in IH |- *.
    set (A := D_list_disj (map Box Gamma)) in *.
    assert (Hlift : GL_proves (Imp A (Box A))).
    { subst A. exact (GL_proves_boxed_list_disj_Four Gamma). }
    assert (Hinside :
      GL_proves (Imp (Or (Box p) A) (Or (Box p) (Box A)))).
    { apply D_logic_or_mono; [exact GL_classical_logic | |].
      - apply logic_identity. exact GL_classical_logic.
      - exact Hlift. }
    assert (Hpre :
      GL_proves
        (Imp (Box (Or (Box p) A))
             (Box (Or (Box p) (Box A))))).
    { exact (logic_box_regularity GL_normal_logic Hinside). }
    assert (Hpost :
      D_proves (Imp (Or (Box p) (Box A)) (Or (Box p) A))).
    { apply D_logic_or_mono; [exact D_classical_logic | |].
      - apply logic_identity. exact D_classical_logic.
      - exact IH. }
    assert (Hmiddle :
      D_proves
        (Imp (Box (Or (Box p) (Box A)))
             (Or (Box p) A))).
    { exact
        (logic_imp_trans D_classical_logic
          (D_proves_Dz p A) Hpost). }
    exact
      (logic_imp_trans D_classical_logic
        (GL_weaker_than_D Hpre) Hmiddle).
Qed.

(** The singleton instance is [box box p -> box p].  Foundation names this
    theorem [D.axiomFour]; [C4] is the local syntax name for the exact
    formula, avoiding confusion with transitivity's converse direction. *)
Theorem D_proves_C4 :
  forall p : formula nat, D_proves (C4 p).
Proof.
  intro p.
  pose proof (D_proves_list_Dz [p]) as Hsingleton.
  cbn [D_list_Dz D_boxed_list_disj D_list_disj] in Hsingleton.
  assert (Hleft : GL_proves (Imp (Box p) (Or (Box p) Bottom))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Or, Neg; simpl; tauto. }
  assert (Hpre :
    GL_proves
      (Imp (Box (Box p)) (Box (Or (Box p) Bottom)))).
  { exact (logic_box_regularity GL_normal_logic Hleft). }
  assert (Hpost : GL_proves (Imp (Or (Box p) Bottom) (Box p))).
  { apply (logic_classical_tautology GL_classical_logic).
    intro rho. unfold Or, Neg; simpl; tauto. }
  unfold C4.
  eapply logic_imp_trans; [exact D_classical_logic | |].
  - exact (GL_weaker_than_D Hpre).
  - eapply logic_imp_trans; [exact D_classical_logic | |].
    + exact Hsingleton.
    + exact (GL_weaker_than_D Hpost).
Qed.

(** Source-facing aliases for the finite Dz theorem and converse-Four
    consequence. *)
Definition D_ldisj_axiomDz := D_proves_list_Dz.
Definition D_fdisj_axiomDz := D_proves_list_Dz.
Definition D_axiomFour := D_proves_C4.

(** * The finite dz-subformula context *)

(** Foundation [Formula.dzSubformula].  The preimage of the subformula list
    under box is [formula_list_unbox]; [finite_powerset] enumerates every
    list subset needed by the semantic filter argument. *)
Definition D_dz_subformula_list (p : formula nat)
    : list (formula nat) :=
  map D_list_Dz
    (finite_powerset (formula_list_unbox (subformulas p))).

Definition D_dz_subformula_conj (p : formula nat) : formula nat :=
  logic_list_conj (D_dz_subformula_list p).

(** Extensional membership interface used by the later tail-model proof. *)
Theorem D_dz_subformula_list_spec :
  forall p q,
    In q (D_dz_subformula_list p) <->
    exists Gamma,
      In Gamma (finite_powerset (formula_list_unbox (subformulas p))) /\
      q = D_list_Dz Gamma.
Proof.
  intros p q. unfold D_dz_subformula_list.
  rewrite in_map_iff. split.
  - intros [Gamma [Hq Hmem]]. exists Gamma. split; [exact Hmem |].
    now symmetry.
  - intros [Gamma [Hmem ->]]. exists Gamma. now split.
Qed.

Theorem D_proves_dz_subformula_member :
  forall p q,
    In q (D_dz_subformula_list p) -> D_proves q.
Proof.
  intros p q Hq.
  apply D_dz_subformula_list_spec in Hq.
  destruct Hq as [Gamma [_ ->]].
  apply D_proves_list_Dz.
Qed.

(** Every finite Dz condition in the reduction context is a D theorem, so
    their finite conjunction is a D theorem as well. *)
Theorem D_proves_dz_subformula_conj :
  forall p, D_proves (D_dz_subformula_conj p).
Proof.
  intro p. unfold D_dz_subformula_conj.
  apply logic_list_conj_intro.
  - exact D_classical_logic.
  - intros q Hq. exact (@D_proves_dz_subformula_member p q Hq).
Qed.

(** Familiar source aliases. *)
Definition D_axiomP := D_proves_P.
Definition D_mem_axiomDz := D_proves_Dz.

(** * The infinite tail frame *)

(** Foundation obtains converse well-foundedness of every finite transitive
    irreflexive frame through a type-class instance.  The local list-cover
    theorem is already stronger because it needs no finite-type packaging. *)
Definition D_finite_transitive_irreflexive_cwf :=
  finite_transitive_irreflexive_cwf.

(** A named three-way sum is substantially easier to reason about in Coq
    than the source's nested [Unit + nat + World]. *)
Inductive D_tail_world (W : Type) : Type :=
| D_tail_top : D_tail_world W
| D_tail_nat : nat -> D_tail_world W
| D_tail_original : W -> D_tail_world W.

Arguments D_tail_top {W}.
Arguments D_tail_nat {W} _.
Arguments D_tail_original {W} _.

Definition D_tail_rel (F : frame)
    (x y : D_tail_world (World F)) : Prop :=
  match x, y with
  | _, D_tail_top => False
  | D_tail_top, D_tail_nat _ => True
  | D_tail_top, D_tail_original _ => True
  | D_tail_nat i, D_tail_nat j => j < i
  | D_tail_nat _, D_tail_original _ => True
  | D_tail_original _, D_tail_nat _ => False
  | D_tail_original u, D_tail_original v => Rel F u v
  end.

Definition D_tail_frame (F : frame) : frame :=
  {| World := D_tail_world (World F);
     Rel := @D_tail_rel F |}.

Definition D_tail_root {F : frame} : World (D_tail_frame F) :=
  D_tail_top.

Definition D_tail_embed_nat {F : frame} (n : nat)
    : World (D_tail_frame F) := D_tail_nat n.

Definition D_tail_embed_original {F : frame} (x : World F)
    : World (D_tail_frame F) := D_tail_original x.

Definition D_tail_valuation {AtomType : Type} {F : frame}
    (V : valuation AtomType F) (r : World F) (o : AtomType -> Prop)
    : valuation AtomType (D_tail_frame F) :=
  fun a x =>
    match x with
    | D_tail_top => o a
    | D_tail_nat _ => V a r
    | D_tail_original y => V a y
    end.

Arguments D_tail_valuation {AtomType F} V r o.

(** The new point is the unique root. *)
Theorem D_tail_rooted :
  forall F, frame_root (D_tail_frame F) D_tail_root.
Proof.
  intros F [|n|x] Hneq; cbn [D_tail_root D_tail_frame D_tail_rel].
  - contradiction.
  - constructor.
  - constructor.
Qed.

Theorem D_tail_point_rooted :
  forall F, frame_point_rooted (D_tail_frame F).
Proof.
  intro F. exists D_tail_root; split.
  - apply D_tail_rooted.
  - intros [|n|x] Hroot; [reflexivity | |].
    + exfalso.
      specialize (Hroot D_tail_root).
      assert (D_tail_root <> @D_tail_nat (World F) n) by discriminate.
      specialize (Hroot H). exact Hroot.
    + exfalso.
      specialize (Hroot D_tail_root).
      assert (D_tail_root <> @D_tail_original (World F) x) by discriminate.
      specialize (Hroot H). exact Hroot.
Qed.

Theorem D_tail_transitive :
  forall F,
    frame_transitive F -> frame_transitive (D_tail_frame F).
Proof.
  intros F Htrans [|i|x] [|j|y] [|k|z];
    cbn [D_tail_frame D_tail_rel Rel]; intros Hxy Hyz;
    try contradiction; try constructor; try lia.
  eapply Htrans; eauto.
Qed.

(** Least-number support for the natural part of the tail. *)
Lemma D_inhabited_nat_predicate_has_least :
  forall X : nat -> Prop,
    (exists n, X n) ->
    exists m, X m /\ forall k, k < m -> ~ X k.
Proof.
  intros X [n Hn]. revert Hn.
  induction n using lt_wf_ind.
  intro Hn.
  destruct (classic (exists k, k < n /\ X k))
    as [[k [Hkn Hk]] | Hnone].
  - exact (H k Hkn Hk).
  - exists n; split; [exact Hn |].
    intros k Hkn Hk. apply Hnone. now exists k.
Qed.

(** Foundation's converse-well-founded tail instance.  Original worlds are
    handled first, then the least selected natural, and finally the top. *)
Theorem D_tail_converse_well_founded :
  forall F,
    frame_converse_well_founded F ->
    frame_converse_well_founded (D_tail_frame F).
Proof.
  intros F Hcwf X [w Hw].
  destruct (classic (exists x : World F, X (D_tail_original x)))
    as [Horiginal | Hno_original].
  - destruct (Hcwf (fun x => X (D_tail_original x)) Horiginal)
      as [m [Hm Hmax]].
    exists (D_tail_original m); split; [exact Hm |].
    intros [|n|y] Hy; cbn [D_tail_frame D_tail_rel].
    + tauto.
    + tauto.
    + exact (Hmax y Hy).
  - destruct (classic (exists n : nat, X (D_tail_nat n)))
      as [Hnat | Hno_nat].
    + destruct (D_inhabited_nat_predicate_has_least
        (X := fun n => X (D_tail_nat n)) Hnat)
        as [m [Hm Hleast]].
      exists (D_tail_nat m); split; [exact Hm |].
      intros [|n|y] Hy; cbn [D_tail_frame D_tail_rel].
      * tauto.
      * intro Hnm. exact (Hleast n Hnm Hy).
      * intro Hrel. apply Hno_original. now exists y.
    + assert (Htop : X D_tail_top).
      { destruct w as [|n|x]; [exact Hw | |].
        - exfalso. apply Hno_nat. now exists n.
        - exfalso. apply Hno_original. now exists x. }
      exists D_tail_top; split; [exact Htop |].
      intros [|n|y] Hy; cbn [D_tail_frame D_tail_rel].
      * tauto.
      * intro Hrel. apply Hno_nat. now exists n.
      * intro Hrel. apply Hno_original. now exists y.
Qed.

(** The original model embeds as a generated submodel of its tail. *)
Definition D_tail_original_p_morphism (F : frame)
    : p_morphism F (D_tail_frame F).
Proof.
  refine {| pmap := @D_tail_embed_original F |}.
  - intros x y Rxy. exact Rxy.
  - intros x [|n|y] Hxy; cbn [D_tail_frame D_tail_rel] in Hxy.
    + contradiction.
    + contradiction.
    + exists y; auto.
Defined.

Theorem D_tail_original_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (o : AtomType -> Prop) x
         (p : formula AtomType),
    satisfies F V x p <->
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      (D_tail_embed_original x) p.
Proof.
  intros AtomType F V r o x p.
  exact
    (p_morphism_truth (D_tail_original_p_morphism F)
      (D_tail_valuation V r o) x p).
Qed.

(** A box true at the tail root is true at every tail world: every
    successor of any world is a non-root world and hence a root successor. *)
Theorem D_tail_box_from_root :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (o : AtomType -> Prop) (p : formula AtomType) x,
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      D_tail_root (Box p) ->
    satisfies (D_tail_frame F) (D_tail_valuation V r o) x (Box p).
Proof.
  intros AtomType F V r o p x Hroot y Hxy.
  apply Hroot. destruct y as [|n|z].
  - destruct x as [|m|u]; exact Hxy.
  - constructor.
  - constructor.
Qed.

(** * The existing finite extended roots map into the infinite tail *)

Definition D_tail_extend_root_map {F : frame} {n : nat}
    (x : World (extend_root_frame F n)) : World (D_tail_frame F) :=
  match x with
  | inl i => D_tail_nat (fin_value i)
  | inr y => D_tail_original y
  end.

Lemma D_fin_value_of_nat_lt :
  forall n k (H : k < n), fin_value (Fin.of_nat_lt H) = k.
Proof.
  intros n k H. unfold fin_value.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Definition D_tail_extend_root_p_morphism (F : frame) (n : nat)
    : p_morphism (extend_root_frame F n) (D_tail_frame F).
Proof.
  refine {| pmap := @D_tail_extend_root_map F n |}.
  - intros [i|x] [j|y] Hxy;
      exact Hxy.
  - intros [i|x] [|k|y] Hxy;
      cbn [D_tail_extend_root_map D_tail_frame D_tail_rel] in Hxy.
    + contradiction.
    + assert (Hkn : k < n).
      { eapply Nat.lt_trans; [exact Hxy |].
        unfold fin_value. exact (proj2_sig (Fin.to_nat i)). }
      set (j := Fin.of_nat_lt Hkn).
      assert (Hj : fin_value j = k).
      { unfold j. apply D_fin_value_of_nat_lt. }
      exists (inl j); split.
      * unfold D_tail_extend_root_map. simpl. now rewrite Hj.
      * simpl. now rewrite Hj.
    + exists (inr y); split; [reflexivity | constructor].
    + contradiction.
    + contradiction.
    + exists (inr y); auto.
Defined.

(** Satisfaction depends only pointwise on the valuation.  This avoids a
    function-extensionality detour when a p-morphism pullback is merely
    pointwise (rather than definitionally) the advertised valuation. *)
Lemma D_satisfies_valuation_iff :
  forall (AtomType : Type) F
         (V W : valuation AtomType F),
    (forall a x, V a x <-> W a x) ->
    forall x (p : formula AtomType),
      satisfies F V x p <-> satisfies F W x p.
Proof.
  intros AtomType F V W Hatomic x p; revert x.
  induction p as [a| |p IHp q IHq|p IHp]; intro x.
  - apply Hatomic.
  - reflexivity.
  - simpl. rewrite (IHp x), (IHq x). reflexivity.
  - split; intros Hbox y Rxy.
    + apply (proj1 (IHp y)). now apply (Hbox y).
    + apply (proj2 (IHp y)). now apply (Hbox y).
Qed.

Theorem D_tail_extend_root_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (o : AtomType -> Prop) n
         (x : World (extend_root_frame F n)) (p : formula AtomType),
    satisfies (extend_root_frame F n) (extend_root_valuation V r n) x p
    <->
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      (D_tail_extend_root_map x) p.
Proof.
  intros AtomType F V r o n x p.
  transitivity
    (satisfies (extend_root_frame F n)
      (pullback_valuation (D_tail_extend_root_p_morphism F n)
        (D_tail_valuation V r o)) x p).
  - apply D_satisfies_valuation_iff.
    intros a [i|y]; reflexivity.
  - exact
      (p_morphism_truth (D_tail_extend_root_p_morphism F n)
        (D_tail_valuation V r o) x p).
Qed.

Corollary D_tail_extend_root_original_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (o : AtomType -> Prop) n x
         (p : formula AtomType),
    satisfies (extend_root_frame F n) (extend_root_valuation V r n)
      (extend_root_embed x) p
    <->
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      (D_tail_embed_original x) p.
Proof.
  intros. apply D_tail_extend_root_truth.
Qed.

Corollary D_tail_extend_root_nat_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (o : AtomType -> Prop) n (i : Fin.t n)
         (p : formula AtomType),
    satisfies (extend_root_frame F n) (extend_root_valuation V r n)
      (extend_root_added i) p
    <->
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      (D_tail_embed_nat (fin_value i)) p.
Proof.
  intros. apply D_tail_extend_root_truth.
Qed.

(** Foundation's final [tailModel] fixes the top valuation to the original
    root valuation.  Frames and valuations are separate records locally. *)
Definition D_tail_model_valuation {AtomType : Type} {F : frame}
    (V : valuation AtomType F) (r : World F)
    : valuation AtomType (D_tail_frame F) :=
  D_tail_valuation V r (fun a => V a r).

Theorem D_tail_model_point_rooted :
  forall F, frame_point_rooted (D_tail_frame F).
Proof. exact D_tail_point_rooted. Qed.

(** * Truth support for finite subformula contexts *)

Lemma D_satisfies_list_disj :
  forall F (V : valuation nat F) w Gamma,
    satisfies F V w (D_list_disj Gamma) <->
    exists p, In p Gamma /\ satisfies F V w p.
Proof.
  intros F V w Gamma; induction Gamma as [|p Gamma IH].
  - cbn [D_list_disj]. split.
    + intro Hfalse. exfalso. exact Hfalse.
    + intros [q [Hq _]]. contradiction.
  - cbn [D_list_disj]. rewrite satisfies_or, IH. split.
    + intros [Hp | [q [Hq Hsat]]].
      * exists p. split; [now left | exact Hp].
      * exists q. split; [now right | exact Hsat].
    + intros [q [[<- | Hq] Hsat]].
      * now left.
      * right. now exists q.
Qed.

Corollary D_satisfies_boxed_list_disj :
  forall F (V : valuation nat F) w Gamma,
    satisfies F V w (D_boxed_list_disj Gamma) <->
    exists p, In p Gamma /\ satisfies F V w (Box p).
Proof.
  intros F V w Gamma. unfold D_boxed_list_disj.
  rewrite D_satisfies_list_disj. split.
  - intros [q [Hq Hsat]]. apply in_map_iff in Hq.
    destruct Hq as [p [<- Hp]]. now exists p.
  - intros [p [Hp Hsat]]. exists (Box p). split; [|exact Hsat].
    apply in_map. exact Hp.
Qed.

Lemma D_satisfies_logic_list_conj :
  forall (AtomType : Type) F (V : valuation AtomType F) w Gamma,
    satisfies F V w (logic_list_conj Gamma) <->
    Forall (satisfies F V w) Gamma.
Proof.
  intros AtomType F V w Gamma; induction Gamma as [|p Gamma IH].
  - cbn [logic_list_conj]. split.
    + intros H. constructor.
    + intros H. apply satisfies_top.
  - change
      (satisfies F V w (And p (logic_list_conj Gamma)) <->
       Forall (satisfies F V w) (p :: Gamma)).
    rewrite satisfies_and, IH, Forall_cons_iff. reflexivity.
Qed.

Definition D_T_subformula_list (p : formula nat)
    : list (formula nat) :=
  map T (formula_list_unbox (subformulas p)).

Definition D_T_subformula_conj (p : formula nat) : formula nat :=
  logic_list_conj (D_T_subformula_list p).

(** Source [of_provable_rflSubformula_original_root].  The statement is
    stronger than the source instance formulation: a designated root is
    enough, and transitivity is not needed. *)
Theorem D_tail_nat_subformula_truth :
  forall F (V : valuation nat F) (r : World F) (o : nat -> Prop)
         (target : formula nat),
    frame_root F r ->
    satisfies F V r (D_T_subformula_conj target) ->
    forall p, In p (subformulas target) -> forall i,
      satisfies F V r p <->
      satisfies (D_tail_frame F) (D_tail_valuation V r o)
        (D_tail_embed_nat i) p.
Proof.
  intros F V r o target Hroot Hcontext p Hsub.
  assert (Hcontext_all :
    forall q, In q (D_T_subformula_list target) ->
      satisfies F V r q).
  { intros q Hq.
    apply (proj1 (@D_satisfies_logic_list_conj nat F V r
      (D_T_subformula_list target))) in Hcontext.
    rewrite Forall_forall in Hcontext. now apply Hcontext. }
  induction p as [a| |p IHp q IHq|p IHp]; intro i.
  - reflexivity.
  - reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left. apply subformulas_self. }
    assert (Hsubq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right. apply subformulas_self. }
    simpl. rewrite (IHp Hsubp i), (IHq Hsubq i). reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box. apply subformulas_self. }
    assert (HT : satisfies F V r (T p)).
    { apply Hcontext_all. unfold D_T_subformula_list.
      apply in_map. apply (proj2 (formula_list_unbox_spec _ p)).
      exact Hsub. }
    split.
    + intros Hbox [|j|x] Hrel.
      * contradiction.
      * apply (proj1 (IHp Hsubp j)). apply HT. exact Hbox.
      * apply (proj1 (@D_tail_original_truth nat F V r o x p)).
        destruct (classic (x = r)) as [-> | Hneq].
        -- apply HT. exact Hbox.
        -- apply Hbox. now apply Hroot.
    + intros Htail x Rrx.
      apply (proj2 (@D_tail_original_truth nat F V r o x p)).
      apply Htail. constructor.
Qed.

(** Classical witness form for failure of box. *)
Lemma D_not_satisfies_box_exists :
  forall (AtomType : Type) F (V : valuation AtomType F) w
         (p : formula AtomType),
    ~ satisfies F V w (Box p) ->
    exists x, Rel F w x /\ ~ satisfies F V x p.
Proof.
  intros AtomType F V w p Hnot.
  apply NNPP; intro Hnone. apply Hnot.
  intros x Rwx. apply NNPP; intro Hbad.
  apply Hnone. now exists x.
Qed.

(** Any two successors of the tail root have a common predecessor which is
    itself a root successor.  This is the semantic content of Dz. *)
Lemma D_tail_root_successors_common_predecessor :
  forall F (x y : World (D_tail_frame F)),
    Rel (D_tail_frame F) D_tail_root x ->
    Rel (D_tail_frame F) D_tail_root y ->
    exists z,
      Rel (D_tail_frame F) D_tail_root z /\
      Rel (D_tail_frame F) z x /\
      Rel (D_tail_frame F) z y.
Proof.
  intros F [|i|x] [|j|y] Hx Hy;
    try contradiction.
  - exists (D_tail_nat (S (Nat.max i j))).
    cbn [D_tail_frame D_tail_rel D_tail_root].
    split; [constructor |]. split.
    + apply (proj2 (Nat.lt_succ_r i (Nat.max i j))).
      apply Nat.le_max_l.
    + apply (proj2 (Nat.lt_succ_r j (Nat.max i j))).
      apply Nat.le_max_r.
  - exists (D_tail_nat (S i)).
    cbn [D_tail_frame D_tail_rel D_tail_root].
    split; [constructor |]. split.
    + exact (Nat.lt_succ_diag_r i).
    + constructor.
  - exists (D_tail_nat (S j)).
    cbn [D_tail_frame D_tail_rel D_tail_root].
    split; [constructor |]. split.
    + constructor.
    + exact (Nat.lt_succ_diag_r j).
  - exists (D_tail_nat 0).
    cbn [D_tail_frame D_tail_rel D_tail_root]. tauto.
Qed.

(** The second member of Foundation's TFAE: validity at the root of every
    tail over a finite rooted GL frame. *)
Definition D_tail_valid (p : formula nat) : Prop :=
  forall F (V : valuation nat F) (r : World F) (o : nat -> Prop),
    finite_frame F ->
    frame_transitive F ->
    frame_irreflexive F ->
    frame_root F r ->
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      D_tail_root p.

Definition D_cwf_tail_valid (p : formula nat) : Prop :=
  forall F (V : valuation nat F) (r : World F) (o : nat -> Prop),
    frame_transitive F ->
    frame_converse_well_founded F ->
    satisfies (D_tail_frame F) (D_tail_valuation V r o)
      D_tail_root p.

(** The proof needs only transitivity and converse well-foundedness of the
    old frame.  The finite rooted formulation used in the source follows
    immediately below and is convenient for the final TFAE. *)
Theorem D_proves_sound_on_cwf_tail :
  forall p, D_proves p -> D_cwf_tail_valid p.
Proof.
  intros p Hp. revert p Hp.
  apply D_proves_induction.
  - intros p Hp F V r o Htrans Hcwf.
    eapply GL_proves_sound_on_transitive_cwf_frame.
    + now apply D_tail_transitive.
    + now apply D_tail_converse_well_founded.
    + exact Hp.
  - intros F V r o Htrans Hcwf Hbox.
    apply (Hbox (D_tail_embed_original r)). constructor.
  - intros p q F V r o Htrans Hcwf Hantecedent.
    apply (proj2 (@satisfies_or nat (D_tail_frame F)
      (D_tail_valuation V r o) D_tail_root (Box p) (Box q))).
    apply NNPP; intro Hnot_disjunction.
    assert (Hnot_p :
      ~ satisfies (D_tail_frame F) (D_tail_valuation V r o)
          D_tail_root (Box p)).
    { intro Hpbox. apply Hnot_disjunction. now left. }
    assert (Hnot_q :
      ~ satisfies (D_tail_frame F) (D_tail_valuation V r o)
          D_tail_root (Box q)).
    { intro Hqbox. apply Hnot_disjunction. now right. }
    destruct (D_not_satisfies_box_exists Hnot_p)
      as [x [Hrx Hxp]].
    destruct (D_not_satisfies_box_exists Hnot_q)
      as [y [Hry Hyq]].
    destruct (D_tail_root_successors_common_predecessor Hrx Hry)
      as [z [Hrz [Hzx Hzy]]].
    pose proof (Hantecedent z Hrz) as Hz.
    apply (proj1 (@satisfies_or nat (D_tail_frame F)
      (D_tail_valuation V r o) z (Box p) (Box q))) in Hz.
    destruct Hz as [Hzp | Hzq].
    + apply Hxp. now apply (Hzp x).
    + apply Hyq. now apply (Hzq y).
  - intros p q Himp Hp F V r o Htrans Hcwf.
    exact (Himp F V r o Htrans Hcwf (Hp F V r o Htrans Hcwf)).
Qed.

Theorem D_proves_sound_on_tail :
  forall p, D_proves p -> D_tail_valid p.
Proof.
  intros p Hp F V r o Hfinite Htrans Hirr Hroot.
  apply (@D_proves_sound_on_cwf_tail p Hp F V r o Htrans).
  now apply finite_transitive_irreflexive_cwf.
Qed.

(** The boxed subformulas which fail at a designated world.  Keeping the
    selector separate gives the finite-powerset argument a small, exact
    membership interface. *)
Definition D_failed_box_selector (F : frame) (V : valuation nat F)
    (r : World F) (q : formula nat) : bool :=
  if excluded_middle_informative
       (~ satisfies F V r (Box q))
  then true else false.

Definition D_failed_box_list (F : frame) (V : valuation nat F)
    (r : World F) (target : formula nat) : list (formula nat) :=
  filter (@D_failed_box_selector F V r)
    (formula_list_unbox (subformulas target)).

Arguments D_failed_box_selector F V r q : clear implicits.
Arguments D_failed_box_list F V r target : clear implicits.

Lemma D_failed_box_list_spec :
  forall F (V : valuation nat F) r target q,
    In q (D_failed_box_list F V r target) <->
    In (Box q) (subformulas target) /\
    ~ satisfies F V r (Box q).
Proof.
  intros F V r target q.
  unfold D_failed_box_list.
  rewrite filter_In, formula_list_unbox_spec.
  unfold D_failed_box_selector.
  destruct (excluded_middle_informative
    (~ satisfies F V r (Box q))) as [Hnot | Hnotnot]; simpl.
  - tauto.
  - split.
    + intros [_ Hfalse]. discriminate.
    + intros [_ Hnot]. contradiction.
Qed.

(** The conjunction of all finite Dz instances selects one successor at
    which every boxed subformula already failing at the root still fails.
    This is the finite common-witness step in Foundation's reduction. *)
Theorem D_failed_boxes_have_common_witness :
  forall F (V : valuation nat F) r target,
    satisfies F V r (D_dz_subformula_conj target) ->
    exists x, Rel F r x /\
      forall q,
        In q (D_failed_box_list F V r target) ->
        ~ satisfies F V x (Box q).
Proof.
  intros F V r target Hcontext.
  set (Gamma := D_failed_box_list F V r target).
  assert (HGamma :
    In Gamma
      (finite_powerset (formula_list_unbox (subformulas target)))).
  { unfold Gamma, D_failed_box_list.
    apply finite_powerset_contains_filter. }
  assert (HDzmem :
    In (D_list_Dz Gamma) (D_dz_subformula_list target)).
  { apply D_dz_subformula_list_spec.
    exists Gamma. now split. }
  assert (HDz : satisfies F V r (D_list_Dz Gamma)).
  { apply (proj1 (@D_satisfies_logic_list_conj nat F V r
      (D_dz_subformula_list target))) in Hcontext.
    rewrite Forall_forall in Hcontext. now apply Hcontext. }
  assert (Hnot_disj :
    ~ satisfies F V r (D_boxed_list_disj Gamma)).
  { intro Hdisj.
    apply D_satisfies_boxed_list_disj in Hdisj.
    destruct Hdisj as [q [Hq Hbox]].
    apply (proj1 (@D_failed_box_list_spec F V r target q)) in Hq.
    exact (proj2 Hq Hbox). }
  assert (Hnot_box_disj :
    ~ satisfies F V r (Box (D_boxed_list_disj Gamma))).
  { intro Hbox. apply Hnot_disj. exact (HDz Hbox). }
  destruct (D_not_satisfies_box_exists Hnot_box_disj)
    as [x [Hrx Hx]].
  exists x. split; [exact Hrx |].
  intros q Hq Hxq. apply Hx.
  apply (proj2 (@D_satisfies_boxed_list_disj F V x Gamma)).
  now exists q.
Qed.

(** At the selected successor, every boxed subformula satisfies reflexivity:
    either its box already holds at the old root, or it belongs to the
    failed list and cannot hold at the selected successor. *)
Lemma D_point_generated_T_subformula_context :
  forall F (V : valuation nat F) r x target,
    frame_transitive F ->
    Rel F r x ->
    (forall q,
      In q (D_failed_box_list F V r target) ->
      ~ satisfies F V x (Box q)) ->
    satisfies (point_generated_frame F x)
      (point_generated_valuation V x)
      (point_generated_root F x)
      (D_T_subformula_conj target).
Proof.
  intros F V r x target Htrans Hrx Hfailed.
  apply (proj2 (@point_generated_truth_at_root nat F V x Htrans
    (D_T_subformula_conj target))).
  apply (proj2 (@D_satisfies_logic_list_conj nat F V x
    (D_T_subformula_list target))).
  rewrite Forall_forall. intros tq Htq.
  unfold D_T_subformula_list in Htq.
  apply in_map_iff in Htq.
  destruct Htq as [q [<- Hq]].
  change (satisfies F V x (Box q) -> satisfies F V x q).
  intro Hboxx.
  destruct (classic (satisfies F V r (Box q))) as [Hboxr | Hnotboxr].
  - exact (Hboxr x Hrx).
  - exfalso. apply (Hfailed q); [|exact Hboxx].
    apply (proj2 (@D_failed_box_list_spec F V r target q)).
    split; [|exact Hnotboxr].
    now apply (proj1 (formula_list_unbox_spec _ q)).
Qed.

(** The core truth lemma.  A formula occurring below [target] has the same
    truth value at the old world [r] as at the new top of the tail over the
    point-generated model rooted at the selected successor [x]. *)
Theorem D_tail_reduction_subformula_truth :
  forall F (V : valuation nat F) r x target,
    frame_transitive F ->
    Rel F r x ->
    (forall q,
      In q (D_failed_box_list F V r target) ->
      ~ satisfies F V x (Box q)) ->
    forall p, In p (subformulas target) ->
      satisfies F V r p <->
      satisfies
        (D_tail_frame (point_generated_frame F x))
        (D_tail_valuation (point_generated_valuation V x)
          (point_generated_root F x) (fun a => V a r))
        D_tail_root p.
Proof.
  intros F V r x target Htrans Hrx Hfailed.
  assert (HTcontext :
    satisfies (point_generated_frame F x)
      (point_generated_valuation V x)
      (point_generated_root F x)
      (D_T_subformula_conj target)).
  { exact (@D_point_generated_T_subformula_context
      F V r x target Htrans Hrx Hfailed). }
  intros p Hsub.
  induction p as [a| |p IHp q IHq|p IHp].
  - reflexivity.
  - reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_left, subformulas_self. }
    assert (Hsubq : In q (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_imp_right, subformulas_self. }
    simpl. rewrite (IHp Hsubp), (IHq Hsubq). reflexivity.
  - assert (Hsubp : In p (subformulas target)).
    { eapply subformulas_trans; [exact Hsub |].
      apply subformulas_box, subformulas_self. }
    split.
    + intros Hbox [|i|y] Htail.
      * contradiction.
      * apply (proj1 (@D_tail_nat_subformula_truth
          (point_generated_frame F x)
          (point_generated_valuation V x)
          (point_generated_root F x) (fun a => V a r)
          target (@point_generated_rooted F x) HTcontext
          p Hsubp i)).
        apply (proj2 (@point_generated_truth_at_root nat F V x Htrans p)).
        exact (Hbox x Hrx).
      * apply (proj1 (@D_tail_original_truth nat
          (point_generated_frame F x)
          (point_generated_valuation V x)
          (point_generated_root F x) (fun a => V a r) y p)).
        apply (proj2 (@point_generated_truth nat F V x Htrans y p)).
        apply Hbox.
        destruct (proj2_sig y) as [-> | Hxy].
        -- exact Hrx.
        -- eapply Htrans; eauto.
    + intro Htail.
      apply NNPP. intro Hnotbox.
      assert (Hpfailed :
        In p (D_failed_box_list F V r target)).
      { apply (proj2 (@D_failed_box_list_spec F V r target p)).
        now split. }
      pose proof (Hfailed p Hpfailed) as Hnotboxx.
      destruct (D_not_satisfies_box_exists Hnotboxx)
        as [z [Hxz Hnotz]].
      set (gz := (exist _ z (or_intror Hxz) :
        World (point_generated_frame F x))).
      apply Hnotz.
      apply (proj1 (@point_generated_truth nat F V x Htrans gz p)).
      apply (proj2 (@D_tail_original_truth nat
        (point_generated_frame F x)
        (point_generated_valuation V x)
        (point_generated_root F x) (fun a => V a r) gz p)).
      apply Htail. constructor.
Qed.

(** Foundation's finite GL reduction formula and its rooted semantic
    reading. *)
Definition D_GL_reduction (p : formula nat) : formula nat :=
  Imp (D_dz_subformula_conj p) p.

Definition D_rooted_GL_reduction_valid (p : formula nat) : Prop :=
  GL_valid_on_finite_rooted_models_at_root (D_GL_reduction p).

Theorem D_tail_valid_implies_rooted_GL_reduction_valid :
  forall p,
    D_tail_valid p -> D_rooted_GL_reduction_valid p.
Proof.
  intros p Htail F V r Hfinite Htrans Hirr Hroot Hcontext.
  destruct (@D_failed_boxes_have_common_witness F V r p Hcontext)
    as [x [Hrx Hfailed]].
  unfold D_tail_valid in Htail.
  specialize (Htail
    (point_generated_frame F x)
    (point_generated_valuation V x)
    (point_generated_root F x)
    (fun a => V a r)
    (@canonical_gl_point_generated_finite F x Hfinite)
    (@point_generated_transitive F x Htrans)
    (@point_generated_irreflexive F x Hirr)
    (@point_generated_rooted F x)).
  apply (proj2 (@D_tail_reduction_subformula_truth
    F V r x p Htrans Hrx Hfailed p (subformulas_self p))).
  exact Htail.
Qed.

(** The main source-facing reduction theorem. *)
Theorem iff_provable_D_provable_GL :
  forall p : formula nat,
    D_proves p <-> GL_proves (D_GL_reduction p).
Proof.
  intro p; split.
  - intro Hp.
    apply (proj2 (GL_finite_rooted_model_sound_complete
      (D_GL_reduction p))).
    apply D_tail_valid_implies_rooted_GL_reduction_valid.
    now apply D_proves_sound_on_tail.
  - intro HGL.
    unfold D_GL_reduction in HGL.
    eapply LSQ_mp.
    + exact (GL_weaker_than_D HGL).
    + exact (D_proves_dz_subformula_conj p).
Qed.

Theorem D_proves_iff_tail_valid :
  forall p : formula nat,
    D_proves p <-> D_tail_valid p.
Proof.
  intro p; split.
  - apply D_proves_sound_on_tail.
  - intro Htail.
    apply (proj2 (iff_provable_D_provable_GL p)).
    apply (proj2 (GL_finite_rooted_model_sound_complete
      (D_GL_reduction p))).
    now apply D_tail_valid_implies_rooted_GL_reduction_valid.
Qed.

Theorem D_tail_valid_iff_rooted_GL_reduction_valid :
  forall p : formula nat,
    D_tail_valid p <-> D_rooted_GL_reduction_valid p.
Proof.
  intro p; split.
  - apply D_tail_valid_implies_rooted_GL_reduction_valid.
  - intro Hvalid.
    apply (proj1 (D_proves_iff_tail_valid p)).
    apply (proj2 (iff_provable_D_provable_GL p)).
    apply (proj2 (GL_finite_rooted_model_sound_complete
      (D_GL_reduction p))).
    exact Hvalid.
Qed.

Theorem D_rooted_GL_reduction_valid_iff_GL_proves :
  forall p : formula nat,
    D_rooted_GL_reduction_valid p <-> GL_proves (D_GL_reduction p).
Proof.
  intro p. symmetry. apply GL_finite_rooted_model_sound_complete.
Qed.

(** Coq presentation of Foundation's four-member [GL_D_TFAE].  A chain of
    adjacent equivalences is the usual propositional encoding of TFAE. *)
Theorem GL_D_TFAE :
  forall p : formula nat,
    (D_proves p <-> D_tail_valid p) /\
    (D_tail_valid p <-> D_rooted_GL_reduction_valid p) /\
    (D_rooted_GL_reduction_valid p <->
      GL_proves (D_GL_reduction p)).
Proof.
  intro p. repeat split.
  - apply (proj1 (D_proves_iff_tail_valid p)).
  - apply (proj2 (D_proves_iff_tail_valid p)).
  - apply (proj1 (D_tail_valid_iff_rooted_GL_reduction_valid p)).
  - apply (proj2 (D_tail_valid_iff_rooted_GL_reduction_valid p)).
  - apply (proj1 (D_rooted_GL_reduction_valid_iff_GL_proves p)).
  - apply (proj2 (D_rooted_GL_reduction_valid_iff_GL_proves p)).
Qed.

(** Foundation [D.unprovable_T].  On the tail over the isolated singleton,
    every non-top world makes the chosen atom true while the top makes it
    false.  Hence the atomic T instance fails at the top. *)
Theorem D_unprovable_T :
  ~ D_proves (T (Atom 0)).
Proof.
  intro HD.
  assert (Hfinite : finite_frame irreflexive_singleton_frame).
  { exists [tt]. intros []; now left. }
  assert (Hirr : frame_irreflexive irreflexive_singleton_frame).
  { intros [] Hrel. exact Hrel. }
  assert (Hroot : frame_root irreflexive_singleton_frame tt).
  { intros [] Hneq. contradiction. }
  pose proof (@D_proves_sound_on_tail (T (Atom 0)) HD
    irreflexive_singleton_frame
    (fun _ _ => True) tt (fun _ : nat => False)
    Hfinite irreflexive_singleton_transitive Hirr Hroot) as HT.
  apply HT.
  intros [|n|[]] Hrel.
  - contradiction.
  - constructor.
  - constructor.
Qed.

(** The second strict inclusion in Foundation's GL < D < S hierarchy. *)
Theorem D_weaker_than_S :
  logic_subset D_proves S_proves.
Proof.
  intros p Hp. revert p Hp.
  apply D_proves_induction.
  - intros p Hp. now apply GL_weaker_than_S.
  - exact (S_proves_T Bottom).
  - intros p q. exact (S_proves_T (Or (Box p) (Box q))).
  - intros p q Himp Hp. eapply LSQ_mp; eassumption.
Qed.

Theorem D_strictly_weaker_S :
  logic_strictly_weaker D_proves S_proves.
Proof.
  split.
  - exact D_weaker_than_S.
  - exists (T (Atom 0)); split.
    + apply S_proves_T.
    + exact D_unprovable_T.
Qed.
