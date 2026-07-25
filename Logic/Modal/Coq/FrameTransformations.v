(**
  Structural transformations of Kripke frames.

  This file ports the mathematical theorem surfaces of Foundation's pinned
  [Modal/Kripke/ExtendRoot.lean] and [Modal/Kripke/Irreflexivize.lean].
  Foundation uses [Fin n] with a positive-natural wrapper; here the carrier
  is Coq's [Fin.t n], and positivity is an explicit hypothesis only for the
  theorems that select the greatest added root.  Finite frames use the
  existing list-cover predicate from [Filtration], so cardinality statements
  are given by exact lengths of duplicate-free covers.

  Foundation's [IsTree] and [IsFiniteTree] are type-class wrappers around,
  respectively, rooted/asymmetric/transitive and rooted/finite frames.  The
  corresponding conjunctions are stated directly below.  This is the only
  representation change.  No theorem is postulated and neither pinned source
  file contains an unfinished proof.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop Logic.ClassicalChoice.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import Vectors.Fin.
From FoundationModal Require Import
  Syntax Axioms Kripke Correspondence Preservation FrameProperties Loeb Root
  Filtration.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Shared finite-list utilities *)

Lemma NoDup_map_on :
  forall (A B : Type) (f : A -> B) (xs : list A),
    NoDup xs ->
    (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
    NoDup (map f xs).
Proof.
  intros A B f xs Hnodup; induction Hnodup as [|x xs Hnotin Hnodup IH];
    intro Hinj; simpl.
  - constructor.
  - constructor.
    + intro Hmem. apply in_map_iff in Hmem.
      destruct Hmem as [y [Hfy Hy]].
      apply Hnotin.
      assert (Heqxy : x = y).
      {
        apply (Hinj x y).
        - now left.
        - now right.
        - now symmetry.
      }
      subst y.
      exact Hy.
    + apply IH. intros y z Hy Hz Heq.
      apply (Hinj y z).
      * now right.
      * now right.
      * exact Heq.
Qed.

(** An order-insensitive list formulation of a relational chain.  It is the
    exact consequence of Foundation's [List.IsChain] used by the cardinality
    arguments: distinct members are comparable. *)
Definition list_relation_chain {A : Type}
    (R : A -> A -> Prop) (xs : list A) : Prop :=
  forall x y, In x xs -> In y xs -> x <> y -> R x y \/ R y x.

Fixpoint list_is_chain {A : Type} (R : A -> A -> Prop)
    (xs : list A) : Prop :=
  match xs with
  | [] => True
  | x :: ys => (forall y, In y ys -> R x y) /\ list_is_chain R ys
  end.

Lemma list_is_chain_map :
  forall (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
         (f : A -> B) xs,
    list_is_chain R xs ->
    (forall x y, R x y -> S (f x) (f y)) ->
    list_is_chain S (map f xs).
Proof.
  intros A B R S f xs; induction xs as [|x xs IH]; simpl; intros Hchain Hmap.
  - constructor.
  - destruct Hchain as [Hhead Htail]. split.
    + intros y Hy. apply in_map_iff in Hy.
      destruct Hy as [z [Hz Hy]]. subst y. now apply Hmap, Hhead.
    + now apply IH.
Qed.

Lemma list_is_chain_app_singleton :
  forall (A : Type) (R : A -> A -> Prop) xs (a : A),
    list_is_chain R xs ->
    (forall x, In x xs -> R x a) ->
    list_is_chain R (xs ++ [a]).
Proof.
  intros A R xs; induction xs as [|x xs IH]; intros a Hchain Hall; simpl.
  - tauto.
  - destruct Hchain as [Hhead Htail]. split.
    + intros y Hy. apply in_app_iff in Hy.
      destruct Hy as [Hy | Hy].
      * now apply Hhead.
      * simpl in Hy. destruct Hy as [Hy | []].
        subst y. apply Hall. now left.
    + apply IH; [exact Htail |].
      intros y Hy. apply Hall. now right.
Qed.

Lemma list_is_chain_relation_chain :
  forall (A : Type) (R : A -> A -> Prop) xs,
    list_is_chain R xs -> list_relation_chain R xs.
Proof.
  intros A R xs; induction xs as [|x xs IH]; simpl; intros Hchain y z Hy Hz Hneq.
  - contradiction.
  - destruct Hchain as [Hhead Htail].
    destruct Hy as [-> | Hy]; destruct Hz as [-> | Hz].
    + contradiction.
    + left. now apply Hhead.
    + right. now apply Hhead.
    + now apply IH.
Qed.

Lemma list_relation_chain_sublist :
  forall (A : Type) (R : A -> A -> Prop) (xs ys : list A),
    incl xs ys -> list_relation_chain R ys -> list_relation_chain R xs.
Proof. firstorder. Qed.

(** * Irreflexivization *)

Definition irreflexivize_frame (F : frame) : frame :=
  {| World := World F;
     Rel := fun x y => Rel F x y /\ x <> y |}.

Arguments irreflexivize_frame F : clear implicits.

Lemma irreflexivize_irreflexive :
  forall F, frame_irreflexive (irreflexivize_frame F).
Proof. intros F x [_ Hneq]. exact (Hneq eq_refl). Qed.

Lemma irreflexivize_transitive :
  forall F,
    frame_antisymmetric F -> frame_transitive F ->
    frame_transitive (irreflexivize_frame F).
Proof.
  intros F Hanti Htrans x y z [Rxy Hxy] [Ryz Hyz].
  split.
  - eapply Htrans; eauto.
  - intro Hxz. subst z.
    apply Hxy. eapply Hanti; eauto.
Qed.

Lemma irreflexivize_antisymmetric :
  forall F,
    frame_antisymmetric F -> frame_antisymmetric (irreflexivize_frame F).
Proof.
  intros F Hanti x y [Rxy _] [Ryx _]. eapply Hanti; eauto.
Qed.

Lemma irreflexivize_piecewise_connected :
  forall F,
    frame_piecewise_strongly_connected F ->
    frame_piecewise_connected (irreflexivize_frame F).
Proof.
  intros F Hpiece x y z [Rxy Hxy] [Rxz Hxz].
  destruct (classic (y = z)) as [-> | Hyz]; [now right; left |].
  destruct (Hpiece x y z Rxy Rxz) as [Ryz | Rzy].
  - left; split; [exact Ryz | exact Hyz].
  - right; right; split; [exact Rzy |].
    intro Hzy. apply Hyz. now symmetry.
Qed.

Lemma irreflexivize_connected :
  forall F,
    frame_strongly_connected F -> frame_connected (irreflexivize_frame F).
Proof.
  intros F Hconnected x y.
  destruct (classic (x = y)) as [-> | Hxy]; [now right; left |].
  destruct (Hconnected x y) as [Rxy | Ryx].
  - left; split; [exact Rxy | exact Hxy].
  - right; right; split; [exact Ryx |].
    intro Hyx. apply Hxy. now symmetry.
Qed.

Lemma irreflexivize_finite_iff :
  forall F,
    finite_frame (irreflexivize_frame F) <-> finite_frame F.
Proof. intros F; unfold finite_frame; reflexivity. Qed.

(** Reflexivizing after irreflexivizing recovers every reflexive relation. *)
Lemma refl_gen_irreflexivize_rel_iff :
  forall F,
    frame_reflexive F ->
    forall x y,
      Rel (frame_refl_gen (irreflexivize_frame F)) x y <-> Rel F x y.
Proof.
  intros F Hrefl x y; split.
  - intros [-> | [Rxy _]]; [apply Hrefl | exact Rxy].
  - intro Rxy. destruct (classic (x = y)) as [-> | Hneq].
    + now left.
    + right; split; [exact Rxy | exact Hneq].
Qed.

Theorem irreflexivize_reflexive_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F),
    frame_reflexive F ->
    forall w (p : formula AtomType),
      satisfies F V w p <->
      satisfies (frame_refl_gen (irreflexivize_frame F)) V w p.
Proof.
  intros AtomType F V Hrefl w p; revert w.
  induction p as [a | | p IHp q IHq | p IHp]; intro w; simpl.
  - reflexivity.
  - tauto.
  - rewrite IHp, IHq; reflexivity.
  - split; intros Hbox u Rwu.
    + apply (proj1 (IHp u)), Hbox.
      apply (proj1 (refl_gen_irreflexivize_rel_iff Hrefl w u)); exact Rwu.
    + apply (proj2 (IHp u)), Hbox.
      apply (proj2 (refl_gen_irreflexivize_rel_iff Hrefl w u)); exact Rwu.
Qed.

Corollary irreflexivize_reflexive_valid_iff :
  forall (AtomType : Type) (F : frame) (p : formula AtomType),
    frame_reflexive F ->
    valid F p <-> valid (frame_refl_gen (irreflexivize_frame F)) p.
Proof.
  intros AtomType F p Hrefl; split; intros Hvalid V w.
  - apply (proj1 (@irreflexivize_reflexive_truth
      AtomType F V Hrefl w p)), Hvalid.
  - apply (proj2 (@irreflexivize_reflexive_truth
      AtomType F V Hrefl w p)), Hvalid.
Qed.

(** * Adding a finite chain of fresh roots *)

Definition fin_value {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Lemma fin_value_F1 :
  forall n, fin_value (@Fin.F1 n) = 0.
Proof. reflexivity. Qed.

Lemma fin_value_FS :
  forall n (i : Fin.t n), fin_value (Fin.FS i) = S (fin_value i).
Proof.
  intros n i. unfold fin_value. simpl.
  destruct (Fin.to_nat i); reflexivity.
Qed.

Definition extend_root_frame (F : frame) (n : nat) : frame :=
  {| World := (Fin.t n + World F)%type;
     Rel := fun x y =>
       match x, y with
       | inl i, inl j => fin_value j < fin_value i
       | inl _, inr _ => True
       | inr _, inl _ => False
       | inr u, inr v => Rel F u v
       end |}.

Arguments extend_root_frame F n : clear implicits.

Definition extend_root_added {F n} (i : Fin.t n)
    : World (extend_root_frame F n) := inl i.

Definition extend_root_embed {F n} (x : World F)
    : World (extend_root_frame F n) := inr x.

Lemma extend_root_world_cases :
  forall (F : frame) n (x : World (extend_root_frame F n)),
    (exists i : Fin.t n, x = extend_root_added i) \/
    (exists y : World F, x = extend_root_embed y).
Proof.
  intros F n [i | y].
  - left; now exists i.
  - right; now exists y.
Qed.

Definition extend_root_top_index (n : nat) (Hn : 0 < n) : Fin.t n :=
  Fin.of_nat_lt (p := n - 1) (n := n) (ltac:(lia)).

Arguments extend_root_top_index n Hn : clear implicits.

Definition extend_root_top (F : frame) (n : nat) (Hn : 0 < n)
    : World (extend_root_frame F n) :=
  extend_root_added (extend_root_top_index n Hn).

Arguments extend_root_top F n Hn : clear implicits.

Lemma fin_value_top_index :
  forall n (Hn : 0 < n), fin_value (extend_root_top_index n Hn) = n - 1.
Proof.
  intros n Hn. unfold fin_value, extend_root_top_index.
  now rewrite Fin.to_nat_of_nat.
Qed.

Lemma extend_root_top_no_predecessor :
  forall (F : frame) n (Hn : 0 < n) x,
    Rel (extend_root_frame F n) x (extend_root_top F n Hn) ->
    x = extend_root_top F n Hn.
Proof.
  intros F n Hn [i | x] Hrel; simpl in Hrel.
  - exfalso. rewrite fin_value_top_index in Hrel.
    assert (Hi : fin_value i < n).
    { unfold fin_value. exact (proj2_sig (Fin.to_nat i)). }
    lia.
  - contradiction.
Qed.

Lemma extend_root_top_is_root :
  forall (F : frame) n (Hn : 0 < n),
    frame_root (extend_root_frame F n) (extend_root_top F n Hn).
Proof.
  intros F n Hn [j | x] Hneq; simpl.
  - rewrite fin_value_top_index.
    assert (Hj : fin_value j < n).
    { unfold fin_value. exact (proj2_sig (Fin.to_nat j)). }
    destruct (Nat.eq_dec (fin_value j) (n - 1)) as [Heq | Heq].
    + exfalso. apply Hneq. unfold extend_root_top, extend_root_added.
      f_equal. apply Fin.to_nat_inj.
      change (fin_value j = fin_value (extend_root_top_index n Hn)).
      rewrite fin_value_top_index. exact Heq.
    + lia.
  - constructor.
Qed.

Theorem extend_root_point_rooted :
  forall (F : frame) n (Hn : 0 < n),
    frame_point_rooted (extend_root_frame F n).
Proof.
  intros F n Hn. exists (extend_root_top F n Hn); split.
  - apply extend_root_top_is_root.
  - intros s Hs.
    destruct (classic (s = extend_root_top F n Hn)) as [Heq | Hneq];
      [exact Heq |].
    exfalso.
    pose proof (Hs (extend_root_top F n Hn)) as Hpred.
    specialize (Hpred (fun Heq => Hneq (eq_sym Heq))).
    apply Hneq. now apply extend_root_top_no_predecessor in Hpred.
Qed.

Corollary extend_root_rooted :
  forall (F : frame) n (Hn : 0 < n),
    frame_rooted (extend_root_frame F n).
Proof.
  intros F n Hn. exists (extend_root_top F n Hn).
  apply extend_root_top_is_root.
Qed.

Lemma extend_root_asymmetric :
  forall F n,
    frame_asymmetric F -> frame_asymmetric (extend_root_frame F n).
Proof.
  intros F n Hasym [i | x] [j | y] Hxy; simpl in *.
  - lia.
  - tauto.
  - contradiction.
  - now apply (Hasym x y).
Qed.

Lemma extend_root_transitive :
  forall F n,
    frame_transitive F -> frame_transitive (extend_root_frame F n).
Proof.
  intros F n Htrans [i | x] [j | y] [k | z]; simpl; intros Hxy Hyz;
    try contradiction; try constructor; try lia.
  eapply Htrans; eauto.
Qed.

Lemma extend_root_irreflexive :
  forall F n,
    frame_irreflexive F -> frame_irreflexive (extend_root_frame F n).
Proof.
  intros F n Hirr [i | x]; simpl.
  - lia.
  - apply Hirr.
Qed.

Definition frame_tree_property (F : frame) : Prop :=
  frame_rooted F /\ frame_asymmetric F /\ frame_transitive F.

Definition frame_finite_tree_property (F : frame) : Prop :=
  frame_rooted F /\ finite_frame F.

Lemma extend_root_tree :
  forall F n (Hn : 0 < n),
    frame_tree_property F -> frame_tree_property (extend_root_frame F n).
Proof.
  intros F n Hn [_ [Hasym Htrans]]. split.
  - now apply extend_root_rooted.
  - split; [now apply extend_root_asymmetric | now apply extend_root_transitive].
Qed.

Lemma extend_root_embedding_p_morphism :
  forall F n, p_morphism F (extend_root_frame F n).
Proof.
  intros F n. refine {| pmap := @extend_root_embed F n |}.
  - intros x y Rxy. exact Rxy.
  - intros x [i | y] Hxy; simpl in Hxy.
    + contradiction.
    + exists y; auto.
Defined.

Lemma extend_root_embedding_injective :
  forall F n x y,
    pmap (extend_root_embedding_p_morphism F n) x =
    pmap (extend_root_embedding_p_morphism F n) y -> x = y.
Proof. intros F n x y H; now inversion H. Qed.

Definition extend_root_generated_subframe (F : frame) (n : nat)
    : generated_subframe F (extend_root_frame F n) :=
  {| generated_subframe_morphism := extend_root_embedding_p_morphism F n;
     generated_subframe_injective :=
       @extend_root_embedding_injective F n |}.

Lemma extend_root_embed_rel_iff :
  forall F n x y,
    Rel (extend_root_frame F n) (extend_root_embed x) (extend_root_embed y)
    <-> Rel F x y.
Proof. reflexivity. Qed.

Lemma extend_root_embed_rel_iter_iff :
  forall F n k x y,
    rel_iter (Rel (extend_root_frame F n)) k
      (extend_root_embed x) (extend_root_embed y) <->
    rel_iter (Rel F) k x y.
Proof.
  intros F n k x y; split.
  - intro Hpath.
    destruct (@p_morphism_back_iter F (extend_root_frame F n)
      (extend_root_embedding_p_morphism F n) k x
      (extend_root_embed y) Hpath)
      as [z [Hz Hxz]].
    inversion Hz. now subst z.
  - intro Hpath.
    exact (@p_morphism_forth_iter F (extend_root_frame F n)
      (extend_root_embedding_p_morphism F n) k x y Hpath).
Qed.

Lemma extend_root_rel_original_root :
  forall F n (Hn : 0 < n) r,
    frame_root F r ->
    Rel (extend_root_frame F n) (extend_root_top F n Hn)
      (extend_root_embed r).
Proof. intros; constructor. Qed.

Lemma extend_root_successor_not_root :
  forall F n (Hn : 0 < n),
    frame_irreflexive F ->
    forall x,
      Rel (extend_root_frame F n) (extend_root_top F n Hn) x ->
      x <> extend_root_top F n Hn.
Proof.
  intros F n Hn Hirr x Hrel Heq. subst x.
  exact ((@extend_root_irreflexive F n Hirr)
    (extend_root_top F n Hn) Hrel).
Qed.

Lemma extend_root_one_cases :
  forall F (x : World (extend_root_frame F 1)),
    x = extend_root_top F 1 (Nat.lt_0_succ 0) \/
    exists y : World F, x = extend_root_embed y.
Proof.
  intros F [i | y].
  - left. unfold extend_root_top, extend_root_added.
    f_equal. apply Fin.to_nat_inj.
    change (fin_value i =
      fin_value (extend_root_top_index 1 (Nat.lt_0_succ 0))).
    rewrite fin_value_top_index.
    assert (Hi : fin_value i < 1).
    { unfold fin_value. exact (proj2_sig (Fin.to_nat i)). }
    lia.
  - right; now exists y.
Qed.

Lemma extend_root_one_successor_is_original :
  forall F (x : World (extend_root_frame F 1)),
    Rel (extend_root_frame F 1)
      (extend_root_top F 1 (Nat.lt_0_succ 0)) x ->
    exists y : World F, x = extend_root_embed y.
Proof.
  intros F x Hrel.
  destruct (@extend_root_one_cases F x) as [-> | Horiginal];
    [simpl in Hrel; rewrite fin_value_top_index in Hrel; lia | exact Horiginal].
Qed.

Lemma extend_root_one_nonroot_is_original :
  forall F (x : World (extend_root_frame F 1)),
    x <> extend_root_top F 1 (Nat.lt_0_succ 0) ->
    exists y : World F, x = extend_root_embed y.
Proof.
  intros F x Hneq.
  destruct (@extend_root_one_cases F x) as [Heq | Horiginal];
    [contradiction | exact Horiginal].
Qed.

(** * Extended valuations and generated models *)

Definition extend_root_valuation {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F) (n : nat)
    : valuation AtomType (extend_root_frame F n) :=
  fun a x =>
    match x with
    | inl _ => V a r
    | inr y => V a y
    end.

Arguments extend_root_valuation {AtomType F} V r n.

Definition extend_root_generated_submodel {AtomType}
    (F : frame) (V : valuation AtomType F) (r : World F) (n : nat)
    : generated_submodel AtomType
        F V (extend_root_frame F n) (extend_root_valuation V r n).
Proof.
  refine {| generated_submodel_frame := extend_root_generated_subframe F n |}.
  intros a x; reflexivity.
Defined.

Theorem extend_root_embedded_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) n x (p : formula AtomType),
    satisfies (extend_root_frame F n) (extend_root_valuation V r n)
      (extend_root_embed x) p <->
    satisfies F V x p.
Proof.
  intros AtomType F V r n x p.
  symmetry.
  exact (p_morphism_truth
    (extend_root_embedding_p_morphism F n)
    (extend_root_valuation V r n) x p).
Qed.

Corollary extend_root_embedded_model_valid :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) n (p : formula AtomType),
    @model_valid AtomType (extend_root_frame F n)
      (extend_root_valuation V r n) p ->
    @model_valid AtomType F V p.
Proof.
  intros AtomType F V r n p Hvalid x.
  apply (proj1 (@extend_root_embedded_truth
    AtomType F V r n x p)).
  apply Hvalid.
Qed.

(** The boxdot translation used by Foundation's extended-root truth lemma. *)
Fixpoint boxdot_translate {AtomType} (p : formula AtomType)
    : formula AtomType :=
  match p with
  | Atom a => Atom a
  | Bottom => Bottom
  | Imp q s => Imp (boxdot_translate q) (boxdot_translate s)
  | Box q => Boxdot (boxdot_translate q)
  end.

Lemma extend_root_added_boxdot_truth :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F),
    frame_root F r ->
    forall n (i : Fin.t n) (p : formula AtomType),
      satisfies (extend_root_frame F n) (extend_root_valuation V r n)
        (extend_root_added i) (boxdot_translate p) <->
      satisfies F V r (boxdot_translate p).
Proof.
  intros AtomType F V r Hroot n i p; revert i.
  induction p as [a | | p IHp q IHq | p IHp]; intro i; simpl.
  - reflexivity.
  - tauto.
  - rewrite IHp, IHq; reflexivity.
  - split; intro Hboxdot.
    + destruct (proj1 (@satisfies_and AtomType
        (extend_root_frame F n) (extend_root_valuation V r n)
        (extend_root_added i) (boxdot_translate p)
        (Box (boxdot_translate p))) Hboxdot) as [Hlocal Hbox].
      apply (proj2 (@satisfies_and AtomType F V r
        (boxdot_translate p) (Box (boxdot_translate p)))).
      split.
      * now apply (proj1 (IHp i)).
      * intros x Rrx.
        apply (proj1 (extend_root_embedded_truth V r n x
          (boxdot_translate p))).
        apply (Hbox (extend_root_embed x)). constructor.
    + destruct (proj1 (@satisfies_and AtomType F V r
        (boxdot_translate p) (Box (boxdot_translate p))) Hboxdot)
        as [Hlocal Hbox].
      apply (proj2 (@satisfies_and AtomType
        (extend_root_frame F n) (extend_root_valuation V r n)
        (extend_root_added i) (boxdot_translate p)
        (Box (boxdot_translate p)))).
      split.
      * now apply (proj2 (IHp i)).
      * intros [j | x] Rij; simpl in Rij.
        -- now apply (proj2 (IHp j)).
        -- apply (proj2 (extend_root_embedded_truth V r n x
             (boxdot_translate p))).
           destruct (classic (x = r)) as [-> | Hneq]; [exact Hlocal |].
           apply Hbox, Hroot. exact Hneq.
Qed.

(** * Explicit finite covers and the added chain *)

Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
  match n as k return list (Fin.t k) with
  | 0 => []
  | S k => @Fin.F1 k :: map (@Fin.FS k) (fin_enum k)
  end.

Lemma fin_enum_complete :
  forall n (i : Fin.t n), In i (fin_enum n).
Proof.
  intros n i. induction i as [n | n i IH].
  - simpl; auto.
  - simpl; right. apply in_map. exact IH.
Qed.

Lemma fin_enum_length :
  forall n, length (fin_enum n) = n.
Proof.
  induction n as [|n IH]; simpl; [reflexivity |].
  now rewrite length_map, IH.
Qed.

Lemma fin_enum_nodup :
  forall n, NoDup (fin_enum n).
Proof.
  induction n as [|n IH]; simpl; constructor.
  - intro Hmem. apply in_map_iff in Hmem.
    destruct Hmem as [i [Heq _]]. discriminate Heq.
  - induction IH as [|i xs Hnotin Hnodup IHnodup]; simpl; constructor.
    + intro Hmem. apply in_map_iff in Hmem.
      destruct Hmem as [j [Heq Hj]].
      apply Hnotin. apply Fin.FS_inj in Heq. subst j. exact Hj.
    + exact IHnodup.
Qed.

Lemma fin_enum_reverse_is_descending_chain :
  forall n,
    list_is_chain
      (fun i j : Fin.t n => fin_value j < fin_value i)
      (rev (fin_enum n)).
Proof.
  induction n as [|n IH]; [simpl; constructor |].
  simpl fin_enum.
  change (list_is_chain
    (fun i j : Fin.t (S n) => fin_value j < fin_value i)
    (rev (map (@Fin.FS n) (fin_enum n)) ++ [@Fin.F1 n])).
  rewrite <- map_rev.
  apply list_is_chain_app_singleton.
  - eapply list_is_chain_map with
      (R := fun i j : Fin.t n => fin_value j < fin_value i).
    + exact IH.
    + intros i j Hij. rewrite !fin_value_FS. lia.
  - intros i Hi. apply in_map_iff in Hi.
    destruct Hi as [j [Hij _]]. subst i.
    rewrite fin_value_F1, fin_value_FS. lia.
Qed.

Definition extend_root_chain (F : frame) (n : nat)
    : list (World (extend_root_frame F n)) :=
  map (@extend_root_added F n) (rev (fin_enum n)).

Arguments extend_root_chain F n : clear implicits.

Lemma extend_root_chain_length :
  forall F n, length (extend_root_chain F n) = n.
Proof.
  intros F n. unfold extend_root_chain.
  rewrite length_map, length_rev. apply fin_enum_length.
Qed.

Lemma extend_root_chain_nodup :
  forall F n, NoDup (extend_root_chain F n).
Proof.
  intros F n. unfold extend_root_chain.
  apply NoDup_map_on.
  - apply NoDup_rev, fin_enum_nodup.
  - intros i j _ _ Heq. now inversion Heq.
Qed.

Lemma extend_root_chain_member :
  forall F n x,
    In x (extend_root_chain F n) ->
    exists i : Fin.t n, x = extend_root_added i.
Proof.
  intros F n x Hmem. unfold extend_root_chain in Hmem.
  apply in_map_iff in Hmem.
  destruct Hmem as [i [Hi _]]. exists i. now symmetry.
Qed.

Lemma extend_root_chain_is_chain :
  forall F n,
    list_relation_chain (Rel (extend_root_frame F n))
      (extend_root_chain F n).
Proof.
  intros F n x y Hx Hy Hneq.
  destruct (extend_root_chain_member Hx) as [i ->].
  destruct (extend_root_chain_member Hy) as [j ->].
  assert (Hij : i <> j).
  { intro Heq. apply Hneq. now subst j. }
  destruct (Nat.lt_trichotomy (fin_value i) (fin_value j))
    as [Hlt | [Heq | Hgt]].
  - right. exact Hlt.
  - exfalso. apply Hij, Fin.to_nat_inj. exact Heq.
  - left. exact Hgt.
Qed.

(** This is the exact ordered [List.IsChain] surface of Foundation's
    [extendRoot.chain_IsChain], using the local recursive presentation. *)
Lemma extend_root_chain_pairwise :
  forall F n,
    list_is_chain (Rel (extend_root_frame F n))
      (extend_root_chain F n).
Proof.
  intros F n. unfold extend_root_chain.
  eapply list_is_chain_map with
    (R := fun i j : Fin.t n => fin_value j < fin_value i).
  - apply fin_enum_reverse_is_descending_chain.
  - intros i j Hij. exact Hij.
Qed.

Corollary extend_root_chain_is_chain_from_pairwise :
  forall F n,
    list_relation_chain (Rel (extend_root_frame F n))
      (extend_root_chain F n).
Proof.
  intros F n. apply list_is_chain_relation_chain.
  apply extend_root_chain_pairwise.
Qed.

Definition extend_root_cover {F : frame} (n : nat)
    (xs : list (World F)) : list (World (extend_root_frame F n)) :=
  map (@extend_root_added F n) (fin_enum n) ++
  map (@extend_root_embed F n) xs.

Lemma extend_root_cover_complete :
  forall F n (xs : list (World F)),
    (forall x, In x xs) ->
    forall x, In x (extend_root_cover n xs).
Proof.
  intros F n xs Hcover [i | x]; unfold extend_root_cover.
  - apply in_or_app; left. apply in_map. apply fin_enum_complete.
  - apply in_or_app; right. apply in_map. apply Hcover.
Qed.

Lemma extend_root_cover_nodup :
  forall F n (xs : list (World F)),
    NoDup xs -> NoDup (extend_root_cover n xs).
Proof.
  intros F n xs Hnodup. unfold extend_root_cover.
  apply NoDup_app.
  - apply NoDup_map_on; [apply fin_enum_nodup |].
    intros i j _ _ Heq. now inversion Heq.
  - apply NoDup_map_on; [exact Hnodup |].
    intros x y _ _ Heq. now inversion Heq.
  - intros [i | x] Hleft Hright.
    + apply in_map_iff in Hright.
      destruct Hright as [y [Heq _]]. discriminate Heq.
    + apply in_map_iff in Hleft.
      destruct Hleft as [j [Heq _]]. discriminate Heq.
Qed.

Lemma extend_root_cover_length :
  forall F n (xs : list (World F)),
    length (extend_root_cover n xs) = n + length xs.
Proof.
  intros F n xs. unfold extend_root_cover.
  rewrite length_app, !length_map, fin_enum_length. reflexivity.
Qed.

Theorem extend_root_finite :
  forall F n,
    finite_frame F -> finite_frame (extend_root_frame F n).
Proof.
  intros F n [xs Hcover].
  exists (extend_root_cover n xs).
  now apply extend_root_cover_complete.
Qed.

Theorem extend_root_finite_cover_exact :
  forall F n (xs : list (World F)),
    NoDup xs -> (forall x, In x xs) ->
    exists ys : list (World (extend_root_frame F n)),
      NoDup ys /\ (forall y, In y ys) /\
      length ys = n + length xs.
Proof.
  intros F n xs Hnodup Hcover.
  exists (extend_root_cover n xs); repeat split.
  - now apply extend_root_cover_nodup.
  - now apply extend_root_cover_complete.
  - apply extend_root_cover_length.
Qed.

Lemma extend_root_finite_tree :
  forall F n (Hn : 0 < n),
    frame_finite_tree_property F ->
    frame_finite_tree_property (extend_root_frame F n).
Proof.
  intros F n Hn [_ Hfinite]. split.
  - now apply extend_root_rooted.
  - now apply extend_root_finite.
Qed.

(** Every finite irreflexive transitive frame is converse well-founded.  This
    is the list-cover counterpart of Foundation's finite type-class instance. *)
Theorem finite_transitive_irreflexive_cwf :
  forall F,
    finite_frame F -> frame_transitive F -> frame_irreflexive F ->
    frame_converse_well_founded F.
Proof.
  intros F [cover Hcover] Htrans Hirr X [x0 Hx0].
  destruct (classic (exists m, X m /\
      forall y, X y -> ~ Rel F m y)) as [Hmax | Hno_max];
    [exact Hmax |].
  exfalso.
  assert (Hsuccessor : forall a, X a ->
      exists b, X b /\ Rel F a b).
  {
    intros a Ha. apply NNPP. intro Hnone.
    apply Hno_max. exists a; split; [exact Ha |].
    intros b Hb Rab. apply Hnone. exists b; auto.
  }
  assert (Htotal : forall a : World F,
      exists b : World F, X a -> X b /\ Rel F a b).
  {
    intro a. destruct (classic (X a)) as [Ha | Hna].
    - destruct (Hsuccessor a Ha) as [b Hb]. exists b. tauto.
    - exists x0. tauto.
  }
  destruct (@choice (World F) (World F)
    (fun a b => X a -> X b /\ Rel F a b) Htotal)
    as [next Hnext].
  pose (f := fun n : nat => Nat.iter n next x0).
  assert (HfX : forall n, X (f n)).
  {
    intro n; induction n as [|n IH].
    - exact Hx0.
    - change (X (next (f n))). exact (proj1 (Hnext (f n) IH)).
  }
  assert (Hfstep : forall n, Rel F (f n) (f (S n))).
  {
    intro n. change (Rel F (f n) (next (f n))).
    exact (proj2 (Hnext (f n) (HfX n))).
  }
  assert (Hchain : forall j i, i < j -> Rel F (f i) (f j)).
  {
    intro j; induction j as [|j IH]; intros i Hij; [lia |].
    destruct (Nat.eq_dec i j) as [-> | Hneq].
    - apply Hfstep.
    - eapply Htrans; [apply IH; lia | apply Hfstep].
  }
  assert (Hdistinct : forall i j, i <> j -> f i <> f j).
  {
    intros i j Hij Heq.
    destruct (Nat.lt_trichotomy i j) as [Hij' | [Hij' | Hji]].
    - pose proof (Hchain j i Hij') as Rij. rewrite Heq in Rij.
      exact (Hirr (f j) Rij).
    - contradiction.
    - pose proof (Hchain i j Hji) as Rji. rewrite Heq in Rji.
      exact (Hirr (f j) Rji).
  }
  pose (prefix := map f (seq 0 (S (length cover)))).
  assert (Hprefix_nodup : NoDup prefix).
  {
    unfold prefix. apply NoDup_map_on.
    - apply seq_NoDup.
    - intros i j _ _ Heq.
      destruct (Nat.eq_dec i j) as [Hij | Hij]; [exact Hij |].
      exfalso. exact (Hdistinct i j Hij Heq).
  }
  assert (Hprefix_incl : incl prefix cover).
  {
    intros x _. apply Hcover.
  }
  pose proof (NoDup_incl_length Hprefix_nodup Hprefix_incl) as Hlen.
  unfold prefix in Hlen. rewrite length_map, length_seq in Hlen. lia.
Qed.

Corollary extend_root_converse_well_founded :
  forall F n,
    finite_frame F -> frame_irreflexive F -> frame_transitive F ->
    frame_converse_well_founded (extend_root_frame F n).
Proof.
  intros F n Hfinite Hirr Htrans.
  apply finite_transitive_irreflexive_cwf.
  - now apply extend_root_finite.
  - now apply extend_root_transitive.
  - now apply extend_root_irreflexive.
Qed.

(** * Cardinality of T-failures on a chain *)

Definition predicate_card_at_most_one {A : Type} (P : A -> Prop) : Prop :=
  forall x y, P x -> P y -> x = y.

Lemma not_satisfies_T_iff :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         x (p : formula AtomType),
    ~ satisfies F V x (T p) <->
    satisfies F V x (Box p) /\ ~ satisfies F V x p.
Proof. intros; unfold T; simpl; tauto. Qed.

Lemma T_failures_at_most_one_on_chain :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (p : formula AtomType) xs,
    list_relation_chain (Rel F) xs ->
    predicate_card_at_most_one
      (fun x => In x xs /\ ~ satisfies F V x (T p)).
Proof.
  intros AtomType F V p xs Hchain x y [Hx Hbadx] [Hy Hbady].
  destruct (classic (x = y)) as [Heq | Hneq]; [exact Heq |].
  destruct (proj1 (@not_satisfies_T_iff AtomType F V x p) Hbadx)
    as [Hboxx Hnotx].
  destruct (proj1 (@not_satisfies_T_iff AtomType F V y p) Hbady)
    as [Hboxy Hnoty].
  destruct (Hchain x y Hx Hy Hneq) as [Rxy | Ryx].
  - exfalso. exact (Hnoty (Hboxx y Rxy)).
  - exfalso. exact (Hnotx (Hboxy x Ryx)).
Qed.

Theorem atmost_one_T_failure_on_chain :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (p : formula AtomType) xs,
    list_relation_chain (Rel F) xs ->
    (forall x, In x xs -> satisfies F V x (T p)) \/
    exists x,
      In x xs /\ ~ satisfies F V x (T p) /\
      forall y, In y xs -> ~ satisfies F V y (T p) -> y = x.
Proof.
  intros AtomType F V p xs Hchain.
  destruct (classic (forall x, In x xs -> satisfies F V x (T p)))
    as [Hall | Hnotall]; [now left | right].
  assert (Hex : exists x, In x xs /\ ~ satisfies F V x (T p)).
  {
    apply NNPP. intro Hnone. apply Hnotall.
    intros x Hx. apply NNPP. intro Hbad.
    apply Hnone. exists x; auto.
  }
  destruct Hex as [x [Hx Hbadx]].
  exists x; repeat split; auto.
  intros y Hy Hbady.
  symmetry. eapply T_failures_at_most_one_on_chain; eauto.
Qed.

Theorem validates_T_list_on_long_chain :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (Gamma : list (formula AtomType)) xs,
    NoDup xs -> list_relation_chain (Rel F) xs ->
    length xs = length Gamma + 1 ->
    exists x, In x xs /\
      forall p, In p Gamma -> satisfies F V x (T p).
Proof.
  intros AtomType F V Gamma xs Hnodup Hchain Hlength.
  destruct Gamma as [|p0 Gamma].
  - destruct xs as [|x xs]; simpl in Hlength; [lia |].
    exists x; split; [now left |]. intros p H; contradiction.
  - apply NNPP. intro Hnone.
    assert (Hbad : forall x, In x xs ->
        exists p, In p (p0 :: Gamma) /\ ~ satisfies F V x (T p)).
    {
      intros x Hx. apply NNPP. intro Hno_bad.
      apply Hnone. exists x; split; [exact Hx |].
      intros p Hp. apply NNPP. intro Hfail.
      apply Hno_bad. exists p; auto.
    }
    assert (Htotal : forall x : World F,
        exists p : formula AtomType,
          In x xs -> In p (p0 :: Gamma) /\ ~ satisfies F V x (T p)).
    {
      intro x. destruct (classic (In x xs)) as [Hx | Hx].
      - destruct (Hbad x Hx) as [p Hp]. exists p. tauto.
      - exists p0. tauto.
    }
    destruct (@choice (World F) (formula AtomType)
      (fun x p => In x xs ->
        In p (p0 :: Gamma) /\ ~ satisfies F V x (T p)) Htotal)
      as [bad Hbad_choice].
    assert (Hbad_in : forall x, In x xs -> In (bad x) (p0 :: Gamma)).
    { intros x Hx. exact (proj1 (Hbad_choice x Hx)). }
    assert (Hbad_fails : forall x, In x xs ->
        ~ satisfies F V x (T (bad x))).
    { intros x Hx. exact (proj2 (Hbad_choice x Hx)). }
    assert (Hbad_injective : forall x y,
        In x xs -> In y xs -> bad x = bad y -> x = y).
    {
      intros x y Hx Hy Heq.
      apply (@T_failures_at_most_one_on_chain
        AtomType F V (bad x) xs Hchain x y).
      - split; [exact Hx | now apply Hbad_fails].
      - split; [exact Hy |].
        pose proof (Hbad_fails y Hy) as Hybad.
        now rewrite <- Heq in Hybad.
    }
    assert (Hmap_nodup : NoDup (map bad xs)).
    { now apply NoDup_map_on. }
    assert (Hmap_incl : incl (map bad xs) (p0 :: Gamma)).
    {
      intros p Hp. apply in_map_iff in Hp.
      destruct Hp as [x [Heq Hx]]. rewrite <- Heq. now apply Hbad_in.
    }
    pose proof (NoDup_incl_length Hmap_nodup Hmap_incl) as Hle.
    rewrite length_map, Hlength in Hle. simpl in Hle. lia.
Qed.

Fixpoint formula_list_conjunction {AtomType}
    (ps : list (formula AtomType)) : formula AtomType :=
  match ps with
  | [] => Top
  | p :: qs => And p (formula_list_conjunction qs)
  end.

Lemma satisfies_formula_list_conjunction :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F) w ps,
    satisfies F V w (formula_list_conjunction ps) <->
    forall p, In p ps -> satisfies F V w p.
Proof.
  intros AtomType F V w ps; induction ps as [|p ps IH]; simpl.
  - split.
    + intros _ q H; contradiction.
    + intros _; tauto.
  - rewrite (@satisfies_and AtomType F V w p
      (formula_list_conjunction ps)), IH.
    split.
    + intros [Hp Hps] q [Hqp | Hq].
      * now subst q.
      * now apply Hps.
    + intro Hall. split.
      * apply Hall. now left.
      * intros q Hq. apply Hall. now right.
Qed.

Theorem extend_root_T_list_witness :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (Gamma : list (formula AtomType)),
    exists i : Fin.t (length Gamma + 1),
      forall p, In p Gamma ->
        satisfies
          (extend_root_frame F (length Gamma + 1))
          (extend_root_valuation V r (length Gamma + 1))
          (extend_root_added i) (T p).
Proof.
  intros AtomType F V r Gamma.
  pose (n := length Gamma + 1).
  destruct (@validates_T_list_on_long_chain AtomType
    (extend_root_frame F n) (extend_root_valuation V r n)
    Gamma (extend_root_chain F n)
    (@extend_root_chain_nodup F n)
    (@extend_root_chain_is_chain F n)) as [x [Hx Hall]].
  - unfold n. rewrite (@extend_root_chain_length F). reflexivity.
  - destruct (@extend_root_chain_member F n x Hx) as [i ->].
    exists i. exact Hall.
Qed.

Corollary extend_root_T_conjunction_witness :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F)
         (r : World F) (Gamma : list (formula AtomType)),
    exists i : Fin.t (length Gamma + 1),
      satisfies
        (extend_root_frame F (length Gamma + 1))
        (extend_root_valuation V r (length Gamma + 1))
        (extend_root_added i)
        (formula_list_conjunction (map (fun p => T p) Gamma)).
Proof.
  intros AtomType F V r Gamma.
  destruct (extend_root_T_list_witness V r Gamma) as [i Hi].
  exists i. apply (proj2 (@satisfies_formula_list_conjunction
    AtomType (extend_root_frame F (length Gamma + 1))
    (extend_root_valuation V r (length Gamma + 1))
    (extend_root_added i) (map (fun p => T p) Gamma))).
  intros q Hq. apply in_map_iff in Hq.
  destruct Hq as [p [Heq Hp]]. rewrite <- Heq. now apply Hi.
Qed.
