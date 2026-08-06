(** Exact list normal forms and finite covers for tree unravellings.

    [StructuralFrames] represents a rooted path intrinsically as a snoc
    derivation.  This module proves that its node list is a complete and
    injective external representation, recovers the source prefix theorems,
    and constructs an explicit cover of every finite transitive irreflexive
    unravelling. *)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Lia Lists.List.
From Stdlib Require Import Logic.ClassicalDescription Logic.ProofIrrelevance.
From FoundationModal Require Import
  Kripke Correspondence FrameProperties Filtration
  RelationProperties StructuralFrames.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Node-list normal form *)

(** Package a predecessor path with its final edge before extending it.  This
    whole-world formulation lets ordinary equality elimination transport the
    dependent edge proof without assuming uniqueness of equality proofs for
    the world's type. *)
Definition tree_step_snoc (F : frame) (r y : World F)
    (step : { p : tree_world F r & Rel F (tree_endpoint p) y })
    : tree_world F r :=
  match step with
  | existT _ p h => tree_snoc p y h
  end.

Arguments tree_step_snoc F r y step : clear implicits.

Lemma tree_immediate_snoc_of_eq :
  forall (F : frame) (r y : World F) (p q : tree_world F r)
    (h : Rel F (tree_endpoint q) y),
    p = q -> tree_immediate_rel F r p (tree_snoc q y h).
Proof.
  intros F r y p q h ->. exists h. reflexivity.
Qed.

Lemma rooted_path_nodes_length :
  forall (F : frame) (r x : World F) (p : rooted_path F r x),
    length (rooted_path_nodes p) = S (rooted_path_length p).
Proof.
  intros F r x p; induction p; simpl.
  - reflexivity.
  - rewrite length_app, IHp. simpl. lia.
Qed.

Lemma rooted_path_nodes_end :
  forall (F : frame) (r x : World F) (p : rooted_path F r x),
    exists prefix, rooted_path_nodes p = prefix ++ [x].
Proof.
  intros F r x p; induction p.
  - exists []. reflexivity.
  - exists (rooted_path_nodes p). reflexivity.
Qed.

Lemma rooted_path_nodes_start :
  forall (F : frame) (r x : World F) (p : rooted_path F r x),
    exists suffix, rooted_path_nodes p = r :: suffix.
Proof.
  intros F r x p; induction p.
  - exists []. reflexivity.
  - destruct IHp as [suffix Hsuffix].
    exists (suffix ++ [y]). simpl. now rewrite Hsuffix.
Qed.

Lemma rooted_path_nodes_sigma_injective :
  forall (F : frame) (r : World F) x (p : rooted_path F r x)
    y (q : rooted_path F r y),
    rooted_path_nodes p = rooted_path_nodes q ->
    existT (fun z => rooted_path F r z) x p =
    existT (fun z => rooted_path F r z) y q.
Proof.
  intros F r x p. induction p as [|x p IHp y h];
    intros z q Heq; destruct q as [|x' q z' h']; simpl in Heq.
  - reflexivity.
  - pose proof (f_equal (@length (World F)) Heq) as Hlen.
    rewrite length_app, rooted_path_nodes_length in Hlen. simpl in Hlen. lia.
  - pose proof (f_equal (@length (World F)) Heq) as Hlen.
    rewrite length_app, rooted_path_nodes_length in Hlen. simpl in Hlen. lia.
  - destruct (app_inj_tail _ _ _ _ Heq) as [Hprefix Hend].
    subst z'. pose proof (IHp _ q Hprefix) as Hprior.
    change
      (tree_step_snoc F r y
        (existT (fun w : tree_world F r =>
          Rel F (tree_endpoint w) y)
          (existT (fun z => rooted_path F r z) x p) h) =
       tree_step_snoc F r y
        (existT (fun w : tree_world F r =>
          Rel F (tree_endpoint w) y)
          (existT (fun z => rooted_path F r z) x' q) h')).
    apply (f_equal (tree_step_snoc F r y)).
    apply eq_sigT_hprop.
    + intros. apply proof_irrelevance.
    + exact Hprior.
Qed.

Theorem tree_nodes_injective :
  forall (F : frame) (r : World F) (p q : tree_world F r),
    tree_nodes p = tree_nodes q -> p = q.
Proof.
  intros F r [x p] [y q].
  apply rooted_path_nodes_sigma_injective.
Qed.

Theorem tree_immediate_nodes_iff :
  forall (F : frame) (r : World F) (p q : tree_world F r),
    tree_immediate_rel F r p q <->
    exists z, tree_nodes q = tree_nodes p ++ [z].
Proof.
  intros F r p [y q]; split.
  - intros [h ->]. exists y. reflexivity.
  - intros [z Heq]. destruct q as [|x q y h].
    + pose proof (f_equal (@length (World F)) Heq) as Hlen.
      destruct p as [px pp]. simpl in Hlen.
      rewrite length_app in Hlen. simpl in Hlen.
      unfold tree_nodes in Hlen. simpl in Hlen.
      destruct (rooted_path_nodes pp) eqn:Hnodes; simpl in Hlen.
      * exfalso. exact (@rooted_path_nodes_nonempty F r px pp Hnodes).
      * lia.
    + simpl in Heq.
      destruct (app_inj_tail _ _ _ _ Heq) as [Hprefix Hend].
      subst z.
      pose proof (@rooted_path_nodes_sigma_injective F r x q
        (tree_endpoint p) (projT2 p) Hprefix) as Hprior.
      change (tree_immediate_rel F r p
        (tree_snoc (existT (fun z => rooted_path F r z) x q) y h)).
      apply (@tree_immediate_snoc_of_eq F r y p
        (existT (fun z => rooted_path F r z) x q) h).
      transitivity (existT (fun z => rooted_path F r z)
        (tree_endpoint p) (projT2 p)).
      * destruct p. reflexivity.
      * exact (eq_sym Hprior).
Qed.

(** A node-list prefix determines the unique iterated immediate path. *)
Lemma rooted_path_nodes_prefix_rel_iter :
  forall (F : frame) (r x : World F) (q : rooted_path F r x)
    (p : tree_world F r) suffix,
    rooted_path_nodes q = tree_nodes p ++ suffix ->
    rel_iter (tree_immediate_rel F r) (length suffix) p
      (existT (fun z => rooted_path F r z) x q).
Proof.
  intros F r x q. induction q as [|x q IH y h];
    intros p suffix Heq; destruct suffix as [|z suffix].
  - rewrite app_nil_r in Heq.
    change (tree_nodes (tree_root F r) = tree_nodes p) in Heq.
    pose proof (tree_nodes_injective Heq) as Hworld.
    simpl. now symmetry.
  - pose proof (f_equal (@length (World F)) Heq) as Hlen.
    rewrite length_app in Hlen. simpl in Hlen.
    destruct p as [px pp]. unfold tree_nodes in Hlen. simpl in Hlen.
    destruct (rooted_path_nodes pp) eqn:Hnodes; simpl in Hlen.
    + exfalso. exact (@rooted_path_nodes_nonempty F r px pp Hnodes).
    + lia.
  - rewrite app_nil_r in Heq.
    change (tree_nodes
      (existT (fun u => rooted_path F r u) y
        (rooted_path_snoc F r x q y h)) = tree_nodes p) in Heq.
    pose proof (tree_nodes_injective Heq) as Hworld.
    simpl. now symmetry.
  - destruct (@exists_last _ (z :: suffix) ltac:(discriminate))
      as [prefix [last Hlast]].
    rewrite Hlast in Heq |- *. rewrite length_app. simpl.
    replace (tree_nodes p ++ (prefix ++ [last]))
      with ((tree_nodes p ++ prefix) ++ [last]) in Heq
      by now rewrite app_assoc.
    destruct (app_inj_tail _ _ _ _ Heq) as [Hprefix Hend].
    subst last.
    rewrite Nat.add_1_r.
    apply (proj2 (rel_iter_succ_right_iff
      (tree_immediate_rel F r) (length prefix) p
      (existT (fun u => rooted_path F r u) y
        (rooted_path_snoc F r x q y h)))).
    exists (existT (fun u => rooted_path F r u) x q). split.
    + now apply IH.
    + exists h. reflexivity.
Qed.

Theorem tree_rel_iter_nodes_iff :
  forall (F : frame) (r : World F) n (p q : tree_world F r),
    rel_iter (tree_immediate_rel F r) n p q <->
    exists suffix,
      length suffix = n /\ tree_nodes q = tree_nodes p ++ suffix.
Proof.
  intros F r n. induction n as [|n IH]; intros p q; split.
  - intro Heq. simpl in Heq. subst q. exists []. split.
    + reflexivity.
    + now rewrite app_nil_r.
  - intros [suffix [Hlen Heq]].
    destruct suffix; simpl in Hlen; [|discriminate].
    rewrite app_nil_r in Heq.
    apply tree_nodes_injective in Heq. now subst q.
  - intros [u [Hpu Huq]].
    apply tree_immediate_nodes_iff in Hpu.
    destruct Hpu as [z Hzu].
    apply (proj1 (IH u q)) in Huq.
    destruct Huq as [suffix [Hlen Heq]].
    exists (z :: suffix). split; [simpl; lia |].
    rewrite Heq, Hzu, <- app_assoc. reflexivity.
  - intros [suffix [Hlen Heq]].
    rewrite <- Hlen. destruct q as [qx qq].
    now apply rooted_path_nodes_prefix_rel_iter.
Qed.

Theorem trans_tree_rel_nodes_iff :
  forall (F : frame) (r : World F) (p q : tree_world F r),
    Rel (trans_tree_unravelling F r) p q <->
    exists suffix,
      suffix <> [] /\ tree_nodes q = tree_nodes p ++ suffix.
Proof.
  intros F r p q; split.
  - intros [n [Hn Hpq]].
    apply tree_rel_iter_nodes_iff in Hpq.
    destruct Hpq as [suffix [Hlen Heq]].
    exists suffix. split.
    + intro Hnil. rewrite Hnil in Hlen. simpl in Hlen. lia.
    + exact Heq.
  - intros [suffix [Hnonempty Heq]].
    exists (length suffix). split.
    + destruct suffix; [contradiction | simpl; lia].
    + apply tree_rel_iter_nodes_iff. exists suffix. now split.
Qed.

(** * No-repetition and finite covers *)

Lemma rooted_path_node_eq_or_rel_endpoint :
  forall (F : frame), frame_transitive F ->
    forall r x (p : rooted_path F r x) z,
      In z (rooted_path_nodes p) -> z = x \/ Rel F z x.
Proof.
  intros F Htrans r x p. induction p as [|x p IH y h]; intros z Hz.
  - simpl in Hz. destruct Hz as [-> | []]. now left.
  - simpl in Hz. apply in_app_or in Hz. destruct Hz as [Hz | Hz].
    + destruct (IH z Hz) as [-> | Hzx].
      * now right.
      * right. eapply Htrans; eauto.
    + simpl in Hz. destruct Hz as [-> | []]. now left.
Qed.

Lemma rooted_path_nodes_nodup :
  forall (F : frame), frame_transitive F -> frame_irreflexive F ->
    forall r x (p : rooted_path F r x), NoDup (rooted_path_nodes p).
Proof.
  intros F Htrans Hirrefl r x p. induction p as [|x p IH y h].
  - simpl. repeat constructor; simpl; auto.
  - simpl. apply NoDup_app.
    + exact IH.
    + repeat constructor; simpl; auto.
    + intros z Hz Hsingle. simpl in Hsingle.
      destruct Hsingle as [-> | []].
      destruct (@rooted_path_node_eq_or_rel_endpoint
        F Htrans r x p z Hz)
        as [Heq | Hyx].
      * subst z. exact (Hirrefl x h).
      * exact (Hirrefl z (Htrans z x z Hyx h)).
Qed.

Fixpoint lists_exact {A : Type} (xs : list A) (n : nat) : list (list A) :=
  match n with
  | 0 => [[]]
  | S k => flat_map (fun x => map (cons x) (lists_exact xs k)) xs
  end.

Lemma lists_exact_complete :
  forall (A : Type) (xs : list A),
    (forall x : A, In x xs) ->
    forall ys, In ys (lists_exact xs (length ys)).
Proof.
  intros A xs Hcover ys. induction ys as [|y ys IH].
  - simpl. now left.
  - simpl. apply in_flat_map. exists y. split; [apply Hcover |].
    apply in_map. exact IH.
Qed.

Fixpoint lists_upto {A : Type} (xs : list A) (n : nat)
    : list (list A) :=
  match n with
  | 0 => [[]]
  | S k => lists_upto xs k ++ lists_exact xs (S k)
  end.

Lemma lists_upto_complete :
  forall (A : Type) (xs : list A),
    (forall x : A, In x xs) ->
    forall n ys, length ys <= n -> In ys (lists_upto xs n).
Proof.
  intros A xs Hcover n. induction n as [|n IH]; intros ys Hlen.
  - assert (ys = []) by (apply length_zero_iff_nil; lia). subst ys.
    simpl. now left.
  - change (In ys (lists_upto xs n ++ lists_exact xs (S n))).
    apply in_app_iff.
    destruct (le_lt_dec (length ys) n) as [Hle | Hlt].
    + left. now apply IH.
    + right. assert (length ys = S n) by lia.
      rewrite <- H. apply lists_exact_complete. exact Hcover.
Qed.

Definition tree_nodes_realized (F : frame) (r : World F)
    (nodes : list (World F)) : Prop :=
  exists p : tree_world F r, tree_nodes p = nodes.

Arguments tree_nodes_realized F r nodes : clear implicits.

Lemma tree_nodes_realized_unique :
  forall F r nodes,
    tree_nodes_realized F r nodes ->
    exists! p : tree_world F r, tree_nodes p = nodes.
Proof.
  intros F r nodes [p Hp]. exists p. split; [exact Hp |].
  intros q Hq. apply tree_nodes_injective. now rewrite Hp, Hq.
Qed.

Definition tree_node_candidates (F : frame) (r : World F)
    (cover : list (World F))
    : list { nodes : list (World F) | tree_nodes_realized F r nodes } :=
  @sig_filter (list (World F)) (tree_nodes_realized F r)
    (fun nodes => excluded_middle_informative
      (tree_nodes_realized F r nodes))
    (lists_upto cover (length cover)).

Arguments tree_node_candidates F r cover : clear implicits.

Definition tree_world_of_candidate (F : frame) (r : World F)
    (candidate : { nodes : list (World F) |
      tree_nodes_realized F r nodes }) : tree_world F r :=
  proj1_sig (constructive_definite_description _
    (tree_nodes_realized_unique (proj2_sig candidate))).

Arguments tree_world_of_candidate F r candidate : clear implicits.

Definition tree_unravelling_cover (F : frame) (r : World F)
    (cover : list (World F)) : list (tree_world F r) :=
  map (tree_world_of_candidate F r) (tree_node_candidates F r cover).

Arguments tree_unravelling_cover F r cover : clear implicits.

Lemma tree_world_of_candidate_nodes :
  forall F r candidate,
    tree_nodes (tree_world_of_candidate F r candidate) = proj1_sig candidate.
Proof.
  intros F r candidate. unfold tree_world_of_candidate.
  exact (proj2_sig (constructive_definite_description _
    (tree_nodes_realized_unique (proj2_sig candidate)))).
Qed.

Theorem tree_unravelling_cover_complete :
  forall F r (cover : list (World F)),
    (forall x, In x cover) ->
    frame_transitive F -> frame_irreflexive F ->
    forall p : tree_world F r,
      In p (tree_unravelling_cover F r cover).
Proof.
  intros F r cover Hcover Htrans Hirrefl p.
  assert (Hnodes : In (tree_nodes p)
      (lists_upto cover (length cover))).
  {
    apply lists_upto_complete; [exact Hcover |].
    apply NoDup_incl_length with (l := tree_nodes p).
    - destruct p as [x path].
      apply rooted_path_nodes_nodup; assumption.
    - intros x Hx. apply Hcover.
  }
  set (candidate := exist (tree_nodes_realized F r) (tree_nodes p)
    (ex_intro _ p eq_refl)).
  assert (Hcandidate : In candidate (tree_node_candidates F r cover)).
  {
    unfold tree_node_candidates. apply sig_filter_complete. exact Hnodes.
  }
  unfold tree_unravelling_cover. apply in_map_iff.
  exists candidate. split; [|exact Hcandidate].
  apply tree_nodes_injective.
  rewrite tree_world_of_candidate_nodes. reflexivity.
Qed.

Theorem trans_tree_unravelling_finite :
  forall F r,
    finite_frame F -> frame_transitive F -> frame_irreflexive F ->
    finite_frame (trans_tree_unravelling F r).
Proof.
  intros F r [cover Hcover] Htrans Hirrefl.
  exists (tree_unravelling_cover F r cover).
  apply tree_unravelling_cover_complete; assumption.
Qed.

Definition frame_is_finite_tree (F : frame) : Prop :=
  finite_frame F /\ frame_is_tree F.

Corollary trans_tree_is_finite_tree :
  forall F r,
    finite_frame F -> frame_transitive F -> frame_irreflexive F ->
    frame_is_finite_tree (trans_tree_unravelling F r).
Proof.
  intros F r Hfinite Htrans Hirrefl. split.
  - now apply trans_tree_unravelling_finite.
  - apply trans_tree_is_tree.
Qed.
