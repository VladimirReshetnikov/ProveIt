(*
  No finite deterministic truth-functional matrix characterizes
  intuitionistic propositional logic.

  The obstruction is Goedel's 1932 finite-matrix (collision) formula.  For a
  matrix with an exhaustive list of n values, take n+1 atoms and disjoin their
  pairwise biconditionals.
  Every valuation identifies two atoms.  Atom-renaming turns that particular
  biconditional into p <-> p, so soundness makes the whole disjunction
  designated.  A branching Kripke model refutes the same formula at its root.
*)

From Stdlib Require Import List Arith Bool Lia.
From NaturalDeduction Require Import Calculus.

Import ListNotations.
Import NaturalDeduction.

Set Implicit Arguments.

Module FiniteMatrixTheorem.

(** * Goedel's finite-matrix collision formulas *)

Definition indices (n : nat) : list nat := seq 0 (S n).

Definition raw_pairs (n : nat) : list (nat * nat) :=
  flat_map
    (fun i => map (fun j => (i, j)) (indices n))
    (indices n).

(** There is exactly one disjunct for each pair [i < j]. *)
Definition increasing_pairs (n : nat) : list (nat * nat) :=
  filter (fun ij => Nat.ltb (fst ij) (snd ij)) (raw_pairs n).

Definition atom (i : nat) : formula nat := FAtom i.

Definition biconditional (p q : formula nat) : formula nat :=
  Conj (Impl p q) (Impl q p).

Definition atom_biconditional (ij : nat * nat) : formula nat :=
  biconditional (atom (fst ij)) (atom (snd ij)).

Fixpoint big_disjunction (xs : list (formula nat)) : formula nat :=
  match xs with
  | [] => Falsum
  | p :: ps => Disj p (big_disjunction ps)
  end.

Definition goedel_disjuncts (n : nat) : list (formula nat) :=
  map atom_biconditional (increasing_pairs n).

Definition goedel_formula (n : nat) : formula nat :=
  big_disjunction (goedel_disjuncts n).

Lemma in_raw_pairs : forall n i j,
    In (i, j) (raw_pairs n) <->
    In i (indices n) /\ In j (indices n).
Proof.
  intros n i j. unfold raw_pairs.
  rewrite in_flat_map.
  split.
  - intros [k [Hk Hmap]].
    apply in_map_iff in Hmap.
    destruct Hmap as [l [Heq Hl]].
    injection Heq as Hik Hjl. subst k l.
    split; assumption.
  - intros [Hi Hj].
    exists i. split.
    + exact Hi.
    + apply in_map. exact Hj.
Qed.

Lemma in_increasing_pairs : forall n i j,
    In (i, j) (increasing_pairs n) <->
    In i (indices n) /\ In j (indices n) /\ i < j.
Proof.
  intros n i j. unfold increasing_pairs.
  rewrite filter_In, in_raw_pairs. simpl.
  rewrite Nat.ltb_lt.
  tauto.
Qed.

(** * Renaming atoms and deriving the collapsed formula *)

Fixpoint rename (s : nat -> nat) (p : formula nat) : formula nat :=
  match p with
  | FAtom a => FAtom (s a)
  | Falsum => Falsum
  | Conj q r => Conj (rename s q) (rename s r)
  | Disj q r => Disj (rename s q) (rename s r)
  | Impl q r => Impl (rename s q) (rename s r)
  end.

Definition collapse (i j a : nat) : nat :=
  if Nat.eq_dec a j then i else a.

Lemma collapse_source : forall i j, i <> j -> collapse i j i = i.
Proof.
  intros i j Hneq. unfold collapse.
  destruct (Nat.eq_dec i j); congruence.
Qed.

Lemma collapse_target : forall i j, collapse i j j = i.
Proof.
  intros i j. unfold collapse.
  destruct (Nat.eq_dec j j); congruence.
Qed.

Lemma rename_big_disjunction : forall s xs,
    rename s (big_disjunction xs) =
    big_disjunction (map (rename s) xs).
Proof.
  intros s xs. induction xs as [|p ps IH].
  - reflexivity.
  - simpl. now rewrite IH.
Qed.

Lemma derives_big_disjunction_member :
    forall (Gamma : context nat) p xs,
    intuitionistically_derives Gamma p ->
    In p xs ->
    intuitionistically_derives Gamma (big_disjunction xs).
Proof.
  intros Gamma p xs Hp Hin.
  induction xs as [|q qs IH].
  - contradiction.
  - simpl in Hin |- *. destruct Hin as [Heq | Hin].
    + subst q. apply D_orIntroLeft. exact Hp.
    + apply D_orIntroRight. apply IH. exact Hin.
Qed.

Lemma derives_reflexive_biconditional :
    forall (Gamma : context nat) p,
    intuitionistically_derives Gamma (biconditional p p).
Proof.
  intros Gamma p. unfold biconditional.
  apply D_andIntro.
  - apply D_impIntro. apply D_assumption. left. reflexivity.
  - apply D_impIntro. apply D_assumption. left. reflexivity.
Qed.

Lemma collapsed_goedel_formula_derivable : forall n i j,
    In (i, j) (increasing_pairs n) ->
    intuitionistically_derives []
      (rename (collapse i j) (goedel_formula n)).
Proof.
  intros n i j Hpair.
  apply in_increasing_pairs in Hpair.
  destruct Hpair as [Hi [Hj Hij]].
  unfold goedel_formula. rewrite rename_big_disjunction.
  eapply derives_big_disjunction_member with
      (p := rename (collapse i j) (atom_biconditional (i, j))).
  - unfold atom_biconditional, biconditional, atom. simpl.
    rewrite collapse_source by lia.
    rewrite collapse_target.
    apply derives_reflexive_biconditional.
  - unfold goedel_disjuncts. apply in_map. apply in_map.
    apply in_increasing_pairs.
    repeat split; assumption.
Qed.

(** * Finite deterministic truth-functional matrices *)

Record finite_matrix : Type := {
  value : Type;
  value_eq_dec : forall x y : value, {x = y} + {x <> y};
  false_value : value;
  and_value : value -> value -> value;
  or_value : value -> value -> value;
  imp_value : value -> value -> value;
  designated : value -> Prop;
  values : list value;
  values_exhaustive : forall x : value, In x values
}.

Arguments value _ : clear implicits.

Fixpoint matrix_eval (M : finite_matrix)
    (rho : nat -> value M) (p : formula nat) : value M :=
  match p with
  | FAtom a => rho a
  | Falsum => false_value M
  | Conj q r => and_value M (matrix_eval M rho q) (matrix_eval M rho r)
  | Disj q r => or_value M (matrix_eval M rho q) (matrix_eval M rho r)
  | Impl q r => imp_value M (matrix_eval M rho q) (matrix_eval M rho r)
  end.

Definition matrix_valid (M : finite_matrix) (p : formula nat) : Prop :=
  forall rho : nat -> value M, designated M (matrix_eval M rho p).

Definition sound_for_IPC_theorems (M : finite_matrix) : Prop :=
  forall p, intuitionistically_derives [] p -> matrix_valid M p.

Definition complete_for_IPC_theorems (M : finite_matrix) : Prop :=
  forall p, matrix_valid M p -> intuitionistically_derives [] p.

Definition characterizes_IPC (M : finite_matrix) : Prop :=
  forall p, matrix_valid M p <-> intuitionistically_derives [] p.

(** Evaluating a renamed formula under [rho] agrees with evaluating the
    original formula under any valuation that matches [fun a => rho (s a)]
    pointwise.  The congruence and renaming laws below are both instances of
    this single induction. *)
Lemma matrix_eval_rename_ext : forall M (rho sigma : nat -> value M) s p,
    (forall a, rho (s a) = sigma a) ->
    matrix_eval M rho (rename s p) = matrix_eval M sigma p.
Proof.
  intros M rho sigma s p Hext.
  induction p; simpl.
  - apply Hext.
  - reflexivity.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
Qed.

Lemma matrix_eval_ext : forall M (rho sigma : nat -> value M) p,
    (forall a, rho a = sigma a) ->
    matrix_eval M rho p = matrix_eval M sigma p.
Proof.
  intros M rho sigma p Hext.
  transitivity (matrix_eval M rho (rename (fun a => a) p)).
  - symmetry. apply matrix_eval_rename_ext. intro a. reflexivity.
  - apply matrix_eval_rename_ext. exact Hext.
Qed.

Lemma matrix_eval_rename : forall M rho s p,
    matrix_eval M rho (rename s p) =
    matrix_eval M (fun a => rho (s a)) p.
Proof.
  intros M rho s p.
  apply matrix_eval_rename_ext. intro a. reflexivity.
Qed.

Lemma collapse_preserves_valuation : forall M (rho : nat -> value M) i j,
    rho i = rho j ->
    forall a, rho (collapse i j a) = rho a.
Proof.
  intros M rho i j Heq a. unfold collapse.
  destruct (Nat.eq_dec a j) as [-> | Hneq].
  - exact Heq.
  - reflexivity.
Qed.

Lemma matrix_eval_collapsed : forall M (rho : nat -> value M) p i j,
    rho i = rho j ->
    matrix_eval M rho (rename (collapse i j) p) = matrix_eval M rho p.
Proof.
  intros M rho p i j Heq.
  rewrite matrix_eval_rename.
  apply matrix_eval_ext.
  apply collapse_preserves_valuation. exact Heq.
Qed.

(** A constructive finite pigeonhole lemma.  Decidable equality is part of
    the conventional data of a finite logical matrix. *)
Lemma duplicate_map_collision : forall A B (eq_dec : forall x y : B,
    {x = y} + {x <> y}) (f : A -> B) xs,
    NoDup xs ->
    ~ NoDup (map f xs) ->
    exists x y,
      In x xs /\ In y xs /\ x <> y /\ f x = f y.
Proof.
  intros A B eq_dec f xs Hnodup.
  induction Hnodup as [|x xs Hnotin Hnodup IH].
  - intro Hdup. exfalso. apply Hdup. constructor.
  - intro Hdup. simpl in Hdup.
    destruct (in_dec eq_dec (f x) (map f xs)) as [Hin | Hnotinmap].
    + apply in_map_iff in Hin.
      destruct Hin as [y [Heq Hy]].
      exists x, y. repeat split.
      * left. reflexivity.
      * right. exact Hy.
      * intro Hxy. subst y. contradiction.
      * symmetry. exact Heq.
    + assert (Htaildup : ~ NoDup (map f xs)).
      { intro Htail. apply Hdup. constructor; assumption. }
      destruct (IH Htaildup) as [y [z [Hy [Hz [Hyz Heq]]]]].
      exists y, z. repeat split; try (right; assumption); assumption.
Qed.

Lemma finite_cover_collision : forall A
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (cover : list A) (f : nat -> A),
    (forall x, In x cover) ->
    exists i j,
      In i (indices (length cover)) /\
      In j (indices (length cover)) /\
      i <> j /\ f i = f j.
Proof.
  intros A eq_dec cover f Hcover.
  set (xs := indices (length cover)).
  assert (Hxs : NoDup xs).
  { unfold xs, indices. apply seq_NoDup. }
  assert (Hmapdup : ~ NoDup (map f xs)).
  { intro Hnodup.
    assert (Hincl : incl (map f xs) cover).
    { intros x Hin. apply in_map_iff in Hin.
      destruct Hin as [i [<- _]]. apply Hcover. }
    pose proof (NoDup_incl_length Hnodup Hincl) as Hlength.
    unfold xs, indices in Hlength.
    rewrite length_map, length_seq in Hlength. lia. }
  destruct (duplicate_map_collision eq_dec f Hxs Hmapdup)
    as [i [j [Hi [Hj [Hij Heq]]]]].
  exists i, j. repeat split; assumption.
Qed.

Lemma finite_matrix_collision : forall (M : finite_matrix)
    (rho : nat -> value M),
    exists i j,
      In i (indices (length (values M))) /\
      In j (indices (length (values M))) /\
      i <> j /\ rho i = rho j.
Proof.
  intros M rho.
  eapply (@finite_cover_collision
    (value M) (value_eq_dec M) (values M) rho).
  apply values_exhaustive.
Qed.

Lemma finite_matrix_increasing_collision : forall (M : finite_matrix)
    (rho : nat -> value M),
    exists i j,
      In (i, j) (increasing_pairs (length (values M))) /\
      rho i = rho j.
Proof.
  intros M rho.
  destruct (finite_matrix_collision M rho)
    as [i [j [Hi [Hj [Hneq Heq]]]]].
  destruct (Nat.lt_trichotomy i j) as [Hij | [Hij | Hji]].
  - exists i, j. split.
    + apply in_increasing_pairs. repeat split; assumption.
    + exact Heq.
  - contradiction.
  - exists j, i. split.
    + apply in_increasing_pairs. repeat split; assumption.
    + symmetry. exact Heq.
Qed.

(** Soundness alone forces every finite matrix to validate its Goedel
    collision formula.  No algebraic property of the operations or designated
    set is assumed here. *)
Theorem sound_finite_matrix_validates_goedel_formula : forall M,
    sound_for_IPC_theorems M ->
    matrix_valid M (goedel_formula (length (values M))).
Proof.
  intros M Hsound rho.
  destruct (finite_matrix_increasing_collision M rho)
    as [i [j [Hpair Heq]]].
  pose proof (@collapsed_goedel_formula_derivable
    (length (values M)) i j Hpair) as Hderives.
  pose proof (Hsound _ Hderives rho) as Hdesignated.
  rewrite (@matrix_eval_collapsed M rho
    (goedel_formula (length (values M))) i j Heq) in Hdesignated.
  exact Hdesignated.
Qed.

(** * Kripke semantics and soundness of intuitionistic natural deduction *)

Record kripke_model (A W : Type) : Type := {
  reachable : W -> W -> Prop;
  reachable_refl : forall w, reachable w w;
  reachable_trans : forall u v w,
      reachable u v -> reachable v w -> reachable u w;
  atom_forced : W -> A -> Prop;
  atom_forced_monotone : forall u v a,
      reachable u v -> atom_forced u a -> atom_forced v a
}.

Arguments reachable {A W} _ _ _.
Arguments atom_forced {A W} _ _ _.

Fixpoint forces {A W} (M : kripke_model A W)
    (w : W) (p : formula A) : Prop :=
  match p with
  | FAtom a => atom_forced M w a
  | Falsum => False
  | Conj q r => forces M w q /\ forces M w r
  | Disj q r => forces M w q \/ forces M w r
  | Impl q r => forall v, reachable M w v ->
      forces M v q -> forces M v r
  end.

Definition context_forced {A W} (M : kripke_model A W)
    (w : W) (Gamma : context A) : Prop :=
  forall p, In p Gamma -> forces M w p.

(** Extending a forced context by a forced formula keeps it forced. *)
Lemma context_forced_cons : forall A W (M : kripke_model A W) w p Gamma,
    forces M w p ->
    context_forced M w Gamma ->
    context_forced M w (p :: Gamma).
Proof.
  intros A W M w p Gamma Hp Hctx s Hs. simpl in Hs.
  destruct Hs as [<- | Hs].
  - exact Hp.
  - apply Hctx. exact Hs.
Qed.

Lemma forces_monotone : forall A W (M : kripke_model A W) p u v,
    reachable M u v -> forces M u p -> forces M v p.
Proof.
  intros A W M p. induction p; intros u v Huv Hforce; simpl in *.
  - eapply atom_forced_monotone; eauto.
  - contradiction.
  - destruct Hforce as [H1 H2]. split.
    + eapply IHp1; eauto.
    + eapply IHp2; eauto.
  - destruct Hforce as [H1 | H2].
    + left. eapply IHp1; eauto.
    + right. eapply IHp2; eauto.
  - intros w Hvw Hp.
    apply (Hforce w).
    + eapply reachable_trans; eauto.
    + exact Hp.
Qed.

Theorem intuitionistic_kripke_soundness : forall A W
    (M : kripke_model A W) Gamma p,
    intuitionistically_derives Gamma p ->
    forall w, context_forced M w Gamma -> forces M w p.
Proof.
  intros A W M Gamma p Hderives.
  unfold intuitionistically_derives in Hderives.
  induction Hderives; intros w Hctx; simpl in *.
  - apply Hctx. exact H.
  - contradiction.
  - exfalso. exact (IHHderives w Hctx).
  - split.
    + apply IHHderives1. exact Hctx.
    + apply IHHderives2. exact Hctx.
  - apply IHHderives. exact Hctx.
  - apply IHHderives. exact Hctx.
  - left. apply IHHderives. exact Hctx.
  - right. apply IHHderives. exact Hctx.
  - destruct (IHHderives1 w Hctx) as [Hp | Hq].
    + apply IHHderives2. apply context_forced_cons.
      * exact Hp.
      * exact Hctx.
    + apply IHHderives3. apply context_forced_cons.
      * exact Hq.
      * exact Hctx.
  - intros v Hwv Hp.
    apply IHHderives. apply context_forced_cons.
    + exact Hp.
    + intros s Hs. eapply forces_monotone.
      * exact Hwv.
      * apply Hctx. exact Hs.
  - apply (IHHderives1 w Hctx w).
    + apply reachable_refl.
    + apply IHHderives2. exact Hctx.
Qed.

(** The countermodel is a root with one incomparable leaf for every atom.
    Leaf [i] forces exactly atom [i]. *)
Inductive branch_world : Type :=
| root
| leaf (i : nat).

Definition branch_reachable (u v : branch_world) : Prop :=
  match u with
  | root => True
  | leaf i => v = leaf i
  end.

Definition branch_atom_forced (w : branch_world) (a : nat) : Prop :=
  w = leaf a.

Lemma branch_reachable_refl : forall w, branch_reachable w w.
Proof. intros [|i]; simpl; auto. Qed.

Lemma branch_reachable_trans : forall u v w,
    branch_reachable u v -> branch_reachable v w ->
    branch_reachable u w.
Proof.
  intros [|i] v w Huv Hvw.
  - exact I.
  - simpl in Huv. subst v. exact Hvw.
Qed.

Lemma branch_atom_monotone : forall u v a,
    branch_reachable u v -> branch_atom_forced u a ->
    branch_atom_forced v a.
Proof.
  intros [|i] v a Huv Hua.
  - discriminate Hua.
  - simpl in Huv. subst v. exact Hua.
Qed.

Definition branching_model : kripke_model nat branch_world :=
  {| reachable := branch_reachable;
     reachable_refl := branch_reachable_refl;
     reachable_trans := branch_reachable_trans;
     atom_forced := branch_atom_forced;
     atom_forced_monotone := branch_atom_monotone |}.

Lemma root_refutes_distinct_biconditional : forall i j,
    i <> j ->
    ~ forces branching_model root
        (biconditional (atom i) (atom j)).
Proof.
  intros i j Hneq Hforce.
  destruct Hforce as [Hij _].
  specialize (Hij (leaf i) I eq_refl).
  unfold branch_atom_forced in Hij.
  injection Hij as Heq. contradiction.
Qed.

Lemma forces_big_disjunction_member : forall W
    (M : kripke_model nat W) (w : W) xs,
    forces M w (big_disjunction xs) ->
    exists p, In p xs /\ forces M w p.
Proof.
  intros W M w xs. induction xs as [|p ps IH].
  - simpl. contradiction.
  - simpl. intros [Hp | Hps].
    + exists p. split; [left; reflexivity | exact Hp].
    + destruct (IH Hps) as [q [Hq Hforce]].
      exists q. split; [right; exact Hq | exact Hforce].
Qed.

Theorem root_refutes_goedel_formula : forall n,
    ~ forces branching_model root (goedel_formula n).
Proof.
  intros n Hforce. unfold goedel_formula in Hforce.
  apply forces_big_disjunction_member in Hforce.
  destruct Hforce as [p [Hin Hp]].
  unfold goedel_disjuncts in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [[i j] [Heq Hpair]]. simpl in Heq. subst p.
  apply in_increasing_pairs in Hpair.
  destruct Hpair as [_ [_ Hij]].
  apply (@root_refutes_distinct_biconditional i j).
  - lia.
  - exact Hp.
Qed.

Theorem goedel_formula_not_intuitionistically_derivable : forall n,
    ~ intuitionistically_derives [] (goedel_formula n).
Proof.
  intros n Hderives.
  apply (root_refutes_goedel_formula n).
  eapply intuitionistic_kripke_soundness.
  - exact Hderives.
  - intros p Hin. contradiction.
Qed.

(** * The noncharacterizability theorem *)

Theorem finite_matrix_sound_not_complete : forall M,
    sound_for_IPC_theorems M ->
    ~ complete_for_IPC_theorems M.
Proof.
  intros M Hsound Hcomplete.
  apply (goedel_formula_not_intuitionistically_derivable
    (length (values M))).
  apply Hcomplete.
  apply sound_finite_matrix_validates_goedel_formula.
  exact Hsound.
Qed.

Theorem no_finite_matrix_characterizes_IPC : forall M,
    ~ characterizes_IPC M.
Proof.
  intros M Hcharacterizes.
  apply (@finite_matrix_sound_not_complete M).
  - intros p Hderives. apply (proj2 (Hcharacterizes p)). exact Hderives.
  - intros p Hvalid. apply (proj1 (Hcharacterizes p)). exact Hvalid.
Qed.

Theorem no_finite_matrix_is_sound_and_complete : forall M,
    ~ (sound_for_IPC_theorems M /\ complete_for_IPC_theorems M).
Proof.
  intros M [Hsound Hcomplete].
  exact (@finite_matrix_sound_not_complete M Hsound Hcomplete).
Qed.

(** * Local preservation of all natural-deduction rules is sufficient *)

Record preserves_intuitionistic_rules (M : finite_matrix) : Prop := {
  preserves_false_elim : forall a,
      designated M (false_value M) -> designated M a;
  preserves_and_intro : forall a b,
      designated M a -> designated M b ->
      designated M (and_value M a b);
  preserves_and_elim_left : forall a b,
      designated M (and_value M a b) -> designated M a;
  preserves_and_elim_right : forall a b,
      designated M (and_value M a b) -> designated M b;
  preserves_or_intro_left : forall a b,
      designated M a -> designated M (or_value M a b);
  preserves_or_intro_right : forall a b,
      designated M b -> designated M (or_value M a b);
  preserves_or_elim : forall a b c,
      designated M (or_value M a b) ->
      (designated M a -> designated M c) ->
      (designated M b -> designated M c) ->
      designated M c;
  preserves_imp_intro : forall a b,
      (designated M a -> designated M b) ->
      designated M (imp_value M a b);
  preserves_imp_elim : forall a b,
      designated M (imp_value M a b) ->
      designated M a -> designated M b
}.

Definition matrix_context_designated (M : finite_matrix)
    (rho : nat -> value M) (Gamma : context nat) : Prop :=
  forall p, In p Gamma -> designated M (matrix_eval M rho p).

(** The matrix analogue of [context_forced_cons]: extending a designated
    context by a designated formula keeps it designated. *)
Lemma matrix_context_designated_cons : forall M rho p Gamma,
    designated M (matrix_eval M rho p) ->
    matrix_context_designated M rho Gamma ->
    matrix_context_designated M rho (p :: Gamma).
Proof.
  intros M rho p Gamma Hp Hctx s Hs. simpl in Hs.
  destruct Hs as [<- | Hs].
  - exact Hp.
  - apply Hctx. exact Hs.
Qed.

Theorem rule_preservation_semantic_soundness : forall M,
    preserves_intuitionistic_rules M ->
    forall Gamma p,
      intuitionistically_derives Gamma p ->
      forall rho, matrix_context_designated M rho Gamma ->
      designated M (matrix_eval M rho p).
Proof.
  intros M R Gamma p Hderives.
  unfold intuitionistically_derives in Hderives.
  induction Hderives; intros rho Hctx; simpl in *.
  - apply Hctx. exact H.
  - contradiction.
  - eapply (preserves_false_elim R); eauto.
  - eapply (preserves_and_intro R); eauto.
  - eapply (preserves_and_elim_left R); eauto.
  - eapply (preserves_and_elim_right R); eauto.
  - eapply (preserves_or_intro_left R); eauto.
  - eapply (preserves_or_intro_right R); eauto.
  - eapply (preserves_or_elim R).
    + apply IHHderives1. exact Hctx.
    + intro Hp. apply IHHderives2.
      apply matrix_context_designated_cons; [exact Hp | exact Hctx].
    + intro Hq. apply IHHderives3.
      apply matrix_context_designated_cons; [exact Hq | exact Hctx].
  - apply (preserves_imp_intro R). intro Hp.
    apply IHHderives.
    apply matrix_context_designated_cons; [exact Hp | exact Hctx].
  - eapply (preserves_imp_elim R).
    + apply IHHderives1. exact Hctx.
    + apply IHHderives2. exact Hctx.
Qed.

Corollary rule_preservation_implies_theorem_soundness : forall M,
    preserves_intuitionistic_rules M -> sound_for_IPC_theorems M.
Proof.
  intros M R p Hderives rho.
  eapply rule_preservation_semantic_soundness.
  - exact R.
  - exact Hderives.
  - intros q Hin. contradiction.
Qed.

Corollary no_rule_preserving_finite_matrix_characterizes_IPC : forall M,
    preserves_intuitionistic_rules M -> ~ characterizes_IPC M.
Proof.
  intros M _. apply no_finite_matrix_characterizes_IPC.
Qed.

(** * The exact three-valued corollary *)

Inductive three : Type :=
| true_value
| false_value_3
| undecided_value.

Definition three_eq_dec (x y : three) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition make_three_valued_matrix
    (bottom : three)
    (conj disj impl : three -> three -> three)
    (is_designated : three -> Prop) : finite_matrix.
Proof.
  refine
    {| value := three;
       value_eq_dec := three_eq_dec;
       false_value := bottom;
       and_value := conj;
       or_value := disj;
       imp_value := impl;
       designated := is_designated;
       values := [true_value; false_value_3; undecided_value] |}.
  intros x. destruct x; simpl; auto.
Defined.

Definition three_value_obstruction : formula nat := goedel_formula 3.

Lemma three_value_obstruction_has_six_disjuncts :
    length (goedel_disjuncts 3) = 6.
Proof. reflexivity. Qed.

Theorem sound_three_valued_matrix_validates_obstruction :
    forall bottom conj disj impl is_designated,
    let M := make_three_valued_matrix
      bottom conj disj impl is_designated in
    sound_for_IPC_theorems M -> matrix_valid M three_value_obstruction.
Proof.
  intros bottom conj disj impl is_designated M Hsound.
  unfold three_value_obstruction.
  change (matrix_valid M (goedel_formula (length (values M)))).
  apply sound_finite_matrix_validates_goedel_formula. exact Hsound.
Qed.

Theorem three_value_obstruction_not_in_IPC :
    ~ intuitionistically_derives [] three_value_obstruction.
Proof.
  apply goedel_formula_not_intuitionistically_derivable.
Qed.

Theorem no_three_valued_matrix_characterizes_IPC :
    forall bottom conj disj impl is_designated,
    let M := make_three_valued_matrix
      bottom conj disj impl is_designated in
    ~ characterizes_IPC M.
Proof.
  intros bottom conj disj impl is_designated M.
  apply no_finite_matrix_characterizes_IPC.
Qed.

Corollary no_rule_preserving_three_valued_matrix_characterizes_IPC :
    forall bottom conj disj impl is_designated,
    let M := make_three_valued_matrix
      bottom conj disj impl is_designated in
    preserves_intuitionistic_rules M -> ~ characterizes_IPC M.
Proof.
  intros bottom conj disj impl is_designated M R.
  apply no_rule_preserving_finite_matrix_characterizes_IPC. exact R.
Qed.

End FiniteMatrixTheorem.
