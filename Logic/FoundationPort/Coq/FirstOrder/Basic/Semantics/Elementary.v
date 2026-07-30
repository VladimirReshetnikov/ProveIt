(**
  Homomorphisms, embeddings, closed substructures, and elementary equivalence.

  This ports the mathematical surface of
  [Foundation/FirstOrder/Basic/Semantics/Elementary.lean].  Maps and
  structures are explicit, avoiding a parallel hierarchy of typeclasses.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Logic.ProofIrrelevance.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics RewriteClosure ModelTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma semiformula_eval_bound_extensional :
  forall L M X n (S : first_order_structure L M)
         (b c : Fin.t n -> M) (f : X -> M) (p : semiformula L X n),
    (forall i, b i = c i) ->
    (semiformula_eval S b f p <-> semiformula_eval S c f p).
Proof.
  intros L M X n S b c f p H.
  assert (Hbc : b = c) by (apply functional_extensionality; exact H).
  now subst c.
Qed.

(** * Structure maps *)

Record first_order_hom {L M N}
    (S : first_order_structure L M) (T : first_order_structure L N) : Type := {
  first_order_hom_fun : M -> N;
  first_order_hom_func : forall k (F : language_func L k) (v : Fin.t k -> M),
    first_order_hom_fun (structure_func S F v) =
    structure_func T F (fun i => first_order_hom_fun (v i));
  first_order_hom_rel : forall k (R : language_rel L k) (v : Fin.t k -> M),
    structure_rel S R v ->
    structure_rel T R (fun i => first_order_hom_fun (v i))
}.

Arguments first_order_hom_fun {L M N S T} _ _.

Record first_order_embedding {L M N}
    (S : first_order_structure L M) (T : first_order_structure L N) : Type := {
  first_order_embedding_fun : M -> N;
  first_order_embedding_func : forall k (F : language_func L k)
      (v : Fin.t k -> M),
    first_order_embedding_fun (structure_func S F v) =
    structure_func T F (fun i => first_order_embedding_fun (v i));
  first_order_embedding_rel : forall k (R : language_rel L k)
      (v : Fin.t k -> M),
    structure_rel S R v <->
    structure_rel T R (fun i => first_order_embedding_fun (v i));
  first_order_embedding_injective : forall x y,
    first_order_embedding_fun x = first_order_embedding_fun y -> x = y
}.

Arguments first_order_embedding_fun {L M N S T} _ _.

Definition first_order_embedding_to_hom {L M N}
    {S : first_order_structure L M} {T : first_order_structure L N}
    (e : first_order_embedding S T) : first_order_hom S T :=
  {| first_order_hom_fun := first_order_embedding_fun e;
     first_order_hom_func := first_order_embedding_func e;
     first_order_hom_rel := fun _ R v =>
       proj1 (first_order_embedding_rel e R v) |}.

Record first_order_iso {L M N}
    (S : first_order_structure L M) (T : first_order_structure L N) : Type := {
  first_order_iso_embedding : first_order_embedding S T;
  first_order_iso_surjective : forall y : N, exists x : M,
    first_order_embedding_fun first_order_iso_embedding x = y
}.

Lemma first_order_hom_semiterm_val :
  forall L M N X n (S : first_order_structure L M)
         (T : first_order_structure L N) (h : first_order_hom S T)
         (b : Fin.t n -> M) (f : X -> M) (t : semiterm L X n),
    first_order_hom_fun h (semiterm_val S b f t) =
    semiterm_val T
      (fun i => first_order_hom_fun h (b i))
      (fun x => first_order_hom_fun h (f x)) t.
Proof.
  intros L M N X n S T h b f t.
  induction t as [i | x | k F v IH]; simpl; try reflexivity.
  rewrite first_order_hom_func. f_equal.
  apply functional_extensionality. exact IH.
Qed.

Lemma first_order_embedding_semiterm_val :
  forall L M N X n (S : first_order_structure L M)
         (T : first_order_structure L N) (e : first_order_embedding S T)
         (b : Fin.t n -> M) (f : X -> M) (t : semiterm L X n),
    first_order_embedding_fun e (semiterm_val S b f t) =
    semiterm_val T
      (fun i => first_order_embedding_fun e (b i))
      (fun x => first_order_embedding_fun e (f x)) t.
Proof.
  intros. exact (first_order_hom_semiterm_val
    (first_order_embedding_to_hom e) b f t).
Qed.

(** Embeddings preserve and reflect quantifier-free formulas.  No
    surjectivity is needed because an open formula never ranges over the
    target carrier. *)
Theorem first_order_embedding_eval_open :
  forall L M N X n (S : first_order_structure L M)
         (T : first_order_structure L N) (e : first_order_embedding S T)
         (b : Fin.t n -> M) (f : X -> M) (p : semiformula L X n),
    semiformula_open p ->
    (semiformula_eval S b f p <->
     semiformula_eval T
       (fun i => first_order_embedding_fun e (b i))
       (fun x => first_order_embedding_fun e (f x)) p).
Proof.
  intros L M N X n S T e b f p; revert b.
  induction p; intros b Hopen; simpl.
  - tauto.
  - tauto.
  - assert (Hargs :
      (fun i => semiterm_val T
        (fun j => first_order_embedding_fun e (b j))
        (fun x => first_order_embedding_fun e (f x)) (s i)) =
      (fun i => first_order_embedding_fun e (semiterm_val S b f (s i)))).
    { apply functional_extensionality. intro i. symmetry.
      apply first_order_embedding_semiterm_val. }
    rewrite Hargs. apply first_order_embedding_rel.
  - assert (Hargs :
      (fun i => semiterm_val T
        (fun j => first_order_embedding_fun e (b j))
        (fun x => first_order_embedding_fun e (f x)) (s i)) =
      (fun i => first_order_embedding_fun e (semiterm_val S b f (s i)))).
    { apply functional_extensionality. intro i. symmetry.
      apply first_order_embedding_semiterm_val. }
    rewrite Hargs, <- first_order_embedding_rel. tauto.
  - destruct (proj1 (semiformula_open_and p1 p2) Hopen) as [H1 H2].
    rewrite (IHp1 b H1), (IHp2 b H2). tauto.
  - destruct (proj1 (semiformula_open_or p1 p2) Hopen) as [H1 H2].
    rewrite (IHp1 b H1), (IHp2 b H2). tauto.
  - unfold semiformula_open in Hopen. simpl in Hopen. discriminate.
  - unfold semiformula_open in Hopen. simpl in Hopen. discriminate.
Qed.

Theorem first_order_embedding_eval_all_closure_open :
  forall L M N X n (S : first_order_structure L M)
         (T : first_order_structure L N) (e : first_order_embedding S T)
         (bM : Fin.t 0 -> M) (bN : Fin.t 0 -> N)
         (f : X -> M) (p : semiformula L X n),
    semiformula_open p ->
    semiformula_eval T bN (fun x => first_order_embedding_fun e (f x))
      (first_all_closure (semiformula_universal_quantifier L X) n p) ->
    semiformula_eval S bM f
      (first_all_closure (semiformula_universal_quantifier L X) n p).
Proof.
  intros L M N X n S T e bM bN f p Hopen Htarget.
  apply (proj2 (@semiformula_eval_all_closure L M X n S bM f p)). intro env.
  apply (proj2 (@first_order_embedding_eval_open
    L M N X n S T e env f p Hopen)).
  pose proof (proj1 (@semiformula_eval_all_closure L N X n T bN
    (fun x => first_order_embedding_fun e (f x)) p) Htarget) as Hall.
  exact (Hall (fun i => first_order_embedding_fun e (env i))).
Qed.

(** * Closed subsets and their inclusion embeddings *)

Record first_order_closed_subset {L M} (S : first_order_structure L M) : Type := {
  first_order_closed_subset_pred : M -> Prop;
  first_order_closed_subset_func : forall k (F : language_func L k)
      (v : Fin.t k -> M),
    (forall i, first_order_closed_subset_pred (v i)) ->
    first_order_closed_subset_pred (structure_func S F v)
}.

Arguments first_order_closed_subset_pred {L M S} _ _.

Definition first_order_closed_subset_structure {L M}
    {S : first_order_structure L M} (U : first_order_closed_subset S) :
    first_order_structure L {x : M | first_order_closed_subset_pred U x} :=
  {| structure_func := fun k F v =>
       exist _ (structure_func S F (fun i => proj1_sig (v i)))
         (@first_order_closed_subset_func L M S U k F
           (fun i => proj1_sig (v i)) (fun i => proj2_sig (v i)));
     structure_rel := fun k R v =>
       structure_rel S R (fun i => proj1_sig (v i)) |}.

Definition first_order_closed_subset_inclusion {L M}
    {S : first_order_structure L M} (U : first_order_closed_subset S) :
    first_order_embedding (first_order_closed_subset_structure U) S.
Proof.
  refine {| first_order_embedding_fun := @proj1_sig M _ |}.
  - reflexivity.
  - intros. reflexivity.
  - intros [x Hx] [y Hy] H. simpl in H. subst y.
    f_equal. apply proof_irrelevance.
Defined.

(** * Truth invariance under an equivalence of carriers *)

Lemma carrier_equiv_to_fin_env_cons :
  forall M N n (e : carrier_equiv M N) (x : M) (b : Fin.t n -> M),
    (fun i => carrier_equiv_to e (fin_env_cons x b i)) =
    fin_env_cons (carrier_equiv_to e x)
      (fun i => carrier_equiv_to e (b i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    carrier_equiv_to e (fin_env_cons x b j) =
    fin_env_cons (carrier_equiv_to e x)
      (fun u => carrier_equiv_to e (b u)) j) eq_refl _).
  intro j. reflexivity.
Qed.

Theorem semiformula_eval_carrier_equiv :
  forall L M N X n (S : first_order_structure L M)
         (T : first_order_structure L N) (e : carrier_equiv M N)
         (Hfunc : forall k (F : language_func L k) (v : Fin.t k -> M),
           carrier_equiv_to e (structure_func S F v) =
           structure_func T F (fun i => carrier_equiv_to e (v i)))
         (Hrel : forall k (R : language_rel L k) (v : Fin.t k -> M),
           structure_rel S R v <->
           structure_rel T R (fun i => carrier_equiv_to e (v i)))
         (b : Fin.t n -> M) (f : X -> M) (p : semiformula L X n),
    semiformula_eval S b f p <->
    semiformula_eval T
      (fun i => carrier_equiv_to e (b i))
      (fun x => carrier_equiv_to e (f x)) p.
Proof.
  intros L M N X n S T e Hfunc Hrel b f p; revert b.
  assert (Hterm : forall j (b0 : Fin.t j -> M) (t : semiterm L X j),
    carrier_equiv_to e (semiterm_val S b0 f t) =
    semiterm_val T
      (fun i => carrier_equiv_to e (b0 i))
      (fun x => carrier_equiv_to e (f x)) t).
  { intros j b0 t. induction t as [i | x | k F v IH]; simpl; try reflexivity.
    rewrite Hfunc. f_equal. apply functional_extensionality. exact IH. }
  induction p; intro b; simpl; try tauto.
  - assert (Hargs :
      (fun i => semiterm_val T
        (fun j => carrier_equiv_to e (b j))
        (fun x => carrier_equiv_to e (f x)) (s i)) =
      (fun i => carrier_equiv_to e (semiterm_val S b f (s i)))).
    { apply functional_extensionality. intro i. symmetry. apply Hterm. }
    rewrite Hargs. apply Hrel.
  - assert (Hargs :
      (fun i => semiterm_val T
        (fun j => carrier_equiv_to e (b j))
        (fun x => carrier_equiv_to e (f x)) (s i)) =
      (fun i => carrier_equiv_to e (semiterm_val S b f (s i)))).
    { apply functional_extensionality. intro i. symmetry. apply Hterm. }
    rewrite Hargs, <- Hrel. tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - split; intros H y.
    + specialize (H (carrier_equiv_from e y)).
      apply (proj1 (IHp (fin_env_cons (carrier_equiv_from e y) b))) in H.
      rewrite carrier_equiv_to_fin_env_cons in H.
      rewrite carrier_equiv_to_from in H. exact H.
    + apply (proj2 (IHp (fin_env_cons y b))).
      rewrite carrier_equiv_to_fin_env_cons. apply H.
  - split; intros H.
    + destruct H as [x Hx]. exists (carrier_equiv_to e x).
      apply (proj1 (IHp (fin_env_cons x b))) in Hx.
      now rewrite carrier_equiv_to_fin_env_cons in Hx.
    + destruct H as [y Hy]. exists (carrier_equiv_from e y).
      apply (proj2 (IHp (fin_env_cons (carrier_equiv_from e y) b))).
      rewrite carrier_equiv_to_fin_env_cons, carrier_equiv_to_from. exact Hy.
Qed.

(** * Elementary equivalence of bundled models *)

Record first_order_elementary_equiv {L}
    (m n : first_order_model L) : Prop := {
  first_order_elementary_equiv_realize : forall p : sentence L,
    first_order_model_realize m p <-> first_order_model_realize n p
}.

Lemma first_order_elementary_equiv_refl :
  forall L (m : first_order_model L), first_order_elementary_equiv m m.
Proof. intros. constructor. reflexivity. Qed.

Lemma first_order_elementary_equiv_sym :
  forall L (m n : first_order_model L),
    first_order_elementary_equiv m n -> first_order_elementary_equiv n m.
Proof. intros L m n H. constructor. intro p. symmetry. apply H. Qed.

Lemma first_order_elementary_equiv_trans :
  forall L (m n q : first_order_model L),
    first_order_elementary_equiv m n ->
    first_order_elementary_equiv n q ->
    first_order_elementary_equiv m q.
Proof.
  intros L m n q Hmn Hnq. constructor. intro p.
  transitivity (first_order_model_realize n p); [apply Hmn | apply Hnq].
Qed.

Lemma first_order_elementary_equiv_models_theory :
  forall L (m n : first_order_model L) (T : theory L),
    first_order_elementary_equiv m n ->
    (first_order_models_theory m T <-> first_order_models_theory n T).
Proof.
  intros L m n T H. rewrite !first_order_models_theory_iff.
  split; intros Hmodels p Hp; apply (first_order_elementary_equiv_realize H p);
    auto.
Qed.

Theorem first_order_elementary_equiv_of_carrier_equiv :
  forall L M N (S : first_order_structure L M)
         (T : first_order_structure L N) (HM : inhabited M) (HN : inhabited N)
         (e : carrier_equiv M N)
         (Hfunc : forall k (F : language_func L k) (v : Fin.t k -> M),
           carrier_equiv_to e (structure_func S F v) =
           structure_func T F (fun i => carrier_equiv_to e (v i)))
         (Hrel : forall k (R : language_rel L k) (v : Fin.t k -> M),
           structure_rel S R v <->
           structure_rel T R (fun i => carrier_equiv_to e (v i))),
    first_order_elementary_equiv
      (first_order_model_of_structure HM S)
      (first_order_model_of_structure HN T).
Proof.
  intros. constructor. intro p.
  unfold first_order_model_realize, sentence_realize, formula_eval. simpl.
  pose proof (@semiformula_eval_carrier_equiv L M N Empty_set 0 S T e
    Hfunc Hrel
    (fun i : Fin.t 0 => match i with end)
    (fun x : Empty_set => match x with end) p) as Heval.
  etransitivity.
  - exact Heval.
  - transitivity (semiformula_eval T
      (fun i : Fin.t 0 => match i with end)
      (fun x : Empty_set => carrier_equiv_to e
        ((fun y : Empty_set => match y with end) x)) p).
    + apply semiformula_eval_bound_extensional. intro i. inversion i.
    + apply semiformula_eval_free_ext. intros x _. destruct x.
Qed.
