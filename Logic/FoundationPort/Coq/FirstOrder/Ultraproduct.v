(** Pointwise first-order ultraproducts and Łoś's theorem. *)

From Stdlib Require Import Logic.ClassicalChoice Logic.ClassicalEpsilon
  Logic.Classical_Prop Logic.FunctionalExtensionality Lists.List Vectors.Fin.
From Foundation.Vorspiel.Set Require Import Basic Ultrafilter.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics ModelTheory Elementary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

Record first_order_ultraproduct {I : Type} (A : I -> Type)
    (U : set_ultrafilter I) : Type := {
  ultraproduct_value : forall i, A i
}.

Arguments ultraproduct_value {I A U} _ _.

Lemma first_order_ultraproduct_ext : forall I (A : I -> Type)
    (U : set_ultrafilter I) (x y : first_order_ultraproduct A U),
  (forall i, ultraproduct_value x i = ultraproduct_value y i) -> x = y.
Proof.
  intros I A U [x] [y] H. cbn in H. f_equal.
  apply functional_extensionality_dep. exact H.
Qed.

Definition first_order_ultraproduct_structure {L I} {A : I -> Type}
    (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) :
    first_order_structure L (first_order_ultraproduct A U) :=
  {| structure_func := fun _ F v =>
       {| ultraproduct_value := fun i =>
          structure_func (S i) F
            (fun x => ultraproduct_value (v x) i) |};
     structure_rel := fun _ R v =>
       ultrafilter_member U (fun i =>
         structure_rel (S i) R
           (fun x => ultraproduct_value (v x) i)) |}.

Lemma first_order_ultraproduct_structure_func : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) k (F : language_func L k) v i,
  ultraproduct_value
    (structure_func (first_order_ultraproduct_structure S U) F v) i =
  structure_func (S i) F (fun x => ultraproduct_value (v x) i).
Proof. reflexivity. Qed.

Lemma first_order_ultraproduct_structure_rel : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) k (R : language_rel L k) v,
  structure_rel (first_order_ultraproduct_structure S U) R v <->
  ultrafilter_member U (fun i =>
    structure_rel (S i) R (fun x => ultraproduct_value (v x) i)).
Proof. reflexivity. Qed.

Definition first_order_ultraproduct_inhabited {I} {A : I -> Type}
    (U : set_ultrafilter I) (HA : forall i, inhabited (A i)) :
    inhabited (first_order_ultraproduct A U) :=
  inhabits {| ultraproduct_value := fun i =>
    epsilon (HA i) (fun _ => True) |}.

Lemma first_order_ultraproduct_term_value : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) X n (t : semiterm L X n)
    (b : Fin.t n -> first_order_ultraproduct A U)
    (f : X -> first_order_ultraproduct A U) i,
  ultraproduct_value
    (semiterm_val (first_order_ultraproduct_structure S U) b f t) i =
  semiterm_val (S i)
    (fun x => ultraproduct_value (b x) i)
    (fun x => ultraproduct_value (f x) i) t.
Proof.
  intros L I A S U X n t; induction t as [j | x | k F v IH];
    intros b f i; cbn; try reflexivity.
  f_equal. apply functional_extensionality. intro j. apply IH.
Qed.

Corollary first_order_ultraproduct_term_value_eq : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) X n (t : semiterm L X n)
    (b : Fin.t n -> first_order_ultraproduct A U)
    (f : X -> first_order_ultraproduct A U),
  semiterm_val (first_order_ultraproduct_structure S U) b f t =
  {| ultraproduct_value := fun i =>
      semiterm_val (S i)
        (fun x => ultraproduct_value (b x) i)
        (fun x => ultraproduct_value (f x) i) t |}.
Proof.
  intros. apply first_order_ultraproduct_ext.
  intro i. apply first_order_ultraproduct_term_value.
Qed.

Lemma first_order_ultraproduct_fin_env_cons : forall I
    (A : I -> Type) (U : set_ultrafilter I) n
    (z : first_order_ultraproduct A U)
    (b : Fin.t n -> first_order_ultraproduct A U) i,
  (fun x => ultraproduct_value (fin_env_cons z b x) i) =
  fin_env_cons (ultraproduct_value z i)
    (fun x => ultraproduct_value (b x) i).
Proof.
  intros I A U n z b i. apply functional_extensionality. intro j.
  refine (@Fin.caseS' n j (fun x =>
    ultraproduct_value (fin_env_cons z b x) i =
    fin_env_cons (ultraproduct_value z i)
      (fun y => ultraproduct_value (b y) i) x) eq_refl _).
  intro x. reflexivity.
Qed.

Theorem first_order_ultraproduct_formula_eval : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) (HA : forall i, inhabited (A i))
    X n (phi : semiformula L X n)
    (b : Fin.t n -> first_order_ultraproduct A U)
    (f : X -> first_order_ultraproduct A U),
  semiformula_eval (first_order_ultraproduct_structure S U) b f phi <->
  ultrafilter_member U (fun i =>
    semiformula_eval (S i)
      (fun x => ultraproduct_value (b x) i)
      (fun x => ultraproduct_value (f x) i) phi).
Proof.
  intros L I A S U HA X n phi; induction phi as
    [n | n | n k R v | n k R v |
     n phi IHphi psi IHpsi | n phi IHphi psi IHpsi |
     n phi IHphi | n phi IHphi]; intros b f; cbn.
  - split; intro.
    + apply ultrafilter_universal_mem.
    + constructor.
  - split; intro H.
    + contradiction.
    + exfalso. exact (ultrafilter_void_not_mem H).
  - apply ultrafilter_member_equiv. intro i. cbn.
    assert (Hv :
      (fun x => ultraproduct_value
        (semiterm_val (first_order_ultraproduct_structure S U)
          b f (v x)) i) =
      (fun x => semiterm_val (S i)
        (fun j => ultraproduct_value (b j) i)
        (fun y => ultraproduct_value (f y) i) (v x))).
    { apply functional_extensionality. intro x.
      apply first_order_ultraproduct_term_value. }
    now rewrite Hv.
  - rewrite <- ultrafilter_complement_mem_iff.
    apply ultrafilter_member_equiv. intro i. cbn.
    assert (Hv :
      (fun x => ultraproduct_value
        (semiterm_val (first_order_ultraproduct_structure S U)
          b f (v x)) i) =
      (fun x => semiterm_val (S i)
        (fun j => ultraproduct_value (b j) i)
        (fun y => ultraproduct_value (f y) i) (v x))).
    { apply functional_extensionality. intro x.
      apply first_order_ultraproduct_term_value. }
    unfold set_complement. now rewrite Hv.
  - rewrite IHphi, IHpsi.
    unfold set_intersection. symmetry.
    apply ultrafilter_intersection_mem_iff.
  - rewrite IHphi, IHpsi.
    unfold set_union. symmetry.
    apply ultrafilter_union_mem_iff.
  - split.
    + intro Hall.
      pose (z := ({| ultraproduct_value := fun i => epsilon (HA i) (fun a =>
          ~ semiformula_eval (S i)
            (fin_env_cons a (fun x => ultraproduct_value (b x) i))
            (fun x => ultraproduct_value (f x) i) phi) |} :
        first_order_ultraproduct A U)).
      pose proof (proj1 (IHphi (fin_env_cons z b) f) (Hall z)) as Hz.
      eapply ultrafilter_mem_of_superset; [|exact Hz].
      intros i Hi a.
      rewrite first_order_ultraproduct_fin_env_cons in Hi.
      apply NNPP. intro Ha.
      pose proof (epsilon_spec (HA i)
        (fun x => ~ semiformula_eval (S i)
          (fin_env_cons x (fun j => ultraproduct_value (b j) i))
          (fun x => ultraproduct_value (f x) i) phi)
        (ex_intro _ a Ha)) as Hznot.
      exact (Hznot Hi).
    + intro Hlarge. intro z.
      apply (proj2 (IHphi (fin_env_cons z b) f)).
      eapply ultrafilter_mem_of_superset; [|exact Hlarge].
      intros i Hi. rewrite first_order_ultraproduct_fin_env_cons.
      exact (Hi (ultraproduct_value z i)).
  - split.
    + intros [z Hz].
      apply (proj1 (IHphi (fin_env_cons z b) f)) in Hz.
      eapply ultrafilter_mem_of_superset; [|exact Hz].
      intros i Hi. exists (ultraproduct_value z i).
      rewrite <- first_order_ultraproduct_fin_env_cons. exact Hi.
    + intro Hlarge.
      pose (z := ({| ultraproduct_value := fun i => epsilon (HA i) (fun a =>
          semiformula_eval (S i)
            (fin_env_cons a (fun x => ultraproduct_value (b x) i))
            (fun x => ultraproduct_value (f x) i) phi) |} :
        first_order_ultraproduct A U)).
      exists z. apply (proj2 (IHphi (fin_env_cons z b) f)).
      eapply ultrafilter_mem_of_superset; [|exact Hlarge].
      intros i [a Ha].
      pose proof (epsilon_spec (HA i)
        (fun x => semiformula_eval (S i)
          (fin_env_cons x (fun j => ultraproduct_value (b j) i))
          (fun x => ultraproduct_value (f x) i) phi)
        (ex_intro _ a Ha)) as Hz.
      rewrite first_order_ultraproduct_fin_env_cons. exact Hz.
Qed.

Corollary first_order_ultraproduct_formula_realize : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) (HA : forall i, inhabited (A i))
    X (phi : formula L X)
    (f : X -> first_order_ultraproduct A U),
  formula_eval (first_order_ultraproduct_structure S U) f phi <->
  ultrafilter_member U (fun i =>
    formula_eval (S i) (fun x => ultraproduct_value (f x) i) phi).
Proof.
  intros L I A S U HA X phi f. unfold formula_eval.
  etransitivity.
  - apply first_order_ultraproduct_formula_eval; exact HA.
  - apply ultrafilter_member_equiv. intro i.
    apply semiformula_eval_bound_extensional. intro j. inversion j.
Qed.

Corollary first_order_ultraproduct_sentence_realize : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) (HA : forall i, inhabited (A i))
    (sigma : sentence L),
  sentence_realize (first_order_ultraproduct_structure S U) sigma <->
  ultrafilter_member U (fun i => sentence_realize (S i) sigma).
Proof.
  intros L I A S U HA sigma. unfold sentence_realize.
  etransitivity.
  - apply first_order_ultraproduct_formula_realize; exact HA.
  - apply ultrafilter_member_equiv. intro i.
    apply semiformula_eval_free_ext. intros x _. destruct x.
Qed.

Definition first_order_ultraproduct_model {L I} (A : I -> Type)
    (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) (HA : forall i, inhabited (A i)) :
    first_order_model L :=
  first_order_model_of_structure
    (first_order_ultraproduct_inhabited U HA)
    (first_order_ultraproduct_structure S U).

Corollary first_order_ultraproduct_model_realize : forall L I
    (A : I -> Type) (S : forall i, first_order_structure L (A i))
    (U : set_ultrafilter I) (HA : forall i, inhabited (A i))
    (sigma : sentence L),
  first_order_model_realize
    (@first_order_ultraproduct_model L I A S U HA) sigma <->
  ultrafilter_member U (fun i => sentence_realize (S i) sigma).
Proof.
  intros. exact (@first_order_ultraproduct_sentence_realize
    L I A S U HA sigma).
Qed.

(** * Semantic compactness *)

(** Lists give the finite subtheories directly.  Unlike finite sets, this
    representation needs neither decidable sentence equality nor quotienting;
    duplicate assumptions are semantically harmless. *)
Record first_order_finite_subtheory {L} (T : theory L) : Type := {
  finite_subtheory_sentences : list (sentence L);
  finite_subtheory_subset : forall sigma,
    In sigma finite_subtheory_sentences -> T sigma
}.

Arguments finite_subtheory_sentences {L T} _.

Definition finite_subtheory_theory {L} {T : theory L}
    (Gamma : first_order_finite_subtheory T) : theory L :=
  fun sigma => In sigma (finite_subtheory_sentences Gamma).

Definition empty_finite_subtheory {L} (T : theory L) :
    first_order_finite_subtheory T :=
  {| finite_subtheory_sentences := [];
     finite_subtheory_subset := fun sigma H => match H with end |}.

Definition first_order_sentence_domain {L I}
    (M : I -> first_order_model L) (sigma : sentence L) : pred_set I :=
  fun i => first_order_model_realize (M i) sigma.

Lemma first_order_sentence_domains_fip : forall L (T : theory L)
    (M : first_order_finite_subtheory T -> first_order_model L),
  (forall i, first_order_models_theory (M i) (finite_subtheory_theory i)) ->
  set_family_finite_intersection_property
    (fun d => exists sigma, T sigma /\
      d = first_order_sentence_domain M sigma).
Proof.
  intros L T M HM domains Hdomains.
  destruct domains as [|d domains].
  - exists (empty_finite_subtheory T). cbn. constructor.
  - destruct (Hdomains d (or_introl eq_refl)) as
      [sigma0 [HT0 Hd0]].
    pose (pick := fun e : pred_set (first_order_finite_subtheory T) =>
      epsilon (inhabits sigma0) (fun sigma =>
        T sigma /\ e = first_order_sentence_domain M sigma)).
    assert (Hpick : forall e, In e (d :: domains) ->
      T (pick e) /\ e = first_order_sentence_domain M (pick e)).
    { intros e He. unfold pick. apply epsilon_spec.
      exact (Hdomains e He). }
    pose (sentences := map pick (d :: domains)).
    assert (Hsentences : forall sigma, In sigma sentences -> T sigma).
    { intros sigma Hsigma. unfold sentences in Hsigma.
      apply in_map_iff in Hsigma. destruct Hsigma as [e [<- He]].
      exact (proj1 (Hpick e He)). }
    pose (i := {| finite_subtheory_sentences := sentences;
      finite_subtheory_subset := Hsentences |}).
    exists i. apply (proj2 (@set_list_intersection_member_iff
      (first_order_finite_subtheory T) (d :: domains) i)).
    intros e He.
    destruct (Hpick e He) as [_ Heq]. rewrite Heq.
    apply (first_order_models_of_member (HM i)).
    unfold finite_subtheory_theory, sentences.
    apply in_map. exact He.
Qed.

Theorem first_order_ultrafilter_exists : forall L (T : theory L)
    (M : first_order_finite_subtheory T -> first_order_model L),
  (forall i, first_order_models_theory (M i) (finite_subtheory_theory i)) ->
  exists U : set_ultrafilter (first_order_finite_subtheory T),
    forall sigma, T sigma ->
      ultrafilter_member U (first_order_sentence_domain M sigma).
Proof.
  intros L T M HM.
  destruct (ultrafilter_of_finite_intersection_property
    (first_order_sentence_domains_fip HM)) as [U HU].
  exists U. intros sigma Hsigma. apply HU.
  now exists sigma.
Qed.

Theorem first_order_compactness_aux : forall L (T : theory L),
  first_order_satisfiable T <->
  forall i : first_order_finite_subtheory T,
    first_order_satisfiable (finite_subtheory_theory i).
Proof.
  intros L T. split.
  - intros [m Hm] i. exists m.
    eapply first_order_models_of_subset; [exact Hm |].
    intros sigma Hsigma. exact (@finite_subtheory_subset L T i sigma Hsigma).
  - intro Hfinite.
    assert (Hmodels : forall i : first_order_finite_subtheory T,
      exists m : first_order_model L,
        first_order_models_theory m (finite_subtheory_theory i)).
    { intro i. exact (Hfinite i). }
    destruct (@choice (first_order_finite_subtheory T)
      (first_order_model L)
      (fun i m => first_order_models_theory m (finite_subtheory_theory i))
      Hmodels) as [M HM].
    destruct (@first_order_ultrafilter_exists L T M HM) as [U HU].
    pose (A := fun i : first_order_finite_subtheory T =>
      first_order_model_domain (M i)).
    pose (S := fun i : first_order_finite_subtheory T =>
      first_order_model_structure (M i)).
    pose (HA := fun i : first_order_finite_subtheory T =>
      first_order_model_nonempty (M i)).
    exists (@first_order_ultraproduct_model L
      (first_order_finite_subtheory T) A S U HA).
    apply (proj2 (first_order_models_theory_iff
      (@first_order_ultraproduct_model L
        (first_order_finite_subtheory T) A S U HA) T)).
    intros sigma Hsigma.
    apply (proj2 (@first_order_ultraproduct_model_realize L
      (first_order_finite_subtheory T) A S U HA sigma)).
    exact (HU sigma Hsigma).
Qed.

Theorem first_order_compactness : forall L (T : theory L),
  first_order_satisfiable T <->
  forall Gamma : list (sentence L),
    (forall sigma, In sigma Gamma -> T sigma) ->
    first_order_satisfiable (fun sigma => In sigma Gamma).
Proof.
  intros L T. rewrite first_order_compactness_aux. split.
  - intros Hall Gamma Hsubset.
    exact (Hall {| finite_subtheory_sentences := Gamma;
      finite_subtheory_subset := Hsubset |}).
  - intros Hall [Gamma Hsubset]. exact (Hall Gamma Hsubset).
Qed.
