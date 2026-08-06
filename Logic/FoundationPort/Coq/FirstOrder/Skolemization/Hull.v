(**
  Skolem functions and Skolem hulls.

  This ports the semantic core of
  [Foundation/FirstOrder/Skolemization/Hull.lean].  The source packages
  structures and formulas through typeclasses; here the language, structure,
  and evaluation are explicit.  The resulting closure theorem is therefore
  reusable for any first-order structure and any seed predicate.
*)

From Stdlib Require Import Logic.ClassicalEpsilon Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics ModelTheory OperatorSemantics Elementary.
From Foundation.FirstOrder.Basic Require Import Operator.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ModelTheory.

(** A Skolem symbol of arity [k] names a formula with one output and [k]
    input variables.  There are no new relation symbols. *)
Definition skolem_language (L : language) : language :=
  {| language_func := fun k => semisentence L (S k);
     language_rel := fun _ => Empty_set |}.

Lemma skolem_language_func : forall L k,
  language_func (skolem_language L) k = semisentence L (S k).
Proof. reflexivity. Qed.

Lemma skolem_language_rel_empty : forall L k,
  language_rel (skolem_language L) k = Empty_set.
Proof. reflexivity. Qed.

Definition skolem_symbol {L k} (phi : semisentence L (Datatypes.S k)) :
    language_func (skolem_language L) k := phi.

Definition skolem_formula {L k}
    (phi : language_func (skolem_language L) k) :
    semisentence L (Datatypes.S k) := phi.

(** Interpret a Skolem symbol by epsilon.  The inhabited carrier supplies the
    harmless default used when a formula has no witness. *)
Definition skolem_structure {L M}
    (Hinh : inhabited M) (S : first_order_structure L M) :
    first_order_structure (skolem_language L) M :=
  @Build_first_order_structure (skolem_language L) M
    (fun _ phi v =>
       epsilon Hinh
         (fun z => semiformula_eval S (fin_env_cons z v)
           (fun x : Empty_set => match x with end) (skolem_formula phi)))
    (fun k r v => match r with end).

Lemma skolem_structure_func : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) k (phi : semisentence L (Datatypes.S k))
    (v : Fin.t k -> M),
  structure_func (skolem_structure Hinh S) (skolem_symbol phi) v =
    epsilon Hinh
      (fun z => semiformula_eval S (fin_env_cons z v)
        (fun x : Empty_set => match x with end) phi).
Proof. reflexivity. Qed.

Lemma skolem_structure_rel_empty : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) k (r : language_rel (skolem_language L) k)
    (v : Fin.t k -> M),
  structure_rel (skolem_structure Hinh S) r v.
Proof. intros L M Hinh S k r; destruct r. Qed.

Lemma skolem_structure_func_spec : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) k (phi : semisentence L (Datatypes.S k))
    (v : Fin.t k -> M),
  (exists z, semiformula_eval S (fin_env_cons z v)
      (fun x : Empty_set => match x with end) phi) ->
  semiformula_eval S
    (fin_env_cons (structure_func (skolem_structure Hinh S)
      (skolem_symbol phi) v) v)
    (fun x : Empty_set => match x with end) phi.
Proof.
  intros L M Hinh S k phi v Hex.
  apply (@epsilon_spec M Hinh
    (fun z => semiformula_eval S (fin_env_cons z v)
      (fun x : Empty_set => match x with end) phi)).
  exact Hex.
Qed.

(** A graph formula for an original function symbol.  Its first bound
    variable is the output and the remaining variables are the inputs. *)
Definition skolem_graph_output {L k} :
    semiterm L Empty_set (Datatypes.S k) := Semiterm_bvar Fin.F1.

Definition skolem_graph_arg {L k} (i : Fin.t k) :
    semiterm L Empty_set (Datatypes.S k) := Semiterm_bvar (Fin.FS i).

Definition skolem_graph_term {L k} (F : language_func L k) :
    semiterm L Empty_set (Datatypes.S k) :=
  Semiterm_func F (fun i => skolem_graph_arg i).

Definition skolem_graph_formula {L k}
    (Heq : semiformula_has_eq_operator L) (F : language_func L k) :
    semisentence L (Datatypes.S k) :=
  semiformula_operator_apply (semiformula_eq_operator Heq)
    (fin_two skolem_graph_output (skolem_graph_term F)).

Lemma skolem_graph_exists : forall L M k
    (S : first_order_structure L M)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    (F : language_func L k) (v : Fin.t k -> M),
  exists z, semiformula_eval S (fin_env_cons z v)
    (fun x : Empty_set => match x with end)
    (skolem_graph_formula Heq F).
Proof.
  intros L M k S Heq Hstd F v.
  exists (structure_func S F v).
  unfold skolem_graph_formula.
  rewrite semiformula_eval_operator_apply.
  assert (Hvec :
    (fun i : Fin.t 2 =>
      semiterm_val S (fin_env_cons (structure_func S F v) v)
        (fun x : Empty_set => match x with end)
        (fin_two skolem_graph_output (skolem_graph_term F) i)) =
    fin_two (structure_func S F v) (structure_func S F v)).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      semiterm_val S (fin_env_cons (structure_func S F v) v)
        (fun x : Empty_set => match x with end)
        (fin_two skolem_graph_output (skolem_graph_term F) j) =
      fin_two (structure_func S F v) (structure_func S F v) j)
      eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      semiterm_val S (fin_env_cons (structure_func S F v) v)
        (fun x : Empty_set => match x with end)
        (fin_two skolem_graph_output (skolem_graph_term F) (Fin.FS q)) =
      fin_two (structure_func S F v) (structure_func S F v) (Fin.FS q))
      eq_refl _).
    intros q; inversion q. }
  rewrite Hvec.
  apply (proj2 (structure_eq_operator Hstd
    (structure_func S F v) (structure_func S F v))).
  reflexivity.
Qed.

(** The hull is the range of closed Skolem terms whose free variables are
    restricted to the seed predicate. *)
Definition skolem_hull {L M}
    (Hinh : inhabited M) (S : first_order_structure L M)
    (seed : M -> Prop) (x : M) : Prop :=
  exists t : semiterm (skolem_language L) {y : M | seed y} 0,
    semiterm_val (skolem_structure Hinh S)
      (fun i : Fin.t 0 => match i with end)
      (fun a : {y : M | seed y} => proj1_sig a) t = x.

Lemma skolem_hull_mem_iff : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop) (x : M),
  skolem_hull Hinh S seed x <->
  exists t : semiterm (skolem_language L) {y : M | seed y} 0,
    semiterm_val (skolem_structure Hinh S)
      (fun i : Fin.t 0 => match i with end)
      (fun a : {y : M | seed y} => proj1_sig a) t = x.
Proof. intros; split; trivial. Qed.

Lemma skolem_hull_term_mem : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (t : semiterm (skolem_language L) {y : M | seed y} 0),
  skolem_hull Hinh S seed
    (semiterm_val (skolem_structure Hinh S)
      (fun i : Fin.t 0 => match i with end)
      (fun a : {y : M | seed y} => proj1_sig a) t).
Proof.
  intros. exists t. reflexivity.
Qed.

Lemma skolem_hull_subset : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop) x,
  seed x -> skolem_hull Hinh S seed x.
Proof.
  intros L M Hinh S seed x Hx.
  exists (Semiterm_fvar (exist _ x Hx)). reflexivity.
Qed.

(** If a formula has a witness over parameters already in the hull, epsilon
    turns that witness into a Skolem term, hence into another hull element. *)
Lemma skolem_hull_closed : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    k (phi : semisentence L (Datatypes.S k)) (v : Fin.t k -> M),
  (forall i, skolem_hull Hinh S seed (v i)) ->
  (exists z, semiformula_eval S (fin_env_cons z v)
      (fun x : Empty_set => match x with end) phi) ->
  exists z, skolem_hull Hinh S seed z /\
    semiformula_eval S (fin_env_cons z v)
      (fun x : Empty_set => match x with end) phi.
Proof.
  intros L M Hinh S seed k phi v Hv Hex.
  assert (Hterms : forall i,
      exists t : semiterm (skolem_language L) {y : M | seed y} 0,
        semiterm_val (skolem_structure Hinh S)
          (fun j : Fin.t 0 => match j with end)
          (fun a : {y : M | seed y} => proj1_sig a) t = v i).
  { intro i. exact (proj1 (skolem_hull_mem_iff Hinh S seed (v i)) (Hv i)). }
  destruct (@fin_forall_exists_choice k
    (semiterm (skolem_language L) {y : M | seed y} 0)
    (fun i t =>
      semiterm_val (skolem_structure Hinh S)
        (fun j : Fin.t 0 => match j with end)
        (fun a : {y : M | seed y} => proj1_sig a) t = v i)
    Hterms) as [u Hu].
  set (z := @structure_func (skolem_language L) M
    (skolem_structure Hinh S) k (skolem_symbol phi)
    (fun i => semiterm_val (skolem_structure Hinh S)
      (fun j : Fin.t 0 => match j with end)
      (fun a : {y : M | seed y} => proj1_sig a) (u i))).
  exists z. split.
  - exists (Semiterm_func (skolem_symbol phi) u). reflexivity.
  - assert (Hspec :
      semiformula_eval S
        (fin_env_cons z
          (fun i => semiterm_val (skolem_structure Hinh S)
            (fun j : Fin.t 0 => match j with end)
            (fun a : {y : M | seed y} => proj1_sig a) (u i)))
        (fun x : Empty_set => match x with end) phi).
    { unfold z. apply skolem_structure_func_spec.
      destruct Hex as [w Hw]. exists w.
      assert (Henv :
        fin_env_cons w
          (fun i => semiterm_val (skolem_structure Hinh S)
            (fun j : Fin.t 0 => match j with end)
            (fun a : {y : M | seed y} => proj1_sig a) (u i)) =
        fin_env_cons w v).
      { apply functional_extensionality. intro i.
        refine (@Fin.caseS' k i (fun j =>
          fin_env_cons w
            (fun q => semiterm_val (skolem_structure Hinh S)
              (fun r : Fin.t 0 => match r with end)
              (fun a : {y : M | seed y} => proj1_sig a) (u q)) j =
          fin_env_cons w v j) eq_refl _).
        intro j. apply Hu. }
      rewrite Henv. exact Hw. }
    assert (Henv :
      fin_env_cons z
        (fun i => semiterm_val (skolem_structure Hinh S)
          (fun j : Fin.t 0 => match j with end)
          (fun a : {y : M | seed y} => proj1_sig a) (u i)) =
      fin_env_cons z v).
    { apply functional_extensionality. intro i.
      refine (@Fin.caseS' k i (fun j =>
        fin_env_cons z
          (fun q => semiterm_val (skolem_structure Hinh S)
            (fun r : Fin.t 0 => match r with end)
            (fun a : {y : M | seed y} => proj1_sig a) (u q)) j =
        fin_env_cons z v j) eq_refl _).
      intro j. apply Hu. }
    rewrite <- Henv. exact Hspec.
Qed.

(** Original functions are closed on the hull whenever equality is interpreted
    as actual Coq equality. *)
Lemma skolem_hull_closed_func : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    k (F : language_func L k) (v : Fin.t k -> M),
  (forall i, skolem_hull Hinh S seed (v i)) ->
  skolem_hull Hinh S seed (structure_func S F v).
Proof.
  intros L M Hinh S seed Heq Hstd k F v Hv.
  destruct (@skolem_hull_closed L M Hinh S seed k
    (skolem_graph_formula Heq F) v Hv
    (@skolem_graph_exists L M k S Heq Hstd F v)) as [z [Hz Hgraph]].
  unfold skolem_graph_formula in Hgraph.
  rewrite semiformula_eval_operator_apply in Hgraph.
  assert (Hvec :
    (fun i : Fin.t 2 =>
      semiterm_val S (fin_env_cons z v)
        (fun x : Empty_set => match x with end)
        (fin_two skolem_graph_output (skolem_graph_term F) i)) =
    fin_two z (structure_func S F v)).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      semiterm_val S (fin_env_cons z v)
        (fun x : Empty_set => match x with end)
        (fin_two skolem_graph_output (skolem_graph_term F) j) =
      fin_two z (structure_func S F v) j) eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      semiterm_val S (fin_env_cons z v)
        (fun x : Empty_set => match x with end)
        (fin_two skolem_graph_output (skolem_graph_term F) (Fin.FS q)) =
      fin_two z (structure_func S F v) (Fin.FS q)) eq_refl _).
    intros q; inversion q. }
  rewrite Hvec in Hgraph.
  apply (proj1 (structure_eq_operator Hstd z (structure_func S F v))) in Hgraph.
  rewrite <- Hgraph. exact Hz.
Qed.

(** The hull carries the expected substructure of the original language. *)
Definition skolem_hull_structure {L M}
    (Hinh : inhabited M) (S : first_order_structure L M)
    (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq) :
    first_order_structure L
      {x : M | skolem_hull Hinh S seed x} :=
  @Build_first_order_structure L
    {x : M | skolem_hull Hinh S seed x}
    (fun k F v =>
      exist _ (structure_func S F (fun i => proj1_sig (v i)))
        (@skolem_hull_closed_func L M Hinh S seed Heq Hstd k F
          (fun i => proj1_sig (v i)) (fun i => proj2_sig (v i))))
    (fun k R v => structure_rel S R (fun i => proj1_sig (v i))).

Lemma skolem_hull_structure_func_val : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    k (F : language_func L k)
    (v : Fin.t k -> {x : M | skolem_hull Hinh S seed x}),
  proj1_sig (structure_func
      (@skolem_hull_structure L M Hinh S seed Heq Hstd) F v) =
  structure_func S F (fun i => proj1_sig (v i)).
Proof. reflexivity. Qed.

Lemma skolem_hull_structure_rel : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    k (R : language_rel L k)
    (v : Fin.t k -> {x : M | skolem_hull Hinh S seed x}),
  structure_rel (@skolem_hull_structure L M Hinh S seed Heq Hstd) R v <->
  structure_rel S R (fun i => proj1_sig (v i)).
Proof. reflexivity. Qed.

Lemma skolem_hull_semiterm_val : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    X n (b : Fin.t n -> {x : M | skolem_hull Hinh S seed x})
    (f : X -> {x : M | skolem_hull Hinh S seed x})
    (t : semiterm L X n),
  proj1_sig (semiterm_val
      (@skolem_hull_structure L M Hinh S seed Heq Hstd) b f t) =
  semiterm_val S (fun i => proj1_sig (b i))
    (fun x => proj1_sig (f x)) t.
Proof.
  intros L M Hinh S seed Heq Hstd X n b f t.
  induction t as [i | x | k F v IH]; simpl; try reflexivity.
  f_equal. apply functional_extensionality. intro i.
  apply IH.
Qed.

Lemma skolem_hull_closed_semiterm_val : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    n (b : Fin.t n -> {x : M | skolem_hull Hinh S seed x})
    (t : closed_semiterm L n),
  proj1_sig (semiterm_val
      (@skolem_hull_structure L M Hinh S seed Heq Hstd) b
      (fun x : Empty_set => match x with end) t) =
  semiterm_val S (fun i => proj1_sig (b i))
    (fun x : Empty_set => match x with end) t.
Proof.
  intros L M Hinh S seed Heq Hstd n b t.
  pose proof (@skolem_hull_semiterm_val L M Hinh S seed Heq Hstd
    Empty_set n b (fun x : Empty_set => match x with end) t) as H.
  assert (Hempty :
    (fun x : Empty_set => proj1_sig
      (match x return {y : M | skolem_hull Hinh S seed y} with end)) =
    (fun x : Empty_set => match x with end)).
  { apply functional_extensionality. intros []. }
  cbn beta in H.
  rewrite Hempty in H. exact H.
Qed.

(** Every semisentence has the same truth value in the hull and in the
    ambient structure.  Existential reflection is exactly the closure lemma;
    universal reflection is obtained by applying it to the negated body. *)
Lemma skolem_hull_semiformula_eval : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq)
    n (b : Fin.t n -> {x : M | skolem_hull Hinh S seed x})
    (p : semisentence L n),
  semiformula_eval
      (@skolem_hull_structure L M Hinh S seed Heq Hstd) b
      (fun x : Empty_set => match x with end) p <->
  semiformula_eval S (fun i => proj1_sig (b i))
      (fun x : Empty_set => match x with end) p.
Proof.
  intros L M Hinh S seed Heq Hstd n b p.
  revert b.
  induction p; intro b; simpl; try tauto.
  - assert (Hargs :
      (fun i : Fin.t k =>
        proj1_sig (semiterm_val
          (@skolem_hull_structure L M Hinh S seed Heq Hstd) b
          (fun x : Empty_set => match x with end) (s i))) =
      (fun i : Fin.t k =>
        semiterm_val S (fun j => proj1_sig (b j))
          (fun x : Empty_set => match x with end) (s i))).
    { apply functional_extensionality. intro i.
      apply (@skolem_hull_closed_semiterm_val L M Hinh S seed Heq Hstd
        n b (s i)). }
    rewrite Hargs. reflexivity.
  - assert (Hargs :
      (fun i : Fin.t k =>
        proj1_sig (semiterm_val
          (@skolem_hull_structure L M Hinh S seed Heq Hstd) b
          (fun x : Empty_set => match x with end) (s i))) =
      (fun i : Fin.t k =>
        semiterm_val S (fun j => proj1_sig (b j))
          (fun x : Empty_set => match x with end) (s i))).
    { apply functional_extensionality. intro i.
      apply (@skolem_hull_closed_semiterm_val L M Hinh S seed Heq Hstd
        n b (s i)). }
    rewrite Hargs. reflexivity.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - split; intros H x.
    + destruct (classic
        (semiformula_eval S
          (fin_env_cons x (fun i => proj1_sig (b i)))
          (fun y : Empty_set => match y with end) p)) as [Hx | Hx].
      * exact Hx.
      * exfalso.
        pose proof (proj2 (@semiformula_eval_neg L M Empty_set
          (Datatypes.S n) S
          (fin_env_cons x (fun i => proj1_sig (b i)))
          (fun y : Empty_set => match y with end) p) Hx) as Hneg.
        destruct (@skolem_hull_closed L M Hinh S seed
          n (semiformula_neg p) (fun i => proj1_sig (b i))
          (fun i => proj2_sig (b i)) (ex_intro _ x Hneg)) as [z [Hz Hzneg]].
        pose proof (H (exist _ z Hz)) as Hzpos.
        pose proof (proj1 (IHp (fin_env_cons (exist _ z Hz) b))
          Hzpos) as HzposM.
        pose proof (proj1 (@semiformula_eval_neg L M Empty_set
          (Datatypes.S n) S
          (fin_env_cons z (fun i => proj1_sig (b i)))
          (fun y : Empty_set => match y with end) p) Hzneg) as Hznot.
        assert (Henv :
          (fun i => proj1_sig (fin_env_cons (exist _ z Hz) b i)) =
          fin_env_cons z (fun i => proj1_sig (b i))).
        { apply functional_extensionality. intro i.
          refine (@Fin.caseS' n i (fun j =>
            proj1_sig (fin_env_cons (exist _ z Hz) b j) =
            fin_env_cons z (fun q => proj1_sig (b q)) j) eq_refl _).
          intro j. reflexivity. }
        assert (HzposM' :
          semiformula_eval S
            (fin_env_cons z (fun i => proj1_sig (b i)))
            (fun y : Empty_set => match y with end) p).
        { apply (proj1 (@semiformula_eval_bound_ext L M Empty_set
            (Datatypes.S n) S
            (fun i => proj1_sig (fin_env_cons (exist _ z Hz) b i))
            (fin_env_cons z (fun i => proj1_sig (b i)))
            (fun y : Empty_set => match y with end) p
            (fun i => f_equal (fun h => h i) Henv))).
          exact HzposM. }
        exact (Hznot HzposM').
    + apply (proj2 (IHp (fin_env_cons x b))).
      assert (Henv :
        fin_env_cons (proj1_sig x) (fun i => proj1_sig (b i)) =
        (fun i => proj1_sig (fin_env_cons x b i))).
      { apply functional_extensionality. intro i.
        refine (@Fin.caseS' n i (fun j =>
          fin_env_cons (proj1_sig x) (fun q => proj1_sig (b q)) j =
          proj1_sig (fin_env_cons x b j)) eq_refl _).
        intro j. reflexivity. }
      apply (proj1 (@semiformula_eval_bound_ext L M Empty_set
        (Datatypes.S n) S
        (fin_env_cons (proj1_sig x) (fun i => proj1_sig (b i)))
        (fun i => proj1_sig (fin_env_cons x b i))
        (fun y : Empty_set => match y with end) p
        (fun i => f_equal (fun h => h i) Henv))).
      apply H.
  - split.
    + intros H. destruct H as [x Hx].
      exists (proj1_sig x).
      pose proof (proj1 (IHp (fin_env_cons x b)) Hx) as HxM.
      assert (Henv :
        (fun i => proj1_sig (fin_env_cons x b i)) =
        fin_env_cons (proj1_sig x) (fun i => proj1_sig (b i))).
      { apply functional_extensionality. intro i.
        refine (@Fin.caseS' n i (fun j =>
          proj1_sig (fin_env_cons x b j) =
          fin_env_cons (proj1_sig x) (fun q => proj1_sig (b q)) j)
          eq_refl _).
        intro j. reflexivity. }
      apply (proj1 (@semiformula_eval_bound_ext L M Empty_set
        (Datatypes.S n) S
        (fun i => proj1_sig (fin_env_cons x b i))
        (fin_env_cons (proj1_sig x) (fun i => proj1_sig (b i)))
        (fun y : Empty_set => match y with end) p
        (fun i => f_equal (fun h => h i) Henv))).
      exact HxM.
    + intros H. destruct H as [x Hx].
      destruct (@skolem_hull_closed L M Hinh S seed
        n p (fun i => proj1_sig (b i))
        (fun i => proj2_sig (b i)) (ex_intro _ x Hx)) as [z [Hz Hzp]].
      exists (exist _ z Hz).
      assert (Henv :
        fin_env_cons z (fun i => proj1_sig (b i)) =
        (fun i => proj1_sig (fin_env_cons (exist _ z Hz) b i))).
      { apply functional_extensionality. intro i.
        refine (@Fin.caseS' n i (fun j =>
          fin_env_cons z (fun q => proj1_sig (b q)) j =
          proj1_sig (fin_env_cons (exist _ z Hz) b j)) eq_refl _).
        intro j. reflexivity. }
      apply (proj2 (IHp (fin_env_cons (exist _ z Hz) b))).
      apply (proj1 (@semiformula_eval_bound_ext L M Empty_set
        (Datatypes.S n) S
        (fin_env_cons z (fun i => proj1_sig (b i)))
        (fun i => proj1_sig (fin_env_cons (exist _ z Hz) b i))
        (fun y : Empty_set => match y with end) p
        (fun i => f_equal (fun h => h i) Henv))).
      exact Hzp.
Qed.

Lemma skolem_hull_nonempty : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop),
  exists z, skolem_hull Hinh S seed z.
Proof.
  intros L M Hinh S seed.
  pose (t := (Semiterm_func (skolem_symbol (Semiformula_verum 1))
      (fun i : Fin.t 0 => match i with end) :
      semiterm (skolem_language L) {y : M | seed y} 0)).
  exists (semiterm_val (skolem_structure Hinh S)
    (fun i : Fin.t 0 => match i with end)
    (fun a : {y : M | seed y} => proj1_sig a) t).
  apply skolem_hull_term_mem.
Qed.

Lemma skolem_hull_inhabited : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop),
  inhabited {x : M | skolem_hull Hinh S seed x}.
Proof.
  intros L M Hinh S seed.
  destruct (skolem_hull_nonempty Hinh S seed) as [x Hx].
  exact (inhabits (exist _ x Hx)).
Qed.

Theorem skolem_hull_elementary_equiv : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq),
  first_order_elementary_equiv
    (first_order_model_of_structure
      (skolem_hull_inhabited Hinh S seed)
      (@skolem_hull_structure L M Hinh S seed Heq Hstd))
    (first_order_model_of_structure Hinh S).
Proof.
  intros L M Hinh S seed Heq Hstd.
  constructor. intro p.
  unfold first_order_model_realize, sentence_realize, formula_eval.
  change (semiformula_eval
    (@skolem_hull_structure L M Hinh S seed Heq Hstd)
    (fun i : Fin.t 0 => match i with end)
    (fun x : Empty_set => match x with end) p <->
    semiformula_eval S (fun i : Fin.t 0 => match i with end)
      (fun x : Empty_set => match x with end) p).
  pose proof (@skolem_hull_semiformula_eval L M Hinh S seed Heq Hstd
    0 (fun i : Fin.t 0 => match i with end) p) as H.
  split.
  - intro Hp.
    apply (proj1 (@semiformula_eval_bound_ext L M Empty_set 0 S
      (fun i : Fin.t 0 => proj1_sig
        (@fin_zero {x : M | skolem_hull Hinh S seed x} i))
      (fun i : Fin.t 0 => @fin_zero M i)
      (fun x : Empty_set => match x with end) p
      (fun i : Fin.t 0 =>
        @Fin.case0 (fun j =>
          proj1_sig (@fin_zero {x : M | skolem_hull Hinh S seed x} j) =
          @fin_zero M j) i))).
    apply (proj1 H). exact Hp.
  - intro Hp.
    apply (proj2 H).
    apply (proj2 (@semiformula_eval_bound_ext L M Empty_set 0 S
      (fun i : Fin.t 0 => proj1_sig
        (@fin_zero {x : M | skolem_hull Hinh S seed x} i))
      (fun i : Fin.t 0 => @fin_zero M i)
      (fun x : Empty_set => match x with end) p
      (fun i : Fin.t 0 =>
        @Fin.case0 (fun j =>
          proj1_sig (@fin_zero {x : M | skolem_hull Hinh S seed x} j) =
          @fin_zero M j) i))).
    exact Hp.
Qed.

Lemma skolem_hull_structure_interprets_eq : forall L M (Hinh : inhabited M)
    (S : first_order_structure L M) (seed : M -> Prop)
    (Heq : semiformula_has_eq_operator L)
    (Hstd : structure_interprets_eq S Heq),
  structure_interprets_eq
    (@skolem_hull_structure L M Hinh S seed Heq Hstd) Heq.
Proof.
  intros L M Hinh S seed Heq Hstd.
  constructor. intros a b.
  unfold semiformula_operator_eval.
  rewrite (@skolem_hull_semiformula_eval L M Hinh S seed Heq Hstd
    2 (fin_two a b) (semiformula_operator_sentence
      (semiformula_eq_operator Heq))).
  assert (Hvec :
    (fun i : Fin.t 2 => proj1_sig (fin_two a b i)) =
    fin_two (proj1_sig a) (proj1_sig b)).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      proj1_sig (fin_two a b j) =
      fin_two (proj1_sig a) (proj1_sig b) j) eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      proj1_sig (fin_two a b (Fin.FS q)) =
      fin_two (proj1_sig a) (proj1_sig b) (Fin.FS q)) eq_refl _).
    intros q; inversion q. }
  rewrite Hvec.
  change (semiformula_operator_eval S
    (fin_two (proj1_sig a) (proj1_sig b))
    (semiformula_eq_operator Heq) <-> a = b).
  rewrite (structure_eq_operator Hstd (proj1_sig a) (proj1_sig b)).
  split.
  - intro H. apply (@eq_sig M (fun x => skolem_hull Hinh S seed x) a b H).
    apply proof_irrelevance.
  - intro H. now inversion H.
Qed.
