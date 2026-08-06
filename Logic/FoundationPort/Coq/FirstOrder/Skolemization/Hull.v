(**
  Skolem functions and Skolem hulls.

  This ports the semantic core of
  [Foundation/FirstOrder/Skolemization/Hull.lean].  The source packages
  structures and formulas through typeclasses; here the language, structure,
  and evaluation are explicit.  The resulting closure theorem is therefore
  reusable for any first-order structure and any seed predicate.
*)

From Stdlib Require Import Logic.ClassicalEpsilon Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics OperatorSemantics.
From Foundation.FirstOrder.Basic Require Import Operator.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

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
