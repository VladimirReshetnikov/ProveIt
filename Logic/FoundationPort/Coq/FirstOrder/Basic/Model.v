(**
  Canonical model carriers and composite first-order structures.

  This ports [Foundation/FirstOrder/Basic/Model.lean].  Operator-induced
  operations are factored by arity, and all carrier wrappers reuse the
  generic equivalence transport from the semantics layer.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics ModelTheory Elementary.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * A transparent wrapper carrying canonical operator interpretations *)

Record structure_model (M : Type) : Type := {
  structure_model_value : M
}.

Arguments structure_model_value {M} _.

Definition structure_model_equiv (M : Type) :
    carrier_equiv M (structure_model M) :=
  {| carrier_equiv_to := fun x => {| structure_model_value := x |};
     carrier_equiv_from := structure_model_value;
     carrier_equiv_to_from := fun y =>
       match y with {| structure_model_value := x |} => eq_refl end;
     carrier_equiv_from_to := fun _ => eq_refl |}.

Definition structure_model_structure {L M}
    (Str : first_order_structure L M) :
    first_order_structure L (structure_model M) :=
  first_order_structure_transport Str (structure_model_equiv M).

Definition structure_model_inhabited {M} (HM : inhabited M) :
    inhabited (structure_model M) :=
  match HM with
  | inhabits x => inhabits {| structure_model_value := x |}
  end.

Theorem structure_model_elementary_equiv :
  forall L M (Str : first_order_structure L M) (HM : inhabited M),
    first_order_elementary_equiv
      (first_order_model_of_structure HM Str)
      (first_order_model_of_structure (structure_model_inhabited HM)
        (structure_model_structure Str)).
Proof.
  intros. apply first_order_elementary_equiv_of_carrier_equiv
    with (e := structure_model_equiv M).
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

(** Generic operator interpretations on the wrapped carrier. *)
Definition structure_model_nullary {L M}
    (Str : first_order_structure L M) (o : semiterm_operator L 0) :
    structure_model M :=
  semiterm_operator_val (structure_model_structure Str) fin_zero o.

Definition structure_model_unary {L M}
    (Str : first_order_structure L M) (o : semiterm_operator L 1)
    (x : structure_model M) : structure_model M :=
  semiterm_operator_val (structure_model_structure Str) (fin_one x) o.

Definition structure_model_binary {L M}
    (Str : first_order_structure L M) (o : semiterm_operator L 2)
    (x y : structure_model M) : structure_model M :=
  semiterm_operator_val (structure_model_structure Str) (fin_two x y) o.

Definition structure_model_relation {L M}
    (Str : first_order_structure L M) (o : semiformula_operator L 2)
    (x y : structure_model M) : Prop :=
  semiformula_operator_eval (structure_model_structure Str) (fin_two x y) o.

Lemma structure_model_interprets_relation :
  forall L M (Str : first_order_structure L M) (o : semiformula_operator L 2),
    structure_interprets_relation (structure_model_structure Str) o
      (structure_model_relation Str o).
Proof. intros. constructor. reflexivity. Qed.

Definition structure_model_zero {L M} (Str : first_order_structure L M)
    (H : semiterm_has_zero_operator L) : structure_model M :=
  structure_model_nullary Str (semiterm_zero_operator H).

Definition structure_model_one {L M} (Str : first_order_structure L M)
    (H : semiterm_has_one_operator L) : structure_model M :=
  structure_model_nullary Str (semiterm_one_operator H).

Definition structure_model_add {L M} (Str : first_order_structure L M)
    (H : semiterm_has_add_operator L) :
    structure_model M -> structure_model M -> structure_model M :=
  structure_model_binary Str (semiterm_add_operator H).

Definition structure_model_mul {L M} (Str : first_order_structure L M)
    (H : semiterm_has_mul_operator L) :
    structure_model M -> structure_model M -> structure_model M :=
  structure_model_binary Str (semiterm_mul_operator H).

Definition structure_model_exp {L M} (Str : first_order_structure L M)
    (H : semiterm_has_exp_operator L) :
    structure_model M -> structure_model M :=
  structure_model_unary Str (semiterm_exp_operator H).

Lemma structure_model_interprets_zero :
  forall L M (Str : first_order_structure L M)
         (H : semiterm_has_zero_operator L),
    structure_interprets_zero (structure_model_structure Str) H
      (structure_model_zero Str H).
Proof. intros. constructor. reflexivity. Qed.

Lemma structure_model_interprets_one :
  forall L M (Str : first_order_structure L M)
         (H : semiterm_has_one_operator L),
    structure_interprets_one (structure_model_structure Str) H
      (structure_model_one Str H).
Proof. intros. constructor. reflexivity. Qed.

Lemma structure_model_interprets_add :
  forall L M (Str : first_order_structure L M)
         (H : semiterm_has_add_operator L),
    structure_interprets_add (structure_model_structure Str) H
      (structure_model_add Str H).
Proof. intros. constructor. reflexivity. Qed.

Lemma structure_model_interprets_mul :
  forall L M (Str : first_order_structure L M)
         (H : semiterm_has_mul_operator L),
    structure_interprets_mul (structure_model_structure Str) H
      (structure_model_mul Str H).
Proof. intros. constructor. reflexivity. Qed.

Lemma structure_model_interprets_exp :
  forall L M (Str : first_order_structure L M)
         (H : semiterm_has_exp_operator L),
    structure_interprets_exp (structure_model_structure Str) H
      (structure_model_exp Str H).
Proof. intros. constructor. reflexivity. Qed.

Definition structure_model_lt {L M} (Str : first_order_structure L M)
    (H : semiformula_has_lt_operator L) :
    structure_model M -> structure_model M -> Prop :=
  structure_model_relation Str (semiformula_lt_operator H).

Definition structure_model_mem {L M} (Str : first_order_structure L M)
    (H : semiformula_has_mem_operator L) :
    structure_model M -> structure_model M -> Prop :=
  structure_model_relation Str (semiformula_mem_operator H).

Lemma structure_model_interprets_lt :
  forall L M (Str : first_order_structure L M)
         (H : semiformula_has_lt_operator L),
    structure_interprets_lt (structure_model_structure Str) H
      (structure_model_lt Str H).
Proof. intros. apply structure_model_interprets_relation. Qed.

Lemma structure_model_interprets_mem :
  forall L M (Str : first_order_structure L M)
         (H : semiformula_has_mem_operator L),
    structure_interprets_mem (structure_model_structure Str) H
      (structure_model_mem Str H).
Proof. intros. apply structure_model_interprets_relation. Qed.

Lemma structure_model_interprets_eq :
  forall L M (Str : first_order_structure L M)
         (H : semiformula_has_eq_operator L),
    structure_interprets_eq Str H ->
    structure_interprets_eq (structure_model_structure Str) H.
Proof.
  intros L M Str H Heq. constructor. intros [a] [b].
  unfold structure_model_structure.
  rewrite semiformula_operator_eval_transport. simpl.
  assert (Henv :
    (fun i => structure_model_value
      (fin_two {| structure_model_value := a |}
        {| structure_model_value := b |} i)) = fin_two a b).
  { apply functional_extensionality. intro i.
    refine (@Fin.caseS' 1 i (fun j =>
      structure_model_value
        (fin_two {| structure_model_value := a |}
          {| structure_model_value := b |} j) = fin_two a b j)
      eq_refl _).
    intro j. refine (@Fin.caseS' 0 j (fun q =>
      structure_model_value
        (fin_two {| structure_model_value := a |}
          {| structure_model_value := b |} (Fin.FS q)) =
      fin_two a b (Fin.FS q)) eq_refl _).
    intros q; inversion q. }
  rewrite Henv, (structure_eq_operator Heq a b).
  split; intro Hab.
  - now subst b.
  - now inversion Hab.
Qed.

(** * Function-only, binary-sum, and indexed-sum structures *)

Definition function_only_structure {F M}
    (fF : forall k, F k -> (Fin.t k -> M) -> M) :
    first_order_structure (function_only_language F) M.
Proof.
  refine {| structure_func := _; structure_rel := _ |}.
  - intros k f v. exact (fF k f v).
  - intros k r v. exact (match r with end).
Defined.

Lemma function_only_structure_func :
  forall F M (fF : forall k, F k -> (Fin.t k -> M) -> M)
         k (f : F k) v,
    structure_func (function_only_structure fF) f v = fF k f v.
Proof. reflexivity. Qed.

Definition first_order_structure_add {L K M}
    (S : first_order_structure L M) (T : first_order_structure K M) :
    first_order_structure (language_add L K) M.
Proof.
  refine {| structure_func := _; structure_rel := _ |}.
  - intros k [f | g] v; [exact (structure_func S f v) |
                         exact (structure_func T g v)].
  - intros k [r | q] v; [exact (structure_rel S r v) |
                         exact (structure_rel T q v)].
Defined.

Lemma first_order_structure_add_func_left :
  forall L K M (S : first_order_structure L M)
         (T : first_order_structure K M) k (F : language_func L k) v,
    structure_func (first_order_structure_add S T) (inl F) v =
    structure_func S F v.
Proof. reflexivity. Qed.

Lemma first_order_structure_add_func_right :
  forall L K M (S : first_order_structure L M)
         (T : first_order_structure K M) k (F : language_func K k) v,
    structure_func (first_order_structure_add S T) (inr F) v =
    structure_func T F v.
Proof. reflexivity. Qed.

Lemma first_order_structure_add_rel_left :
  forall L K M (S : first_order_structure L M)
         (T : first_order_structure K M) k (R : language_rel L k) v,
    structure_rel (first_order_structure_add S T) (inl R) v <->
    structure_rel S R v.
Proof. reflexivity. Qed.

Lemma first_order_structure_add_rel_right :
  forall L K M (S : first_order_structure L M)
         (T : first_order_structure K M) k (R : language_rel K k) v,
    structure_rel (first_order_structure_add S T) (inr R) v <->
    structure_rel T R v.
Proof. reflexivity. Qed.

Lemma first_order_structure_add_language_map_left :
  forall L K M (S : first_order_structure L M)
         (T : first_order_structure K M),
    first_order_structure_language_map (language_hom_add_left L K)
      (first_order_structure_add S T) = S.
Proof. intros L K M [Sf Sr] [Tf Tr]. reflexivity. Qed.

Lemma first_order_structure_add_language_map_right :
  forall L K M (S : first_order_structure L M)
         (T : first_order_structure K M),
    first_order_structure_language_map (language_hom_add_right L K)
      (first_order_structure_add S T) = T.
Proof. intros L K M [Sf Sr] [Tf Tr]. reflexivity. Qed.

Lemma semiterm_val_language_add_left :
  forall L K M X n (S : first_order_structure L M)
         (T : first_order_structure K M) (b : Fin.t n -> M) (f : X -> M)
         (t : semiterm L X n),
    semiterm_val (first_order_structure_add S T) b f
      (semiterm_language_map (language_hom_add_left L K) t) =
    semiterm_val S b f t.
Proof.
  intros. rewrite semiterm_val_language_map.
  now rewrite first_order_structure_add_language_map_left.
Qed.

Lemma semiterm_val_language_add_right :
  forall L K M X n (S : first_order_structure L M)
         (T : first_order_structure K M) (b : Fin.t n -> M) (f : X -> M)
         (t : semiterm K X n),
    semiterm_val (first_order_structure_add S T) b f
      (semiterm_language_map (language_hom_add_right L K) t) =
    semiterm_val T b f t.
Proof.
  intros. rewrite semiterm_val_language_map.
  now rewrite first_order_structure_add_language_map_right.
Qed.

Lemma semiformula_eval_language_add_left :
  forall L K M X n (S : first_order_structure L M)
         (T : first_order_structure K M) (b : Fin.t n -> M) (f : X -> M)
         (p : semiformula L X n),
    semiformula_eval (first_order_structure_add S T) b f
      (semiformula_language_map (language_hom_add_left L K) p) <->
    semiformula_eval S b f p.
Proof.
  intros. rewrite semiformula_eval_language_map.
  now rewrite first_order_structure_add_language_map_left.
Qed.

Lemma semiformula_eval_language_add_right :
  forall L K M X n (S : first_order_structure L M)
         (T : first_order_structure K M) (b : Fin.t n -> M) (f : X -> M)
         (p : semiformula K X n),
    semiformula_eval (first_order_structure_add S T) b f
      (semiformula_language_map (language_hom_add_right L K) p) <->
    semiformula_eval T b f p.
Proof.
  intros. rewrite semiformula_eval_language_map.
  now rewrite first_order_structure_add_language_map_right.
Qed.

Definition first_order_structure_sigma {I} {Ls : I -> language} {M}
    (Ss : forall i, first_order_structure (Ls i) M) :
    first_order_structure (language_sigma Ls) M.
Proof.
  refine {| structure_func := _; structure_rel := _ |}.
  - intros k [i f] v. exact (structure_func (Ss i) f v).
  - intros k [i r] v. exact (structure_rel (Ss i) r v).
Defined.

Lemma first_order_structure_sigma_func :
  forall I (Ls : I -> language) M
         (Ss : forall i, first_order_structure (Ls i) M)
         i k (F : language_func (Ls i) k) v,
    structure_func (first_order_structure_sigma Ss) (existT _ i F) v =
    structure_func (Ss i) F v.
Proof. reflexivity. Qed.

Lemma first_order_structure_sigma_rel :
  forall I (Ls : I -> language) M
         (Ss : forall i, first_order_structure (Ls i) M)
         i k (R : language_rel (Ls i) k) v,
    structure_rel (first_order_structure_sigma Ss) (existT _ i R) v <->
    structure_rel (Ss i) R v.
Proof. reflexivity. Qed.

Lemma semiterm_val_language_sigma :
  forall I (Ls : I -> language) M X n
         (Ss : forall i, first_order_structure (Ls i) M)
         i (b : Fin.t n -> M) (f : X -> M) (t : semiterm (Ls i) X n),
    semiterm_val (first_order_structure_sigma Ss) b f
      (semiterm_language_map (language_hom_sigma Ls i) t) =
    semiterm_val (Ss i) b f t.
Proof.
  intros I Ls M X n Ss i b f t.
  induction t as [j | x | k F v IH]; simpl; try reflexivity.
  f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma semiformula_eval_language_sigma :
  forall I (Ls : I -> language) M X n
         (Ss : forall i, first_order_structure (Ls i) M)
         i (b : Fin.t n -> M) (f : X -> M) (p : semiformula (Ls i) X n),
    semiformula_eval (first_order_structure_sigma Ss) b f
      (semiformula_language_map (language_hom_sigma Ls i) p) <->
    semiformula_eval (Ss i) b f p.
Proof.
  intros I Ls M X n Ss i b f p; revert b.
  induction p; intro b; simpl; try tauto.
  - assert (Hargs :
      (fun j => semiterm_val (first_order_structure_sigma Ss) b f
        (semiterm_language_map (language_hom_sigma Ls i) (s j))) =
      (fun j => semiterm_val (Ss i) b f (s j))).
    { apply functional_extensionality. intro j.
      apply semiterm_val_language_sigma. }
    now rewrite Hargs.
  - assert (Hargs :
      (fun j => semiterm_val (first_order_structure_sigma Ss) b f
        (semiterm_language_map (language_hom_sigma Ls i) (s j))) =
      (fun j => semiterm_val (Ss i) b f (s j))).
    { apply functional_extensionality. intro j.
      apply semiterm_val_language_sigma. }
    now rewrite Hargs.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - split; intros Hall x.
    + apply (proj1 (IHp (fin_env_cons x b))). apply Hall.
    + apply (proj2 (IHp (fin_env_cons x b))). apply Hall.
  - split; intros Hex; destruct Hex as [x Hx]; exists x.
    + apply (proj1 (IHp (fin_env_cons x b))). exact Hx.
    + apply (proj2 (IHp (fin_env_cons x b))). exact Hx.
Qed.

(** * Universe-lift-style carrier transport *)

Definition structure_lift := structure_model.
Definition structure_lift_value {M} : structure_lift M -> M :=
  structure_model_value.
Definition structure_lift_equiv := structure_model_equiv.

Definition structure_lift_structure {L M}
    (Str : first_order_structure L M) :
    first_order_structure L (structure_lift M) :=
  first_order_structure_transport Str (structure_lift_equiv M).

Lemma semiterm_val_structure_lift :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> structure_lift M) (f : X -> structure_lift M)
         (t : semiterm L X n),
    semiterm_val (structure_lift_structure Str) b f t =
    carrier_equiv_to (structure_lift_equiv M)
      (semiterm_val Str
        (fun i => structure_lift_value (b i))
        (fun x => structure_lift_value (f x)) t).
Proof. intros. apply semiterm_val_transport. Qed.

Lemma semiformula_eval_structure_lift :
  forall L M X n (Str : first_order_structure L M)
         (b : Fin.t n -> structure_lift M) (f : X -> structure_lift M)
         (p : semiformula L X n),
    semiformula_eval (structure_lift_structure Str) b f p <->
    semiformula_eval Str
      (fun i => structure_lift_value (b i))
      (fun x => structure_lift_value (f x)) p.
Proof. intros. apply semiformula_eval_transport. Qed.

Theorem structure_lift_elementary_equiv :
  forall L M (Str : first_order_structure L M) (HM : inhabited M),
    first_order_elementary_equiv
      (first_order_model_of_structure
        (structure_model_inhabited HM) (structure_lift_structure Str))
      (first_order_model_of_structure HM Str).
Proof.
  intros. apply first_order_elementary_equiv_sym.
  apply structure_model_elementary_equiv.
Qed.
