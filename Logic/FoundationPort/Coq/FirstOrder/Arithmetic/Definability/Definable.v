(**
  Definability at a fixed level of the arithmetical hierarchy.

  This ports the witness layer of
  [Foundation/FirstOrder/Arithmetic/Definability/Definable.lean].  Structures
  are explicit and witnesses live in [Type], so formula-producing closure
  operations require no choice or elimination from existential propositions.
*)

From Stdlib Require Import Vectors.Fin.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic Require Import Operator Definability.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics RewriteClosure OperatorSemantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Import ListNotations.

(** * Definitions and definability witnesses *)

Definition arithmetic_sorted_formula_proper {M : Type} {X : Type} {n class rank}
    (Str : first_order_structure oring_language M)
    (f : X -> M) (p : arithmetic_sorted_formula_by X n class rank) : Prop :=
  match class as c return
      arithmetic_sorted_formula_by X n c rank -> Prop with
  | ArithmeticHierarchySigma => fun _ => True
  | ArithmeticHierarchyPi => fun _ => True
  | ArithmeticHierarchyDelta => arithmetic_sorted_delta_proper Str f
  end p.

Definition arithmetic_sorted_is_defined_by {M : Type} {k symbol}
    (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula Empty_set k symbol) : Prop :=
  arithmetic_sorted_formula_proper Str
      (fun x : Empty_set => match x with end) p /\
  first_order_is_defined_by Str P (arithmetic_sorted_formula_val p).

Definition arithmetic_sorted_is_defined_by_with_params
    {M : Type} {k symbol}
    (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula M k symbol) : Prop :=
  arithmetic_sorted_formula_proper Str (fun x => x) p /\
  first_order_is_defined_by_with_params Str P
    (arithmetic_sorted_formula_val p).

Record arithmetic_sorted_defined {M : Type} {k symbol}
    (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula Empty_set k symbol) : Prop := {
  arithmetic_sorted_defined_spec : arithmetic_sorted_is_defined_by Str P p
}.

Record arithmetic_sorted_definable {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (symbol : arithmetic_hierarchy_symbol)
    (P : (Fin.t k -> M) -> Prop) : Type := {
  arithmetic_sorted_definable_formula :
    arithmetic_sorted_formula M k symbol;
  arithmetic_sorted_definable_spec :
    arithmetic_sorted_is_defined_by_with_params Str P
      arithmetic_sorted_definable_formula
}.

Arguments arithmetic_sorted_definable_formula {M k Str symbol P} _.
Arguments arithmetic_sorted_definable_spec {M k Str symbol P} _.

Definition arithmetic_sorted_defined_function {M : Type} {k symbol}
    (Str : first_order_structure oring_language M)
    (f : (Fin.t k -> M) -> M)
    (p : arithmetic_sorted_formula Empty_set (S k) symbol) : Prop :=
  arithmetic_sorted_defined Str
    (fun v => v Fin.F1 = f (fun i => v (Fin.FS i))) p.

Definition arithmetic_sorted_definable_function {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (symbol : arithmetic_hierarchy_symbol)
    (f : (Fin.t k -> M) -> M) : Type :=
  arithmetic_sorted_definable Str symbol
    (fun v : Fin.t (S k) -> M =>
      v Fin.F1 = f (fun i => v (Fin.FS i))).

Definition arithmetic_sorted_definable_predicate {M : Type}
    (Str : first_order_structure oring_language M)
    (symbol : arithmetic_hierarchy_symbol) (P : M -> Prop) : Type :=
  arithmetic_sorted_definable Str symbol
    (fun v : Fin.t 1 -> M => P (v Fin.F1)).

Definition arithmetic_sorted_definable_relation {M : Type}
    (Str : first_order_structure oring_language M)
    (symbol : arithmetic_hierarchy_symbol) (R : M -> M -> Prop) : Type :=
  arithmetic_sorted_definable Str symbol
    (fun v : Fin.t 2 -> M => R (v Fin.F1) (v (Fin.FS Fin.F1))).

(** * Elimination laws *)

Lemma arithmetic_sorted_defined_first_order : forall
    (M : Type) k symbol (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula Empty_set k symbol),
  arithmetic_sorted_defined Str P p ->
  first_order_defined Str P (arithmetic_sorted_formula_val p).
Proof.
  intros M k symbol Str P p H.
  constructor. exact (proj2 (arithmetic_sorted_defined_spec H)).
Qed.

Lemma arithmetic_sorted_defined_iff : forall
    (M : Type) k symbol (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula Empty_set k symbol),
  arithmetic_sorted_defined Str P p ->
  forall v,
    semiformula_eval Str v (fun x : Empty_set => match x with end)
      (arithmetic_sorted_formula_val p) <-> P v.
Proof.
  intros M k symbol Str P p H.
  exact (proj2 (arithmetic_sorted_defined_spec H)).
Qed.

Lemma arithmetic_sorted_defined_delta_proper : forall
    (M : Type) k rank (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula Empty_set k (arithmetic_delta_symbol rank)),
  arithmetic_sorted_defined Str P p ->
  arithmetic_sorted_delta_proper_on Str p.
Proof.
  intros M k rank Str P p H.
  exact (proj1 (arithmetic_sorted_defined_spec H)).
Qed.

Lemma arithmetic_sorted_defined_delta_pi_iff : forall
    (M : Type) k rank (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (p : arithmetic_sorted_formula Empty_set k (arithmetic_delta_symbol rank)),
  arithmetic_sorted_defined Str P p ->
  forall v,
    semiformula_eval Str v (fun x : Empty_set => match x with end)
      (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi p)) <-> P v.
Proof.
  intros M k rank Str P p H v.
  rewrite (arithmetic_sorted_delta_pi_eval_iff
    (arithmetic_sorted_defined_delta_proper H) v).
  apply (arithmetic_sorted_defined_iff H).
Qed.

Lemma arithmetic_sorted_definable_iff : forall
    (M : Type) k symbol (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (H : arithmetic_sorted_definable Str symbol P) v,
  semiformula_eval Str v (fun x => x)
    (arithmetic_sorted_formula_val
      (arithmetic_sorted_definable_formula H)) <-> P v.
Proof.
  intros M k symbol Str P H.
  exact (proj2 (arithmetic_sorted_definable_spec H)).
Qed.

Lemma arithmetic_sorted_definable_delta_proper : forall
    (M : Type) k rank (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (H : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P),
  arithmetic_sorted_delta_proper_with_params_on Str
    (arithmetic_sorted_definable_formula H).
Proof.
  intros M k rank Str P H.
  exact (proj1 (arithmetic_sorted_definable_spec H)).
Qed.

Lemma arithmetic_sorted_definable_delta_pi_iff : forall
    (M : Type) k rank (Str : first_order_structure oring_language M)
    (P : (Fin.t k -> M) -> Prop)
    (H : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P) v,
  semiformula_eval Str v (fun x => x)
    (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi
      (arithmetic_sorted_definable_formula H))) <-> P v.
Proof.
  intros M k rank Str P H v.
  rewrite (arithmetic_sorted_delta_pi_eval_iff
    (arithmetic_sorted_definable_delta_proper H) v).
  apply arithmetic_sorted_definable_iff.
Qed.

(** * Elementary witness transport *)

Definition arithmetic_sorted_defined_of_iff {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    {p : arithmetic_sorted_formula Empty_set k symbol}
    (H : arithmetic_sorted_defined Str Q p)
    (HPQ : forall v, P v <-> Q v) :
    arithmetic_sorted_defined Str P p.
Proof.
  constructor. split.
  - exact (proj1 (arithmetic_sorted_defined_spec H)).
  - intro v. rewrite (arithmetic_sorted_defined_iff H v).
    symmetry. apply HPQ.
Qed.

Definition arithmetic_sorted_definable_of_iff {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str symbol Q)
    (HPQ : forall v, P v <-> Q v) :
    arithmetic_sorted_definable Str symbol P.
Proof.
  destruct H as [p Hp]. refine {| arithmetic_sorted_definable_formula := p |}.
  split; [exact (proj1 Hp) |].
  intro v. rewrite (proj2 Hp v). symmetry. apply HPQ.
Defined.

Definition arithmetic_sorted_defined_to_definable {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (p : arithmetic_sorted_formula Empty_set k symbol)
    (H : arithmetic_sorted_defined Str P p) :
    arithmetic_sorted_definable Str symbol P.
Proof.
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_rewrite
      (@rew_emb oring_language Empty_set M k
        (fun x : Empty_set => match x with end)) p |}.
  split.
  - destruct symbol as [class rank]. destruct class; simpl; trivial.
    exact (arithmetic_sorted_delta_proper_on_rewrite_with_params
      (@rew_emb oring_language Empty_set M k
        (fun x : Empty_set => match x with end))
      (arithmetic_sorted_defined_delta_proper H)).
  - intro v. rewrite arithmetic_sorted_rewrite_val.
    change
      (semiformula_eval Str v (fun x => x)
        (semiformula_embed_empty (arithmetic_sorted_formula_val p)) <-> P v).
    rewrite semiformula_eval_embed_empty.
    apply (arithmetic_sorted_defined_iff H).
Defined.

(** * Hierarchy conversion *)

Definition arithmetic_sorted_definable_of_zero {M : Type} {k class}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := 0 |} P)
    (target : arithmetic_hierarchy_symbol) :
    arithmetic_sorted_definable Str target P.
Proof.
  destruct target as [target_class target_rank].
  destruct H as [p [Hp Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_of_zero p
      {| arithmetic_hierarchy_symbol_class := target_class;
         arithmetic_hierarchy_symbol_rank := target_rank |} |}.
  split.
  - destruct target_class; simpl; trivial.
    apply arithmetic_sorted_delta_proper_of_zero.
  - intro v. rewrite arithmetic_sorted_of_zero_val. apply Hspec.
Defined.

Definition arithmetic_sorted_definable_of_delta {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P)
    (target_class : arithmetic_hierarchy_class) :
    arithmetic_sorted_definable Str
      {| arithmetic_hierarchy_symbol_class := target_class;
         arithmetic_hierarchy_symbol_rank := rank |} P.
Proof.
  destruct H as [p [Hp Hspec]]. destruct target_class.
  - refine {| arithmetic_sorted_definable_formula :=
      arithmetic_sorted_delta_sigma p |}. split; [exact I | exact Hspec].
  - refine {| arithmetic_sorted_definable_formula :=
      arithmetic_sorted_delta_pi p |}. split; [exact I |].
    intro v. transitivity (semiformula_eval Str v (fun x => x)
      (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p))).
    + symmetry. apply Hp.
    + apply Hspec.
  - refine {| arithmetic_sorted_definable_formula := p |}.
    exact (conj Hp Hspec).
Defined.

Definition arithmetic_sorted_definable_delta_of_sigma_pi
    {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (Hs : arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank) P)
    (Hp : arithmetic_sorted_definable Str (arithmetic_pi_symbol rank) P) :
    arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P.
Proof.
  destruct Hs as [p [_ Hps]], Hp as [q [_ Hqs]].
  refine {| arithmetic_sorted_definable_formula :=
    ArithmeticSortedDelta rank p q |}. split.
  - intro v. rewrite (Hps v), (Hqs v). reflexivity.
  - exact Hps.
Defined.

Definition arithmetic_sorted_definable_of_sigma_pi
    {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (Hs : arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank) P)
    (Hp : arithmetic_sorted_definable Str (arithmetic_pi_symbol rank) P)
    (target_class : arithmetic_hierarchy_class) :
    arithmetic_sorted_definable Str
      {| arithmetic_hierarchy_symbol_class := target_class;
         arithmetic_hierarchy_symbol_rank := rank |} P :=
  arithmetic_sorted_definable_of_delta
    (arithmetic_sorted_definable_delta_of_sigma_pi Hs Hp) target_class.

(** * Boolean closure *)

Definition arithmetic_sorted_definable_verum {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (symbol : arithmetic_hierarchy_symbol) :
    arithmetic_sorted_definable Str symbol
      (fun _ : Fin.t k -> M => True).
Proof.
  destruct symbol as [class rank].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_verum
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := rank |} |}. split.
  - destruct class; simpl; trivial.
    apply arithmetic_sorted_delta_proper_verum.
  - intro v. rewrite arithmetic_sorted_verum_val. reflexivity.
Defined.

Definition arithmetic_sorted_definable_falsum {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (symbol : arithmetic_hierarchy_symbol) :
    arithmetic_sorted_definable Str symbol
      (fun _ : Fin.t k -> M => False).
Proof.
  destruct symbol as [class rank].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_falsum
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := rank |} |}. split.
  - destruct class; simpl; trivial.
    apply arithmetic_sorted_delta_proper_falsum.
  - intro v. rewrite arithmetic_sorted_falsum_val. reflexivity.
Defined.

Definition arithmetic_sorted_definable_and {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : arithmetic_sorted_definable Str symbol P)
    (HQ : arithmetic_sorted_definable Str symbol Q) :
    arithmetic_sorted_definable Str symbol (fun v => P v /\ Q v).
Proof.
  destruct symbol as [class rank].
  destruct HP as [p [Hpp Hps]], HQ as [q [Hqp Hqs]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_and p q |}. split.
  - destruct class; simpl in *; trivial.
    now apply arithmetic_sorted_delta_proper_and.
  - intro v. rewrite arithmetic_sorted_and_val. simpl.
    change
      ((semiformula_eval Str v (fun x => x)
          (arithmetic_sorted_formula_val p) /\
        semiformula_eval Str v (fun x => x)
          (arithmetic_sorted_formula_val q)) <-> P v /\ Q v).
    now rewrite (Hps v), (Hqs v).
Defined.

Definition arithmetic_sorted_definable_or {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : arithmetic_sorted_definable Str symbol P)
    (HQ : arithmetic_sorted_definable Str symbol Q) :
    arithmetic_sorted_definable Str symbol (fun v => P v \/ Q v).
Proof.
  destruct symbol as [class rank].
  destruct HP as [p [Hpp Hps]], HQ as [q [Hqp Hqs]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_or p q |}. split.
  - destruct class; simpl in *; trivial.
    now apply arithmetic_sorted_delta_proper_or.
  - intro v. rewrite arithmetic_sorted_or_val. simpl.
    change
      ((semiformula_eval Str v (fun x => x)
          (arithmetic_sorted_formula_val p) \/
        semiformula_eval Str v (fun x => x)
          (arithmetic_sorted_formula_val q)) <-> P v \/ Q v).
    now rewrite (Hps v), (Hqs v).
Defined.

Definition arithmetic_sorted_definable_not_sigma {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank) P) :
    arithmetic_sorted_definable Str (arithmetic_pi_symbol rank)
      (fun v => ~ P v).
Proof.
  destruct H as [p [_ Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_neg_sigma p |}. split; [exact I |].
  intro v. rewrite arithmetic_sorted_neg_sigma_val.
  rewrite semiformula_eval_neg. specialize (Hspec v). tauto.
Defined.

Definition arithmetic_sorted_definable_not_pi {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str (arithmetic_pi_symbol rank) P) :
    arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank)
      (fun v => ~ P v).
Proof.
  destruct H as [p [_ Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_neg_pi p |}. split; [exact I |].
  intro v. rewrite arithmetic_sorted_neg_pi_val.
  rewrite semiformula_eval_neg. specialize (Hspec v). tauto.
Defined.

Definition arithmetic_sorted_definable_not_delta {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P) :
    arithmetic_sorted_definable Str (arithmetic_delta_symbol rank)
      (fun v => ~ P v).
Proof.
  destruct H as [p [Hp Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_neg_delta p |}. split.
  - now apply arithmetic_sorted_delta_proper_neg.
  - intro v. rewrite (arithmetic_sorted_delta_eval_neg_iff Hp v).
    specialize (Hspec v). tauto.
Defined.

Definition arithmetic_sorted_definable_imp_sigma {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : arithmetic_sorted_definable Str (arithmetic_pi_symbol rank) P)
    (HQ : arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank) Q) :
    arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank)
      (fun v => P v -> Q v).
Proof.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_or
      (arithmetic_sorted_definable_not_pi HP) HQ)).
  intro v. destruct (classic (P v)); tauto.
Defined.

Definition arithmetic_sorted_definable_imp_pi {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : arithmetic_sorted_definable Str (arithmetic_sigma_symbol rank) P)
    (HQ : arithmetic_sorted_definable Str (arithmetic_pi_symbol rank) Q) :
    arithmetic_sorted_definable Str (arithmetic_pi_symbol rank)
      (fun v => P v -> Q v).
Proof.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_or
      (arithmetic_sorted_definable_not_sigma HP) HQ)).
  intro v. destruct (classic (P v)); tauto.
Defined.

Definition arithmetic_sorted_definable_imp_delta {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P)
    (HQ : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) Q) :
    arithmetic_sorted_definable Str (arithmetic_delta_symbol rank)
      (fun v => P v -> Q v).
Proof.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_or
      (arithmetic_sorted_definable_not_delta HP) HQ)).
  intro v. destruct (classic (P v)); tauto.
Defined.

Definition arithmetic_sorted_definable_iff_delta {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {P Q : (Fin.t k -> M) -> Prop}
    (HP : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) P)
    (HQ : arithmetic_sorted_definable Str (arithmetic_delta_symbol rank) Q) :
    arithmetic_sorted_definable Str (arithmetic_delta_symbol rank)
      (fun v => P v <-> Q v) :=
  arithmetic_sorted_definable_and
    (arithmetic_sorted_definable_imp_delta HP HQ)
    (arithmetic_sorted_definable_imp_delta HQ HP).

(** List representatives make finite-family closure duplicate tolerant and
    remove the source's decidable-equality requirement. *)
Fixpoint arithmetic_sorted_definable_list_conj
    {M : Type} {I : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (R : I -> (Fin.t k -> M) -> Prop)
    (s : list I)
    (H : forall i, arithmetic_sorted_definable Str symbol (R i)) {struct s} :
    arithmetic_sorted_definable Str symbol
      (fun v => forall i, In i s -> R i v).
Proof.
  destruct s as [| a s].
  - apply (arithmetic_sorted_definable_of_iff
      (arithmetic_sorted_definable_verum (k := k) Str symbol)).
    intro v. split.
    + intros _. constructor.
    + intros _ i Hin. contradiction.
  - apply (arithmetic_sorted_definable_of_iff
      (arithmetic_sorted_definable_and (H a)
        (@arithmetic_sorted_definable_list_conj
          M I k symbol Str R s H))).
    intro v. split.
    + intro Hall. split.
      * apply (Hall a). now left.
      * intros i Hin. apply (Hall i). now right.
    + intros [Ha Hs] i [Hi | Hin].
      * now subst i.
      * now apply Hs.
Defined.

Fixpoint arithmetic_sorted_definable_list_disj
    {M : Type} {I : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (R : I -> (Fin.t k -> M) -> Prop)
    (s : list I)
    (H : forall i, arithmetic_sorted_definable Str symbol (R i)) {struct s} :
    arithmetic_sorted_definable Str symbol
      (fun v => exists i, In i s /\ R i v).
Proof.
  destruct s as [| a s].
  - apply (arithmetic_sorted_definable_of_iff
      (arithmetic_sorted_definable_falsum (k := k) Str symbol)).
    intro v. split.
    + intros [i [Hin _]]. contradiction.
    + contradiction.
  - apply (arithmetic_sorted_definable_of_iff
      (arithmetic_sorted_definable_or (H a)
        (@arithmetic_sorted_definable_list_disj
          M I k symbol Str R s H))).
    intro v. split.
    + intros [i [[Hi | Hin] HR]].
      * left. now subst i.
      * right. now exists i.
    + intros [Ha | [i [Hin HR]]].
      * exists a. split; [now left | exact Ha].
      * exists i. split; [now right | exact HR].
Defined.

Definition arithmetic_sorted_definable_finite_conj
    {M : Type} {I : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (C : finite_cover I) (R : I -> (Fin.t k -> M) -> Prop)
    (H : forall i, arithmetic_sorted_definable Str symbol (R i)) :
    arithmetic_sorted_definable Str symbol
      (fun v => forall i, R i v).
Proof.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_list_conj
      (R := R) (finite_cover_list C) H)).
  intro v. split.
  - intros Hall i _. apply Hall.
  - intros Hall i. apply (Hall i). exact (finite_cover_complete C i).
Defined.

Definition arithmetic_sorted_definable_finite_disj
    {M : Type} {I : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    (C : finite_cover I) (R : I -> (Fin.t k -> M) -> Prop)
    (H : forall i, arithmetic_sorted_definable Str symbol (R i)) :
    arithmetic_sorted_definable Str symbol
      (fun v => exists i, R i v).
Proof.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_list_disj
      (R := R) (finite_cover_list C) H)).
  intro v. split.
  - intros [i HR]. exists i. split.
    + exact (finite_cover_complete C i).
    + exact HR.
  - intros [i [_ HR]]. now exists i.
Defined.

(** * Equality and term graphs *)

Definition arithmetic_sorted_definable_eq_terms {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (symbol : arithmetic_hierarchy_symbol)
    (t u : semiterm oring_language M k) :
    arithmetic_sorted_definable Str symbol
      (fun v => semiterm_val Str v (fun x => x) t =
        semiterm_val Str v (fun x => x) u).
Proof.
  destruct symbol as [class rank].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_eq
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := rank |} t u |}. split.
  - destruct class; simpl; trivial. intro v; reflexivity.
  - intro v. rewrite arithmetic_sorted_eq_val.
    change
      (semiformula_eval Str v (fun x => x)
        (first_order_definable_formula
          (first_order_definable_eq_terms
            (H := arithmetic_eq_operator) HEq t u)) <->
       semiterm_val Str v (fun x => x) t =
       semiterm_val Str v (fun x => x) u).
    apply (first_order_definable_spec
      (first_order_definable_eq_terms
        (H := arithmetic_eq_operator) HEq t u)).
Defined.

Definition arithmetic_sorted_definable_term_graph {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (symbol : arithmetic_hierarchy_symbol)
    (t : semiterm oring_language M k) :
    arithmetic_sorted_definable_function Str symbol
      (fun v => semiterm_val Str v (fun x => x) t).
Proof.
  unfold arithmetic_sorted_definable_function.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_eq_terms (Str := Str) HEq symbol
      (@Semiterm_bvar oring_language M (S k) Fin.F1)
      (rew_apply (rew_map Fin.FS (fun x => x)) t))).
  intro w. rewrite semiterm_val_map. reflexivity.
Defined.

Definition arithmetic_sorted_definable_projection {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (symbol : arithmetic_hierarchy_symbol) (i : Fin.t k) :
    arithmetic_sorted_definable_function Str symbol (fun v => v i) :=
  arithmetic_sorted_definable_term_graph (Str := Str) HEq symbol
    (@Semiterm_bvar oring_language M k i).

Definition arithmetic_sorted_definable_parameter_constant {M : Type} {k}
    (Str : first_order_structure oring_language M)
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (symbol : arithmetic_hierarchy_symbol) (c : M) :
    arithmetic_sorted_definable_function Str symbol
      (fun _ : Fin.t k -> M => c) :=
  arithmetic_sorted_definable_term_graph (Str := Str) HEq symbol
    (@Semiterm_fvar oring_language M k c).

(** * Bound-variable substitution and quantifier closure *)

(** This single term-substitution theorem subsumes the source's variable
    retraction and term-retraction operations.  Its target predicate exposes
    exactly the valuation induced by the substituted terms. *)
Definition arithmetic_sorted_definable_substitute_bound
    {M : Type} {k m symbol}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str symbol P)
    (t : Fin.t k -> semiterm oring_language M m) :
    arithmetic_sorted_definable Str symbol
      (fun v : Fin.t m -> M =>
        P (fun i => semiterm_val Str v (fun x => x) (t i))).
Proof.
  destruct symbol as [class rank]. destruct H as [p [Hp Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_rewrite (rew_subst t) p |}. split.
  - destruct class; simpl in *; trivial.
    now apply arithmetic_sorted_delta_proper_with_params_on_subst.
  - intro v. rewrite arithmetic_sorted_rewrite_val.
    rewrite semiformula_eval_rewrite.
    change
      (semiformula_eval Str
        (fun i => semiterm_val Str v (fun x => x) (t i))
        (fun x => x) (arithmetic_sorted_formula_val p) <->
       P (fun i => semiterm_val Str v (fun x => x) (t i))).
    apply Hspec.
Defined.

Definition arithmetic_sorted_definable_retraction
    {M : Type} {k m symbol}
    {Str : first_order_structure oring_language M}
    {P : (Fin.t k -> M) -> Prop}
    (H : arithmetic_sorted_definable Str symbol P)
    (e : Fin.t k -> Fin.t m) :
    arithmetic_sorted_definable Str symbol
      (fun v : Fin.t m -> M => P (fun i => v (e i))).
Proof.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_substitute_bound H
      (fun i => @Semiterm_bvar oring_language M m (e i)))).
  intro v. reflexivity.
Defined.

Definition arithmetic_sorted_definable_ball {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {R : (Fin.t k -> M) -> M -> Prop}
    (H : arithmetic_sorted_definable Str symbol
      (fun w : Fin.t (S k) -> M =>
        R (fun i => w (Fin.FS i)) (w Fin.F1)))
    (t : semiterm oring_language M k) :
    arithmetic_sorted_definable Str symbol
      (fun v : Fin.t k -> M => forall x : M,
        semiformula_operator_eval Str
          (fin_two x (semiterm_val Str v (fun y => y) t))
          (semiformula_lt_operator arithmetic_lt_operator) -> R v x).
Proof.
  destruct symbol as [class rank]. destruct H as [p [Hp Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_ball t p |}. split.
  - destruct class; simpl in *; trivial.
    now apply arithmetic_sorted_delta_proper_ball.
  - intro v. rewrite arithmetic_sorted_ball_val.
    rewrite semiformula_eval_ball_lt.
    split; intros Hall x Hguard.
    + apply (proj1 (Hspec (fin_env_cons x v))). now apply Hall.
    + apply (proj2 (Hspec (fin_env_cons x v))). now apply Hall.
Defined.

Definition arithmetic_sorted_definable_bex {M : Type} {k symbol}
    {Str : first_order_structure oring_language M}
    {R : (Fin.t k -> M) -> M -> Prop}
    (H : arithmetic_sorted_definable Str symbol
      (fun w : Fin.t (S k) -> M =>
        R (fun i => w (Fin.FS i)) (w Fin.F1)))
    (t : semiterm oring_language M k) :
    arithmetic_sorted_definable Str symbol
      (fun v : Fin.t k -> M => exists x : M,
        semiformula_operator_eval Str
          (fin_two x (semiterm_val Str v (fun y => y) t))
          (semiformula_lt_operator arithmetic_lt_operator) /\ R v x).
Proof.
  destruct symbol as [class rank]. destruct H as [p [Hp Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_bex t p |}. split.
  - destruct class; simpl in *; trivial.
    now apply arithmetic_sorted_delta_proper_bex.
  - intro v. rewrite arithmetic_sorted_bex_val.
    rewrite semiformula_eval_bex_lt.
    split.
    + intros [x [Hguard Hbody]]. exists x. split; [exact Hguard |].
      exact (proj1 (Hspec (fin_env_cons x v)) Hbody).
    + intros [x [Hguard Hbody]]. exists x. split; [exact Hguard |].
      exact (proj2 (Hspec (fin_env_cons x v)) Hbody).
Defined.

Definition arithmetic_sorted_definable_exists {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {R : (Fin.t k -> M) -> M -> Prop}
    (H : arithmetic_sorted_definable Str
      (arithmetic_sigma_symbol (S rank))
      (fun w : Fin.t (S k) -> M =>
        R (fun i => w (Fin.FS i)) (w Fin.F1))) :
    arithmetic_sorted_definable Str (arithmetic_sigma_symbol (S rank))
      (fun v : Fin.t k -> M => exists x : M, R v x).
Proof.
  destruct H as [p [_ Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_exists p |}. split; [exact I |].
  intro v. rewrite arithmetic_sorted_exists_val. simpl.
  split.
  - intros [x Hbody]. exists x.
    exact (proj1 (Hspec (fin_env_cons x v)) Hbody).
  - intros [x Hbody]. exists x.
    exact (proj2 (Hspec (fin_env_cons x v)) Hbody).
Defined.

Definition arithmetic_sorted_definable_all {M : Type} {k rank}
    {Str : first_order_structure oring_language M}
    {R : (Fin.t k -> M) -> M -> Prop}
    (H : arithmetic_sorted_definable Str
      (arithmetic_pi_symbol (S rank))
      (fun w : Fin.t (S k) -> M =>
        R (fun i => w (Fin.FS i)) (w Fin.F1))) :
    arithmetic_sorted_definable Str (arithmetic_pi_symbol (S rank))
      (fun v : Fin.t k -> M => forall x : M, R v x).
Proof.
  destruct H as [p [_ Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_all p |}. split; [exact I |].
  intro v. rewrite arithmetic_sorted_all_val. simpl.
  split; intros Hall x.
  - exact (proj1 (Hspec (fin_env_cons x v)) (Hall x)).
  - exact (proj2 (Hspec (fin_env_cons x v)) (Hall x)).
Defined.

Definition arithmetic_sorted_definable_exists_vector
    {M : Type} {l k rank}
    {Str : first_order_structure oring_language M}
    (Q : (Fin.t (l + k) -> M) -> Prop)
    (H : arithmetic_sorted_definable Str
      (arithmetic_sigma_symbol (S rank)) Q) :
    arithmetic_sorted_definable Str (arithmetic_sigma_symbol (S rank))
      (fun b : Fin.t k -> M => exists e : Fin.t l -> M,
        Q (fin_env_append l k e b)).
Proof.
  destruct H as [p [_ Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_exists_iter p |}. split; [exact I |].
  intro b. rewrite arithmetic_sorted_exists_iter_val.
  rewrite semiformula_eval_exists_iter. split.
  - intros [e Hbody]. exists e.
    exact (proj1 (Hspec (fin_env_append l k e b)) Hbody).
  - intros [e HQ]. exists e.
    exact (proj2 (Hspec (fin_env_append l k e b)) HQ).
Defined.

Definition arithmetic_sorted_definable_all_vector
    {M : Type} {l k rank}
    {Str : first_order_structure oring_language M}
    (Q : (Fin.t (l + k) -> M) -> Prop)
    (H : arithmetic_sorted_definable Str
      (arithmetic_pi_symbol (S rank)) Q) :
    arithmetic_sorted_definable Str (arithmetic_pi_symbol (S rank))
      (fun b : Fin.t k -> M => forall e : Fin.t l -> M,
        Q (fin_env_append l k e b)).
Proof.
  destruct H as [p [_ Hspec]].
  refine {| arithmetic_sorted_definable_formula :=
    arithmetic_sorted_all_iter p |}. split; [exact I |].
  intro b. rewrite arithmetic_sorted_all_iter_val.
  rewrite semiformula_eval_all_iter. split; intros Hall e.
  - exact (proj1 (Hspec (fin_env_append l k e b)) (Hall e)).
  - exact (proj2 (Hspec (fin_env_append l k e b)) (Hall e)).
Defined.

(** * Substitution by formula-defined functions *)

(** The graph equations share the existential prefix holding the selected
    function values and the suffix holding the original parameters. *)
Definition arithmetic_sorted_definable_graph_family
    {M : Type} {k l rank}
    {Str : first_order_structure oring_language M}
    (f : Fin.t k -> (Fin.t l -> M) -> M)
    (Hf : forall i, arithmetic_sorted_definable_function Str
      (arithmetic_sigma_symbol (S rank)) (f i)) :
    arithmetic_sorted_definable Str (arithmetic_sigma_symbol (S rank))
      (fun w : Fin.t (k + l) -> M => forall i,
        w (Fin.L l i) = f i (fun j => w (Fin.R k j))).
Proof.
  apply (arithmetic_sorted_definable_finite_conj
    (R := fun i w =>
      w (Fin.L l i) = f i (fun j => w (Fin.R k j)))
    (fin_t_finite_cover k)).
  intro i.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_retraction (Hf i)
      (fin_graph_retraction i))).
  intro w. reflexivity.
Defined.

Definition arithmetic_sorted_definable_substitution_sigma
    {M : Type} {k l rank}
    {Str : first_order_structure oring_language M}
    (P : (Fin.t k -> M) -> Prop)
    (f : Fin.t k -> (Fin.t l -> M) -> M)
    (HP : arithmetic_sorted_definable Str
      (arithmetic_sigma_symbol (S rank)) P)
    (Hf : forall i, arithmetic_sorted_definable_function Str
      (arithmetic_sigma_symbol (S rank)) (f i)) :
    arithmetic_sorted_definable Str (arithmetic_sigma_symbol (S rank))
      (fun z : Fin.t l -> M => P (fun i => f i z)).
Proof.
  refine (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_exists_vector
      (Q := fun w : Fin.t (k + l) -> M =>
        (forall i, w (Fin.L l i) =
          f i (fun j => w (Fin.R k j))) /\
        P (fun i => w (Fin.L l i)))
      (arithmetic_sorted_definable_and
        (arithmetic_sorted_definable_graph_family (f := f) Hf)
        (arithmetic_sorted_definable_retraction HP (Fin.L l)))) _).
  intro z. split.
  - intro Hz. exists (fun i => f i z). split.
    + intro i. rewrite fin_env_append_left, fin_env_append_right_eta.
      reflexivity.
    + now rewrite fin_env_append_left_eta.
  - intros [ys [Hgraph HPys]].
    assert (Hys : ys = fun i => f i z).
    { apply functional_extensionality. intro i.
      specialize (Hgraph i).
      now rewrite fin_env_append_left, fin_env_append_right_eta in Hgraph. }
    rewrite fin_env_append_left_eta in HPys. now rewrite <- Hys.
Defined.

Definition arithmetic_sorted_definable_substitution_pi
    {M : Type} {k l rank}
    {Str : first_order_structure oring_language M}
    (P : (Fin.t k -> M) -> Prop)
    (f : Fin.t k -> (Fin.t l -> M) -> M)
    (HP : arithmetic_sorted_definable Str
      (arithmetic_pi_symbol (S rank)) P)
    (Hf : forall i, arithmetic_sorted_definable_function Str
      (arithmetic_sigma_symbol (S rank)) (f i)) :
    arithmetic_sorted_definable Str (arithmetic_pi_symbol (S rank))
      (fun z : Fin.t l -> M => P (fun i => f i z)).
Proof.
  refine (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_all_vector
      (Q := fun w : Fin.t (k + l) -> M =>
        (forall i, w (Fin.L l i) =
          f i (fun j => w (Fin.R k j))) ->
        P (fun i => w (Fin.L l i)))
      (arithmetic_sorted_definable_imp_pi
        (arithmetic_sorted_definable_graph_family (f := f) Hf)
        (arithmetic_sorted_definable_retraction HP (Fin.L l)))) _).
  intro z. split.
  - intros HPz ys Hgraph.
    assert (Hys : ys = fun i => f i z).
    { apply functional_extensionality. intro i.
      specialize (Hgraph i).
      now rewrite fin_env_append_left, fin_env_append_right_eta in Hgraph. }
    rewrite fin_env_append_left_eta. now rewrite Hys.
  - intros Hall.
    specialize (Hall (fun i => f i z)).
    assert (Hgraph : forall i,
      fin_env_append k l (fun i => f i z) z (Fin.L l i) =
      f i (fun j =>
        fin_env_append k l (fun i => f i z) z (Fin.R k j))).
    { intro i. rewrite fin_env_append_left, fin_env_append_right_eta.
      reflexivity. }
    specialize (Hall Hgraph).
    now rewrite fin_env_append_left_eta in Hall.
Defined.

Definition arithmetic_sorted_definable_substitution
    {M : Type} {k l rank class}
    {Str : first_order_structure oring_language M}
    (P : (Fin.t k -> M) -> Prop)
    (f : Fin.t k -> (Fin.t l -> M) -> M)
    (HP : arithmetic_sorted_definable Str
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := S rank |} P)
    (Hf : forall i, arithmetic_sorted_definable_function Str
      (arithmetic_sigma_symbol (S rank)) (f i)) :
    arithmetic_sorted_definable Str
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := S rank |}
      (fun z : Fin.t l -> M => P (fun i => f i z)).
Proof.
  destruct class.
  - exact (arithmetic_sorted_definable_substitution_sigma
      (P := P) (f := f) HP Hf).
  - exact (arithmetic_sorted_definable_substitution_pi
      (P := P) (f := f) HP Hf).
  - apply arithmetic_sorted_definable_delta_of_sigma_pi.
    + apply (arithmetic_sorted_definable_substitution_sigma
        (P := P) (f := f)
        (arithmetic_sorted_definable_of_delta HP ArithmeticHierarchySigma) Hf).
    + apply (arithmetic_sorted_definable_substitution_pi
        (P := P) (f := f)
        (arithmetic_sorted_definable_of_delta HP ArithmeticHierarchyPi) Hf).
Defined.

(** Reindex a function graph while keeping its distinguished output in the
    head coordinate. *)
Definition arithmetic_function_graph_reindex {k l}
    (e : Fin.t k -> Fin.t l) : Fin.t (S k) -> Fin.t (S l) :=
  fun j => @Fin.caseS' k j (fun _ => Fin.t (S l))
    Fin.F1 (fun i => Fin.FS (e i)).

Lemma arithmetic_function_graph_reindex_head : forall k l
    (e : Fin.t k -> Fin.t l),
  arithmetic_function_graph_reindex e Fin.F1 = Fin.F1.
Proof. reflexivity. Qed.

Lemma arithmetic_function_graph_reindex_tail : forall k l
    (e : Fin.t k -> Fin.t l) (i : Fin.t k),
  arithmetic_function_graph_reindex e (Fin.FS i) = Fin.FS (e i).
Proof. reflexivity. Qed.

Definition arithmetic_sorted_definable_function_retraction
    {M : Type} {k l symbol}
    {Str : first_order_structure oring_language M}
    {f : (Fin.t k -> M) -> M}
    (Hf : arithmetic_sorted_definable_function Str symbol f)
    (e : Fin.t k -> Fin.t l) :
    arithmetic_sorted_definable_function Str symbol
      (fun v : Fin.t l -> M => f (fun i => v (e i))).
Proof.
  unfold arithmetic_sorted_definable_function in *.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_retraction Hf
      (arithmetic_function_graph_reindex e))).
  intro w. reflexivity.
Defined.

(** The family substituted into an outer function graph: the head member is
    the preserved output coordinate, and every tail member is an inner
    function evaluated on the parameter tail. *)
Definition arithmetic_function_substitution_family
    {M : Type} {k l}
    (f : Fin.t k -> (Fin.t l -> M) -> M)
    (i : Fin.t (S k)) (w : Fin.t (S l) -> M) : M :=
  @Fin.caseS' k i (fun _ => M)
    (w Fin.F1) (fun j => f j (fun q => w (Fin.FS q))).

Lemma arithmetic_function_substitution_family_head : forall
    (M : Type) k l (f : Fin.t k -> (Fin.t l -> M) -> M)
    (w : Fin.t (S l) -> M),
  arithmetic_function_substitution_family f Fin.F1 w = w Fin.F1.
Proof. reflexivity. Qed.

Lemma arithmetic_function_substitution_family_tail : forall
    (M : Type) k l (f : Fin.t k -> (Fin.t l -> M) -> M)
    (i : Fin.t k) (w : Fin.t (S l) -> M),
  arithmetic_function_substitution_family f (Fin.FS i) w =
  f i (fun q => w (Fin.FS q)).
Proof. reflexivity. Qed.

Definition arithmetic_sorted_definable_function_substitution
    {M : Type} {k l rank class}
    {Str : first_order_structure oring_language M}
    (HEq : structure_interprets_eq Str arithmetic_eq_operator)
    (F : (Fin.t k -> M) -> M)
    (f : Fin.t k -> (Fin.t l -> M) -> M)
    (HF : arithmetic_sorted_definable_function Str
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := S rank |} F)
    (Hf : forall i, arithmetic_sorted_definable_function Str
      (arithmetic_sigma_symbol (S rank)) (f i)) :
    arithmetic_sorted_definable_function Str
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := S rank |}
      (fun z : Fin.t l -> M => F (fun i => f i z)).
Proof.
  assert (Hg : forall i : Fin.t (S k),
    arithmetic_sorted_definable_function Str
      (arithmetic_sigma_symbol (S rank))
      (arithmetic_function_substitution_family f i)).
  { intro i.
    refine (@Fin.caseS' k i
      (fun i => arithmetic_sorted_definable_function Str
        (arithmetic_sigma_symbol (S rank))
        (arithmetic_function_substitution_family f i)) _ _).
    - apply (arithmetic_sorted_definable_projection (Str := Str) HEq
        (arithmetic_sigma_symbol (S rank)) Fin.F1).
    - intro j.
      apply (arithmetic_sorted_definable_of_iff
        (arithmetic_sorted_definable_function_retraction
          (Hf j) (fun q => Fin.FS q))).
      intro w. reflexivity. }
  unfold arithmetic_sorted_definable_function in *.
  apply (arithmetic_sorted_definable_of_iff
    (arithmetic_sorted_definable_substitution
      (P := fun y : Fin.t (S k) -> M =>
        y Fin.F1 = F (fun i => y (Fin.FS i)))
      (f := arithmetic_function_substitution_family f) HF Hg)).
  intro w. reflexivity.
Defined.
