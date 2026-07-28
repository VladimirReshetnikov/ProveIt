(**
  Coherence spaces and their linear-connective constructions.

  This module ports the active mathematical surface of Foundation's
  [Semantics/CoherenceSpace/Basic.lean].  Sets are predicates and points are
  cliques.  Equality of points is deliberately extensional: none of the set,
  colimit, or linear-identity laws needs functional or propositional
  extensionality.
*)

From Stdlib Require Import Logic.Classical_Prop RelationClasses Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Coherence, incoherence, and their strict variants *)

Record coherence_space (A : Type) := {
  coherent : A -> A -> Prop;
  coherent_reflexive : forall x, coherent x x;
  coherent_symmetric : forall x y, coherent x y -> coherent y x
}.

Arguments coherent {A} _ _ _.
Arguments coherent_reflexive {A} _ _.
Arguments coherent_symmetric {A} _ _ _ _.

Definition incoherent {A} (C : coherence_space A) (x y : A) : Prop :=
  ~ coherent C x y \/ x = y.

Definition strictly_incoherent {A} (C : coherence_space A)
    (x y : A) : Prop :=
  ~ coherent C x y.

Definition strictly_coherent {A} (C : coherence_space A)
    (x y : A) : Prop :=
  ~ incoherent C x y.

Lemma coherence_refl :
  forall A (C : coherence_space A) (x : A), coherent C x x.
Proof. intros A C x; apply coherent_reflexive. Qed.

Lemma coherence_sym :
  forall A (C : coherence_space A) (x y : A),
    coherent C x y -> coherent C y x.
Proof. intros A C x y; apply coherent_symmetric. Qed.

Lemma coherence_sym_iff :
  forall A (C : coherence_space A) (x y : A),
    coherent C x y <-> coherent C y x.
Proof.
  intros A C x y; split; apply coherence_sym.
Qed.

Lemma incoherence_refl :
  forall A (C : coherence_space A) (x : A), incoherent C x x.
Proof. intros A C x; right; reflexivity. Qed.

Lemma incoherence_sym :
  forall A (C : coherence_space A) (x y : A),
    incoherent C x y -> incoherent C y x.
Proof.
  intros A C x y [Hnot | ->].
  - left. intro Hyx. apply Hnot. now apply coherence_sym.
  - apply incoherence_refl.
Qed.

Lemma incoherence_sym_iff :
  forall A (C : coherence_space A) (x y : A),
    incoherent C x y <-> incoherent C y x.
Proof.
  intros A C x y; split; apply incoherence_sym.
Qed.

Lemma strictly_incoherent_iff_incoherent_ne :
  forall A (C : coherence_space A) (x y : A),
    strictly_incoherent C x y <-> incoherent C x y /\ x <> y.
Proof.
  intros A C x y; unfold strictly_incoherent, incoherent; split.
  - intro Hnot. split; [now left |].
    intros ->. apply Hnot. apply coherence_refl.
  - intros [[Hnot | Heq] Hneq]; [exact Hnot | contradiction].
Qed.

Lemma incoherent_iff_strictly_incoherent_or_eq :
  forall A (C : coherence_space A) (x y : A),
    incoherent C x y <-> strictly_incoherent C x y \/ x = y.
Proof. reflexivity. Qed.

Lemma strictly_incoherent_sym :
  forall A (C : coherence_space A) (x y : A),
    strictly_incoherent C x y -> strictly_incoherent C y x.
Proof.
  intros A C x y Hnot Hyx. apply Hnot. now apply coherence_sym.
Qed.

Lemma strictly_incoherent_sym_iff :
  forall A (C : coherence_space A) (x y : A),
    strictly_incoherent C x y <-> strictly_incoherent C y x.
Proof.
  intros A C x y; split; apply strictly_incoherent_sym.
Qed.

Lemma strictly_coherent_iff_coherent_ne :
  forall A (C : coherence_space A) (x y : A),
    strictly_coherent C x y <-> coherent C x y /\ x <> y.
Proof.
  intros A C x y; unfold strictly_coherent, incoherent; split.
  - intro H. split.
    + apply NNPP. intro Hnot. apply H. now left.
    + intro Heq. apply H. now right.
  - intros [Hcoh Hneq] [Hnot | Heq].
    + exact (Hnot Hcoh).
    + exact (Hneq Heq).
Qed.

Lemma coherent_iff_strictly_coherent_or_eq :
  forall A (C : coherence_space A) (x y : A),
    coherent C x y <-> strictly_coherent C x y \/ x = y.
Proof.
  intros A C x y; split.
  - intro Hcoh. destruct (classic (x = y)) as [Heq | Hneq].
    + now right.
    + left. apply (proj2 (strictly_coherent_iff_coherent_ne C x y)).
      now split.
  - intros [Hstrict | ->].
    + exact (proj1
        (proj1 (strictly_coherent_iff_coherent_ne C x y) Hstrict)).
    + apply coherence_refl.
Qed.

Lemma strictly_coherent_sym :
  forall A (C : coherence_space A) (x y : A),
    strictly_coherent C x y -> strictly_coherent C y x.
Proof.
  intros A C x y Hstrict.
  unfold strictly_coherent, incoherent in *.
  intros [Hnot | Heq].
  - apply Hstrict. left. intro Hxy.
    apply Hnot. now apply coherence_sym.
  - apply Hstrict. right. now symmetry.
Qed.

Lemma strictly_coherent_sym_iff :
  forall A (C : coherence_space A) (x y : A),
    strictly_coherent C x y <-> strictly_coherent C y x.
Proof.
  intros A C x y; split; apply strictly_coherent_sym.
Qed.

Lemma coherence_trichotomy :
  forall A (C : coherence_space A) (x y : A),
    strictly_coherent C x y \/ x = y \/ strictly_incoherent C x y.
Proof.
  intros A C x y. destruct (classic (x = y)) as [Heq | Hneq].
  - now right; left.
  - destruct (classic (coherent C x y)) as [Hcoh | Hnot].
    + left. apply (proj2 (strictly_coherent_iff_coherent_ne C x y)).
      now split.
    + now right; right.
Qed.

(** * Predicate sets, cliques, and points *)

Definition coherence_set (A : Type) : Type := A -> Prop.

Definition set_included {A} (s t : coherence_set A) : Prop :=
  forall x, s x -> t x.

Definition set_equiv {A} (s t : coherence_set A) : Prop :=
  forall x, s x <-> t x.

Definition set_empty {A} : coherence_set A := fun _ => False.

Definition set_singleton {A} (x : A) : coherence_set A :=
  fun y => y = x.

Definition set_insert {A} (x : A) (s : coherence_set A) : coherence_set A :=
  fun y => y = x \/ s y.

Definition set_intersection {A} (s t : coherence_set A) : coherence_set A :=
  fun x => s x /\ t x.

Definition set_union {A} (s t : coherence_set A) : coherence_set A :=
  fun x => s x \/ t x.

Definition set_big_union {A}
    (families : coherence_set A -> Prop) : coherence_set A :=
  fun x => exists s, families s /\ s x.

Definition is_clique {A} (C : coherence_space A)
    (s : coherence_set A) : Prop :=
  forall x, s x -> forall y, s y -> coherent C x y.

Definition is_coclique {A} (C : coherence_space A)
    (s : coherence_set A) : Prop :=
  forall x, s x -> forall y, s y -> incoherent C x y.

Lemma clique_empty :
  forall A (C : coherence_space A), is_clique C (@set_empty A).
Proof. intros A C x Hx; contradiction. Qed.

Lemma clique_singleton :
  forall A (C : coherence_space A) x,
    is_clique C (set_singleton x).
Proof.
  intros A C x y -> z ->. apply coherence_refl.
Qed.

Lemma clique_of_subset :
  forall A (C : coherence_space A) s t,
    is_clique C s -> set_included t s -> is_clique C t.
Proof.
  intros A C s t Hclique Hsub x Hx y Hy.
  apply Hclique; now apply Hsub.
Qed.

Lemma clique_insert_iff :
  forall A (C : coherence_space A) x s,
    is_clique C (set_insert x s) <->
    (forall y, s y -> coherent C x y) /\ is_clique C s.
Proof.
  intros A C x s; split.
  - intro H; split.
    + intros y Hy. apply H; [now left | now right].
    + intros y Hy z Hz. apply H; now right.
  - intros [Hx Hs] y [-> | Hy] z [-> | Hz].
    + apply coherence_refl.
    + now apply Hx.
    + apply coherence_sym. now apply Hx.
    + now apply Hs.
Qed.

Definition set_doubleton {A} (x y : A) : coherence_set A :=
  set_insert x (set_singleton y).

Lemma clique_doubleton_iff :
  forall A (C : coherence_space A) x y,
    is_clique C (set_doubleton x y) <-> coherent C x y.
Proof.
  intros A C x y. unfold set_doubleton. rewrite clique_insert_iff; split.
  - intros [H _]. apply H. reflexivity.
  - intro Hxy. split.
    + intros z ->. exact Hxy.
    + apply clique_singleton.
Qed.

Lemma clique_big_union_of_pairwise_union :
  forall A (C : coherence_space A) (families : coherence_set A -> Prop),
    (forall a, families a -> forall b, families b ->
      is_clique C (set_union a b)) ->
    is_clique C (set_big_union families).
Proof.
  intros A C families Hpair x [a [Ha Hxa]] y [b [Hb Hyb]].
  apply (Hpair a Ha b Hb); [now left | now right].
Qed.

Record point {A : Type} (C : coherence_space A) := {
  point_member : A -> Prop;
  point_is_clique : is_clique C point_member
}.

Arguments point_member {A C} _ _.
Arguments point_is_clique {A C} _.

Definition point_included {A} {C : coherence_space A}
    (p q : point C) : Prop :=
  forall x, point_member p x -> point_member q x.

Definition point_equiv {A} {C : coherence_space A}
    (p q : point C) : Prop :=
  forall x, point_member p x <-> point_member q x.

Lemma point_equiv_refl :
  forall A (C : coherence_space A) (p : point C), point_equiv p p.
Proof. intros A C p x; reflexivity. Qed.

Lemma point_equiv_sym :
  forall A (C : coherence_space A) (p q : point C),
    point_equiv p q -> point_equiv q p.
Proof. intros A C p q H x; symmetry; apply H. Qed.

Lemma point_equiv_trans :
  forall A (C : coherence_space A) (p q r : point C),
    point_equiv p q -> point_equiv q r -> point_equiv p r.
Proof.
  intros A C p q r Hpq Hqr x.
  transitivity (point_member q x); [apply Hpq | apply Hqr].
Qed.

#[global] Instance point_equiv_equivalence A (C : coherence_space A) :
  Equivalence (@point_equiv A C).
Proof.
  split.
  - intro p. apply point_equiv_refl.
  - intros p q. apply point_equiv_sym.
  - intros p q r. apply point_equiv_trans.
Qed.

Lemma point_included_refl :
  forall A (C : coherence_space A) (p : point C), point_included p p.
Proof. firstorder. Qed.

Lemma point_included_trans :
  forall A (C : coherence_space A) (p q r : point C),
    point_included p q -> point_included q r -> point_included p r.
Proof. firstorder. Qed.

#[global] Instance point_included_preorder A (C : coherence_space A) :
  PreOrder (@point_included A C).
Proof.
  split.
  - intro p. apply point_included_refl.
  - intros p q r. apply point_included_trans.
Qed.

Lemma point_equiv_iff_mutual_inclusion :
  forall A (C : coherence_space A) (p q : point C),
    point_equiv p q <-> point_included p q /\ point_included q p.
Proof.
  intros A C p q; split.
  - intro H; split; intros x Hx; [apply (proj1 (H x)) | apply (proj2 (H x))];
      exact Hx.
  - intros [Hpq Hqp] x; split; auto.
Qed.

Lemma point_included_respects_equiv :
  forall A (C : coherence_space A) (p p' q q' : point C),
    point_equiv p p' -> point_equiv q q' ->
    (point_included p q <-> point_included p' q').
Proof.
  intros A C p p' q q' Hpp Hqq; split; intros H x Hx.
  - apply (proj1 (Hqq x)), H, (proj2 (Hpp x)), Hx.
  - apply (proj2 (Hqq x)), H, (proj1 (Hpp x)), Hx.
Qed.

Definition point_empty {A} (C : coherence_space A) : point C :=
  {| point_member := set_empty;
     point_is_clique := @clique_empty A C |}.

Definition point_singleton {A} (C : coherence_space A) (x : A) : point C :=
  {| point_member := set_singleton x;
     point_is_clique := @clique_singleton A C x |}.

Definition point_meet {A} {C : coherence_space A}
    (p q : point C) : point C.
Proof.
  refine {| point_member := set_intersection (point_member p) (point_member q) |}.
  apply (clique_of_subset (point_is_clique p)). firstorder.
Defined.

Lemma point_meet_member :
  forall A (C : coherence_space A) (p q : point C) x,
    point_member (point_meet p q) x <->
    point_member p x /\ point_member q x.
Proof. reflexivity. Qed.

Lemma point_clique :
  forall A (C : coherence_space A) (p : point C),
    is_clique C (point_member p).
Proof. intros; apply point_is_clique. Qed.

Lemma point_le_def :
  forall A (C : coherence_space A) (p q : point C),
    point_included p q <->
    set_included (point_member p) (point_member q).
Proof. reflexivity. Qed.

(** Directed families use the source's nonempty-upper-bound formulation. *)
Definition directed_on {X : Type} (R : X -> X -> Prop)
    (s : X -> Prop) : Prop :=
  forall x, s x -> forall y, s y ->
    exists z, s z /\ R x z /\ R y z.

Lemma directed_on_of_terminal_element :
  forall X (R : X -> X -> Prop) (s : X -> Prop) u,
    s u -> (forall x, s x -> R x u) -> directed_on R s.
Proof.
  intros X R s u Hu Htop x Hx y Hy.
  exists u; repeat split; auto.
Qed.

Definition raw_clique_colimit {A} (C : coherence_space A)
    (families : coherence_set A -> Prop)
    (Hcliques : forall s, families s -> is_clique C s)
    (Hdirected : directed_on set_included families) : point C.
Proof.
  refine {| point_member := set_big_union families |}.
  intros x [a [Ha Hxa]] y [b [Hb Hyb]].
  destruct (Hdirected a Ha b Hb) as [c [Hc [Hac Hbc]]].
  exact (Hcliques c Hc x (Hac x Hxa) y (Hbc y Hyb)).
Defined.

Definition point_colimit {A} {C : coherence_space A}
    (s : point C -> Prop)
    (Hdirected : directed_on point_included s) : point C.
Proof.
  refine {| point_member := fun x => exists p, s p /\ point_member p x |}.
  intros x [p [Hp Hxp]] y [q [Hq Hyq]].
  destruct (Hdirected p Hp q Hq) as [r [Hr [Hpr Hqr]]].
  exact (point_is_clique r x (Hpr x Hxp) y (Hqr y Hyq)).
Defined.

Lemma raw_clique_colimit_member :
  forall A (C : coherence_space A) families Hcliques Hdirected x,
    point_member
      (@raw_clique_colimit A C families Hcliques Hdirected) x <->
    exists s, families s /\ s x.
Proof. reflexivity. Qed.

Lemma point_colimit_member :
  forall A (C : coherence_space A) s Hdirected x,
    point_member (@point_colimit A C s Hdirected) x <->
    exists p, s p /\ point_member p x.
Proof. reflexivity. Qed.

(** * Discrete and total coherence spaces *)

Definition discrete_coherence_space (A : Type) : coherence_space A.
Proof.
  refine {| coherent := eq |}.
  - reflexivity.
  - intros x y; now symmetry.
Defined.

Definition total_coherence_space (A : Type) : coherence_space A.
Proof.
  refine {| coherent := fun _ _ => True |}; firstorder.
Defined.

Inductive coherence_top : Type := .
Inductive coherence_zero : Type := .
Inductive coherence_one : Type := coherence_star.
Inductive coherence_bottom : Type := coherence_absurd.

Definition coherence_top_space : coherence_space coherence_top :=
  discrete_coherence_space coherence_top.

Definition coherence_zero_space : coherence_space coherence_zero :=
  discrete_coherence_space coherence_zero.

Definition coherence_one_space : coherence_space coherence_one :=
  total_coherence_space coherence_one.

Definition coherence_bottom_space : coherence_space coherence_bottom :=
  total_coherence_space coherence_bottom.

Definition empty_type_coherence_space : coherence_space Empty_set :=
  discrete_coherence_space Empty_set.

Definition unit_coherence_space : coherence_space unit :=
  discrete_coherence_space unit.

Definition bool_coherence_space : coherence_space bool :=
  discrete_coherence_space bool.

(** * Linear negation *)

Inductive lneg (A : Type) : Type :=
| lneg_mk : A -> lneg A.

Arguments lneg_mk {A} _.

Definition lneg_coherent {A} (C : coherence_space A)
    (p q : lneg A) : Prop :=
  match p, q with
  | lneg_mk a, lneg_mk b => incoherent C a b
  end.

Definition lneg_space {A} (C : coherence_space A) : coherence_space (lneg A).
Proof.
  refine {| coherent := lneg_coherent C |}.
  - intros [a]. apply incoherence_refl.
  - intros [a] [b]. apply incoherence_sym.
Defined.

Lemma lneg_coherence_def :
  forall A (C : coherence_space A) (p q : lneg A),
    coherent (lneg_space C) p q <-> lneg_coherent C p q.
Proof. reflexivity. Qed.

Lemma lneg_mk_coherent_iff :
  forall A (C : coherence_space A) (a b : A),
    coherent (lneg_space C) (lneg_mk a) (lneg_mk b) <->
    incoherent C a b.
Proof. reflexivity. Qed.

Lemma lneg_mk_strictly_coherent_iff :
  forall A (C : coherence_space A) (a b : A),
    strictly_coherent (lneg_space C) (lneg_mk a) (lneg_mk b) <->
    strictly_incoherent C a b.
Proof.
  intros A C a b.
  unfold strictly_coherent, strictly_incoherent, incoherent; simpl.
  split.
  - intros Hstrict Hcoh.
    apply Hstrict. left.
    intros [Hnot | Heq].
    + exact (Hnot Hcoh).
    + apply Hstrict. right. now subst b.
  - intros Hnot [Hlincoh | Heq].
    + apply Hlincoh. now left.
    + inversion Heq; subst b. apply Hnot, coherence_refl.
Qed.

Lemma lneg_mk_incoherent_iff :
  forall A (C : coherence_space A) (a b : A),
    incoherent (lneg_space C) (lneg_mk a) (lneg_mk b) <->
    coherent C a b.
Proof.
  intros A C a b; unfold incoherent; simpl; split.
  - intros [Hnot | Heq].
    + apply NNPP. intro Hncoh. apply Hnot. now left.
    + inversion Heq. apply coherence_refl.
  - intro Hcoh. destruct (classic (a = b)) as [-> | Hneq].
    + now right.
    + left. intros [Hnot | Heq]; [exact (Hnot Hcoh) | contradiction].
Qed.

Lemma lneg_mk_strictly_incoherent_iff :
  forall A (C : coherence_space A) (a b : A),
    strictly_incoherent (lneg_space C) (lneg_mk a) (lneg_mk b) <->
    strictly_coherent C a b.
Proof.
  intros A C a b. unfold strictly_incoherent.
  rewrite lneg_mk_coherent_iff.
  reflexivity.
Qed.

(** * Multiplicative conjunction *)

Inductive tensor (A B : Type) : Type :=
| tensor_mk : A -> B -> tensor A B.

Arguments tensor_mk {A B} _ _.

Definition tensor_coherent {A B}
    (CA : coherence_space A) (CB : coherence_space B)
    (p q : tensor A B) : Prop :=
  match p, q with
  | tensor_mk a b, tensor_mk a' b' =>
      coherent CA a a' /\ coherent CB b b'
  end.

Definition tensor_space {A B}
    (CA : coherence_space A) (CB : coherence_space B) :
    coherence_space (tensor A B).
Proof.
  refine {| coherent := tensor_coherent CA CB |}.
  - intros [a b]; split; apply coherence_refl.
  - intros [a b] [a' b'] [Ha Hb]; split;
      now apply coherence_sym.
Defined.

Lemma tensor_coherence_def :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (p q : tensor A B),
    coherent (tensor_space CA CB) p q <-> tensor_coherent CA CB p q.
Proof. reflexivity. Qed.

Lemma tensor_mk_coherent_iff :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      a a' b b',
    coherent (tensor_space CA CB) (tensor_mk a b) (tensor_mk a' b') <->
    coherent CA a a' /\ coherent CB b b'.
Proof. reflexivity. Qed.

(** * Multiplicative disjunction *)

Inductive par (A B : Type) : Type :=
| par_mk : A -> B -> par A B.

Arguments par_mk {A B} _ _.

Definition par_to_pair {A B} (p : par A B) : A * B :=
  match p with par_mk a b => (a, b) end.

Definition par_coherent {A B}
    (CA : coherence_space A) (CB : coherence_space B)
    (p q : par A B) : Prop :=
  match p, q with
  | par_mk a b, par_mk a' b' =>
      (a = a' /\ b = b') \/
      strictly_coherent CA a a' \/ strictly_coherent CB b b'
  end.

Definition par_space {A B}
    (CA : coherence_space A) (CB : coherence_space B) :
    coherence_space (par A B).
Proof.
  refine {| coherent := par_coherent CA CB |}.
  - intros [a b]. now left.
  - intros [a b] [a' b'] [[Ha Hb] | [Ha | Hb]].
    + left. now split; symmetry.
    + right; left. now apply strictly_coherent_sym.
    + right; right. now apply strictly_coherent_sym.
Defined.

Lemma par_coherence_def :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (p q : par A B),
    coherent (par_space CA CB) p q <-> par_coherent CA CB p q.
Proof. reflexivity. Qed.

Lemma par_mk_coherent_iff :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      a a' b b',
    coherent (par_space CA CB) (par_mk a b) (par_mk a' b') <->
    (a = a' /\ b = b') \/
    strictly_coherent CA a a' \/ strictly_coherent CB b b'.
Proof. reflexivity. Qed.

Lemma par_mk_strictly_coherent_iff :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      a a' b b',
    strictly_coherent (par_space CA CB) (par_mk a b) (par_mk a' b') <->
    strictly_coherent CA a a' \/ strictly_coherent CB b b'.
Proof.
  intros A B CA CB a a' b b'.
  rewrite strictly_coherent_iff_coherent_ne. simpl. split.
  - intros [[[Ha Hb] | [Ha | Hb]] Hneq].
    + exfalso. apply Hneq. now subst a'; subst b'.
    + now left.
    + now right.
  - intros [Ha | Hb]; split.
    + now right; left.
    + destruct
        (proj1 (strictly_coherent_iff_coherent_ne CA a a') Ha)
        as [_ Hneq].
      intros Heq. apply Hneq. now inversion Heq.
    + now right; right.
    + destruct
        (proj1 (strictly_coherent_iff_coherent_ne CB b b') Hb)
        as [_ Hneq].
      intros Heq. apply Hneq. now inversion Heq.
Qed.

(** * Arbitrary par *)

Definition arrow_par_coherent {I} {R : I -> Type}
    (CR : forall i, coherence_space (R i))
    (f g : forall i, R i) : Prop :=
  f = g \/ exists i, strictly_coherent (CR i) (f i) (g i).

Definition arrow_par_space {I} {R : I -> Type}
    (CR : forall i, coherence_space (R i)) :
    coherence_space (forall i, R i).
Proof.
  refine {| coherent := arrow_par_coherent CR |}.
  - intro f. now left.
  - intros f g [-> | [i Hi]].
    + now left.
    + right. exists i. now apply strictly_coherent_sym.
Defined.

Lemma arrow_par_coherence_def :
  forall I (R : I -> Type) (CR : forall i, coherence_space (R i))
      (f g : forall i, R i),
    coherent (arrow_par_space CR) f g <-> arrow_par_coherent CR f g.
Proof. reflexivity. Qed.

Lemma arrow_par_coherent_iff :
  forall I (R : I -> Type) (CR : forall i, coherence_space (R i))
      (f g : forall i, R i),
    coherent (arrow_par_space CR) f g <->
    f = g \/ exists i, strictly_coherent (CR i) (f i) (g i).
Proof. reflexivity. Qed.

Lemma arrow_par_strictly_coherent_iff :
  forall I (R : I -> Type) (CR : forall i, coherence_space (R i))
      (f g : forall i, R i),
    strictly_coherent (arrow_par_space CR) f g <->
    exists i, strictly_coherent (CR i) (f i) (g i).
Proof.
  intros I R CR f g. rewrite strictly_coherent_iff_coherent_ne.
  simpl. split.
  - intros [[Heq | Hex] Hneq]; [contradiction | exact Hex].
  - intros [i Hi]. split.
    + right. now exists i.
    + intros ->. destruct
        (proj1 (strictly_coherent_iff_coherent_ne (CR i) (g i) (g i)) Hi)
        as [_ Hneq]. now apply Hneq.
Qed.

(** * Linear implication and its identity point *)

Definition lolli (A B : Type) : Type := par (lneg A) B.

Definition lolli_space {A B}
    (CA : coherence_space A) (CB : coherence_space B) :
    coherence_space (lolli A B) := par_space (lneg_space CA) CB.

Definition lolli_identity_member {A} (p : lolli A A) : Prop :=
  exists a, p = par_mk (lneg_mk a) a.

Lemma lolli_identity_clique :
  forall A (C : coherence_space A),
    is_clique (lolli_space C C) (@lolli_identity_member A).
Proof.
  intros A C p [a ->] q [b ->].
  destruct (coherence_trichotomy C a b) as [Hcoh | [-> | Hincoh]].
  - apply (proj2 (par_mk_coherent_iff (lneg_space C) C
      (lneg_mk a) (lneg_mk b) a b)).
    now right; right.
  - apply coherence_refl.
  - apply (proj2 (par_mk_coherent_iff (lneg_space C) C
      (lneg_mk a) (lneg_mk b) a b)).
    right; left. apply (proj2 (lneg_mk_strictly_coherent_iff C a b)).
    exact Hincoh.
Qed.

Definition lolli_identity {A} (C : coherence_space A) :
    point (lolli_space C C) :=
  {| point_member := lolli_identity_member;
     point_is_clique := lolli_identity_clique C |}.

(** * Binary additive conjunction *)

Inductive with_space_type (A B : Type) : Type :=
| with_inl : A -> with_space_type A B
| with_inr : B -> with_space_type A B.

Arguments with_inl {A B} _.
Arguments with_inr {A B} _.

Definition with_coherent {A B}
    (CA : coherence_space A) (CB : coherence_space B)
    (p q : with_space_type A B) : Prop :=
  match p, q with
  | with_inl a, with_inl a' => coherent CA a a'
  | with_inr b, with_inr b' => coherent CB b b'
  | _, _ => True
  end.

Definition additive_with_space {A B}
    (CA : coherence_space A) (CB : coherence_space B) :
    coherence_space (with_space_type A B).
Proof.
  refine {| coherent := with_coherent CA CB |}.
  - intros [a | b]; simpl; apply coherence_refl.
  - intros [a | b] [a' | b']; simpl; auto using coherence_sym.
Defined.

Lemma with_coherence_def :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (p q : with_space_type A B),
    coherent (additive_with_space CA CB) p q <->
    with_coherent CA CB p q.
Proof. reflexivity. Qed.

(** * Arbitrary additive conjunction *)

Inductive big_with {I : Type} (R : I -> Type) : Type :=
| big_with_mk : forall i, R i -> big_with R.

Arguments big_with_mk {I R} _ _.

Inductive big_with_coherent {I} {R : I -> Type}
    (CR : forall i, coherence_space (R i)) :
    big_with R -> big_with R -> Prop :=
| big_with_coherent_same :
    forall i (a b : R i), coherent (CR i) a b ->
      big_with_coherent CR (big_with_mk i a) (big_with_mk i b)
| big_with_coherent_different :
    forall i j (a : R i) (b : R j), i <> j ->
      big_with_coherent CR (big_with_mk i a) (big_with_mk j b).

Definition additive_big_with_space {I} {R : I -> Type}
    (CR : forall i, coherence_space (R i)) :
    coherence_space (big_with R).
Proof.
  refine {| coherent := big_with_coherent CR |}.
  - intros [i a]. apply big_with_coherent_same. apply coherence_refl.
  - intros p q H. destruct H.
    + apply big_with_coherent_same. now apply coherence_sym.
    + apply big_with_coherent_different. congruence.
Defined.

Lemma big_with_coherence_def :
  forall I (R : I -> Type) (CR : forall i, coherence_space (R i))
      (p q : big_with R),
    coherent (additive_big_with_space CR) p q <->
    big_with_coherent CR p q.
Proof. reflexivity. Qed.

(** * Binary additive disjunction *)

Inductive plus_space_type (A B : Type) : Type :=
| plus_inl : A -> plus_space_type A B
| plus_inr : B -> plus_space_type A B.

Arguments plus_inl {A B} _.
Arguments plus_inr {A B} _.

Inductive plus_coherent {A B}
    (CA : coherence_space A) (CB : coherence_space B) :
    plus_space_type A B -> plus_space_type A B -> Prop :=
| plus_coherent_left : forall a a', coherent CA a a' ->
    plus_coherent CA CB (plus_inl a) (plus_inl a')
| plus_coherent_right : forall b b', coherent CB b b' ->
    plus_coherent CA CB (plus_inr b) (plus_inr b').

Definition additive_plus_space {A B}
    (CA : coherence_space A) (CB : coherence_space B) :
    coherence_space (plus_space_type A B).
Proof.
  refine {| coherent := plus_coherent CA CB |}.
  - intros [a | b].
    + apply plus_coherent_left. apply coherence_refl.
    + apply plus_coherent_right. apply coherence_refl.
  - intros p q H. destruct H.
    + apply plus_coherent_left. now apply coherence_sym.
    + apply plus_coherent_right. now apply coherence_sym.
Defined.

Lemma plus_coherence_def :
  forall A B (CA : coherence_space A) (CB : coherence_space B)
      (p q : plus_space_type A B),
    coherent (additive_plus_space CA CB) p q <->
    plus_coherent CA CB p q.
Proof. reflexivity. Qed.

(** * Arbitrary additive disjunction *)

Inductive big_plus {I : Type} (R : I -> Type) : Type :=
| big_plus_mk : forall i, R i -> big_plus R.

Arguments big_plus_mk {I R} _ _.

Inductive big_plus_coherent {I} {R : I -> Type}
    (CR : forall i, coherence_space (R i)) :
    big_plus R -> big_plus R -> Prop :=
| big_plus_coherent_same :
    forall i (a b : R i), coherent (CR i) a b ->
      big_plus_coherent CR (big_plus_mk i a) (big_plus_mk i b).

Definition additive_big_plus_space {I} {R : I -> Type}
    (CR : forall i, coherence_space (R i)) :
    coherence_space (big_plus R).
Proof.
  refine {| coherent := big_plus_coherent CR |}.
  - intros [i a]. apply big_plus_coherent_same. apply coherence_refl.
  - intros p q H. destruct H.
    apply big_plus_coherent_same. now apply coherence_sym.
Defined.

Lemma big_plus_coherence_def :
  forall I (R : I -> Type) (CR : forall i, coherence_space (R i))
      (p q : big_plus R),
    coherent (additive_big_plus_space CR) p q <->
    big_plus_coherent CR p q.
Proof. reflexivity. Qed.
