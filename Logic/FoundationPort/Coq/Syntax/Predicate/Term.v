(**
  Arity-correct first-order semiterms with separate bound and free variables.

  This ports [Foundation/Syntax/Predicate/Term.lean].  Occurrence sets are
  exposed primarily as predicates, strictly generalizing the source's
  decidable finite-set interface: clients need no equality decision merely to
  reason about occurrence, positivity, or language maps.  A duplicate-
  tolerant list view is retained for enumeration and indexing.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Vectors.Fin.
From Stdlib Require Import Logic.Eqdep_dec.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive semiterm (L : language) (X : Type) (n : nat) : Type :=
| Semiterm_bvar : Fin.t n -> semiterm L X n
| Semiterm_fvar : X -> semiterm L X n
| Semiterm_func : forall k,
    language_func L k ->
    (Fin.t k -> semiterm L X n) -> semiterm L X n.

Arguments Semiterm_bvar {L X n} _.
Arguments Semiterm_fvar {L X n} _.
Arguments Semiterm_func {L X n k} _ _.

Definition term (L : language) (X : Type) := semiterm L X 0.
Definition closed_semiterm (L : language) (n : nat) := semiterm L Empty_set n.
Definition closed_term (L : language) := semiterm L Empty_set 0.
Definition syntactic_semiterm (L : language) (n : nat) := semiterm L nat n.
Definition syntactic_term (L : language) := semiterm L nat 0.

Definition fin_value {n} (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

Definition semiterm_from_free_default {L X n} (x : X) : semiterm L X n :=
  Semiterm_fvar x.

Definition semiterm_from_constant {L X n}
    (c : language_constant_inhabited L) : semiterm L X n :=
  Semiterm_func c (fun i : Fin.t 0 => match i with end).

(** * Executable equality over finite vectors and semiterms *)

Fixpoint fin_pointwise_eq_dec (n : nat) :
  forall (A : Type) (f g : Fin.t n -> A),
    (forall i, {f i = g i} + {f i <> g i}) ->
    {forall i, f i = g i} + {~ forall i, f i = g i}.
Proof.
  destruct n as [|n].
  - intros A f g decisions. left. intro i; inversion i.
  - intros A f g decisions.
    destruct (decisions Fin.F1) as [Hhead | Hhead].
    + destruct (@fin_pointwise_eq_dec n A
        (fun i => f (Fin.FS i)) (fun i => g (Fin.FS i))
        (fun i => decisions (Fin.FS i)))
        as [Htail | Htail].
      * left. intro i.
        refine (@Fin.caseS' n i (fun j => f j = g j) Hhead _).
        exact Htail.
      * right. intro Hall. apply Htail. intro i. apply Hall.
    + right. intro Hall. apply Hhead. apply Hall.
Defined.

Definition fin_function_eq_dec (n : nat) (A : Type)
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (f g : Fin.t n -> A) : {f = g} + {f <> g}.
Proof.
  destruct (@fin_pointwise_eq_dec n A f g (fun i => eq_dec (f i) (g i)))
    as [Hpointwise | Hneq].
  - left. apply functional_extensionality. exact Hpointwise.
  - right. intro Heq. apply Hneq. intro i. now rewrite Heq.
Defined.

Definition fin_function_pointwise_eq_dec (n : nat) (A : Type)
    (f g : Fin.t n -> A)
    (decisions : forall i, {f i = g i} + {f i <> g i}) :
    {f = g} + {f <> g}.
Proof.
  destruct (@fin_pointwise_eq_dec n A f g decisions)
    as [Hpointwise | Hneq].
  - left. apply functional_extensionality. exact Hpointwise.
  - right. intro Heq. apply Hneq. intro i. now rewrite Heq.
Defined.

Definition semiterm_outer_arity {L X n} (t : semiterm L X n) : option nat :=
  match t with
  | @Semiterm_func _ _ _ k _ _ => Some k
  | _ => None
  end.

Definition semiterm_function_payload (L : language) (X : Type) (n : nat) :=
  {k : nat &
    (language_func L k * (Fin.t k -> semiterm L X n))%type}.

Definition semiterm_outer_function_payload {L X n} (t : semiterm L X n) :
    option (semiterm_function_payload L X n) :=
  match t with
  | @Semiterm_func _ _ _ k f v => Some (existT _ k (f, v))
  | _ => None
  end.

Lemma option_some_injective :
  forall A (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H; now injection H. Qed.

Lemma semiterm_func_arity_injective :
  forall L X n k l (f : language_func L k)
         (v : Fin.t k -> semiterm L X n)
         (g : language_func L l)
         (w : Fin.t l -> semiterm L X n),
    Semiterm_func f v = Semiterm_func g w -> k = l.
Proof.
  intros L X n k l f v g w Heq.
  pose proof (f_equal semiterm_outer_arity Heq) as Harity.
  simpl in Harity. now injection Harity.
Qed.

Lemma semiterm_func_injective_same_arity :
  forall L X n k (f g : language_func L k)
         (v w : Fin.t k -> semiterm L X n),
    Semiterm_func f v = Semiterm_func g w -> f = g /\ v = w.
Proof.
  intros L X n k f g v w Heq.
  pose proof (f_equal semiterm_outer_function_payload Heq) as Hpayload.
  simpl in Hpayload.
  assert (Hsigma :
    existT (fun j =>
      (language_func L j * (Fin.t j -> semiterm L X n))%type)
      k (f, v) =
    existT (fun j =>
      (language_func L j * (Fin.t j -> semiterm L X n))%type)
      k (g, w)).
  { exact (option_some_injective Hpayload). }
  apply (@inj_pair2_eq_dec nat Nat.eq_dec
    (fun j => (language_func L j *
      (Fin.t j -> semiterm L X n))%type)
    k (f, v) (g, w)) in Hsigma.
  now injection Hsigma.
Qed.

Definition semiterm_eq_dec {L X n}
    (func_eq_dec : forall k (f g : language_func L k), {f = g} + {f <> g})
    (free_eq_dec : forall x y : X, {x = y} + {x <> y})
    (t u : semiterm L X n) : {t = u} + {t <> u}.
Proof.
  revert u.
  refine (@semiterm_rect L X n
    (fun t => forall u, {t = u} + {t <> u}) _ _ _ t).
  - intros i u; destruct u as [j | y | l g w].
    + destruct (Fin.eq_dec i j) as [-> | Hneq].
      * left; reflexivity.
      * right; intro Heq; inversion Heq; contradiction.
    + right; discriminate.
    + right; discriminate.
  - intros x u; destruct u as [j | y | l g w].
    + right; discriminate.
    + destruct (free_eq_dec x y) as [-> | Hneq].
      * left; reflexivity.
      * right; intro Heq; inversion Heq; contradiction.
    + right; discriminate.
  - intros k f v IH u; destruct u as [j | y | l g w].
    + right; discriminate.
    + right; discriminate.
    + destruct (Nat.eq_dec k l) as [Harity | Harity].
      * subst l.
        destruct (func_eq_dec k f g) as [Hsymbol | Hsymbol].
        { subst g.
          destruct (@fin_function_pointwise_eq_dec k (semiterm L X n)
            v w (fun i => IH i (w i))) as [Hargs | Hargs].
          - subst w. left; reflexivity.
          - right; intro Heq. apply Hargs.
            exact (proj2 (semiterm_func_injective_same_arity Heq)). }
        { right; intro Heq. apply Hsymbol.
          exact (proj1 (semiterm_func_injective_same_arity Heq)). }
      * right; intro Heq. apply Harity.
        exact (semiterm_func_arity_injective Heq).
Defined.

(** * Finite maxima and complexity *)

Fixpoint fin_max (n : nat) : (Fin.t n -> nat) -> nat :=
  match n as m return (Fin.t m -> nat) -> nat with
  | 0 => fun _ => 0
  | S m => fun f => Nat.max (f Fin.F1) (@fin_max m (fun i => f (Fin.FS i)))
  end.

Lemma fin_le_max :
  forall n (f : Fin.t n -> nat) i, f i <= @fin_max n f.
Proof.
  induction n as [|n IH]; intros f i; [inversion i |].
  refine (@Fin.caseS' n i
    (fun j => f j <= @fin_max (S n) f) _ _).
  - simpl; apply Nat.le_max_l.
  - intro j; simpl. eapply Nat.le_trans.
    + apply (IH (fun u => f (Fin.FS u)) j).
    + apply Nat.le_max_r.
Qed.

Fixpoint semiterm_complexity {L X n} (t : semiterm L X n) : nat :=
  match t with
  | Semiterm_bvar _ => 0
  | Semiterm_fvar _ => 0
  | @Semiterm_func _ _ _ k _ v =>
      S (@fin_max k (fun i => semiterm_complexity (v i)))
  end.

Lemma semiterm_complexity_bvar :
  forall L X n (i : Fin.t n),
    semiterm_complexity (@Semiterm_bvar L X n i) = 0.
Proof. reflexivity. Qed.

Lemma semiterm_complexity_fvar :
  forall L X n (x : X),
    semiterm_complexity (@Semiterm_fvar L X n x) = 0.
Proof. reflexivity. Qed.

Lemma semiterm_complexity_func :
  forall L X n k (f : language_func L k)
         (v : Fin.t k -> semiterm L X n),
    semiterm_complexity (Semiterm_func f v) =
    S (@fin_max k (fun i => semiterm_complexity (v i))).
Proof. reflexivity. Qed.

Lemma semiterm_complexity_func_lt :
  forall L X n k (f : language_func L k)
         (v : Fin.t k -> semiterm L X n) i,
    semiterm_complexity (v i) <
    semiterm_complexity (Semiterm_func f v).
Proof.
  intros; rewrite semiterm_complexity_func.
  pose proof (fin_le_max (fun j => semiterm_complexity (v j)) i); lia.
Qed.

(** * Bound-variable occurrence and positivity *)

Fixpoint semiterm_bound_occurs {L X n}
    (i : Fin.t n) (t : semiterm L X n) : Prop :=
  match t with
  | Semiterm_bvar j => i = j
  | Semiterm_fvar _ => False
  | @Semiterm_func _ _ _ k _ v =>
      exists j : Fin.t k, semiterm_bound_occurs i (v j)
  end.

Definition semiterm_positive {L X n}
    (t : semiterm L X (S n)) : Prop :=
  forall i, semiterm_bound_occurs i t -> 0 < fin_value i.

Lemma semiterm_positive_bvar :
  forall L X n (i : Fin.t (S n)),
    semiterm_positive (@Semiterm_bvar L X (S n) i) <-> 0 < fin_value i.
Proof.
  intros; unfold semiterm_positive; simpl; split.
  - intro H; apply (H i); reflexivity.
  - intros H j ->; exact H.
Qed.

Lemma semiterm_positive_fvar :
  forall L X n (x : X),
    semiterm_positive (@Semiterm_fvar L X (S n) x).
Proof. intros L X n x i H; contradiction. Qed.

Lemma semiterm_positive_func :
  forall L X n k (f : language_func L k)
         (v : Fin.t k -> semiterm L X (S n)),
    semiterm_positive (Semiterm_func f v) <->
    forall j, semiterm_positive (v j).
Proof.
  intros; split.
  - intros H j i Hi. apply H. simpl. now exists j.
  - intros H i [j Hi]. now apply (H j i).
Qed.

Lemma fin_one_is_zero : forall i : Fin.t 1, fin_value i = 0.
Proof.
  intro i. refine (@Fin.caseS' 0 i (fun j => fin_value j = 0) _ _).
  - reflexivity.
  - intro j; inversion j.
Qed.

Theorem semiterm_no_bound_occurs_of_positive_one :
  forall L X (t : semiterm L X 1),
    semiterm_positive t -> forall i, ~ semiterm_bound_occurs i t.
Proof.
  intros L X t Hpositive i Hi.
  specialize (Hpositive i Hi). rewrite fin_one_is_zero in Hpositive. lia.
Qed.

(** * Free-variable occurrence, generalized beyond decidable equality *)

Fixpoint semiterm_free_occurs {L X n}
    (x : X) (t : semiterm L X n) : Prop :=
  match t with
  | Semiterm_bvar _ => False
  | Semiterm_fvar y => x = y
  | @Semiterm_func _ _ _ k _ v =>
      exists j : Fin.t k, semiterm_free_occurs x (v j)
  end.

Lemma semiterm_free_occurs_bvar :
  forall L X n x (i : Fin.t n),
    ~ semiterm_free_occurs x (@Semiterm_bvar L X n i).
Proof. simpl; tauto. Qed.

Lemma semiterm_free_occurs_fvar :
  forall L X n (x y : X),
    semiterm_free_occurs x (@Semiterm_fvar L X n y) <-> x = y.
Proof. reflexivity. Qed.

Lemma semiterm_free_occurs_func :
  forall L X n k x (f : language_func L k)
         (v : Fin.t k -> semiterm L X n),
    semiterm_free_occurs x (Semiterm_func f v) <->
    exists j, semiterm_free_occurs x (v j).
Proof. reflexivity. Qed.

(** * Functorial action of language homomorphisms *)

Fixpoint semiterm_language_map {L M X n}
    (h : language_hom L M) (t : semiterm L X n) : semiterm M X n :=
  match t with
  | Semiterm_bvar i => Semiterm_bvar i
  | Semiterm_fvar x => Semiterm_fvar x
  | @Semiterm_func _ _ _ k f v =>
      Semiterm_func (hom_func h f) (fun i => semiterm_language_map h (v i))
  end.

Lemma semiterm_language_map_bvar :
  forall L M X n (h : language_hom L M) (i : Fin.t n),
    semiterm_language_map h (@Semiterm_bvar L X n i) = Semiterm_bvar i.
Proof. reflexivity. Qed.

Lemma semiterm_language_map_fvar :
  forall L M X n (h : language_hom L M) (x : X),
    semiterm_language_map h (@Semiterm_fvar L X n x) = Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma semiterm_language_map_func :
  forall L M X n k (h : language_hom L M) (f : language_func L k)
         (v : Fin.t k -> semiterm L X n),
    semiterm_language_map h (Semiterm_func f v) =
    Semiterm_func (hom_func h f) (fun i => semiterm_language_map h (v i)).
Proof. reflexivity. Qed.

Lemma semiterm_language_map_bound_occurs :
  forall L M X n (h : language_hom L M) (t : semiterm L X n) i,
    semiterm_bound_occurs i (semiterm_language_map h t) <->
    semiterm_bound_occurs i t.
Proof.
  intros L M X n h t; induction t as [j | x | k f v IH]; intro i; simpl.
  - reflexivity.
  - reflexivity.
  - split; intros [j Hj]; exists j; [apply (proj1 (IH j i)) | apply (proj2 (IH j i))]; exact Hj.
Qed.

Lemma semiterm_language_map_positive :
  forall L M X n (h : language_hom L M) (t : semiterm L X (S n)),
    semiterm_positive (semiterm_language_map h t) <-> semiterm_positive t.
Proof.
  intros; unfold semiterm_positive.
  setoid_rewrite semiterm_language_map_bound_occurs. reflexivity.
Qed.

Lemma semiterm_language_map_free_occurs :
  forall L M X n (h : language_hom L M) (t : semiterm L X n) x,
    semiterm_free_occurs x (semiterm_language_map h t) <->
    semiterm_free_occurs x t.
Proof.
  intros L M X n h t; induction t as [j | y | k f v IH]; intro x; simpl.
  - reflexivity.
  - reflexivity.
  - split; intros [j Hj]; exists j; [apply (proj1 (IH j x)) | apply (proj2 (IH j x))]; exact Hj.
Qed.

Lemma semiterm_language_map_id :
  forall L X n (t : semiterm L X n),
    semiterm_language_map (language_hom_id L) t = t.
Proof.
  intros L X n t; induction t as [i | x | k f v IH]; simpl; auto.
  f_equal. apply functional_extensionality; exact IH.
Qed.

Lemma semiterm_language_map_comp :
  forall L M N X n (g : language_hom M N) (f : language_hom L M)
         (t : semiterm L X n),
    semiterm_language_map g (semiterm_language_map f t) =
    semiterm_language_map (language_hom_comp g f) t.
Proof.
  intros L M N X n g f t; induction t as [i | x | k s v IH]; simpl; auto.
  f_equal. apply functional_extensionality; exact IH.
Qed.

(** * Duplicate-tolerant free-variable lists and enumeration *)

Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
  match n with
  | 0 => []
  | S k => Fin.F1 :: map Fin.FS (fin_enum k)
  end.

Lemma fin_enum_complete : forall n (i : Fin.t n), In i (fin_enum n).
Proof.
  induction n as [|n IH]; intro i; [inversion i |].
  refine (@Fin.caseS' n i (fun j => In j (fin_enum (S n))) _ _).
  - simpl; auto.
  - intro j; simpl; right. apply in_map, IH.
Qed.

Fixpoint semiterm_free_variable_list {L X n} (t : semiterm L X n) : list X :=
  match t with
  | Semiterm_bvar _ => []
  | Semiterm_fvar x => [x]
  | @Semiterm_func _ _ _ k _ v =>
      flat_map (fun i => semiterm_free_variable_list (v i)) (fin_enum k)
  end.

Lemma semiterm_free_variable_list_spec :
  forall L X n (t : semiterm L X n) x,
    In x (semiterm_free_variable_list t) <-> semiterm_free_occurs x t.
Proof.
  intros L X n t; induction t as [i | y | k f v IH]; intro x; simpl.
  - tauto.
  - split.
    + intros [Heq | Hfalse]; [now symmetry | contradiction].
    + intro Heq; left; now symmetry.
  - rewrite in_flat_map. split.
    + intros [j [_ Hj]]. exists j. now apply (proj1 (IH j x)).
    + intros [j Hj]. exists j; split; [apply fin_enum_complete |].
      now apply (proj2 (IH j x)).
Qed.

Fixpoint list_index {X} (eq_dec : forall x y : X, {x = y} + {x <> y})
    (x : X) (xs : list X) : nat :=
  match xs with
  | [] => 0
  | y :: ys => if eq_dec x y then 0 else S (list_index eq_dec x ys)
  end.

Lemma nth_list_index :
  forall X (eq_dec : forall x y : X, {x = y} + {x <> y})
         (d x : X) xs,
    In x xs -> nth (list_index eq_dec x xs) xs d = x.
Proof.
  intros X eq_dec d x xs; induction xs as [|y ys IH]; simpl; [tauto |].
  destruct (eq_dec x y) as [-> | Hneq]; simpl; [reflexivity |].
  intros [Heq | Hin].
  - exfalso. apply Hneq. now symmetry.
  - now apply IH.
Qed.

Definition semiterm_index_of_free_variable {L X n}
    (eq_dec : forall x y : X, {x = y} + {x <> y})
    (t : semiterm L X n) (x : X) : nat :=
  list_index eq_dec x (semiterm_free_variable_list t).

Definition semiterm_enumerate_free_variable {L X n}
    (default : X) (t : semiterm L X n) (i : nat) : X :=
  nth i (semiterm_free_variable_list t) default.

Theorem semiterm_enumerate_index_of_free_variable :
  forall L X n (eq_dec : forall x y : X, {x = y} + {x <> y})
         (default : X) (t : semiterm L X n) x,
    semiterm_free_occurs x t ->
    semiterm_enumerate_free_variable default t
      (semiterm_index_of_free_variable eq_dec t x) = x.
Proof.
  intros. apply nth_list_index.
  now apply (proj2 (semiterm_free_variable_list_spec t x)).
Qed.
