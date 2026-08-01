(**
  Tarski semantics for the generic first-order syntax.

  This ports the central mathematical layer of
  [Foundation/FirstOrder/Basic/Semantics/Semantics.lean].  Structures are
  explicit arguments rather than typeclass instances, which lets a single
  development compare several interpretations on the same carrier.  The
  rewrite laws are proved once for an arbitrary [rew] and then specialized to
  substitution, renaming, weakening, and closed-template instantiation.
*)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.
From Stdlib Require Import Logic.Classical_Prop.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Structures and change of language *)

Record first_order_structure (L : language) (M : Type) : Type := {
  structure_func : forall {k},
    language_func L k -> (Fin.t k -> M) -> M;
  structure_rel : forall {k},
    language_rel L k -> (Fin.t k -> M) -> Prop
}.

Arguments structure_func {L M} _ {k} _ _.
Arguments structure_rel {L M} _ {k} _ _.

Definition unit_first_order_structure (L : language) :
    first_order_structure L unit :=
  {| structure_func := fun _ _ _ => tt;
     structure_rel := fun _ _ _ => True |}.

Definition first_order_structure_language_map {L K M}
    (h : language_hom L K) (S : first_order_structure K M) :
    first_order_structure L M :=
  {| structure_func := fun _ f v => structure_func S (hom_func h f) v;
     structure_rel := fun _ r v => structure_rel S (hom_rel h r) v |}.

(** A lightweight carrier equivalence.  Keeping it local to semantics avoids
    importing either proof-calculus equivalences or frame-specific ones. *)
Record carrier_equiv (M N : Type) : Type := {
  carrier_equiv_to : M -> N;
  carrier_equiv_from : N -> M;
  carrier_equiv_to_from : forall y,
    carrier_equiv_to (carrier_equiv_from y) = y;
  carrier_equiv_from_to : forall x,
    carrier_equiv_from (carrier_equiv_to x) = x
}.

Arguments carrier_equiv_to {M N} _ _.
Arguments carrier_equiv_from {M N} _ _.
Arguments carrier_equiv_to_from {M N} _ _.
Arguments carrier_equiv_from_to {M N} _ _.

Definition first_order_structure_transport {L M N}
    (Str : first_order_structure L M) (e : carrier_equiv M N) :
    first_order_structure L N :=
  {| structure_func := fun _ F v =>
       carrier_equiv_to e
         (structure_func Str F (fun i => carrier_equiv_from e (v i)));
     structure_rel := fun _ R v =>
       structure_rel Str R (fun i => carrier_equiv_from e (v i)) |}.

Lemma first_order_structure_language_map_func :
  forall L K M (h : language_hom L K) (S : first_order_structure K M)
         k (f : language_func L k) v,
    structure_func (first_order_structure_language_map h S) f v =
    structure_func S (hom_func h f) v.
Proof. reflexivity. Qed.

Lemma first_order_structure_language_map_rel :
  forall L K M (h : language_hom L K) (S : first_order_structure K M)
         k (r : language_rel L k) v,
    structure_rel (first_order_structure_language_map h S) r v <->
    structure_rel S (hom_rel h r) v.
Proof. reflexivity. Qed.

(** Add one value at the head of a finite environment. *)
Definition fin_env_cons {M n} (x : M) (b : Fin.t n -> M)
    (i : Fin.t (S n)) : M :=
  @Fin.caseS' n i (fun _ => M) x b.

Lemma fin_env_cons_zero : forall M n (x : M) (b : Fin.t n -> M),
  fin_env_cons x b Fin.F1 = x.
Proof. reflexivity. Qed.

Lemma fin_env_cons_succ : forall M n (x : M) (b : Fin.t n -> M)
    (i : Fin.t n),
  fin_env_cons x b (Fin.FS i) = b i.
Proof. reflexivity. Qed.

Lemma carrier_equiv_from_fin_env_cons :
  forall M N n (e : carrier_equiv M N) (x : N) (b : Fin.t n -> N),
    (fun i => carrier_equiv_from e (fin_env_cons x b i)) =
    fin_env_cons (carrier_equiv_from e x)
      (fun i => carrier_equiv_from e (b i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    carrier_equiv_from e (fin_env_cons x b j) =
    fin_env_cons (carrier_equiv_from e x)
      (fun u => carrier_equiv_from e (b u)) j) eq_refl _).
  intro j. reflexivity.
Qed.

(** * Valuation of terms *)

Fixpoint semiterm_val {L M X n} (S : first_order_structure L M)
    (b : Fin.t n -> M) (f : X -> M) (t : semiterm L X n) : M :=
  match t with
  | Semiterm_bvar i => b i
  | Semiterm_fvar x => f x
  | Semiterm_func F v =>
      structure_func S F (fun i => semiterm_val S b f (v i))
  end.

Definition closed_semiterm_val {L M n} (S : first_order_structure L M)
    (b : Fin.t n -> M) (t : closed_semiterm L n) : M :=
  semiterm_val S b (fun x : Empty_set => match x with end) t.

Lemma semiterm_val_bvar : forall L M X n (S : first_order_structure L M)
    (b : Fin.t n -> M) (f : X -> M) i,
  semiterm_val S b f (Semiterm_bvar i) = b i.
Proof. reflexivity. Qed.

Lemma semiterm_val_fvar : forall L M X n (S : first_order_structure L M)
    (b : Fin.t n -> M) (f : X -> M) x,
  semiterm_val S b f (Semiterm_fvar x) = f x.
Proof. reflexivity. Qed.

Lemma semiterm_val_func : forall L M X n (S : first_order_structure L M)
    (b : Fin.t n -> M) (f : X -> M) k (F : language_func L k) v,
  semiterm_val S b f (Semiterm_func F v) =
  structure_func S F (fun i => semiterm_val S b f (v i)).
Proof. reflexivity. Qed.

(** The fundamental substitution lemma, stated for every structural rewrite. *)
Lemma semiterm_val_rewrite :
  forall L M X n Y m (S : first_order_structure L M)
         (b : Fin.t m -> M) (f : Y -> M)
         (w : rew L X n Y m) (t : semiterm L X n),
    semiterm_val S b f (rew_apply w t) =
    semiterm_val S
      (fun i => semiterm_val S b f
        (rew_apply w (@Semiterm_bvar L X n i)))
      (fun x => semiterm_val S b f
        (rew_apply w (@Semiterm_fvar L X n x))) t.
Proof.
  intros L M X n Y m S b f w t.
  induction t as [i | x | k F v IH]; simpl; try reflexivity.
  rewrite rew_apply_func. simpl. f_equal.
  apply functional_extensionality. exact IH.
Qed.

Lemma semiterm_val_rewrite_free :
  forall L M X Y n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : Y -> M)
         (e : X -> semiterm L Y n) (t : semiterm L X n),
    semiterm_val S b f (rew_apply (rew_rewrite e) t) =
    semiterm_val S b (fun x => semiterm_val S b f (e x)) t.
Proof.
  intros. rewrite semiterm_val_rewrite.
  reflexivity.
Qed.

Lemma semiterm_val_rewrite_map :
  forall L M X Y n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : Y -> M) (e : X -> Y)
         (t : semiterm L X n),
    semiterm_val S b f (rew_apply (rew_rewrite_map e) t) =
    semiterm_val S b (fun x => f (e x)) t.
Proof.
  intros. rewrite semiterm_val_rewrite. reflexivity.
Qed.

Lemma semiterm_val_substitute :
  forall L M X n m (S : first_order_structure L M)
         (b : Fin.t m -> M) (f : X -> M)
         (e : Fin.t n -> semiterm L X m) (t : semiterm L X n),
    semiterm_val S b f (rew_apply (rew_subst e) t) =
    semiterm_val S (fun i => semiterm_val S b f (e i)) f t.
Proof.
  intros. rewrite semiterm_val_rewrite. reflexivity.
Qed.

Lemma semiterm_val_map :
  forall L M X Y n m (S : first_order_structure L M)
         (b : Fin.t m -> M) (f : Y -> M)
         (e : Fin.t n -> Fin.t m) (g : X -> Y) (t : semiterm L X n),
    semiterm_val S b f (rew_apply (rew_map e g) t) =
    semiterm_val S (fun i => b (e i)) (fun x => f (g x)) t.
Proof.
  intros. rewrite semiterm_val_rewrite. reflexivity.
Qed.

Lemma semiterm_val_bshift :
  forall L M X n (S : first_order_structure L M)
         (x : M) (b : Fin.t n -> M) (f : X -> M) (t : semiterm L X n),
    semiterm_val S (fin_env_cons x b) f (rew_apply rew_bshift t) =
    semiterm_val S b f t.
Proof.
  intros. rewrite semiterm_val_rewrite.
  reflexivity.
Qed.

Lemma semiterm_val_emb_substs :
  forall L M X k n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (v : Fin.t k -> semiterm L X n) (t : closed_semiterm L k),
    semiterm_val S b f (rew_apply (rew_emb_substs v) t) =
    closed_semiterm_val S (fun i => semiterm_val S b f (v i)) t.
Proof.
  intros. rewrite semiterm_val_rewrite. unfold closed_semiterm_val.
  assert (Hempty :
    (fun x : Empty_set =>
      semiterm_val S b f
        (rew_apply (rew_emb_substs v) (@Semiterm_fvar L Empty_set k x))) =
    (fun x : Empty_set => match x with end)).
  { apply functional_extensionality. intros []. }
  rewrite Hempty. reflexivity.
Qed.

Lemma semiterm_val_language_map :
  forall L K M X n (h : language_hom L K)
         (S : first_order_structure K M) (b : Fin.t n -> M) (f : X -> M)
         (t : semiterm L X n),
    semiterm_val S b f (semiterm_language_map h t) =
    semiterm_val (first_order_structure_language_map h S) b f t.
Proof.
  intros L K M X n h S b f t.
  induction t as [i | x | k F v IH]; simpl; try reflexivity.
  f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma semiterm_val_transport :
  forall L M N X n (Str : first_order_structure L M)
         (e : carrier_equiv M N) (b : Fin.t n -> N) (f : X -> N)
         (t : semiterm L X n),
    semiterm_val (first_order_structure_transport Str e) b f t =
    carrier_equiv_to e
      (semiterm_val Str
        (fun i => carrier_equiv_from e (b i))
        (fun x => carrier_equiv_from e (f x)) t).
Proof.
  intros L M N X n Str e b f t.
  induction t as [i | x | k F v IH]; simpl.
  - symmetry. apply carrier_equiv_to_from.
  - symmetry. apply carrier_equiv_to_from.
  - f_equal. apply f_equal. apply functional_extensionality. intro i.
    rewrite IH. apply carrier_equiv_from_to.
Qed.

(** Valuation depends only on free variables which actually occur.  Unlike
    the finite-set source statement, this requires no equality decision. *)
Lemma semiterm_val_free_ext :
  forall L M X n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f g : X -> M) (t : semiterm L X n),
    (forall x, semiterm_free_occurs x t -> f x = g x) ->
    semiterm_val S b f t = semiterm_val S b g t.
Proof.
  intros L M X n S b f g t; induction t as [i | x | k F v IH]; intro H;
    simpl; try reflexivity.
  - apply H. reflexivity.
  - f_equal. apply functional_extensionality. intro i.
    apply IH. intros x Hx. apply H. now exists i.
Qed.

(** * Evaluation of formulas *)

Fixpoint semiformula_eval {L M X n} (S : first_order_structure L M)
    (b : Fin.t n -> M) (f : X -> M) (p : semiformula L X n) : Prop :=
  match p as p0 in semiformula _ _ j return (Fin.t j -> M) -> Prop with
  | Semiformula_verum _ => fun _ => True
  | Semiformula_falsum _ => fun _ => False
  | Semiformula_rel r v => fun b0 =>
      structure_rel S r (fun i => semiterm_val S b0 f (v i))
  | Semiformula_nrel r v => fun b0 =>
      ~ structure_rel S r (fun i => semiterm_val S b0 f (v i))
  | Semiformula_and p q => fun b0 =>
      semiformula_eval S b0 f p /\ semiformula_eval S b0 f q
  | Semiformula_or p q => fun b0 =>
      semiformula_eval S b0 f p \/ semiformula_eval S b0 f q
  | Semiformula_all p => fun b0 => forall x : M,
      semiformula_eval S (fin_env_cons x b0) f p
  | Semiformula_exists p => fun b0 => exists x : M,
      semiformula_eval S (fin_env_cons x b0) f p
  end b.

Definition formula_eval {L M X} (S : first_order_structure L M)
    (f : X -> M) (p : formula L X) : Prop :=
  semiformula_eval S (fun i : Fin.t 0 => match i with end) f p.

Definition sentence_realize {L M} (S : first_order_structure L M)
    (p : sentence L) : Prop :=
  formula_eval S (fun x : Empty_set => match x with end) p.

Lemma semiformula_eval_neg :
  forall L M X n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M) (p : semiformula L X n),
    semiformula_eval S b f (semiformula_neg p) <->
    ~ semiformula_eval S b f p.
Proof.
  intros L M X n S b f p; revert b; induction p; intro b; simpl; try tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - setoid_rewrite IHp. split.
    + intros [x Hx] Hall. exact (Hx (Hall x)).
    + intro H. apply NNPP. intro Hnone. apply H. intro x.
      apply NNPP. intro Hx. apply Hnone. now exists x.
  - setoid_rewrite IHp. split.
    + intros Hall [x Hx]. exact (Hall x Hx).
    + intros H x Hx. apply H. now exists x.
Qed.

Lemma semiformula_eval_imp :
  forall L M X n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M) (p q : semiformula L X n),
    semiformula_eval S b f (semiformula_imp p q) <->
    (semiformula_eval S b f p -> semiformula_eval S b f q).
Proof.
  intros. unfold semiformula_imp. simpl. rewrite semiformula_eval_neg. tauto.
Qed.

Lemma semiformula_eval_bounded_all :
  forall L M X n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (p q : semiformula L X (Datatypes.S n)),
    semiformula_eval S b f (semiformula_bounded_all p q) <->
    forall x : M, semiformula_eval S (fin_env_cons x b) f p ->
                  semiformula_eval S (fin_env_cons x b) f q.
Proof.
  intros. unfold semiformula_bounded_all. simpl.
  setoid_rewrite semiformula_eval_neg. split; intros H x.
  - specialize (H x). tauto.
  - destruct (classic (semiformula_eval S (fin_env_cons x b) f p)) as [Hp | Hp].
    + right. now apply H.
    + now left.
Qed.

Lemma semiformula_eval_bounded_exists :
  forall L M X n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (p q : semiformula L X (Datatypes.S n)),
    semiformula_eval S b f (semiformula_bounded_exists p q) <->
    exists x : M, semiformula_eval S (fin_env_cons x b) f p /\
                  semiformula_eval S (fin_env_cons x b) f q.
Proof. reflexivity. Qed.

(** The lifted rewrite under a binder evaluates in the consed environment
    expected by the unrewritten body. *)
Lemma semiterm_val_rew_q_bvar :
  forall L M X n Y m (S : first_order_structure L M)
         (x : M) (b : Fin.t m -> M) (f : Y -> M)
         (w : rew L X n Y m) (i : Fin.t (Datatypes.S n)),
    semiterm_val S (fin_env_cons x b) f
      (rew_apply (rew_q w) (@Semiterm_bvar L X (Datatypes.S n) i)) =
    fin_env_cons x
      (fun j => semiterm_val S b f
        (rew_apply w (@Semiterm_bvar L X n j))) i.
Proof.
  intros L M X n Y m S x b f w i.
  refine (@Fin.caseS' n i (fun j =>
    semiterm_val S (fin_env_cons x b) f
      (rew_apply (rew_q w) (@Semiterm_bvar L X (Datatypes.S n) j)) =
    fin_env_cons x
      (fun u => semiterm_val S b f
        (rew_apply w (@Semiterm_bvar L X n u))) j) _ _).
  - rewrite rew_q_bvar_zero. reflexivity.
  - intro j. rewrite rew_q_bvar_succ. apply semiterm_val_bshift.
Qed.

Lemma semiterm_val_rew_q_fvar :
  forall L M X n Y m (S : first_order_structure L M)
         (x : M) (b : Fin.t m -> M) (f : Y -> M)
         (w : rew L X n Y m) (y : X),
    semiterm_val S (fin_env_cons x b) f
      (rew_apply (rew_q w) (@Semiterm_fvar L X (Datatypes.S n) y)) =
    semiterm_val S b f (rew_apply w (@Semiterm_fvar L X n y)).
Proof.
  intros. rewrite rew_q_fvar. apply semiterm_val_bshift.
Qed.

Lemma semiterm_val_rew_q_bvars :
  forall L M X n Y m (S : first_order_structure L M)
         (x : M) (b : Fin.t m -> M) (f : Y -> M)
         (w : rew L X n Y m),
    (fun i => semiterm_val S (fin_env_cons x b) f
      (rew_apply (rew_q w) (@Semiterm_bvar L X (Datatypes.S n) i))) =
    fin_env_cons x (fun i => semiterm_val S b f
      (rew_apply w (@Semiterm_bvar L X n i))).
Proof.
  intros. apply functional_extensionality. intro i.
  apply semiterm_val_rew_q_bvar.
Qed.

Lemma semiterm_val_rew_q_fvars :
  forall L M X n Y m (S : first_order_structure L M)
         (x : M) (b : Fin.t m -> M) (f : Y -> M)
         (w : rew L X n Y m),
    (fun y => semiterm_val S (fin_env_cons x b) f
      (rew_apply (rew_q w) (@Semiterm_fvar L X (Datatypes.S n) y))) =
    (fun y => semiterm_val S b f
      (rew_apply w (@Semiterm_fvar L X n y))).
Proof.
  intros. apply functional_extensionality. intro y.
  apply semiterm_val_rew_q_fvar.
Qed.

(** Formula-level fundamental substitution lemma. *)
Theorem semiformula_eval_rewrite :
  forall L M X n Y m (S : first_order_structure L M)
         (b : Fin.t m -> M) (f : Y -> M)
         (w : rew L X n Y m) (p : semiformula L X n),
    semiformula_eval S b f (semiformula_rewrite w p) <->
    semiformula_eval S
      (fun i => semiterm_val S b f
        (rew_apply w (@Semiterm_bvar L X n i)))
      (fun x => semiterm_val S b f
        (rew_apply w (@Semiterm_fvar L X n x))) p.
Proof.
  intros L M X n Y m S b f w p; revert Y m b f w.
  induction p; intros Y m b f w; simpl; try tauto.
  - assert (Hargs :
      (fun i => semiterm_val S b f (rew_apply w (s i))) =
      (fun i => semiterm_val S
        (fun j => semiterm_val S b f (rew_apply w (Semiterm_bvar j)))
        (fun x => semiterm_val S b f (rew_apply w (Semiterm_fvar x)))
        (s i))).
    { apply functional_extensionality. intro i. apply semiterm_val_rewrite. }
    now rewrite Hargs.
  - assert (Hargs :
      (fun i => semiterm_val S b f (rew_apply w (s i))) =
      (fun i => semiterm_val S
        (fun j => semiterm_val S b f (rew_apply w (Semiterm_bvar j)))
        (fun x => semiterm_val S b f (rew_apply w (Semiterm_fvar x)))
        (s i))).
    { apply functional_extensionality. intro i. apply semiterm_val_rewrite. }
    now rewrite Hargs.
  - rewrite IHp1, IHp2. tauto.
  - rewrite IHp1, IHp2. tauto.
  - split; intros H x; specialize (H x).
    + apply (proj1 (IHp Y (Datatypes.S m) (fin_env_cons x b) f (rew_q w))) in H.
      rewrite (semiterm_val_rew_q_bvars S x b f w),
        (semiterm_val_rew_q_fvars S x b f w) in H.
      exact H.
    + apply (proj2 (IHp Y (Datatypes.S m) (fin_env_cons x b) f (rew_q w))).
      rewrite (semiterm_val_rew_q_bvars S x b f w),
        (semiterm_val_rew_q_fvars S x b f w).
      exact H.
  - split; intros H.
    + destruct H as [x Hx]. exists x.
      apply (proj1 (IHp Y (Datatypes.S m) (fin_env_cons x b) f (rew_q w))) in Hx.
      rewrite (semiterm_val_rew_q_bvars S x b f w),
        (semiterm_val_rew_q_fvars S x b f w) in Hx.
      exact Hx.
    + destruct H as [x Hx]. exists x.
      apply (proj2 (IHp Y (Datatypes.S m) (fin_env_cons x b) f (rew_q w))).
      rewrite (semiterm_val_rew_q_bvars S x b f w),
        (semiterm_val_rew_q_fvars S x b f w).
      exact Hx.
Qed.

Lemma semiformula_eval_map :
  forall L M X n Y m (S : first_order_structure L M)
         (b : Fin.t m -> M) (f : Y -> M)
         (e : Fin.t n -> Fin.t m) (g : X -> Y) (p : semiformula L X n),
    semiformula_eval S b f (semiformula_rewrite (rew_map e g) p) <->
    semiformula_eval S (fun i => b (e i)) (fun x => f (g x)) p.
Proof. intros; rewrite semiformula_eval_rewrite; reflexivity. Qed.

Lemma semiformula_eval_substitute :
  forall L M X n m (S : first_order_structure L M)
         (b : Fin.t m -> M) (f : X -> M)
         (e : Fin.t n -> semiterm L X m) (p : semiformula L X n),
    semiformula_eval S b f (semiformula_rewrite (rew_subst e) p) <->
    semiformula_eval S (fun i => semiterm_val S b f (e i)) f p.
Proof. intros; rewrite semiformula_eval_rewrite; reflexivity. Qed.

Lemma semiformula_eval_bshift :
  forall L M X n (S : first_order_structure L M)
         (x : M) (b : Fin.t n -> M) (f : X -> M) (p : semiformula L X n),
    semiformula_eval S (fin_env_cons x b) f
      (semiformula_rewrite rew_bshift p) <->
    semiformula_eval S b f p.
Proof. intros; rewrite semiformula_eval_rewrite; reflexivity. Qed.

Lemma semiformula_eval_emb_substs :
  forall L M X k n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f : X -> M)
         (v : Fin.t k -> semiterm L X n) (p : semisentence L k),
    semiformula_eval S b f (semiformula_rewrite (rew_emb_substs v) p) <->
    semiformula_eval S
      (fun i => semiterm_val S b f (v i))
      (fun x : Empty_set => match x with end) p.
Proof.
  intros. rewrite semiformula_eval_rewrite.
  assert (Hempty :
    (fun x : Empty_set => semiterm_val S b f
      (rew_apply (rew_emb_substs v) (Semiterm_fvar x))) =
    (fun x : Empty_set => match x with end)).
  { apply functional_extensionality. intros []. }
  rewrite Hempty. reflexivity.
Qed.

Lemma semiformula_eval_free_ext :
  forall L M X n (S : first_order_structure L M)
         (b : Fin.t n -> M) (f g : X -> M) (p : semiformula L X n),
    (forall x, semiformula_free_occurs x p -> f x = g x) ->
    (semiformula_eval S b f p <-> semiformula_eval S b g p).
Proof.
  intros L M X n S b f g p; revert b; induction p; intros b H;
    simpl; try tauto.
  - assert (Hargs :
      (fun i => semiterm_val S b f (s i)) =
      (fun i => semiterm_val S b g (s i))).
    { apply functional_extensionality. intro i.
      apply semiterm_val_free_ext. intros x Hx. apply H. now exists i. }
    now rewrite Hargs.
  - assert (Hargs :
      (fun i => semiterm_val S b f (s i)) =
      (fun i => semiterm_val S b g (s i))).
    { apply functional_extensionality. intro i.
      apply semiterm_val_free_ext. intros x Hx. apply H. now exists i. }
    now rewrite Hargs.
  - assert (Hleft : forall x, semiformula_free_occurs x p1 -> f x = g x).
    { intros x Hx. apply H. now left. }
    assert (Hright : forall x, semiformula_free_occurs x p2 -> f x = g x).
    { intros x Hx. apply H. now right. }
    rewrite (IHp1 b Hleft), (IHp2 b Hright). tauto.
  - assert (Hleft : forall x, semiformula_free_occurs x p1 -> f x = g x).
    { intros x Hx. apply H. now left. }
    assert (Hright : forall x, semiformula_free_occurs x p2 -> f x = g x).
    { intros x Hx. apply H. now right. }
    rewrite (IHp1 b Hleft), (IHp2 b Hright). tauto.
  - split; intros Hall x.
    + apply (proj1 (IHp (fin_env_cons x b) H)). apply Hall.
    + apply (proj2 (IHp (fin_env_cons x b) H)). apply Hall.
  - split; intros Hex; destruct Hex as [x Hx]; exists x.
    + apply (proj1 (IHp (fin_env_cons x b) H)). exact Hx.
    + apply (proj2 (IHp (fin_env_cons x b) H)). exact Hx.
Qed.

Lemma semiformula_eval_language_map :
  forall L K M X n (h : language_hom L K)
         (S : first_order_structure K M) (b : Fin.t n -> M) (f : X -> M)
         (p : semiformula L X n),
    semiformula_eval S b f (semiformula_language_map h p) <->
    semiformula_eval (first_order_structure_language_map h S) b f p.
Proof.
  intros L K M X n h S b f p; revert b; induction p; intro b;
    simpl; try tauto.
  - assert (Hargs :
      (fun i => semiterm_val S b f (semiterm_language_map h (s i))) =
      (fun i => semiterm_val (first_order_structure_language_map h S)
        b f (s i))).
    { apply functional_extensionality. intro i.
      apply semiterm_val_language_map. }
    now rewrite Hargs.
  - assert (Hargs :
      (fun i => semiterm_val S b f (semiterm_language_map h (s i))) =
      (fun i => semiterm_val (first_order_structure_language_map h S)
        b f (s i))).
    { apply functional_extensionality. intro i.
      apply semiterm_val_language_map. }
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

Lemma semiformula_eval_transport :
  forall L M N X n (Str : first_order_structure L M)
         (e : carrier_equiv M N) (b : Fin.t n -> N) (f : X -> N)
         (p : semiformula L X n),
    semiformula_eval (first_order_structure_transport Str e) b f p <->
    semiformula_eval Str
      (fun i => carrier_equiv_from e (b i))
      (fun x => carrier_equiv_from e (f x)) p.
Proof.
  intros L M N X n Str e b f p; revert b; induction p; intro b;
    simpl; try tauto.
  - assert (Hargs :
      (fun i => carrier_equiv_from e
        (semiterm_val (first_order_structure_transport Str e) b f (s i))) =
      (fun i => semiterm_val Str
        (fun j => carrier_equiv_from e (b j))
        (fun x => carrier_equiv_from e (f x)) (s i))).
    { apply functional_extensionality. intro i.
      rewrite semiterm_val_transport. apply carrier_equiv_from_to. }
    now rewrite Hargs.
  - assert (Hargs :
      (fun i => carrier_equiv_from e
        (semiterm_val (first_order_structure_transport Str e) b f (s i))) =
      (fun i => semiterm_val Str
        (fun j => carrier_equiv_from e (b j))
        (fun x => carrier_equiv_from e (f x)) (s i))).
    { apply functional_extensionality. intro i.
      rewrite semiterm_val_transport. apply carrier_equiv_from_to. }
    now rewrite Hargs.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - rewrite (IHp1 b), (IHp2 b). tauto.
  - split; intros Hall x.
    + specialize (Hall (carrier_equiv_to e x)).
      apply (proj1 (IHp (fin_env_cons (carrier_equiv_to e x) b))) in Hall.
      rewrite carrier_equiv_from_fin_env_cons in Hall.
      rewrite carrier_equiv_from_to in Hall. exact Hall.
    + apply (proj2 (IHp (fin_env_cons x b))).
      rewrite carrier_equiv_from_fin_env_cons. apply Hall.
  - split; intros Hex.
    + destruct Hex as [y Hy].
      apply (proj1 (IHp (fin_env_cons y b))) in Hy.
      rewrite carrier_equiv_from_fin_env_cons in Hy.
      now exists (carrier_equiv_from e y).
    + destruct Hex as [x Hx]. exists (carrier_equiv_to e x).
      apply (proj2 (IHp (fin_env_cons (carrier_equiv_to e x) b))).
      rewrite carrier_equiv_from_fin_env_cons.
      rewrite carrier_equiv_from_to. exact Hx.
Qed.
