(**
  Rewriting of first-order semiterms and formulas.

  The source packages rewrites as proof-carrying functions and uses record
  equality for their algebra.  This port exposes pointwise [rew_equiv]
  instead: clients obtain every application theorem without proof
  irrelevance, while functional extensionality is needed only when comparing
  finite argument vectors.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List Vectors.Fin.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record rew (L : language) (X : Type) (n : nat)
    (Y : Type) (m : nat) : Type := {
  rew_apply : semiterm L X n -> semiterm L Y m;
  rew_apply_func : forall k (f : language_func L k)
      (v : Fin.t k -> semiterm L X n),
    rew_apply (Semiterm_func f v) =
    Semiterm_func f (fun i => rew_apply (v i))
}.

Arguments rew_apply {L X n Y m} _ _.
Arguments rew_apply_func {L X n Y m} _ {k} _ _.

Definition syntactic_rew L n m := rew L nat n nat m.

Definition rew_equiv {L X n Y m}
    (w v : rew L X n Y m) : Prop :=
  forall t, rew_apply w t = rew_apply v t.

Lemma rew_equiv_refl : forall L X n Y m (w : rew L X n Y m), rew_equiv w w.
Proof. intros; intro t; reflexivity. Qed.

Lemma rew_equiv_sym : forall L X n Y m (w v : rew L X n Y m),
  rew_equiv w v -> rew_equiv v w.
Proof. intros; intro t; symmetry; auto. Qed.

Lemma rew_equiv_trans : forall L X n Y m (u v w : rew L X n Y m),
  rew_equiv u v -> rew_equiv v w -> rew_equiv u w.
Proof. intros; intro t; etransitivity; eauto. Qed.

Definition rew_id {L X n} : rew L X n X n :=
  {| rew_apply := fun t => t;
     rew_apply_func := fun _ _ _ => eq_refl |}.

Definition rew_comp {L X n Y m Z l}
    (v : rew L Y m Z l) (w : rew L X n Y m) : rew L X n Z l :=
  {| rew_apply := fun t => rew_apply v (rew_apply w t);
     rew_apply_func := fun k f a =>
       eq_trans (f_equal (rew_apply v) (rew_apply_func w f a))
         (rew_apply_func v f (fun i => rew_apply w (a i))) |}.

Lemma rew_comp_apply : forall L X n Y m Z l
    (v : rew L Y m Z l) (w : rew L X n Y m) t,
  rew_apply (rew_comp v w) t = rew_apply v (rew_apply w t).
Proof. reflexivity. Qed.

Lemma rew_comp_id_left : forall L X n Y m (w : rew L X n Y m),
  rew_equiv (rew_comp rew_id w) w.
Proof. intros; intro t; reflexivity. Qed.

Lemma rew_comp_id_right : forall L X n Y m (w : rew L X n Y m),
  rew_equiv (rew_comp w rew_id) w.
Proof. intros; intro t; reflexivity. Qed.

Lemma rew_comp_assoc : forall L W a X n Y m Z l
    (u : rew L Y m Z l) (v : rew L X n Y m) (w : rew L W a X n),
  rew_equiv (rew_comp u (rew_comp v w)) (rew_comp (rew_comp u v) w).
Proof. intros; intro t; reflexivity. Qed.

Fixpoint rew_bind_aux {L X n Y m}
    (b : Fin.t n -> semiterm L Y m)
    (e : X -> semiterm L Y m)
    (t : semiterm L X n) : semiterm L Y m :=
  match t with
  | Semiterm_bvar i => b i
  | Semiterm_fvar x => e x
  | Semiterm_func f v =>
      Semiterm_func f (fun i => rew_bind_aux b e (v i))
  end.

Definition rew_bind {L X n Y m}
    (b : Fin.t n -> semiterm L Y m)
    (e : X -> semiterm L Y m) : rew L X n Y m :=
  {| rew_apply := rew_bind_aux b e;
     rew_apply_func := fun _ _ _ => eq_refl |}.

Lemma rew_bind_bvar : forall L X n Y m b e (i : Fin.t n),
  rew_apply (@rew_bind L X n Y m b e) (Semiterm_bvar i) = b i.
Proof. reflexivity. Qed.

Lemma rew_bind_fvar : forall L X n Y m b e (x : X),
  rew_apply (@rew_bind L X n Y m b e) (Semiterm_fvar x) = e x.
Proof. reflexivity. Qed.

Lemma rew_eta : forall L X n Y m (w : rew L X n Y m),
  rew_equiv w (rew_bind
    (fun i => rew_apply w (Semiterm_bvar i))
    (fun x => rew_apply w (Semiterm_fvar x))).
Proof.
  intros L X n Y m w t; induction t as [i | x | k f v IH]; simpl;
    try reflexivity.
  rewrite rew_apply_func. f_equal.
  apply functional_extensionality. exact IH.
Qed.

Definition rew_rewrite {L X Y n}
    (e : X -> semiterm L Y n) : rew L X n Y n :=
  rew_bind (fun i => Semiterm_bvar i) e.

Definition rew_rewrite_map {L X Y n} (e : X -> Y) : rew L X n Y n :=
  rew_rewrite (fun x => Semiterm_fvar (e x)).

Definition rew_map {L X n Y m}
    (b : Fin.t n -> Fin.t m) (e : X -> Y) : rew L X n Y m :=
  rew_bind (fun i => Semiterm_bvar (b i))
    (fun x => Semiterm_fvar (e x)).

Definition rew_subst {L X n m}
    (b : Fin.t n -> semiterm L X m) : rew L X n X m :=
  rew_bind b (fun x => Semiterm_fvar x).

Definition rew_emb {L O X n} (empty : O -> False) : rew L O n X n :=
  rew_map (fun i => i) (fun x => False_rect _ (empty x)).

Definition rew_empty {L O X n} (empty : O -> False) : rew L O 0 X n :=
  rew_map (fun i => Fin.case0 (fun _ => Fin.t n) i)
    (fun x => False_rect _ (empty x)).

Lemma rew_rewrite_bvar : forall L X Y n e (i : Fin.t n),
  rew_apply (@rew_rewrite L X Y n e) (Semiterm_bvar i) = Semiterm_bvar i.
Proof. reflexivity. Qed.

Lemma rew_rewrite_fvar : forall L X Y n e (x : X),
  rew_apply (@rew_rewrite L X Y n e) (Semiterm_fvar x) = e x.
Proof. reflexivity. Qed.

Lemma rew_map_bvar : forall L X n Y m b e (i : Fin.t n),
  rew_apply (@rew_map L X n Y m b e) (Semiterm_bvar i) = Semiterm_bvar (b i).
Proof. reflexivity. Qed.

Lemma rew_map_fvar : forall L X n Y m b e (x : X),
  rew_apply (@rew_map L X n Y m b e) (Semiterm_fvar x) = Semiterm_fvar (e x).
Proof. reflexivity. Qed.

Lemma rew_subst_bvar : forall L X n m b (i : Fin.t n),
  rew_apply (@rew_subst L X n m b) (Semiterm_bvar i) = b i.
Proof. reflexivity. Qed.

Lemma rew_subst_fvar : forall L X n m b (x : X),
  rew_apply (@rew_subst L X n m b) (Semiterm_fvar x) = Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma rew_bind_comp : forall L X n Y m Z l
    (b : Fin.t n -> semiterm L Y m) (e : X -> semiterm L Y m)
    (v : rew L Y m Z l),
  rew_equiv (rew_comp v (rew_bind b e))
    (rew_bind (fun i => rew_apply v (b i)) (fun x => rew_apply v (e x))).
Proof.
  intros L X n Y m Z l b e v t; induction t as [i | x | k f a IH]; simpl;
    try reflexivity.
  rewrite rew_apply_func. f_equal.
  apply functional_extensionality. exact IH.
Qed.

Lemma rew_subst_comp_subst : forall L X l k n
    (v : Fin.t l -> semiterm L X k)
    (w : Fin.t k -> semiterm L X n),
  rew_equiv (rew_comp (rew_subst w) (rew_subst v))
    (rew_subst (fun i => rew_apply (rew_subst w) (v i))).
Proof. intros; apply rew_bind_comp. Qed.

Lemma rew_rewrite_comp_rewrite : forall L X Y Z n
    (v : Y -> semiterm L Z n) (w : X -> semiterm L Y n),
  rew_equiv (rew_comp (rew_rewrite v) (rew_rewrite w))
    (rew_rewrite (fun x => rew_apply (rew_rewrite v) (w x))).
Proof. intros; apply rew_bind_comp. Qed.

(** * Lifting beneath binders *)

Definition rew_bshift {L X n} : rew L X n X (S n) :=
  rew_map Fin.FS (fun x => x).

Definition rew_q_bound {L X n Y m} (w : rew L X n Y m)
    (i : Fin.t (S n)) : semiterm L Y (S m) :=
  @Fin.caseS' n i (fun _ => semiterm L Y (S m))
    (Semiterm_bvar Fin.F1)
    (fun j => rew_apply rew_bshift (rew_apply w (Semiterm_bvar j))).

Definition rew_q {L X n Y m} (w : rew L X n Y m) :
    rew L X (S n) Y (S m) :=
  rew_bind (rew_q_bound w)
    (fun x => rew_apply rew_bshift (rew_apply w (Semiterm_fvar x))).

Lemma rew_bshift_bvar : forall L X n (i : Fin.t n),
  rew_apply (@rew_bshift L X n) (Semiterm_bvar i) = Semiterm_bvar (Fin.FS i).
Proof. reflexivity. Qed.

Lemma rew_bshift_fvar : forall L X n (x : X),
  rew_apply (@rew_bshift L X n) (Semiterm_fvar x) = Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma rew_q_bvar_zero : forall L X n Y m (w : rew L X n Y m),
  rew_apply (rew_q w) (Semiterm_bvar Fin.F1) = Semiterm_bvar Fin.F1.
Proof. reflexivity. Qed.

Lemma rew_q_bvar_succ : forall L X n Y m (w : rew L X n Y m)
    (i : Fin.t n),
  rew_apply (rew_q w) (Semiterm_bvar (Fin.FS i)) =
  rew_apply rew_bshift (rew_apply w (Semiterm_bvar i)).
Proof. reflexivity. Qed.

Lemma rew_q_fvar : forall L X n Y m (w : rew L X n Y m) (x : X),
  rew_apply (rew_q w) (Semiterm_fvar x) =
  rew_apply rew_bshift (rew_apply w (Semiterm_fvar x)).
Proof. reflexivity. Qed.

Lemma rew_q_id_apply : forall L X n (t : semiterm L X (S n)),
  rew_apply (rew_q (@rew_id L X n)) t = t.
Proof.
  intros L X n t; induction t as [i | x | k f v IH]; simpl.
  - refine (@Fin.caseS' n i
      (fun j => rew_apply (rew_q rew_id) (Semiterm_bvar j) = Semiterm_bvar j)
      eq_refl _).
    intro j; reflexivity.
  - reflexivity.
  - f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma rew_q_bshift_apply : forall L X n Y m (w : rew L X n Y m)
    (t : semiterm L X n),
  rew_apply (rew_q w) (rew_apply rew_bshift t) =
  rew_apply rew_bshift (rew_apply w t).
Proof.
  intros L X n Y m w t; induction t as [i | x | k f a IH]; simpl;
    try reflexivity.
  rewrite (rew_apply_func w f a). cbn. f_equal.
  apply functional_extensionality. exact IH.
Qed.

Lemma rew_q_comp_apply : forall L X n Y m Z l
    (v : rew L Y m Z l) (w : rew L X n Y m)
    (t : semiterm L X (S n)),
  rew_apply (rew_q (rew_comp v w)) t =
  rew_apply (rew_comp (rew_q v) (rew_q w)) t.
Proof.
  intros L X n Y m Z l v w t; induction t as [i | x | k f a IH].
  - refine (@Fin.caseS' n i
      (fun j =>
        rew_apply (rew_q (rew_comp v w)) (Semiterm_bvar j) =
        rew_apply (rew_comp (rew_q v) (rew_q w)) (Semiterm_bvar j))
      eq_refl _).
    intro j; cbn. symmetry; apply rew_q_bshift_apply.
  - cbn. symmetry; apply rew_q_bshift_apply.
  - cbn. f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma rew_q_respects_equiv : forall L X n Y m
    (w v : rew L X n Y m),
  rew_equiv w v -> rew_equiv (rew_q w) (rew_q v).
Proof.
  intros L X n Y m w v Heq t; induction t as [i | x | k f a IH].
  - refine (@Fin.caseS' n i
      (fun j =>
        rew_apply (rew_q w) (Semiterm_bvar j) =
        rew_apply (rew_q v) (Semiterm_bvar j))
      eq_refl _).
    intro j; cbn. now rewrite (Heq (Semiterm_bvar j)).
  - cbn. now rewrite (Heq (Semiterm_fvar x)).
  - cbn. f_equal. apply functional_extensionality. exact IH.
Qed.

Fixpoint rew_qpow {L X n Y m} (w : rew L X n Y m) (k : nat) :
    rew L X (k + n) Y (k + m) :=
  match k with
  | 0 => w
  | S j => rew_q (@rew_qpow L X n Y m w j)
  end.

(** * Formula action *)

Fixpoint semiformula_rewrite {L X n Y m}
    (w : rew L X n Y m) (p : semiformula L X n) : semiformula L Y m :=
  match p as p0 in semiformula _ _ j return
      rew L X j Y m -> semiformula L Y m with
  | Semiformula_verum _ => fun _ => Semiformula_verum m
  | Semiformula_falsum _ => fun _ => Semiformula_falsum m
  | Semiformula_rel r v => fun w0 =>
      Semiformula_rel r (fun i => rew_apply w0 (v i))
  | Semiformula_nrel r v => fun w0 =>
      Semiformula_nrel r (fun i => rew_apply w0 (v i))
  | Semiformula_and p q => fun w0 =>
      Semiformula_and (semiformula_rewrite w0 p) (semiformula_rewrite w0 q)
  | Semiformula_or p q => fun w0 =>
      Semiformula_or (semiformula_rewrite w0 p) (semiformula_rewrite w0 q)
  | Semiformula_all p => fun w0 =>
      Semiformula_all (semiformula_rewrite (rew_q w0) p)
  | Semiformula_exists p => fun w0 =>
      Semiformula_exists (semiformula_rewrite (rew_q w0) p)
  end w.

Lemma semiformula_rewrite_neg : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X n),
  semiformula_rewrite w (semiformula_neg p) =
  semiformula_neg (semiformula_rewrite w p).
Proof.
  intros L X n Y m w p; revert Y m w; induction p; intros; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Definition semiformula_rewrite_connective_hom {L X n Y m}
    (w : rew L X n Y m) :
    GenericLogicSymbol.generic_connective_hom
      (semiformula_connectives L X n) (semiformula_connectives L Y m).
Proof.
  refine {| GenericLogicSymbol.generic_connective_hom_apply :=
      semiformula_rewrite w |}; try reflexivity.
  - apply semiformula_rewrite_neg.
  - intros p q; unfold semiformula_imp; simpl.
    now rewrite semiformula_rewrite_neg.
Defined.

Lemma semiformula_rewrite_all : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X (S n)),
  semiformula_rewrite w (Semiformula_all p) =
  Semiformula_all (semiformula_rewrite (rew_q w) p).
Proof. reflexivity. Qed.

Lemma semiformula_rewrite_exists : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X (S n)),
  semiformula_rewrite w (Semiformula_exists p) =
  Semiformula_exists (semiformula_rewrite (rew_q w) p).
Proof. reflexivity. Qed.

Lemma semiformula_rewrite_ext : forall L X n Y m
    (w v : rew L X n Y m) (p : semiformula L X n),
  rew_equiv w v -> semiformula_rewrite w p = semiformula_rewrite v p.
Proof.
  intros L X n Y m w v p; revert Y m w v.
  induction p; intros Y m w v Heq; simpl; try reflexivity.
  - f_equal; apply functional_extensionality; intro i; apply Heq.
  - f_equal; apply functional_extensionality; intro i; apply Heq.
  - now rewrite (IHp1 Y m w v Heq), (IHp2 Y m w v Heq).
  - now rewrite (IHp1 Y m w v Heq), (IHp2 Y m w v Heq).
  - f_equal. apply IHp. now apply rew_q_respects_equiv.
  - f_equal. apply IHp. now apply rew_q_respects_equiv.
Qed.

Lemma semiformula_rewrite_id : forall L X n (p : semiformula L X n),
  semiformula_rewrite rew_id p = p.
Proof.
  intros L X n p.
  induction p as [n | n | n k r a | n k r a |
    n p IHp q IHq | n p IHp q IHq | n p IHp | n p IHp];
    simpl; try reflexivity.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - f_equal.
    transitivity (semiformula_rewrite (@rew_id L X (S n)) p).
    + apply semiformula_rewrite_ext. intro t.
      change (rew_apply (rew_q rew_id) t = t). apply rew_q_id_apply.
    + apply IHp.
  - f_equal.
    transitivity (semiformula_rewrite (@rew_id L X (S n)) p).
    + apply semiformula_rewrite_ext. intro t.
      change (rew_apply (rew_q rew_id) t = t). apply rew_q_id_apply.
    + apply IHp.
Qed.

Lemma semiformula_rewrite_comp : forall L X n Y m Z o
    (v : rew L Y m Z o) (w : rew L X n Y m)
    (p : semiformula L X n),
  semiformula_rewrite (rew_comp v w) p =
  semiformula_rewrite v (semiformula_rewrite w p).
Proof.
  intros L X n Y m Z o v w p; revert Y m Z o v w.
  induction p; intros Y m Z o v w; simpl; try reflexivity.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - f_equal.
    transitivity
      (semiformula_rewrite (rew_comp (rew_q v) (rew_q w)) p).
    + apply semiformula_rewrite_ext. intro t. apply rew_q_comp_apply.
    + apply IHp.
  - f_equal.
    transitivity
      (semiformula_rewrite (rew_comp (rew_q v) (rew_q w)) p).
    + apply semiformula_rewrite_ext. intro t. apply rew_q_comp_apply.
    + apply IHp.
Qed.
