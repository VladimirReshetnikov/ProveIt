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

Lemma rew_equiv_of_variables : forall L X n Y m
    (w v : rew L X n Y m),
  (forall i, rew_apply w (Semiterm_bvar i) =
             rew_apply v (Semiterm_bvar i)) ->
  (forall x, rew_apply w (Semiterm_fvar x) =
             rew_apply v (Semiterm_fvar x)) ->
  rew_equiv w v.
Proof.
  intros L X n Y m w v Hb Hf t.
  induction t as [i | x | k f a IH]; [apply Hb | apply Hf |].
  rewrite (rew_apply_func w f a), (rew_apply_func v f a).
  f_equal. apply functional_extensionality. exact IH.
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

Definition rew_emb_substs {L X k n}
  (v : Fin.t k -> semiterm L X n) : rew L Empty_set k X n :=
  rew_bind v (fun x : Empty_set => match x with end).

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

Lemma rew_emb_substs_bvar : forall L X k n
    (v : Fin.t k -> semiterm L X n) (i : Fin.t k),
  rew_apply (rew_emb_substs v) (Semiterm_bvar i) = v i.
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

Lemma rew_subst_comp_emb_substs : forall L X l k n
    (v : Fin.t l -> semiterm L X k)
    (w : Fin.t k -> semiterm L X n),
  rew_equiv (rew_comp (rew_subst w) (rew_emb_substs v))
    (rew_emb_substs (fun i => rew_apply (rew_subst w) (v i))).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; reflexivity.
  - intros [].
Qed.

Lemma rew_emb_substs_variables : forall L X n,
  rew_equiv
    (@rew_emb_substs L X n n (fun i => Semiterm_bvar i))
    (rew_emb (fun x : Empty_set => match x with end)).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; reflexivity.
  - intros [].
Qed.

(** * Lifting beneath binders *)

Definition rew_bshift {L X n} : rew L X n X (S n) :=
  rew_map Fin.FS (fun x => x).

Definition rew_bshift_add {L X n} (m : nat) : rew L X n X (n + m) :=
  rew_map (Fin.L m) (fun x => x).

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

Lemma rew_bshift_add_bvar : forall L X n m (i : Fin.t n),
  rew_apply (@rew_bshift_add L X n m) (Semiterm_bvar i) =
  Semiterm_bvar (Fin.L m i).
Proof. reflexivity. Qed.

Lemma rew_bshift_add_fvar : forall L X n m (x : X),
  rew_apply (@rew_bshift_add L X n m) (Semiterm_fvar x) =
  Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma rew_bshift_comp_subst : forall L X n m
    (v : Fin.t n -> semiterm L X m),
  rew_equiv (rew_comp rew_bshift (rew_subst v))
    (rew_subst (fun i => rew_apply rew_bshift (v i))).
Proof.
  intros. apply rew_equiv_of_variables; intros; reflexivity.
Qed.

Lemma rew_rewrite_comp_emb : forall L O Y Z n
    (empty : O -> False) (f : Y -> semiterm L Z n),
  rew_equiv (rew_comp (rew_rewrite f) (@rew_emb L O Y n empty))
    (@rew_emb L O Z n empty).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; reflexivity.
  - intro x; exact (False_rect _ (empty x)).
Qed.

Lemma rew_comp_emb_empty : forall L O X Y (empty : O -> False)
    (w : rew L X 0 Y 0),
  rew_equiv (rew_comp w (@rew_emb L O X 0 empty))
    (@rew_emb L O Y 0 empty).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; exact (Fin.case0 (fun i => _ = _) i).
  - intro x; exact (False_rect _ (empty x)).
Qed.

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

(** * Standard syntactic rewrites *)

Definition rew_shift {L n} : syntactic_rew L n n :=
  rew_map (fun i => i) Nat.succ.

Definition rew_unshift {L n} : syntactic_rew L n n :=
  rew_map (fun i => i) Nat.pred.

Definition rew_free_bound {L n} (i : Fin.t (n + 1)) :
    syntactic_semiterm L n :=
  @Fin.case_L_R' n 1 (fun _ => syntactic_semiterm L n) i
    (fun j => Semiterm_bvar j)
    (fun _ => Semiterm_fvar 0).

Definition rew_free {L n} : syntactic_rew L (n + 1) n :=
  rew_bind rew_free_bound (fun x => Semiterm_fvar (S x)).

Definition rew_fix {L n} : syntactic_rew L n (n + 1) :=
  rew_bind (fun i => Semiterm_bvar (Fin.L 1 i))
    (fun x => match x with
      | 0 => Semiterm_bvar (Fin.R n Fin.F1)
      | S y => Semiterm_fvar y
      end).

Lemma fin_one_eq_f1 : forall i : Fin.t 1, i = Fin.F1.
Proof.
  intro i. refine (@Fin.caseS' 0 i (fun j => j = Fin.F1) eq_refl _).
  intro j. exact (Fin.case0 (fun u => Fin.FS u = Fin.F1) j).
Qed.

Lemma rew_shift_bvar : forall L n (i : Fin.t n),
  rew_apply (@rew_shift L n) (Semiterm_bvar i) = Semiterm_bvar i.
Proof. reflexivity. Qed.

Lemma rew_shift_fvar : forall L n x,
  rew_apply (@rew_shift L n) (Semiterm_fvar x) = Semiterm_fvar (S x).
Proof. reflexivity. Qed.

Lemma rew_shift_comp_subst : forall L n m
    (v : Fin.t n -> syntactic_semiterm L m),
  rew_equiv (rew_comp rew_shift (rew_subst v))
    (rew_comp (rew_subst (fun i => rew_apply rew_shift (v i))) rew_shift).
Proof.
  intros. apply rew_equiv_of_variables; intros; reflexivity.
Qed.

Lemma rew_shift_comp_emb : forall L O n (empty : O -> False),
  rew_equiv (rew_comp rew_shift (@rew_emb L O nat n empty))
    (@rew_emb L O nat n empty).
Proof. intros; apply rew_rewrite_comp_emb. Qed.

Lemma rew_unshift_shift : forall L n,
  rew_equiv (rew_comp (@rew_unshift L n) rew_shift) rew_id.
Proof.
  intros. apply rew_equiv_of_variables; intros; reflexivity.
Qed.

Lemma rew_shift_injective : forall L n,
  forall t u : syntactic_semiterm L n,
    rew_apply rew_shift t = rew_apply rew_shift u -> t = u.
Proof.
  intros L n t u H.
  apply (f_equal (rew_apply (@rew_unshift L n))) in H.
  change (rew_apply (rew_comp rew_unshift rew_shift) t =
          rew_apply (rew_comp rew_unshift rew_shift) u) in H.
  now rewrite (@rew_unshift_shift L n t), (@rew_unshift_shift L n u) in H.
Qed.

Lemma rew_free_bound_old : forall L n (i : Fin.t n),
  @rew_free_bound L n (Fin.L 1 i) = Semiterm_bvar i.
Proof.
  intros L n i. unfold rew_free_bound.
  rewrite Fin.case_L_R'_L. reflexivity.
Qed.

Lemma rew_free_bound_last : forall L n (i : Fin.t 1),
  @rew_free_bound L n (Fin.R n i) = Semiterm_fvar 0.
Proof.
  intros L n i. unfold rew_free_bound.
  rewrite Fin.case_L_R'_R. reflexivity.
Qed.

Lemma rew_free_bvar_old : forall L n (i : Fin.t n),
  rew_apply (@rew_free L n) (Semiterm_bvar (Fin.L 1 i)) = Semiterm_bvar i.
Proof. intros; apply rew_free_bound_old. Qed.

Lemma rew_free_bvar_last : forall L n,
  rew_apply (@rew_free L n) (Semiterm_bvar (Fin.R n Fin.F1)) =
  Semiterm_fvar 0.
Proof. intros; apply rew_free_bound_last. Qed.

Lemma rew_free_fvar : forall L n x,
  rew_apply (@rew_free L n) (Semiterm_fvar x) = Semiterm_fvar (S x).
Proof. reflexivity. Qed.

Lemma rew_fix_bvar : forall L n (i : Fin.t n),
  rew_apply (@rew_fix L n) (Semiterm_bvar i) =
  Semiterm_bvar (Fin.L 1 i).
Proof. reflexivity. Qed.

Lemma rew_fix_fvar_zero : forall L n,
  rew_apply (@rew_fix L n) (Semiterm_fvar 0) =
  Semiterm_bvar (Fin.R n Fin.F1).
Proof. reflexivity. Qed.

Lemma rew_fix_fvar_succ : forall L n x,
  rew_apply (@rew_fix L n) (Semiterm_fvar (S x)) = Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma rew_free_comp_fix : forall L n,
  rew_equiv (rew_comp (@rew_free L n) rew_fix) rew_id.
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; cbn. apply rew_free_bound_old.
  - intros [|x]; [apply rew_free_bound_last | reflexivity].
Qed.

Lemma rew_fix_free_bound : forall L n (i : Fin.t (n + 1)),
  rew_apply (@rew_fix L n) (@rew_free_bound L n i) = Semiterm_bvar i.
Proof.
  intros L n i.
  refine (@Fin.case_L_R' n 1
    (fun j => rew_apply rew_fix (rew_free_bound j) = Semiterm_bvar j)
    i _ _).
  - intro j. rewrite rew_free_bound_old. reflexivity.
  - intro j. rewrite rew_free_bound_last.
    assert (Hj : j = Fin.F1) by apply fin_one_eq_f1.
    now subst j.
Qed.

Lemma rew_fix_comp_free : forall L n,
  rew_equiv (rew_comp (@rew_fix L n) rew_free) rew_id.
Proof.
  intros. apply rew_equiv_of_variables.
  - apply rew_fix_free_bound.
  - intro x; reflexivity.
Qed.

Lemma rew_free_bshift_eq_shift : forall L,
  rew_equiv (rew_comp (@rew_free L 0) rew_bshift) rew_shift.
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i. exact (Fin.case0 (fun _ => _ = _) i).
  - intro x; reflexivity.
Qed.

Lemma fin_value_fs_positive : forall n (i : Fin.t n),
  0 < fin_value (Fin.FS i).
Proof.
  intros n i. apply Nat.neq_0_lt_0. intro Hz.
  assert (Heq : fin_value (Fin.FS i) =
      fin_value (@Fin.F1 n)).
  { rewrite Hz. reflexivity. }
  apply Fin.to_nat_inj in Heq. discriminate.
Qed.

Lemma rew_bshift_positive : forall L X n (t : semiterm L X n),
  semiterm_positive (rew_apply rew_bshift t).
Proof.
  intros L X n t; induction t as [i | x | k f a IH].
  - unfold semiterm_positive; simpl. intros j H; subst j.
    apply fin_value_fs_positive.
  - unfold semiterm_positive; simpl; tauto.
  - cbn. apply (proj2 (semiterm_positive_func f
      (fun i => rew_apply rew_bshift (a i)))); exact IH.
Qed.

Lemma rew_bshift_free_occurs : forall L X n x (t : semiterm L X n),
  semiterm_free_occurs x (rew_apply rew_bshift t) <->
  semiterm_free_occurs x t.
Proof.
  intros L X n x t; induction t as [i | y | k f a IH]; simpl;
    try reflexivity.
  split; intros [j Hj]; exists j;
    [apply (proj1 (IH j)) | apply (proj2 (IH j))]; exact Hj.
Qed.

Lemma rew_free_occurs_sources : forall L X n Y m
    (w : rew L X n Y m) (t : semiterm L X n) y,
  semiterm_free_occurs y (rew_apply w t) ->
  (exists i : Fin.t n,
      semiterm_free_occurs y (rew_apply w (Semiterm_bvar i))) \/
  (exists x : X,
      semiterm_free_occurs x t /\
      semiterm_free_occurs y (rew_apply w (Semiterm_fvar x))).
Proof.
  intros L X n Y m w t; induction t as [i | x | k f a IH]; intro y.
  - intro H; left; now exists i.
  - intro H; right; exists x; split; [reflexivity|exact H].
  - rewrite rew_apply_func. simpl. intros [j Hj].
    destruct (IH j y Hj) as [[i Hi] | [x [Hx Hy]]].
    + left; now exists i.
    + right; exists x; split; [now exists j|exact Hy].
Qed.

(** Language maps commute with syntactic rewrites. *)

Lemma semiterm_language_map_rew_bind : forall L M X n Y m
    (h : language_hom L M)
    (b : Fin.t n -> semiterm L Y m) (e : X -> semiterm L Y m)
    (t : semiterm L X n),
  semiterm_language_map h (rew_apply (rew_bind b e) t) =
  rew_apply (rew_bind
    (fun i => semiterm_language_map h (b i))
    (fun x => semiterm_language_map h (e x)))
    (semiterm_language_map h t).
Proof.
  intros L M X n Y m h b e t.
  induction t as [i | x | k f a IH]; simpl; try reflexivity.
  f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma semiterm_language_map_rew_map : forall L M X n Y m
    (h : language_hom L M) (b : Fin.t n -> Fin.t m) (e : X -> Y)
    (t : semiterm L X n),
  semiterm_language_map h (rew_apply (rew_map b e) t) =
  rew_apply (rew_map b e) (semiterm_language_map h t).
Proof.
  intros. unfold rew_map. apply semiterm_language_map_rew_bind.
Qed.

Lemma semiterm_language_map_rew_bshift : forall L M X n
    (h : language_hom L M) (t : semiterm L X n),
  semiterm_language_map h (rew_apply rew_bshift t) =
  rew_apply rew_bshift (semiterm_language_map h t).
Proof. intros; apply semiterm_language_map_rew_map. Qed.

Lemma semiterm_language_map_rew_shift : forall L M n
    (h : language_hom L M) (t : syntactic_semiterm L n),
  semiterm_language_map h (rew_apply rew_shift t) =
  rew_apply rew_shift (semiterm_language_map h t).
Proof. intros; apply semiterm_language_map_rew_map. Qed.

Lemma semiterm_language_map_rew_free_bound : forall L M n
    (h : language_hom L M) (i : Fin.t (n + 1)),
  semiterm_language_map h (@rew_free_bound L n i) =
  @rew_free_bound M n i.
Proof.
  intros L M n h i.
  refine (@Fin.case_L_R' n 1
    (fun j => semiterm_language_map h (rew_free_bound j) = rew_free_bound j)
    i _ _).
  - intro j. now rewrite !rew_free_bound_old.
  - intro j. now rewrite !rew_free_bound_last.
Qed.

Lemma semiterm_language_map_rew_free : forall L M n
    (h : language_hom L M) (t : syntactic_semiterm L (n + 1)),
  semiterm_language_map h (rew_apply rew_free t) =
  rew_apply rew_free (semiterm_language_map h t).
Proof.
  intros. unfold rew_free. rewrite semiterm_language_map_rew_bind.
  assert (Hb :
    (fun i => semiterm_language_map h (@rew_free_bound L n i)) =
    (@rew_free_bound M n)).
  { apply functional_extensionality; intro i.
    apply semiterm_language_map_rew_free_bound. }
  now rewrite Hb.
Qed.

Lemma semiterm_language_map_rew_fix : forall L M n
    (h : language_hom L M) (t : syntactic_semiterm L n),
  semiterm_language_map h (rew_apply rew_fix t) =
  rew_apply rew_fix (semiterm_language_map h t).
Proof.
  intros. unfold rew_fix. rewrite semiterm_language_map_rew_bind.
  assert (Hb :
    (fun i => semiterm_language_map h (Semiterm_bvar (Fin.L 1 i))) =
    (fun i => @Semiterm_bvar M nat (n + 1) (Fin.L 1 i))).
  { apply functional_extensionality; intro i; reflexivity. }
  assert (He :
    (fun x => semiterm_language_map h
      (match x with
       | 0 => Semiterm_bvar (Fin.R n Fin.F1)
       | S y => Semiterm_fvar y
       end)) =
    (fun x =>
      match x with
      | 0 => @Semiterm_bvar M nat (n + 1) (Fin.R n Fin.F1)
      | S y => @Semiterm_fvar M nat (n + 1) y
      end)).
  { apply functional_extensionality; intros [|x]; reflexivity. }
  now rewrite Hb, He.
Qed.

Lemma rew_q_shift : forall L n,
  rew_equiv (rew_q (@rew_shift L n)) (@rew_shift L (S n)).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i. refine (@Fin.caseS' n i
      (fun j =>
        rew_apply (rew_q rew_shift) (Semiterm_bvar j) =
        rew_apply rew_shift (Semiterm_bvar j))
      eq_refl _).
    intro j; reflexivity.
  - intro x; reflexivity.
Qed.

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

Lemma semiformula_rewrite_all_iter : forall L X n Y m
    (w : rew L X n Y m) k (p : semiformula L X (k + n)),
  semiformula_rewrite w
    (first_all_iter (semiformula_universal_quantifier L X) k n p) =
  first_all_iter (semiformula_universal_quantifier L Y) k m
    (semiformula_rewrite (rew_qpow w k) p).
Proof.
  intros L X n Y m w k; induction k as [|k IH]; intro p; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma semiformula_rewrite_exists_iter : forall L X n Y m
    (w : rew L X n Y m) k (p : semiformula L X (k + n)),
  semiformula_rewrite w
    (first_exists_iter (semiformula_existential_quantifier L X) k n p) =
  first_exists_iter (semiformula_existential_quantifier L Y) k m
    (semiformula_rewrite (rew_qpow w k) p).
Proof.
  intros L X n Y m w k; induction k as [|k IH]; intro p; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma semiformula_rewrite_bounded_all : forall L X n Y m
    (w : rew L X n Y m) (p q : semiformula L X (S n)),
  semiformula_rewrite w (semiformula_bounded_all p q) =
  semiformula_bounded_all (semiformula_rewrite (rew_q w) p)
    (semiformula_rewrite (rew_q w) q).
Proof.
  intros; unfold semiformula_bounded_all, semiformula_imp; simpl.
  now rewrite semiformula_rewrite_neg.
Qed.

Lemma semiformula_rewrite_bounded_exists : forall L X n Y m
    (w : rew L X n Y m) (p q : semiformula L X (S n)),
  semiformula_rewrite w (semiformula_bounded_exists p q) =
  semiformula_bounded_exists (semiformula_rewrite (rew_q w) p)
    (semiformula_rewrite (rew_q w) q).
Proof. reflexivity. Qed.

Lemma semiformula_rewrite_complexity : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X n),
  semiformula_complexity (semiformula_rewrite w p) =
  semiformula_complexity p.
Proof.
  intros L X n Y m w p; revert Y m w.
  induction p; intros; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Lemma semiformula_rewrite_quantifier_rank : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X n),
  semiformula_quantifier_rank (semiformula_rewrite w p) =
  semiformula_quantifier_rank p.
Proof.
  intros L X n Y m w p; revert Y m w.
  induction p; intros; simpl; try reflexivity;
    now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Lemma semiformula_rewrite_open : forall L X n Y m
    (w : rew L X n Y m) (p : semiformula L X n),
  semiformula_open (semiformula_rewrite w p) <-> semiformula_open p.
Proof.
  intros; unfold semiformula_open.
  now rewrite semiformula_rewrite_quantifier_rank.
Qed.

Lemma semiformula_rewrite_free_occurs_sources :
  forall L X n Y m (w : rew L X n Y m)
    (p : semiformula L X n) (y : Y),
  semiformula_free_occurs y (semiformula_rewrite w p) ->
  (exists i : Fin.t n,
      semiterm_free_occurs y (rew_apply w (Semiterm_bvar i))) \/
  (exists x : X,
      semiformula_free_occurs x p /\
      semiterm_free_occurs y (rew_apply w (Semiterm_fvar x))).
Proof.
  intros L X n Y m w p; revert Y m w.
  induction p; intros Y m w y H; simpl in H.
  - contradiction.
  - contradiction.
  - destruct H as [j Hj].
    destruct (@rew_free_occurs_sources L X n Y m w (s j) y Hj)
      as [[i Hi] | [x [Hx Hy]]].
    + left. now exists i.
    + right. exists x. split; [now exists j | exact Hy].
  - destruct H as [j Hj].
    destruct (@rew_free_occurs_sources L X n Y m w (s j) y Hj)
      as [[i Hi] | [x [Hx Hy]]].
    + left. now exists i.
    + right. exists x. split; [now exists j | exact Hy].
  - destruct H as [Hp | Hq].
    + destruct (IHp1 Y m w y Hp) as [Hb | [x [Hx Hy]]].
      * now left.
      * right. exists x. now split; [left |].
    + destruct (IHp2 Y m w y Hq) as [Hb | [x [Hx Hy]]].
      * now left.
      * right. exists x. now split; [right |].
  - destruct H as [Hp | Hq].
    + destruct (IHp1 Y m w y Hp) as [Hb | [x [Hx Hy]]].
      * now left.
      * right. exists x. now split; [left |].
    + destruct (IHp2 Y m w y Hq) as [Hb | [x [Hx Hy]]].
      * now left.
      * right. exists x. now split; [right |].
  - destruct (IHp Y (S m) (rew_q w) y H)
      as [[j Hj] | [x [Hx Hy]]].
    + revert Hj. refine (@Fin.caseS' n j
        (fun j =>
          semiterm_free_occurs y
            (rew_apply (rew_q w) (Semiterm_bvar j)) ->
          (exists i : Fin.t n,
              semiterm_free_occurs y
                (rew_apply w (Semiterm_bvar i))) \/
          (exists x : X,
              semiformula_free_occurs x (Semiformula_all p) /\
              semiterm_free_occurs y
                (rew_apply w (Semiterm_fvar x)))) _ _).
      * intro Hj. rewrite rew_q_bvar_zero in Hj. cbn in Hj. contradiction.
      * intros i Hj. rewrite rew_q_bvar_succ in Hj.
        apply (proj1 (@rew_bshift_free_occurs L Y m y
          (rew_apply w (Semiterm_bvar i)))) in Hj.
        left. now exists i.
    + rewrite rew_q_fvar in Hy.
      apply (proj1 (@rew_bshift_free_occurs L Y m y
        (rew_apply w (Semiterm_fvar x)))) in Hy.
      right. exists x. now split.
  - destruct (IHp Y (S m) (rew_q w) y H)
      as [[j Hj] | [x [Hx Hy]]].
    + revert Hj. refine (@Fin.caseS' n j
        (fun j =>
          semiterm_free_occurs y
            (rew_apply (rew_q w) (Semiterm_bvar j)) ->
          (exists i : Fin.t n,
              semiterm_free_occurs y
                (rew_apply w (Semiterm_bvar i))) \/
          (exists x : X,
              semiformula_free_occurs x (Semiformula_exists p) /\
              semiterm_free_occurs y
                (rew_apply w (Semiterm_fvar x)))) _ _).
      * intro Hj. rewrite rew_q_bvar_zero in Hj. cbn in Hj. contradiction.
      * intros i Hj. rewrite rew_q_bvar_succ in Hj.
        apply (proj1 (@rew_bshift_free_occurs L Y m y
          (rew_apply w (Semiterm_bvar i)))) in Hj.
        left. now exists i.
    + rewrite rew_q_fvar in Hy.
      apply (proj1 (@rew_bshift_free_occurs L Y m y
        (rew_apply w (Semiterm_fvar x)))) in Hy.
      right. exists x. now split.
Qed.

Definition semiformula_substitute {L X n m}
    (b : Fin.t n -> semiterm L X m) (p : semiformula L X n) :
    semiformula L X m :=
  semiformula_rewrite (rew_subst b) p.

Definition semiformula_shift {L n} (p : semiproposition L n) :
    semiproposition L n :=
  semiformula_rewrite rew_shift p.

Definition semiformula_unshift {L n} (p : semiproposition L n) :
    semiproposition L n :=
  semiformula_rewrite rew_unshift p.

Definition semiformula_free {L n} (p : semiproposition L (n + 1)) :
    semiproposition L n :=
  semiformula_rewrite rew_free p.

Definition semiformula_fix {L n} (p : semiproposition L n) :
    semiproposition L (n + 1) :=
  semiformula_rewrite rew_fix p.

Lemma rew_subst_variables_id : forall L X n,
  rew_equiv (@rew_subst L X n n (fun i => Semiterm_bvar i)) rew_id.
Proof.
  intros. apply rew_equiv_of_variables; intros; reflexivity.
Qed.

Lemma semiformula_substitute_id : forall L X n (p : semiformula L X n),
  semiformula_substitute (fun i => Semiterm_bvar i) p = p.
Proof.
  intros; unfold semiformula_substitute.
  transitivity (semiformula_rewrite rew_id p).
  - apply semiformula_rewrite_ext, rew_subst_variables_id.
  - apply semiformula_rewrite_id.
Qed.

Lemma semiformula_substitute_comp : forall L X l k n
    (v : Fin.t l -> semiterm L X k)
    (w : Fin.t k -> semiterm L X n) (p : semiformula L X l),
  semiformula_substitute w (semiformula_substitute v p) =
  semiformula_substitute
    (fun i => rew_apply (rew_subst w) (v i)) p.
Proof.
  intros; unfold semiformula_substitute.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_subst_comp_subst.
Qed.

Lemma semiformula_shift_injective : forall L n
    (p q : semiproposition L n),
  semiformula_shift p = semiformula_shift q -> p = q.
Proof.
  intros L n p q H.
  apply (f_equal semiformula_unshift) in H.
  unfold semiformula_unshift, semiformula_shift in H.
  rewrite <- !semiformula_rewrite_comp in H.
  assert (Hu : forall r : semiproposition L n,
      semiformula_rewrite (rew_comp rew_unshift rew_shift) r = r).
  { intro r. transitivity (semiformula_rewrite rew_id r).
    - apply semiformula_rewrite_ext, rew_unshift_shift.
    - apply semiformula_rewrite_id. }
  now rewrite !Hu in H.
Qed.

Lemma semiformula_free_fix : forall L n (p : semiproposition L n),
  semiformula_free (semiformula_fix p) = p.
Proof.
  intros; unfold semiformula_free, semiformula_fix.
  rewrite <- semiformula_rewrite_comp.
  transitivity (semiformula_rewrite rew_id p).
  - apply semiformula_rewrite_ext, rew_free_comp_fix.
  - apply semiformula_rewrite_id.
Qed.

Lemma semiformula_fix_free : forall L n
    (p : semiproposition L (n + 1)),
  semiformula_fix (semiformula_free p) = p.
Proof.
  intros; unfold semiformula_free, semiformula_fix.
  rewrite <- semiformula_rewrite_comp.
  transitivity (semiformula_rewrite rew_id p).
  - apply semiformula_rewrite_ext, rew_fix_comp_free.
  - apply semiformula_rewrite_id.
Qed.
