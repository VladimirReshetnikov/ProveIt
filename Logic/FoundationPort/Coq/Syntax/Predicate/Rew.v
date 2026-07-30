(**
  Rewriting of first-order semiterms and formulas.

  The source packages rewrites as proof-carrying functions and uses record
  equality for their algebra.  This port exposes pointwise [rew_equiv]
  instead: clients obtain every application theorem without proof
  irrelevance, while functional extensionality is needed only when comparing
  finite argument vectors.
*)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Lia Lists.List Vectors.Fin.
From Stdlib Require Import Logic.Eqdep_dec.
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

Definition rew_cast {L X n m} (h : n = m) : rew L X n X m :=
  rew_map (fun i => Fin.cast i h) (fun x => x).

Definition fin_cast_le {n m} (h : n <= m) (i : Fin.t n) : Fin.t m :=
  Fin.of_nat_lt
    (Nat.lt_le_trans (fin_value i) n m (proj2_sig (Fin.to_nat i)) h).

Definition rew_cast_le {L X n m} (h : n <= m) : rew L X n X m :=
  rew_map (fin_cast_le h) (fun x => x).

Lemma fin_cast_refl : forall n (i : Fin.t n),
  Fin.cast i eq_refl = i.
Proof.
  intros n i; induction i; simpl; [reflexivity | now rewrite IHi].
Qed.

Lemma fin_cast_L_zero : forall n (i : Fin.t n),
  Fin.cast (Fin.L 0 i) (Nat.add_0_r n) = i.
Proof.
  intros n i; induction i; simpl; [reflexivity |].
  f_equal.
  pose proof (@UIP_dec nat Nat.eq_dec (n + 0) n
    (f_equal Nat.pred (Nat.add_0_r (S n))) (Nat.add_0_r n)) as Hp.
  etransitivity.
  - exact (f_equal (fun q : n + 0 = n => Fin.cast (Fin.L 0 i) q) Hp).
  - exact IHi.
Qed.

Lemma fin_cast_le_refl : forall n (h : n <= n) (i : Fin.t n),
  fin_cast_le h i = i.
Proof.
  intros n h i. apply Fin.to_nat_inj.
  unfold fin_cast_le. rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma fin_value_ext : forall n (i j : Fin.t n),
  fin_value i = fin_value j -> i = j.
Proof. intros; apply Fin.to_nat_inj; exact H. Qed.

Lemma fin_value_cast : forall n m (i : Fin.t n) (h : n = m),
  fin_value (Fin.cast i h) = fin_value i.
Proof.
  intros n m i h; destruct h. now rewrite fin_cast_refl.
Qed.

Lemma fin_value_cast_le : forall n m (h : n <= m) (i : Fin.t n),
  fin_value (fin_cast_le h i) = fin_value i.
Proof.
  intros. unfold fin_value, fin_cast_le.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

Lemma fin_value_FS : forall n (i : Fin.t n),
  fin_value (Fin.FS i) = S (fin_value i).
Proof.
  intros. unfold fin_value. cbn [Fin.to_nat].
  destruct (Fin.to_nat i). reflexivity.
Qed.

Lemma fin_value_L : forall n m (i : Fin.t n),
  fin_value (Fin.L m i) = fin_value i.
Proof.
  intros n m i; induction i; [reflexivity |].
  cbn [Fin.L].
  transitivity (S (fin_value (Fin.L m i))).
  - apply fin_value_FS.
  - rewrite IHi. symmetry. apply fin_value_FS.
Qed.

Lemma fin_value_R_f1 : forall n,
  fin_value (Fin.R n (@Fin.F1 0)) = n.
Proof.
  induction n as [|n IH]; [reflexivity |].
  cbn [Fin.R].
  transitivity (S (fin_value (Fin.R n (@Fin.F1 0)))).
  - apply fin_value_FS.
  - now rewrite IH.
Qed.

Definition fin_add_right_of_lt (n x m : nat) (h : x < m) : Fin.t (n + m) :=
  Fin.of_nat_lt ((proj1 (Nat.add_lt_mono_l x m n)) h).

Lemma fin_value_add_right_of_lt : forall n x m (h : x < m),
  fin_value (@fin_add_right_of_lt n x m h) = n + x.
Proof.
  intros. unfold fin_value, fin_add_right_of_lt.
  rewrite Fin.to_nat_of_nat. reflexivity.
Qed.

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

Lemma rew_cast_bvar : forall L X n m (h : n = m) (i : Fin.t n),
  rew_apply (@rew_cast L X n m h) (Semiterm_bvar i) =
  Semiterm_bvar (Fin.cast i h).
Proof. reflexivity. Qed.

Lemma rew_cast_fvar : forall L X n m (h : n = m) (x : X),
  rew_apply (@rew_cast L X n m h) (Semiterm_fvar x) =
  Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma rew_cast_refl : forall L X n (h : n = n),
  rew_equiv (@rew_cast L X n n h) rew_id.
Proof.
  intros L X n h.
  pose proof (@UIP_dec nat Nat.eq_dec n n h eq_refl) as Hh.
  rewrite Hh.
  apply rew_equiv_of_variables.
  - intro i; simpl. now rewrite fin_cast_refl.
  - intro x; reflexivity.
Qed.

Lemma rew_cast_le_bvar : forall L X n m (h : n <= m) (i : Fin.t n),
  rew_apply (@rew_cast_le L X n m h) (Semiterm_bvar i) =
  Semiterm_bvar (fin_cast_le h i).
Proof. reflexivity. Qed.

Lemma rew_cast_le_fvar : forall L X n m (h : n <= m) (x : X),
  rew_apply (@rew_cast_le L X n m h) (Semiterm_fvar x) =
  Semiterm_fvar x.
Proof. reflexivity. Qed.

Lemma rew_cast_le_refl : forall L X n (h : n <= n),
  rew_equiv (@rew_cast_le L X n n h) rew_id.
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; simpl. now rewrite fin_cast_le_refl.
  - intro x; reflexivity.
Qed.

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

(** An arbitrary rewrite, not merely a bound-variable substitution, can be
    pushed through instantiation of a closed template.  This is the common
    algebraic core of term- and formula-operator composition. *)
Lemma rew_comp_emb_substs : forall L X Y l k n
    (v : Fin.t l -> semiterm L X k) (w : rew L X k Y n),
  rew_equiv (rew_comp w (rew_emb_substs v))
    (rew_emb_substs (fun i => rew_apply w (v i))).
Proof.
  intros L X Y l k n v w.
  apply rew_equiv_of_variables.
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

Lemma rew_emb_substs_variables_empty : forall L n,
  rew_equiv
    (@rew_emb_substs L Empty_set n n (fun i => Semiterm_bvar i))
    rew_id.
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

Lemma rew_bshift_add_zero_cast : forall L X n,
  rew_equiv
    (rew_comp (@rew_cast L X (n + 0) n (Nat.add_0_r n))
      (@rew_bshift_add L X n 0))
    rew_id.
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i; simpl. now rewrite fin_cast_L_zero.
  - intro x; reflexivity.
Qed.

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

Lemma rew_subst_bound_occurs : forall L X n m
    (v : Fin.t n -> semiterm L X m) (t : semiterm L X n) j,
  semiterm_bound_occurs j (rew_apply (rew_subst v) t) <->
  exists i : Fin.t n,
    semiterm_bound_occurs i t /\ semiterm_bound_occurs j (v i).
Proof.
  intros L X n m v t; induction t as [i | x | k f a IH]; intro j; simpl.
  - split.
    + intro H. exists i. now split.
    + intros [i' [-> H]]. exact H.
  - split; [contradiction | intros [i [H _]]; contradiction].
  - split.
    + intros [c Hc].
      apply (proj1 (IH c j)) in Hc.
      destruct Hc as [i [Hi Hj]].
      exists i. split; [now exists c | exact Hj].
    + intros [i [[c Hc] Hj]].
      exists c. apply (proj2 (IH c j)).
      exists i. now split.
Qed.

Lemma rew_subst_positive : forall L X n m
    (v : Fin.t n -> semiterm L X (S m)) (t : semiterm L X n),
  semiterm_positive (rew_apply (rew_subst v) t) <->
  forall i, semiterm_bound_occurs i t -> semiterm_positive (v i).
Proof.
  intros L X n m v t. unfold semiterm_positive.
  split.
  - intros H i Hi j Hj. apply (H j).
    apply (proj2 (rew_subst_bound_occurs v t j)).
    exists i. now split.
  - intros H j Hj.
    apply (proj1 (rew_subst_bound_occurs v t j)) in Hj.
    destruct Hj as [i [Hi Hj]]. exact (H i Hi j Hj).
Qed.

Lemma rew_emb_substs_bound_occurs : forall L X n m
    (v : Fin.t n -> semiterm L X m) (t : semiterm L Empty_set n) j,
  semiterm_bound_occurs j (rew_apply (rew_emb_substs v) t) <->
  exists i : Fin.t n,
    semiterm_bound_occurs i t /\ semiterm_bound_occurs j (v i).
Proof.
  intros L X n m v t; induction t as [i | x | k f a IH]; intro j; simpl.
  - split.
    + intro H. exists i. now split.
    + intros [i' [-> H]]. exact H.
  - destruct x.
  - split.
    + intros [c Hc].
      apply (proj1 (IH c j)) in Hc.
      destruct Hc as [i [Hi Hj]].
      exists i. split; [now exists c | exact Hj].
    + intros [i [[c Hc] Hj]].
      exists c. apply (proj2 (IH c j)).
      exists i. now split.
Qed.

Lemma rew_emb_substs_positive : forall L X n m
    (v : Fin.t n -> semiterm L X (S m)) (t : semiterm L Empty_set n),
  semiterm_positive (rew_apply (rew_emb_substs v) t) <->
  forall i, semiterm_bound_occurs i t -> semiterm_positive (v i).
Proof.
  intros L X n m v t. unfold semiterm_positive.
  split.
  - intros H i Hi j Hj. apply (H j).
    apply (proj2 (rew_emb_substs_bound_occurs v t j)).
    exists i. now split.
  - intros H j Hj.
    apply (proj1 (rew_emb_substs_bound_occurs v t j)) in Hj.
    destruct Hj as [i [Hi Hj]]. exact (H i Hi j Hj).
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

(** * Iterated conversion of leading free variables to bound variables *)

Lemma nat_fix_iter_step : forall n m,
  (n + m) + 1 = n + S m.
Proof. intros; lia. Qed.

Fixpoint rew_fix_iter {L} (n m : nat) : syntactic_rew L n (n + m) :=
  match m as m0 return syntactic_rew L n (n + m0) with
  | 0 => rew_cast (eq_sym (Nat.add_0_r n))
  | S k =>
      rew_comp (rew_cast (nat_fix_iter_step n k))
        (rew_comp (@rew_fix L (n + k)) (@rew_fix_iter L n k))
  end.

Lemma rew_fix_iter_zero : forall L n,
  rew_equiv
    (rew_comp (@rew_cast L nat (n + 0) n (Nat.add_0_r n))
      (@rew_fix_iter L n 0))
    rew_id.
Proof.
  intros. cbn [rew_fix_iter].
  apply rew_equiv_of_variables.
  - intro i; simpl.
    f_equal. apply fin_value_ext. rewrite !fin_value_cast. reflexivity.
  - intro x; reflexivity.
Qed.

Lemma rew_fix_iter_succ : forall L n m,
  rew_equiv (@rew_fix_iter L n (S m))
    (rew_comp (rew_cast (nat_fix_iter_step n m))
      (rew_comp (@rew_fix L (n + m)) (@rew_fix_iter L n m))).
Proof. intros; apply rew_equiv_refl. Qed.

Lemma rew_fix_iter_bvar : forall L n m (i : Fin.t n),
  rew_apply (@rew_fix_iter L n m) (Semiterm_bvar i) =
  Semiterm_bvar (fin_cast_le (Nat.le_add_r n m) i).
Proof.
  intros L n m; induction m as [|m IH]; intro i.
  - cbn [rew_fix_iter]. rewrite rew_cast_bvar. f_equal.
    apply fin_value_ext. rewrite fin_value_cast, fin_value_cast_le. reflexivity.
  - rewrite (@rew_fix_iter_succ L n m (Semiterm_bvar i)).
    rewrite !rew_comp_apply.
    rewrite IH, rew_fix_bvar, rew_cast_bvar. f_equal.
    apply fin_value_ext.
    rewrite fin_value_cast, fin_value_L, !fin_value_cast_le. reflexivity.
Qed.

Lemma rew_fix_iter_fvar_ge : forall L n m x,
  m <= x ->
  rew_apply (@rew_fix_iter L n m) (Semiterm_fvar x) =
  Semiterm_fvar (x - m).
Proof.
  intros L n m; induction m as [|m IH]; intros x Hmx.
  - cbn [rew_fix_iter]. rewrite rew_cast_fvar. now rewrite Nat.sub_0_r.
  - rewrite (@rew_fix_iter_succ L n m (Semiterm_fvar x)).
    rewrite !rew_comp_apply.
    rewrite IH by lia.
    assert (Hx : x - m = S (x - S m)) by lia.
    rewrite Hx, rew_fix_fvar_succ, rew_cast_fvar. reflexivity.
Qed.

Lemma rew_fix_iter_fvar_lt : forall L n m x (h : x < m),
  rew_apply (@rew_fix_iter L n m) (Semiterm_fvar x) =
  Semiterm_bvar (@fin_add_right_of_lt n x m h).
Proof.
  intros L n m; induction m as [|m IH]; intros x h; [lia |].
  rewrite (@rew_fix_iter_succ L n m (Semiterm_fvar x)).
  rewrite !rew_comp_apply.
  destruct (lt_dec x m) as [Hxm | Hxm].
  - rewrite (IH x Hxm), rew_fix_bvar, rew_cast_bvar. f_equal.
    apply fin_value_ext.
    rewrite fin_value_cast, fin_value_L, !fin_value_add_right_of_lt.
    reflexivity.
  - assert (Hxeq : x = m) by lia. subst x.
    rewrite rew_fix_iter_fvar_ge by lia.
    rewrite Nat.sub_diag, rew_fix_fvar_zero, rew_cast_bvar. f_equal.
    apply fin_value_ext.
    rewrite fin_value_cast, fin_value_R_f1, fin_value_add_right_of_lt.
    reflexivity.
Qed.

(** * Constructive conversion of free-variable-free terms *)

Fixpoint semiterm_to_closed {L X n} (t : semiterm L X n) :
    (forall x, ~ semiterm_free_occurs x t) -> closed_semiterm L n :=
  match t as t0 return
      (forall x, ~ semiterm_free_occurs x t0) -> closed_semiterm L n with
  | Semiterm_bvar i => fun _ => Semiterm_bvar i
  | Semiterm_fvar y => fun H => False_rect _ (H y eq_refl)
  | @Semiterm_func _ _ _ k f a => fun H =>
      Semiterm_func f (fun i =>
        @semiterm_to_closed L X n (a i)
          (fun x Hx => H x (ex_intro (fun j => semiterm_free_occurs x (a j)) i Hx)))
  end.

Lemma semiterm_to_closed_bvar : forall L X n (i : Fin.t n) H,
  @semiterm_to_closed L X n (Semiterm_bvar i) H = Semiterm_bvar i.
Proof. reflexivity. Qed.

Lemma semiterm_to_closed_func : forall L X n k
    (f : language_func L k) (a : Fin.t k -> semiterm L X n) H,
  @semiterm_to_closed L X n (Semiterm_func f a) H =
  Semiterm_func f (fun i =>
    @semiterm_to_closed L X n (a i)
      (fun x Hx => H x (ex_intro (fun j => semiterm_free_occurs x (a j)) i Hx))).
Proof. reflexivity. Qed.

Lemma semiterm_emb_to_closed : forall L X n
    (t : semiterm L X n) (H : forall x, ~ semiterm_free_occurs x t),
  rew_apply (rew_emb (fun x : Empty_set => match x with end))
    (@semiterm_to_closed L X n t H) = t.
Proof.
  intros L X n t; induction t as [i | y | k f a IH]; intro H; simpl.
  - reflexivity.
  - exact (False_rect _ (H y eq_refl)).
  - f_equal. apply functional_extensionality. intro i. apply IH.
Qed.

Lemma semiterm_emb_no_free_occurs : forall L O X n
    (empty : O -> False) (t : semiterm L O n) x,
  ~ semiterm_free_occurs x (rew_apply (@rew_emb L O X n empty) t).
Proof.
  intros L O X n empty t; induction t as [i | y | k f a IH]; intro x; simpl.
  - tauto.
  - exact (False_rect _ (empty y)).
  - intros [i Hi]. exact (IH i x Hi).
Qed.

Lemma semiterm_to_closed_emb : forall L O n (empty : O -> False)
    (t : semiterm L O n) H,
  @semiterm_to_closed L Empty_set n
    (rew_apply (@rew_emb L O Empty_set n empty) t) H =
  rew_apply (@rew_emb L O Empty_set n empty) t.
Proof.
  intros L O n empty t; induction t as [i | y | k f a IH]; intro H; simpl.
  - reflexivity.
  - exact (False_rect _ (empty y)).
  - f_equal. apply functional_extensionality. intro i. apply IH.
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

(** Transport a rewrite across a language homomorphism by mapping only the
    terms assigned to its bound and free variables. *)
Definition rew_language_map {L M X n Y m}
    (h : language_hom L M) (w : rew L X n Y m) : rew M X n Y m :=
  rew_bind
    (fun i => semiterm_language_map h (rew_apply w (Semiterm_bvar i)))
    (fun x => semiterm_language_map h (rew_apply w (Semiterm_fvar x))).

Lemma semiterm_language_map_rew_apply : forall L M X n Y m
    (h : language_hom L M) (w : rew L X n Y m)
    (t : semiterm L X n),
  semiterm_language_map h (rew_apply w t) =
  rew_apply (rew_language_map h w) (semiterm_language_map h t).
Proof.
  intros L M X n Y m h w t.
  rewrite (rew_eta w t).
  apply semiterm_language_map_rew_bind.
Qed.

Lemma rew_language_map_q : forall L M X n Y m
    (h : language_hom L M) (w : rew L X n Y m),
  rew_equiv (rew_language_map h (rew_q w))
            (rew_q (rew_language_map h w)).
Proof.
  intros L M X n Y m h w.
  apply rew_equiv_of_variables.
  - intro i.
    refine (@Fin.caseS' n i (fun j =>
      rew_apply (rew_language_map h (rew_q w)) (Semiterm_bvar j) =
      rew_apply (rew_q (rew_language_map h w)) (Semiterm_bvar j)) _ _).
    + reflexivity.
    + intro j.
      change (semiterm_language_map h
        (rew_apply rew_bshift (rew_apply w (Semiterm_bvar j))) =
        rew_apply rew_bshift
          (semiterm_language_map h (rew_apply w (Semiterm_bvar j)))).
      apply semiterm_language_map_rew_bshift.
  - intro x.
    change (semiterm_language_map h
      (rew_apply rew_bshift (rew_apply w (Semiterm_fvar x))) =
      rew_apply rew_bshift
        (semiterm_language_map h (rew_apply w (Semiterm_fvar x)))).
    apply semiterm_language_map_rew_bshift.
Qed.

Lemma semiformula_language_map_rewrite : forall L M X n Y m
    (h : language_hom L M) (w : rew L X n Y m)
    (p : semiformula L X n),
  semiformula_language_map h (semiformula_rewrite w p) =
  semiformula_rewrite (rew_language_map h w)
    (semiformula_language_map h p).
Proof.
  intros L M X n Y m h w p; revert Y m w.
  induction p; intros Y m w; simpl; try reflexivity.
  - f_equal. apply functional_extensionality. intro i.
    apply semiterm_language_map_rew_apply.
  - f_equal. apply functional_extensionality. intro i.
    apply semiterm_language_map_rew_apply.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - f_equal. rewrite IHp.
    apply semiformula_rewrite_ext, rew_language_map_q.
  - f_equal. rewrite IHp.
    apply semiformula_rewrite_ext, rew_language_map_q.
Qed.

Lemma rew_language_map_subst : forall L M X k n
    (h : language_hom L M) (v : Fin.t k -> semiterm L X n),
  rew_equiv (rew_language_map h (rew_subst v))
    (rew_subst (fun i => semiterm_language_map h (v i))).
Proof.
  intros. apply rew_equiv_of_variables; intro x; reflexivity.
Qed.

Lemma rew_language_map_shift : forall L M n (h : language_hom L M),
  rew_equiv (rew_language_map h (@rew_shift L n)) (@rew_shift M n).
Proof.
  intros. apply rew_equiv_of_variables; intro x; reflexivity.
Qed.

Lemma rew_language_map_free : forall L M n (h : language_hom L M),
  rew_equiv (rew_language_map h (@rew_free L n)) (@rew_free M n).
Proof.
  intros L M n h. apply rew_equiv_of_variables.
  - intro i. apply semiterm_language_map_rew_free_bound.
  - intro x. reflexivity.
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

(** Rewriting a freed binder reserves free variable zero for that binder and
    shifts the rewritten images of all pre-existing free variables. *)
Definition rew_rewrite_under_free {L}
    (f : nat -> syntactic_term L) : nat -> syntactic_term L :=
  fun x =>
    match x with
    | 0 => Semiterm_fvar 0
    | S y => rew_apply rew_shift (f y)
    end.

Lemma rew_rewrite_under_free_comp_shift : forall L
    (f : nat -> syntactic_term L),
  rew_equiv
    (rew_comp (rew_rewrite (rew_rewrite_under_free f)) rew_shift)
    (rew_comp rew_shift (rew_rewrite f)).
Proof.
  intros. apply rew_equiv_of_variables.
  - intros i. exact (Fin.case0 (fun _ => _ = _) i).
  - intro x. reflexivity.
Qed.

Lemma rew_rewrite_under_free_comp_free : forall L
    (f : nat -> syntactic_term L),
  rew_equiv
    (rew_comp (rew_rewrite (rew_rewrite_under_free f)) (@rew_free L 0))
    (rew_comp (@rew_free L 0) (rew_q (rew_rewrite f))).
Proof.
  intros L f. apply rew_equiv_of_variables.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    subst i. reflexivity.
  - intro x. cbn. symmetry.
    apply rew_free_bshift_eq_shift.
Qed.

Lemma semiformula_rewrite_under_free_shift : forall L
    (f : nat -> syntactic_term L) (p : proposition L),
  semiformula_rewrite (rew_rewrite (rew_rewrite_under_free f))
      (semiformula_shift p) =
  semiformula_shift (semiformula_rewrite (rew_rewrite f) p).
Proof.
  intros. unfold semiformula_shift.
  rewrite <- !semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_rewrite_under_free_comp_shift.
Qed.

Lemma semiformula_rewrite_under_free_free : forall L
    (f : nat -> syntactic_term L) (p : semiproposition L 1),
  semiformula_rewrite (rew_rewrite (rew_rewrite_under_free f))
      (@semiformula_free L 0 p) =
  @semiformula_free L 0
    (semiformula_rewrite (rew_q (rew_rewrite f)) p).
Proof.
  intros. unfold semiformula_free.
  rewrite <- !semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_rewrite_under_free_comp_free.
Qed.

Lemma rew_subst_bshift_zero : forall L X
    (v : Fin.t 1 -> semiterm L X 0) (t : semiterm L X 0),
  rew_apply (rew_subst v) (rew_apply rew_bshift t) = t.
Proof.
  intros L X v t. induction t as [i | x | k g a IH]; simpl.
  - exact (Fin.case0 (fun _ => _ = _) i).
  - reflexivity.
  - f_equal. apply functional_extensionality. exact IH.
Qed.

Lemma rew_rewrite_comp_substitute_one : forall L
    (f : nat -> syntactic_term L) (t : syntactic_term L),
  rew_equiv
    (rew_comp (rew_rewrite f) (rew_subst (fun _ : Fin.t 1 => t)))
    (rew_comp
      (rew_subst
        (fun _ : Fin.t 1 => rew_apply (rew_rewrite f) t))
      (rew_q (rew_rewrite f))).
Proof.
  intros L f t. apply rew_equiv_of_variables.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    now subst i.
  - intro x. cbn. symmetry. apply rew_subst_bshift_zero.
Qed.

Lemma semiformula_rewrite_substitute_one : forall L
    (f : nat -> syntactic_term L) (t : syntactic_term L)
    (p : semiproposition L 1),
  semiformula_rewrite (rew_rewrite f)
      (semiformula_substitute (fun _ : Fin.t 1 => t) p) =
  semiformula_substitute
      (fun _ : Fin.t 1 => rew_apply (rew_rewrite f) t)
      (semiformula_rewrite (rew_q (rew_rewrite f)) p).
Proof.
  intros. unfold semiformula_substitute.
  rewrite <- !semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_rewrite_comp_substitute_one.
Qed.

Lemma semiformula_language_map_substitute : forall L M X k n
    (h : language_hom L M) (v : Fin.t k -> semiterm L X n)
    (p : semiformula L X k),
  semiformula_language_map h (semiformula_substitute v p) =
  semiformula_substitute (fun i => semiterm_language_map h (v i))
    (semiformula_language_map h p).
Proof.
  intros. unfold semiformula_substitute.
  rewrite semiformula_language_map_rewrite.
  apply semiformula_rewrite_ext, rew_language_map_subst.
Qed.

Lemma semiformula_language_map_shift : forall L M n
    (h : language_hom L M) (p : semiproposition L n),
  semiformula_language_map h (semiformula_shift p) =
  semiformula_shift (semiformula_language_map h p).
Proof.
  intros. unfold semiformula_shift.
  rewrite semiformula_language_map_rewrite.
  apply semiformula_rewrite_ext, rew_language_map_shift.
Qed.

Lemma semiformula_language_map_free : forall L M n
    (h : language_hom L M) (p : semiproposition L (n + 1)),
  semiformula_language_map h (semiformula_free p) =
  semiformula_free (semiformula_language_map h p).
Proof.
  intros. unfold semiformula_free.
  rewrite semiformula_language_map_rewrite.
  apply semiformula_rewrite_ext, rew_language_map_free.
Qed.

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

(** * Constructive conversion of free-variable-free formulas *)

Lemma rew_q_emb : forall L O X n (empty : O -> False),
  rew_equiv (rew_q (@rew_emb L O X n empty))
    (@rew_emb L O X (S n) empty).
Proof.
  intros. apply rew_equiv_of_variables.
  - intro i. refine (@Fin.caseS' n i (fun j =>
      rew_apply (rew_q (rew_emb empty)) (Semiterm_bvar j) =
      rew_apply (rew_emb empty) (Semiterm_bvar j)) _ _).
    + reflexivity.
    + intro j; reflexivity.
  - intro x; exact (False_rect _ (empty x)).
Qed.

Fixpoint semiformula_to_closed {L X n} (p : semiformula L X n) :
    (forall x, ~ semiformula_free_occurs x p) -> semisentence L n :=
  match p as p0 in semiformula _ _ j return
      (forall x, ~ semiformula_free_occurs x p0) -> semisentence L j with
  | Semiformula_verum j => fun _ => Semiformula_verum j
  | Semiformula_falsum j => fun _ => Semiformula_falsum j
  | @Semiformula_rel _ _ j k r a => fun H =>
      Semiformula_rel r (fun i =>
        @semiterm_to_closed L X j (a i)
          (fun x Hx => H x (ex_intro (fun j => semiterm_free_occurs x (a j)) i Hx)))
  | @Semiformula_nrel _ _ j k r a => fun H =>
      Semiformula_nrel r (fun i =>
        @semiterm_to_closed L X j (a i)
          (fun x Hx => H x (ex_intro (fun j => semiterm_free_occurs x (a j)) i Hx)))
  | @Semiformula_and _ _ j q r => fun H =>
      Semiformula_and
        (@semiformula_to_closed L X j q (fun x Hx => H x (or_introl Hx)))
        (@semiformula_to_closed L X j r (fun x Hx => H x (or_intror Hx)))
  | @Semiformula_or _ _ j q r => fun H =>
      Semiformula_or
        (@semiformula_to_closed L X j q (fun x Hx => H x (or_introl Hx)))
        (@semiformula_to_closed L X j r (fun x Hx => H x (or_intror Hx)))
  | @Semiformula_all _ _ j q => fun H =>
      Semiformula_all (@semiformula_to_closed L X (S j) q H)
  | @Semiformula_exists _ _ j q => fun H =>
      Semiformula_exists (@semiformula_to_closed L X (S j) q H)
  end.

Lemma semiformula_emb_to_closed : forall L X n
    (p : semiformula L X n)
    (H : forall x, ~ semiformula_free_occurs x p),
  semiformula_rewrite
    (rew_emb (fun x : Empty_set => match x with end))
    (@semiformula_to_closed L X n p H) = p.
Proof.
  intros L X n p; induction p; intro H; simpl; try reflexivity.
  - f_equal. apply functional_extensionality. intro i.
    apply semiterm_emb_to_closed.
  - f_equal. apply functional_extensionality. intro i.
    apply semiterm_emb_to_closed.
  - f_equal; [apply IHp1 | apply IHp2].
  - f_equal; [apply IHp1 | apply IHp2].
  - f_equal.
    transitivity (semiformula_rewrite
      (@rew_emb L Empty_set X (S n) (fun x => match x with end))
      (@semiformula_to_closed L X (S n) p H)).
    + apply semiformula_rewrite_ext, rew_q_emb.
    + apply IHp.
  - f_equal.
    transitivity (semiformula_rewrite
      (@rew_emb L Empty_set X (S n) (fun x => match x with end))
      (@semiformula_to_closed L X (S n) p H)).
    + apply semiformula_rewrite_ext, rew_q_emb.
    + apply IHp.
Qed.

Lemma semiformula_emb_no_free_occurs : forall L O X n
    (empty : O -> False) (p : semiformula L O n) x,
  ~ semiformula_free_occurs x
    (semiformula_rewrite (@rew_emb L O X n empty) p).
Proof.
  intros L O X n empty p x H.
  destruct (@semiformula_rewrite_free_occurs_sources
    L O n X n (rew_emb empty) p x H)
    as [[i Hi] | [y [_ Hy]]].
  - exact Hi.
  - exact (False_rect _ (empty y)).
Qed.

(** * Exact universal closure *)

Fixpoint nat_free_bound (xs : list nat) : nat :=
  match xs with
  | nil => 0
  | cons x ys => Nat.max (S x) (nat_free_bound ys)
  end.

Lemma in_nat_free_bound : forall x xs,
  In x xs -> x < nat_free_bound xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl; [tauto |].
  intros [-> | Hin].
  - change (x < Nat.max (S x) (nat_free_bound ys)).
    eapply Nat.lt_le_trans.
    + apply Nat.lt_succ_diag_r.
    + apply Nat.le_max_l.
  - change (x < Nat.max (S y) (nat_free_bound ys)).
    eapply Nat.lt_le_trans.
    + apply IH, Hin.
    + apply Nat.le_max_r.
Qed.

Definition semiformula_free_bound {L n} (p : semiproposition L n) : nat :=
  nat_free_bound (semiformula_free_variable_list p).

Lemma semiformula_lt_free_bound_of_occurs : forall L n
    (p : semiproposition L n) x,
  semiformula_free_occurs x p -> x < semiformula_free_bound p.
Proof.
  intros. apply in_nat_free_bound.
  now apply (proj2 (semiformula_free_variable_list_spec p x)).
Qed.

Lemma semiformula_free_bound_zero : forall L n (p : semiproposition L n),
  (forall x, ~ semiformula_free_occurs x p) ->
  semiformula_free_bound p = 0.
Proof.
  intros L n p H. unfold semiformula_free_bound.
  destruct (semiformula_free_variable_list p) as [|x xs] eqn:Hxs;
    [reflexivity |].
  exfalso. apply (H x).
  apply (proj1 (semiformula_free_variable_list_spec p x)).
  rewrite Hxs. now left.
Qed.

Definition semiformula_fix_all_free {L} (p : proposition L) :
    semiproposition L (semiformula_free_bound p) :=
  semiformula_rewrite
    (@rew_fix_iter L 0 (semiformula_free_bound p)) p.

Lemma semiformula_fix_all_free_no_free : forall L (p : proposition L) x,
  ~ semiformula_free_occurs x (semiformula_fix_all_free p).
Proof.
  intros L p x H.
  destruct (@semiformula_rewrite_free_occurs_sources
    L nat 0 nat (semiformula_free_bound p)
    (rew_fix_iter 0 (semiformula_free_bound p)) p x H)
    as [[i Hi] | [y [Hy Himage]]].
  - exact (Fin.case0 (fun i => ~ semiterm_free_occurs x
      (rew_apply (rew_fix_iter 0 (semiformula_free_bound p))
        (Semiterm_bvar i))) i Hi).
  - pose proof (@semiformula_lt_free_bound_of_occurs L 0 p y Hy) as Hlt.
    pose proof (@rew_fix_iter_fvar_lt L 0
      (semiformula_free_bound p) y Hlt) as Heq.
    assert (Hbound : semiterm_free_occurs x
      (@Semiterm_bvar L nat (semiformula_free_bound p)
        (@fin_add_right_of_lt 0 y (semiformula_free_bound p) Hlt))).
    { exact (eq_rect _ (fun P : Prop => P) Himage _
        (f_equal (fun t => semiterm_free_occurs x t) Heq)). }
    exact Hbound.
Qed.

Definition semiformula_universal_closure_open {L} (p : proposition L) :
    proposition L :=
  first_all_closure (semiformula_universal_quantifier L nat)
    (semiformula_free_bound p) (semiformula_fix_all_free p).

Lemma semiformula_universal_closure_open_no_free :
  forall L (p : proposition L) x,
  ~ semiformula_free_occurs x (semiformula_universal_closure_open p).
Proof.
  intros L p x H.
  apply (proj1 (@semiformula_free_occurs_all_closure
    L nat (semiformula_free_bound p) x (semiformula_fix_all_free p))) in H.
  exact (@semiformula_fix_all_free_no_free L p x H).
Qed.

Definition semiformula_universal_closure {L} (p : proposition L) : sentence L :=
  @semiformula_to_closed L nat 0 (semiformula_universal_closure_open p)
    (@semiformula_universal_closure_open_no_free L p).

Lemma semiformula_emb_universal_closure : forall L (p : proposition L),
  semiformula_rewrite
    (rew_emb (fun x : Empty_set => match x with end))
    (semiformula_universal_closure p) =
  semiformula_universal_closure_open p.
Proof. intros; apply semiformula_emb_to_closed. Qed.

Lemma semiformula_universal_closure_open_id :
  forall L (p : proposition L),
  (forall x, ~ semiformula_free_occurs x p) ->
  semiformula_universal_closure_open p = p.
Proof.
  intros L p Hclosed.
  pose proof (@semiformula_free_bound_zero L 0 p Hclosed) as Hb.
  unfold semiformula_universal_closure_open, semiformula_fix_all_free.
  rewrite Hb. cbn.
  transitivity (semiformula_rewrite (@rew_id L nat 0) p).
  - apply semiformula_rewrite_ext.
    apply rew_equiv_of_variables.
    + intro i; exact (Fin.case0 (fun i => _ = _) i).
    + intro x; reflexivity.
  - apply semiformula_rewrite_id.
Qed.
