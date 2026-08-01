(** Capture-avoiding rewrites for monadic second-order formulas. *)

From Stdlib Require Import Logic.FunctionalExtensionality Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.SecondOrder.Syntax Require Import Formula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Lift a map of bound predicate variables beneath one predicate binder. *)
Definition fin_retrusion {n m} (f : Fin.t n -> Fin.t m) :
    Fin.t (S n) -> Fin.t (S m) :=
  fun i => @Fin.caseS' n i (fun _ => Fin.t (S m)) Fin.F1
    (fun j => Fin.FS (f j)).

Lemma fin_retrusion_zero : forall n m (f : Fin.t n -> Fin.t m),
  fin_retrusion f Fin.F1 = Fin.F1.
Proof. reflexivity. Qed.

Lemma fin_retrusion_succ : forall n m (f : Fin.t n -> Fin.t m)
    (i : Fin.t n),
  fin_retrusion f (Fin.FS i) = Fin.FS (f i).
Proof. reflexivity. Qed.

Lemma fin_retrusion_comp_succ : forall n m (f : Fin.t n -> Fin.t m),
  (fun i => fin_retrusion f (Fin.FS i)) = fun i => Fin.FS (f i).
Proof. reflexivity. Qed.

Lemma fin_retrusion_id : forall n,
  @fin_retrusion n n (fun i => i) = fun i => i.
Proof.
  intro n. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j => fin_retrusion (fun x => x) j = j)
    eq_refl _).
  intro j. reflexivity.
Qed.

Lemma fin_retrusion_comp : forall n m p
    (f : Fin.t n -> Fin.t m) (g : Fin.t m -> Fin.t p),
  (fun i => fin_retrusion g (fin_retrusion f i)) =
  fin_retrusion (fun i => g (f i)).
Proof.
  intros n m p f g. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    fin_retrusion g (fin_retrusion f j) =
    fin_retrusion (fun x => g (f x)) j) eq_refl _).
  intro j. reflexivity.
Qed.

(** Rewriting individual terms leaves predicate variables untouched. *)
Fixpoint second_order_rewrite_terms_aux {L P X N n}
    (p : second_order_semiformula L P X N n) : forall Y m,
    rew L X n Y m -> second_order_semiformula L P Y N m :=
  match p with
  | SOFormula_rel r v => fun Y m w =>
      SOFormula_rel r (fun i => rew_apply w (v i))
  | SOFormula_nrel r v => fun Y m w =>
      SOFormula_nrel r (fun i => rew_apply w (v i))
  | SOFormula_bpred A t => fun Y m w => SOFormula_bpred A (rew_apply w t)
  | SOFormula_nbpred A t => fun Y m w => SOFormula_nbpred A (rew_apply w t)
  | SOFormula_fpred A t => fun Y m w => SOFormula_fpred A (rew_apply w t)
  | SOFormula_nfpred A t => fun Y m w => SOFormula_nfpred A (rew_apply w t)
  | SOFormula_verum => fun Y m w => SOFormula_verum
  | SOFormula_falsum => fun Y m w => SOFormula_falsum
  | SOFormula_and q r => fun Y m w => SOFormula_and
      (second_order_rewrite_terms_aux q w)
      (second_order_rewrite_terms_aux r w)
  | SOFormula_or q r => fun Y m w => SOFormula_or
      (second_order_rewrite_terms_aux q w)
      (second_order_rewrite_terms_aux r w)
  | SOFormula_all0 q => fun Y m w => SOFormula_all0
      (second_order_rewrite_terms_aux q (rew_q w))
  | SOFormula_exs0 q => fun Y m w => SOFormula_exs0
      (second_order_rewrite_terms_aux q (rew_q w))
  | SOFormula_all1 q => fun Y m w => SOFormula_all1
      (second_order_rewrite_terms_aux q w)
  | SOFormula_exs1 q => fun Y m w => SOFormula_exs1
      (second_order_rewrite_terms_aux q w)
  end.

Definition second_order_rewrite_terms {L P X n Y m N}
    (w : rew L X n Y m) (p : second_order_semiformula L P X N n) :
    second_order_semiformula L P Y N m :=
  second_order_rewrite_terms_aux p w.

Theorem second_order_rewrite_terms_equiv : forall L P X n Y m N
    (w v : rew L X n Y m),
  rew_equiv w v -> forall p : second_order_semiformula L P X N n,
  second_order_rewrite_terms w p = second_order_rewrite_terms v p.
Proof.
  intros L P X n Y m N w v H p. revert Y m w v H.
  induction p; intros; simpl.
  - f_equal. apply functional_extensionality. intro i. apply H.
  - f_equal. apply functional_extensionality. intro i. apply H.
  - now rewrite H.
  - now rewrite H.
  - now rewrite H.
  - now rewrite H.
  - reflexivity.
  - reflexivity.
  - now rewrite (IHp1 _ _ w v H), (IHp2 _ _ w v H).
  - now rewrite (IHp1 _ _ w v H), (IHp2 _ _ w v H).
  - f_equal. apply IHp. now apply rew_q_respects_equiv.
  - f_equal. apply IHp. now apply rew_q_respects_equiv.
  - now rewrite (IHp _ _ w v H).
  - now rewrite (IHp _ _ w v H).
Qed.

Theorem second_order_rewrite_terms_neg : forall L P X n Y m N
    (w : rew L X n Y m) (p : second_order_semiformula L P X N n),
  second_order_rewrite_terms w (second_order_neg p) =
  second_order_neg (second_order_rewrite_terms w p).
Proof.
  intros L P X n Y m N w p. revert Y m w.
  induction p; intros; simpl; try reflexivity;
    try (now rewrite IHp1, IHp2); try (now rewrite IHp).
Qed.

Theorem second_order_rewrite_terms_id : forall L P X N n
    (p : second_order_semiformula L P X N n),
  second_order_rewrite_terms rew_id p = p.
Proof.
  intros L P X N n p; induction p; simpl; try reflexivity.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - f_equal. etransitivity.
    + eapply second_order_rewrite_terms_equiv with (v := rew_id).
      intro t. exact (rew_q_id_apply t).
    + exact IHp.
  - f_equal. etransitivity.
    + eapply second_order_rewrite_terms_equiv with (v := rew_id).
      intro t. exact (rew_q_id_apply t).
    + exact IHp.
  - now rewrite IHp.
  - now rewrite IHp.
Qed.

Theorem second_order_rewrite_terms_comp : forall L P W a X n Y m Z l N
    (v : rew L X n Y m) (w : rew L W a X n)
    (u : rew L Y m Z l) (p : second_order_semiformula L P W N a),
  second_order_rewrite_terms (rew_comp u (rew_comp v w)) p =
  second_order_rewrite_terms u
    (second_order_rewrite_terms v (second_order_rewrite_terms w p)).
Proof.
  intros L P W a X n Y m Z l N v w u p.
  revert X n Y m Z l v w u.
  induction p; intros; simpl; try reflexivity.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - f_equal. etransitivity.
    + eapply second_order_rewrite_terms_equiv with
        (v := rew_comp (rew_q u) (rew_comp (rew_q v) (rew_q w))).
      intro t.
      rewrite rew_q_comp_apply, !rew_comp_apply,
        rew_q_comp_apply. reflexivity.
    + apply IHp.
  - f_equal. etransitivity.
    + eapply second_order_rewrite_terms_equiv with
        (v := rew_comp (rew_q u) (rew_comp (rew_q v) (rew_q w))).
      intro t.
      rewrite rew_q_comp_apply, !rew_comp_apply,
        rew_q_comp_apply. reflexivity.
    + apply IHp.
  - now rewrite IHp.
  - now rewrite IHp.
Qed.

(** The usual binary composition law follows from the three-stage form above.
    It is convenient when formula templates are instantiated below. *)
Corollary second_order_rewrite_terms_comp2 : forall L P X n Y m Z l N
    (v : rew L X n Y m) (u : rew L Y m Z l)
    (p : second_order_semiformula L P X N n),
  second_order_rewrite_terms (rew_comp u v) p =
  second_order_rewrite_terms u (second_order_rewrite_terms v p).
Proof.
  intros L P X n Y m Z l N v u p.
  transitivity
    (second_order_rewrite_terms
      (rew_comp u (rew_comp v rew_id)) p).
  - symmetry. apply second_order_rewrite_terms_equiv. intro t. reflexivity.
  - rewrite second_order_rewrite_terms_comp.
    now rewrite second_order_rewrite_terms_id.
Qed.

(** Renaming bound predicate variables. *)
Fixpoint second_order_bmap_aux {L P X N n}
    (p : second_order_semiformula L P X N n) : forall M,
    (Fin.t N -> Fin.t M) -> second_order_semiformula L P X M n :=
  match p with
  | SOFormula_rel r v => fun M f => SOFormula_rel r v
  | SOFormula_nrel r v => fun M f => SOFormula_nrel r v
  | SOFormula_bpred A t => fun M f => SOFormula_bpred (f A) t
  | SOFormula_nbpred A t => fun M f => SOFormula_nbpred (f A) t
  | SOFormula_fpred A t => fun M f => SOFormula_fpred A t
  | SOFormula_nfpred A t => fun M f => SOFormula_nfpred A t
  | SOFormula_verum => fun M f => SOFormula_verum
  | SOFormula_falsum => fun M f => SOFormula_falsum
  | SOFormula_and q r => fun M f => SOFormula_and
      (second_order_bmap_aux q f) (second_order_bmap_aux r f)
  | SOFormula_or q r => fun M f => SOFormula_or
      (second_order_bmap_aux q f) (second_order_bmap_aux r f)
  | SOFormula_all0 q => fun M f => SOFormula_all0
      (second_order_bmap_aux q f)
  | SOFormula_exs0 q => fun M f => SOFormula_exs0
      (second_order_bmap_aux q f)
  | SOFormula_all1 q => fun M f => SOFormula_all1
      (second_order_bmap_aux q (fin_retrusion f))
  | SOFormula_exs1 q => fun M f => SOFormula_exs1
      (second_order_bmap_aux q (fin_retrusion f))
  end.

Definition second_order_bmap {L P X N M n}
    (f : Fin.t N -> Fin.t M) (p : second_order_semiformula L P X N n) :
    second_order_semiformula L P X M n := second_order_bmap_aux p f.

Theorem second_order_bmap_neg : forall L P X N M n
    (f : Fin.t N -> Fin.t M) (p : second_order_semiformula L P X N n),
  second_order_bmap f (second_order_neg p) =
  second_order_neg (second_order_bmap f p).
Proof.
  intros L P X N M n f p. revert M f.
  induction p; intros; simpl; try reflexivity;
    try (now rewrite IHp1, IHp2); try (now rewrite IHp).
Qed.

Theorem second_order_bmap_id : forall L P X N n
    (p : second_order_semiformula L P X N n),
  second_order_bmap (fun i => i) p = p.
Proof.
  intros L P X N n p; induction p; simpl; try reflexivity;
    try (now rewrite IHp1, IHp2); try (now rewrite IHp).
  - f_equal. rewrite fin_retrusion_id. exact IHp.
  - f_equal. rewrite fin_retrusion_id. exact IHp.
Qed.

Theorem second_order_bmap_comp : forall L P X N M K n
    (f : Fin.t N -> Fin.t M) (g : Fin.t M -> Fin.t K)
    (p : second_order_semiformula L P X N n),
  second_order_bmap g (second_order_bmap f p) =
  second_order_bmap (fun i => g (f i)) p.
Proof.
  intros L P X N M K n f g p; revert M K f g.
  induction p; intros; simpl; try reflexivity;
    try (now rewrite IHp1, IHp2); try (now rewrite IHp).
  - f_equal. rewrite (IHp _ _ (fin_retrusion f) (fin_retrusion g)).
    rewrite fin_retrusion_comp. reflexivity.
  - f_equal. rewrite (IHp _ _ (fin_retrusion f) (fin_retrusion g)).
    rewrite fin_retrusion_comp. reflexivity.
Qed.

Theorem second_order_bmap_rewrite_terms : forall L P X n Y m N M
    (w : rew L X n Y m) (f : Fin.t N -> Fin.t M)
    (p : second_order_semiformula L P X N n),
  second_order_bmap f (second_order_rewrite_terms w p) =
  second_order_rewrite_terms w (second_order_bmap f p).
Proof.
  intros L P X n Y m N M w f p; revert M f Y m w.
  induction p; intros; simpl; try reflexivity;
    try (now rewrite IHp1, IHp2); try (now rewrite IHp).
Qed.

(** * Formula-valued substitution for predicate variables *)

(** Instantiate the sole bound individual variable of a unary formula. *)
Definition second_order_instantiate {L P X N n}
    (p : second_order_semiformula L P X N 1)
    (t : semiterm L X n) : second_order_semiformula L P X N n :=
  second_order_rewrite_terms (rew_subst (fun _ : Fin.t 1 => t)) p.

Lemma second_order_instantiate_neg : forall L P X N n
    (p : second_order_semiformula L P X N 1) (t : semiterm L X n),
  second_order_instantiate (second_order_neg p) t =
  second_order_neg (second_order_instantiate p t).
Proof. intros. apply second_order_rewrite_terms_neg. Qed.

(** Rewriting after instantiation commutes whenever free individual variables
    are fixed.  Bound substitution is the principal instance. *)
Lemma second_order_instantiate_rewrite : forall L P X N n m
    (w : rew L X n X m)
    (Hfree : forall x, rew_apply w (Semiterm_fvar x) = Semiterm_fvar x)
    (p : second_order_semiformula L P X N 1) (t : semiterm L X n),
  second_order_instantiate p (rew_apply w t) =
  second_order_rewrite_terms w (second_order_instantiate p t).
Proof.
  intros L P X N n m w Hfree p t. unfold second_order_instantiate.
  rewrite <- second_order_rewrite_terms_comp2.
  apply second_order_rewrite_terms_equiv.
  apply rew_equiv_of_variables.
  - intro i. rewrite (fin_one_eq_f1 i). reflexivity.
  - intro x. simpl. symmetry. apply Hfree.
Qed.

Record second_order_predicate_rew (L : language)
    (P1 : Type) (N1 : nat) (P2 : Type) (N2 : nat) (X : Type) : Type := {
  second_order_predicate_rew_bound :
    Fin.t N1 -> second_order_semiformula L P2 X N2 1;
  second_order_predicate_rew_free :
    P1 -> second_order_semiformula L P2 X N2 1
}.

Arguments second_order_predicate_rew_bound {L P1 N1 P2 N2 X} _ _.
Arguments second_order_predicate_rew_free {L P1 N1 P2 N2 X} _ _.

(** Lift a predicate rewrite beneath one bound predicate quantifier. *)
Definition second_order_predicate_rew_q {L P1 N1 P2 N2 X}
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X) :
    second_order_predicate_rew L P1 (S N1) P2 (S N2) X :=
  {| second_order_predicate_rew_bound := fun A =>
       @Fin.caseS' N1 A
         (fun _ => second_order_semiformula L P2 X (S N2) 1)
         (SOFormula_bpred Fin.F1 (Semiterm_bvar Fin.F1))
         (fun B => second_order_bmap Fin.FS
           (second_order_predicate_rew_bound Omega B));
     second_order_predicate_rew_free := fun A =>
       second_order_bmap Fin.FS (second_order_predicate_rew_free Omega A) |}.

Lemma second_order_predicate_rew_q_bound_zero : forall L P1 N1 P2 N2 X
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_bound (second_order_predicate_rew_q Omega)
    Fin.F1 = SOFormula_bpred Fin.F1 (Semiterm_bvar Fin.F1).
Proof. reflexivity. Qed.

Lemma second_order_predicate_rew_q_bound_succ : forall L P1 N1 P2 N2 X
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X) A,
  second_order_predicate_rew_bound (second_order_predicate_rew_q Omega)
    (Fin.FS A) = second_order_bmap Fin.FS
      (second_order_predicate_rew_bound Omega A).
Proof. reflexivity. Qed.

Lemma second_order_predicate_rew_q_free : forall L P1 N1 P2 N2 X
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X) A,
  second_order_predicate_rew_free (second_order_predicate_rew_q Omega) A =
  second_order_bmap Fin.FS (second_order_predicate_rew_free Omega A).
Proof. reflexivity. Qed.

Fixpoint second_order_predicate_rew_app_aux {L P1 X N1 n}
    (p : second_order_semiformula L P1 X N1 n) : forall P2 N2,
    second_order_predicate_rew L P1 N1 P2 N2 X ->
    second_order_semiformula L P2 X N2 n :=
  match p with
  | SOFormula_rel r v => fun P2 N2 Omega => SOFormula_rel r v
  | SOFormula_nrel r v => fun P2 N2 Omega => SOFormula_nrel r v
  | SOFormula_bpred A t => fun P2 N2 Omega =>
      second_order_instantiate
        (second_order_predicate_rew_bound Omega A) t
  | SOFormula_nbpred A t => fun P2 N2 Omega =>
      second_order_neg (second_order_instantiate
        (second_order_predicate_rew_bound Omega A) t)
  | SOFormula_fpred A t => fun P2 N2 Omega =>
      second_order_instantiate
        (second_order_predicate_rew_free Omega A) t
  | SOFormula_nfpred A t => fun P2 N2 Omega =>
      second_order_neg (second_order_instantiate
        (second_order_predicate_rew_free Omega A) t)
  | SOFormula_verum => fun P2 N2 Omega => SOFormula_verum
  | SOFormula_falsum => fun P2 N2 Omega => SOFormula_falsum
  | SOFormula_and q r => fun P2 N2 Omega => SOFormula_and
      (second_order_predicate_rew_app_aux q Omega)
      (second_order_predicate_rew_app_aux r Omega)
  | SOFormula_or q r => fun P2 N2 Omega => SOFormula_or
      (second_order_predicate_rew_app_aux q Omega)
      (second_order_predicate_rew_app_aux r Omega)
  | SOFormula_all0 q => fun P2 N2 Omega => SOFormula_all0
      (second_order_predicate_rew_app_aux q Omega)
  | SOFormula_exs0 q => fun P2 N2 Omega => SOFormula_exs0
      (second_order_predicate_rew_app_aux q Omega)
  | SOFormula_all1 q => fun P2 N2 Omega => SOFormula_all1
      (second_order_predicate_rew_app_aux q
        (second_order_predicate_rew_q Omega))
  | SOFormula_exs1 q => fun P2 N2 Omega => SOFormula_exs1
      (second_order_predicate_rew_app_aux q
        (second_order_predicate_rew_q Omega))
  end.

Definition second_order_predicate_rew_app {L P1 X N1 n P2 N2}
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X)
    (p : second_order_semiformula L P1 X N1 n) :
    second_order_semiformula L P2 X N2 n :=
  second_order_predicate_rew_app_aux p Omega.

Definition second_order_predicate_rew_equiv {L P1 N1 P2 N2 X}
    (Omega Psi : second_order_predicate_rew L P1 N1 P2 N2 X) : Prop :=
  (forall A, second_order_predicate_rew_bound Omega A =
    second_order_predicate_rew_bound Psi A) /\
  (forall A, second_order_predicate_rew_free Omega A =
    second_order_predicate_rew_free Psi A).

Lemma second_order_predicate_rew_q_equiv : forall L P1 N1 P2 N2 X
    (Omega Psi : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv Omega Psi ->
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q Omega)
    (second_order_predicate_rew_q Psi).
Proof.
  intros L P1 N1 P2 N2 X Omega Psi [Hb Hf]. split.
  - intro A. refine (@Fin.caseS' N1 A (fun i =>
      second_order_predicate_rew_bound (second_order_predicate_rew_q Omega) i =
      second_order_predicate_rew_bound (second_order_predicate_rew_q Psi) i)
      eq_refl _).
    intro B. simpl. now rewrite Hb.
  - intro A. simpl. now rewrite Hf.
Qed.

Theorem second_order_predicate_rew_app_equiv : forall L P1 X N1 n P2 N2
    (Omega Psi : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv Omega Psi ->
  forall p : second_order_semiformula L P1 X N1 n,
  second_order_predicate_rew_app Omega p =
  second_order_predicate_rew_app Psi p.
Proof.
  intros L P1 X N1 n P2 N2 Omega Psi H p.
  revert P2 N2 Omega Psi H.
  induction p; intros; simpl; try reflexivity.
  - now rewrite (proj1 H t).
  - now rewrite (proj1 H t).
  - now rewrite (proj2 H p).
  - now rewrite (proj2 H p).
  - now rewrite (IHp1 _ _ Omega Psi H), (IHp2 _ _ Omega Psi H).
  - now rewrite (IHp1 _ _ Omega Psi H), (IHp2 _ _ Omega Psi H).
  - now rewrite (IHp _ _ Omega Psi H).
  - now rewrite (IHp _ _ Omega Psi H).
  - f_equal. apply IHp. now apply second_order_predicate_rew_q_equiv.
  - f_equal. apply IHp. now apply second_order_predicate_rew_q_equiv.
Qed.

Theorem second_order_predicate_rew_app_neg : forall L P1 X N1 n P2 N2
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X)
    (p : second_order_semiformula L P1 X N1 n),
  second_order_predicate_rew_app Omega (second_order_neg p) =
  second_order_neg (second_order_predicate_rew_app Omega p).
Proof.
  intros L P1 X N1 n P2 N2 Omega p. revert P2 N2 Omega.
  induction p; intros; simpl; try reflexivity;
    try (now rewrite IHp1, IHp2); try (now rewrite IHp);
    try (now rewrite second_order_neg_involutive).
Qed.

Lemma rew_q_fixes_free : forall L X n m (w : rew L X n X m),
  (forall x, rew_apply w (Semiterm_fvar x) = Semiterm_fvar x) ->
  forall x, rew_apply (rew_q w) (Semiterm_fvar x) = Semiterm_fvar x.
Proof. intros L X n m w H x. simpl. now rewrite H. Qed.

(** Predicate substitution is natural with respect to every individual-term
    rewrite that fixes free variables.  This strictly generalizes the source
    law stated only for simultaneous bound substitution. *)
Theorem second_order_predicate_rew_app_rewrite_terms :
  forall L P1 X N1 n m P2 N2
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X)
    (w : rew L X n X m)
    (Hfree : forall x, rew_apply w (Semiterm_fvar x) = Semiterm_fvar x)
    (p : second_order_semiformula L P1 X N1 n),
  second_order_predicate_rew_app Omega
    (second_order_rewrite_terms w p) =
  second_order_rewrite_terms w
    (second_order_predicate_rew_app Omega p).
Proof.
  intros L P1 X N1 n m P2 N2 Omega w Hfree p.
  revert m w Hfree P2 N2 Omega.
  induction p; intros; simpl; try reflexivity.
  - apply second_order_instantiate_rewrite. exact Hfree.
  - rewrite second_order_instantiate_rewrite by exact Hfree.
    symmetry. apply second_order_rewrite_terms_neg.
  - apply second_order_instantiate_rewrite. exact Hfree.
  - rewrite second_order_instantiate_rewrite by exact Hfree.
    symmetry. apply second_order_rewrite_terms_neg.
  - now rewrite IHp1, IHp2 by exact Hfree.
  - now rewrite IHp1, IHp2 by exact Hfree.
  - f_equal. apply IHp. now apply rew_q_fixes_free.
  - f_equal. apply IHp. now apply rew_q_fixes_free.
  - f_equal. apply IHp. exact Hfree.
  - f_equal. apply IHp. exact Hfree.
Qed.

Corollary second_order_predicate_rew_app_subst :
  forall L P1 X N1 n m P2 N2
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X)
    (v : Fin.t n -> semiterm L X m)
    (p : second_order_semiformula L P1 X N1 n),
  second_order_predicate_rew_app Omega
    (second_order_rewrite_terms (rew_subst v) p) =
  second_order_rewrite_terms (rew_subst v)
    (second_order_predicate_rew_app Omega p).
Proof.
  intros. apply second_order_predicate_rew_app_rewrite_terms.
  intro x. reflexivity.
Qed.

Definition second_order_predicate_rew_id {L P N X} :
    second_order_predicate_rew L P N P N X :=
  {| second_order_predicate_rew_bound := fun A =>
       SOFormula_bpred A (Semiterm_bvar Fin.F1);
     second_order_predicate_rew_free := fun A =>
       SOFormula_fpred A (Semiterm_bvar Fin.F1) |}.

Lemma second_order_predicate_rew_q_id_equiv : forall L P N X,
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q (@second_order_predicate_rew_id L P N X))
    second_order_predicate_rew_id.
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' N A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q second_order_predicate_rew_id) i =
      second_order_predicate_rew_bound second_order_predicate_rew_id i)
      eq_refl _).
    intro B. reflexivity.
  - intro A. reflexivity.
Qed.

Theorem second_order_predicate_rew_app_id : forall L P X N n
    (p : second_order_semiformula L P X N n),
  second_order_predicate_rew_app second_order_predicate_rew_id p = p.
Proof.
  intros L P X N n p. induction p; simpl; try reflexivity.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp.
  - now rewrite IHp.
  - f_equal. transitivity
      (second_order_predicate_rew_app second_order_predicate_rew_id p).
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_q_id_equiv.
    + exact IHp.
  - f_equal. transitivity
      (second_order_predicate_rew_app second_order_predicate_rew_id p).
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_q_id_equiv.
    + exact IHp.
Qed.

(** Postcomposition by a renaming of target bound predicates. *)
Definition second_order_predicate_rew_bLeft {L P1 N1 P2 N2 N3 X}
    (f : Fin.t N2 -> Fin.t N3)
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X) :
    second_order_predicate_rew L P1 N1 P2 N3 X :=
  {| second_order_predicate_rew_bound := fun A =>
       second_order_bmap f (second_order_predicate_rew_bound Omega A);
     second_order_predicate_rew_free := fun A =>
       second_order_bmap f (second_order_predicate_rew_free Omega A) |}.

Lemma second_order_predicate_rew_bLeft_q_equiv :
  forall L P1 N1 P2 N2 N3 X
    (f : Fin.t N2 -> Fin.t N3)
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_bLeft (fin_retrusion f)
      (second_order_predicate_rew_q Omega))
    (second_order_predicate_rew_q
      (second_order_predicate_rew_bLeft f Omega)).
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' N1 A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_bLeft (fin_retrusion f)
          (second_order_predicate_rew_q Omega)) i =
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q
          (second_order_predicate_rew_bLeft f Omega)) i) _ _).
    + reflexivity.
    + intro B. simpl. rewrite !second_order_bmap_comp. reflexivity.
  - intro A. simpl. rewrite !second_order_bmap_comp. reflexivity.
Qed.

Theorem second_order_predicate_rew_app_bmap : forall L P1 X N1 n P2 N2 N3
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X)
    (f : Fin.t N2 -> Fin.t N3)
    (p : second_order_semiformula L P1 X N1 n),
  second_order_bmap f (second_order_predicate_rew_app Omega p) =
  second_order_predicate_rew_app
    (second_order_predicate_rew_bLeft f Omega) p.
Proof.
  intros L P1 X N1 n P2 N2 N3 Omega f p.
  revert P2 N2 N3 Omega f.
  induction p; intros; simpl; try reflexivity.
  - apply second_order_bmap_rewrite_terms.
  - rewrite second_order_bmap_neg. f_equal.
    apply second_order_bmap_rewrite_terms.
  - apply second_order_bmap_rewrite_terms.
  - rewrite second_order_bmap_neg. f_equal.
    apply second_order_bmap_rewrite_terms.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp.
  - now rewrite IHp.
  - f_equal. transitivity
      (second_order_predicate_rew_app
        (second_order_predicate_rew_bLeft (fin_retrusion f)
          (second_order_predicate_rew_q Omega)) p).
    + apply IHp.
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_bLeft_q_equiv.
  - f_equal. transitivity
      (second_order_predicate_rew_app
        (second_order_predicate_rew_bLeft (fin_retrusion f)
          (second_order_predicate_rew_q Omega)) p).
    + apply IHp.
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_bLeft_q_equiv.
Qed.

(** Precomposition by a renaming of source bound predicates. *)
Definition second_order_predicate_rew_bRight {L P1 N0 N1 P2 N2 X}
    (f : Fin.t N0 -> Fin.t N1)
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X) :
    second_order_predicate_rew L P1 N0 P2 N2 X :=
  {| second_order_predicate_rew_bound := fun A =>
       second_order_predicate_rew_bound Omega (f A);
     second_order_predicate_rew_free :=
       second_order_predicate_rew_free Omega |}.

Lemma second_order_predicate_rew_bRight_q_equiv :
  forall L P1 N0 N1 P2 N2 X
    (f : Fin.t N0 -> Fin.t N1)
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_bRight (fin_retrusion f)
      (second_order_predicate_rew_q Omega))
    (second_order_predicate_rew_q
      (second_order_predicate_rew_bRight f Omega)).
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' N0 A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_bRight (fin_retrusion f)
          (second_order_predicate_rew_q Omega)) i =
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q
          (second_order_predicate_rew_bRight f Omega)) i) eq_refl _).
    intro B. reflexivity.
  - intro A. reflexivity.
Qed.

Theorem second_order_predicate_rew_bmap_app : forall L P1 X N0 N1 n P2 N2
    (f : Fin.t N0 -> Fin.t N1)
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X)
    (p : second_order_semiformula L P1 X N0 n),
  second_order_predicate_rew_app Omega (second_order_bmap f p) =
  second_order_predicate_rew_app
    (second_order_predicate_rew_bRight f Omega) p.
Proof.
  intros L P1 X N0 N1 n P2 N2 f Omega p.
  revert N1 P2 N2 f Omega.
  induction p; intros; simpl; try reflexivity.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp.
  - now rewrite IHp.
  - f_equal. transitivity
      (second_order_predicate_rew_app
        (second_order_predicate_rew_bRight (fin_retrusion f)
          (second_order_predicate_rew_q Omega)) p).
    + apply IHp.
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_bRight_q_equiv.
  - f_equal. transitivity
      (second_order_predicate_rew_app
        (second_order_predicate_rew_bRight (fin_retrusion f)
          (second_order_predicate_rew_q Omega)) p).
    + apply IHp.
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_bRight_q_equiv.
Qed.

Lemma second_order_predicate_rew_q_bRight_succ :
  forall L P1 N1 P2 N2 X
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_bLeft Fin.FS Omega)
    (second_order_predicate_rew_bRight Fin.FS
      (second_order_predicate_rew_q Omega)).
Proof. intros. split; intro A; reflexivity. Qed.

(** Composition substitutes the output templates of the first rewrite into
    the second. *)
Definition second_order_predicate_rew_comp
    {L P1 N1 P2 N2 P3 N3 X}
    (Omega23 : second_order_predicate_rew L P2 N2 P3 N3 X)
    (Omega12 : second_order_predicate_rew L P1 N1 P2 N2 X) :
    second_order_predicate_rew L P1 N1 P3 N3 X :=
  {| second_order_predicate_rew_bound := fun A =>
       second_order_predicate_rew_app Omega23
         (second_order_predicate_rew_bound Omega12 A);
     second_order_predicate_rew_free := fun A =>
       second_order_predicate_rew_app Omega23
         (second_order_predicate_rew_free Omega12 A) |}.

Lemma second_order_predicate_rew_q_comp_equiv :
  forall L P1 N1 P2 N2 P3 N3 X
    (Omega23 : second_order_predicate_rew L P2 N2 P3 N3 X)
    (Omega12 : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q
      (second_order_predicate_rew_comp Omega23 Omega12))
    (second_order_predicate_rew_comp
      (second_order_predicate_rew_q Omega23)
      (second_order_predicate_rew_q Omega12)).
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' N1 A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q
          (second_order_predicate_rew_comp Omega23 Omega12)) i =
      second_order_predicate_rew_bound
        (second_order_predicate_rew_comp
          (second_order_predicate_rew_q Omega23)
          (second_order_predicate_rew_q Omega12)) i) _ _).
    + reflexivity.
    + intro B. simpl.
      rewrite second_order_predicate_rew_app_bmap.
      rewrite second_order_predicate_rew_bmap_app.
      apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_q_bRight_succ.
  - intro A. simpl.
    rewrite second_order_predicate_rew_app_bmap.
    rewrite second_order_predicate_rew_bmap_app.
    apply second_order_predicate_rew_app_equiv.
    apply second_order_predicate_rew_q_bRight_succ.
Qed.

Theorem second_order_predicate_rew_app_comp :
  forall L P1 N1 P2 N2 P3 N3 X n
    (Omega23 : second_order_predicate_rew L P2 N2 P3 N3 X)
    (Omega12 : second_order_predicate_rew L P1 N1 P2 N2 X)
    (p : second_order_semiformula L P1 X N1 n),
  second_order_predicate_rew_app
    (second_order_predicate_rew_comp Omega23 Omega12) p =
  second_order_predicate_rew_app Omega23
    (second_order_predicate_rew_app Omega12 p).
Proof.
  intros L P1 N1 P2 N2 P3 N3 X n Omega23 Omega12 p.
  revert P2 N2 P3 N3 Omega23 Omega12.
  induction p; intros; simpl; try reflexivity.
  - symmetry. apply second_order_predicate_rew_app_subst.
  - rewrite second_order_predicate_rew_app_neg.
    f_equal. symmetry. apply second_order_predicate_rew_app_subst.
  - symmetry. apply second_order_predicate_rew_app_subst.
  - rewrite second_order_predicate_rew_app_neg.
    f_equal. symmetry. apply second_order_predicate_rew_app_subst.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp1, IHp2.
  - now rewrite IHp.
  - now rewrite IHp.
  - f_equal. transitivity
      (second_order_predicate_rew_app
        (second_order_predicate_rew_comp
          (second_order_predicate_rew_q Omega23)
          (second_order_predicate_rew_q Omega12)) p).
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_q_comp_equiv.
    + apply IHp.
  - f_equal. transitivity
      (second_order_predicate_rew_app
        (second_order_predicate_rew_comp
          (second_order_predicate_rew_q Omega23)
          (second_order_predicate_rew_q Omega12)) p).
    + apply second_order_predicate_rew_app_equiv.
      apply second_order_predicate_rew_q_comp_equiv.
    + apply IHp.
Qed.

Lemma second_order_instantiate_bvar : forall L P X N
    (p : second_order_semiformula L P X N 1),
  second_order_instantiate p (Semiterm_bvar Fin.F1) = p.
Proof.
  intros. unfold second_order_instantiate.
  transitivity (second_order_rewrite_terms rew_id p).
  - apply second_order_rewrite_terms_equiv.
    apply rew_equiv_of_variables.
    + intro i. rewrite (fin_one_eq_f1 i). reflexivity.
    + intro x. reflexivity.
  - apply second_order_rewrite_terms_id.
Qed.

Lemma second_order_predicate_rew_comp_id_left :
  forall L P1 N1 P2 N2 X
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_comp second_order_predicate_rew_id Omega)
    Omega.
Proof.
  intros. split; intro A; simpl;
    apply second_order_predicate_rew_app_id.
Qed.

Lemma second_order_predicate_rew_comp_id_right :
  forall L P1 N1 P2 N2 X
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_comp Omega second_order_predicate_rew_id)
    Omega.
Proof.
  intros. split; intro A; simpl;
    apply second_order_instantiate_bvar.
Qed.

(** Apply an individual rewrite uniformly to every predicate template. *)
Definition second_order_predicate_rew_map
    {L P1 N1 P2 N2 X1 X2}
    (w : rew L X1 1 X2 1)
    (Omega : second_order_predicate_rew L P1 N1 P2 N2 X1) :
    second_order_predicate_rew L P1 N1 P2 N2 X2 :=
  {| second_order_predicate_rew_bound := fun A =>
       second_order_rewrite_terms w
         (second_order_predicate_rew_bound Omega A);
     second_order_predicate_rew_free := fun A =>
       second_order_rewrite_terms w
         (second_order_predicate_rew_free Omega A) |}.

(** Rename free predicate variables while retaining every bound predicate. *)
Definition second_order_predicate_rew_rename {L P1 P2 N X}
    (f : P1 -> P2) : second_order_predicate_rew L P1 N P2 N X :=
  {| second_order_predicate_rew_bound := fun A =>
       SOFormula_bpred A (Semiterm_bvar Fin.F1);
     second_order_predicate_rew_free := fun A =>
       SOFormula_fpred (f A) (Semiterm_bvar Fin.F1) |}.

Lemma second_order_predicate_rew_q_rename_equiv : forall L P1 P2 N X
    (f : P1 -> P2),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q
      (@second_order_predicate_rew_rename L P1 P2 N X f))
    (second_order_predicate_rew_rename f).
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' N A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q
          (second_order_predicate_rew_rename f)) i =
      second_order_predicate_rew_bound
        (second_order_predicate_rew_rename f) i) eq_refl _).
    intro B. reflexivity.
  - intro A. reflexivity.
Qed.

Definition second_order_predicate_rew_shift {L N X} :
    second_order_predicate_rew L nat N nat N X :=
  second_order_predicate_rew_rename S.

Lemma second_order_predicate_rew_q_shift_equiv : forall L N X,
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q
      (@second_order_predicate_rew_shift L N X))
    second_order_predicate_rew_shift.
Proof. intros. apply second_order_predicate_rew_q_rename_equiv. Qed.

(** Turn the last bound predicate into free predicate zero, shifting every
    pre-existing free predicate. *)
Definition second_order_predicate_rew_free_last {L N X} :
    second_order_predicate_rew L nat (N + 1) nat N X :=
  {| second_order_predicate_rew_bound := fun A =>
       @Fin.case_L_R' N 1
         (fun _ => second_order_semiformula L nat X N 1) A
         (fun B => SOFormula_bpred B (Semiterm_bvar Fin.F1))
         (fun _ => SOFormula_fpred 0 (Semiterm_bvar Fin.F1));
     second_order_predicate_rew_free := fun A =>
       SOFormula_fpred (S A) (Semiterm_bvar Fin.F1) |}.

Lemma second_order_predicate_rew_free_last_old : forall L N X
    (A : Fin.t N),
  second_order_predicate_rew_bound
    (@second_order_predicate_rew_free_last L N X) (Fin.L 1 A) =
  SOFormula_bpred A (Semiterm_bvar Fin.F1).
Proof.
  intros. change
    (@Fin.case_L_R' N 1
      (fun _ => second_order_semiformula L nat X N 1) (Fin.L 1 A)
      (fun B => SOFormula_bpred B (Semiterm_bvar Fin.F1))
      (fun _ => SOFormula_fpred 0 (Semiterm_bvar Fin.F1)) =
    SOFormula_bpred A (Semiterm_bvar Fin.F1)).
  exact (@Fin.case_L_R'_L N 1 _ A _ _).
Qed.

Lemma second_order_predicate_rew_free_last_new : forall L N X,
  second_order_predicate_rew_bound
    (@second_order_predicate_rew_free_last L N X) (Fin.R N Fin.F1) =
  SOFormula_fpred 0 (Semiterm_bvar Fin.F1).
Proof.
  intros. change
    (@Fin.case_L_R' N 1
      (fun _ => second_order_semiformula L nat X N 1) (Fin.R N Fin.F1)
      (fun B => SOFormula_bpred B (Semiterm_bvar Fin.F1))
      (fun _ => SOFormula_fpred 0 (Semiterm_bvar Fin.F1)) =
    SOFormula_fpred 0 (Semiterm_bvar Fin.F1)).
  exact (@Fin.case_L_R'_R N 1 _ Fin.F1 _ _).
Qed.

Lemma second_order_predicate_rew_free_last_free : forall L N X A,
  second_order_predicate_rew_free
    (@second_order_predicate_rew_free_last L N X) A =
  SOFormula_fpred (S A) (Semiterm_bvar Fin.F1).
Proof. reflexivity. Qed.

Lemma second_order_predicate_rew_q_free_last_equiv : forall L N X,
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q
      (@second_order_predicate_rew_free_last L N X))
    (@second_order_predicate_rew_free_last L (S N) X).
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' (N + 1) A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q
          (@second_order_predicate_rew_free_last L N X)) i =
      second_order_predicate_rew_bound
        (@second_order_predicate_rew_free_last L (S N) X) i) _ _).
    + reflexivity.
    + intro B. refine (@Fin.case_L_R' N 1 (fun j =>
        second_order_predicate_rew_bound
          (second_order_predicate_rew_q
            (@second_order_predicate_rew_free_last L N X)) (Fin.FS j) =
        second_order_predicate_rew_bound
          (@second_order_predicate_rew_free_last L (S N) X)
          (Fin.FS j)) B _ _).
      * intro C. rewrite second_order_predicate_rew_q_bound_succ.
        change
          (second_order_bmap Fin.FS
            (second_order_predicate_rew_bound
              (@second_order_predicate_rew_free_last L N X) (Fin.L 1 C)) =
          second_order_predicate_rew_bound
            (@second_order_predicate_rew_free_last L (S N) X)
            (Fin.L 1 (Fin.FS C))).
        rewrite !second_order_predicate_rew_free_last_old. reflexivity.
      * intro C. rewrite (fin_one_eq_f1 C).
        rewrite second_order_predicate_rew_q_bound_succ.
        change
          (second_order_bmap Fin.FS
            (second_order_predicate_rew_bound
              (@second_order_predicate_rew_free_last L N X)
              (Fin.R N Fin.F1)) =
          second_order_predicate_rew_bound
            (@second_order_predicate_rew_free_last L (S N) X)
            (Fin.R (S N) Fin.F1)).
        rewrite !second_order_predicate_rew_free_last_new. reflexivity.
  - intro A. reflexivity.
Qed.

Definition second_order_predicate_rew_emb {L O P N X}
    (empty : O -> False) : second_order_predicate_rew L O N P N X :=
  second_order_predicate_rew_rename (fun x => False_rect _ (empty x)).

Lemma second_order_predicate_rew_q_emb_equiv : forall L O P N X
    (empty : O -> False),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q
      (@second_order_predicate_rew_emb L O P N X empty))
    (second_order_predicate_rew_emb empty).
Proof. intros. apply second_order_predicate_rew_q_rename_equiv. Qed.

(** Substitute only bound predicates and preserve free predicates. *)
Definition second_order_predicate_rew_subst {L P N1 N2 X}
    (Phi : Fin.t N1 -> second_order_semiformula L P X N2 1) :
    second_order_predicate_rew L P N1 P N2 X :=
  {| second_order_predicate_rew_bound := Phi;
     second_order_predicate_rew_free := fun A =>
       SOFormula_fpred A (Semiterm_bvar Fin.F1) |}.

Definition second_order_predicate_subst_q_family {L P N1 N2 X}
    (Phi : Fin.t N1 -> second_order_semiformula L P X N2 1) :
    Fin.t (S N1) -> second_order_semiformula L P X (S N2) 1 :=
  fun A => @Fin.caseS' N1 A
    (fun _ => second_order_semiformula L P X (S N2) 1)
    (SOFormula_bpred Fin.F1 (Semiterm_bvar Fin.F1))
    (fun B => second_order_bmap Fin.FS (Phi B)).

Lemma second_order_predicate_rew_q_subst_equiv : forall L P N1 N2 X
    (Phi : Fin.t N1 -> second_order_semiformula L P X N2 1),
  second_order_predicate_rew_equiv
    (second_order_predicate_rew_q
      (second_order_predicate_rew_subst Phi))
    (second_order_predicate_rew_subst
      (second_order_predicate_subst_q_family Phi)).
Proof.
  intros. split.
  - intro A. refine (@Fin.caseS' N1 A (fun i =>
      second_order_predicate_rew_bound
        (second_order_predicate_rew_q
          (second_order_predicate_rew_subst Phi)) i =
      second_order_predicate_rew_bound
        (second_order_predicate_rew_subst
          (second_order_predicate_subst_q_family Phi)) i) eq_refl _).
    intro B. reflexivity.
  - intro A. reflexivity.
Qed.

Definition second_order_substitute_predicates {L P X N1 N2 n}
    (Phi : Fin.t N1 -> second_order_semiformula L P X N2 1)
    (p : second_order_semiformula L P X N1 n) :
    second_order_semiformula L P X N2 n :=
  second_order_predicate_rew_app
    (second_order_predicate_rew_subst Phi) p.

(** Source-facing specializations on the canonical natural-number variable
    types. *)
Definition second_order_semiproposition_free_individual {L N n}
    (p : second_order_semiproposition L N (n + 1)) :
    second_order_semiproposition L N n :=
  second_order_rewrite_terms rew_free p.

Definition second_order_semiproposition_shift_individual {L N n}
    (p : second_order_semiproposition L N n) :
    second_order_semiproposition L N n :=
  second_order_rewrite_terms rew_shift p.

Definition second_order_semiproposition_free_predicate {L N n}
    (p : second_order_semiproposition L (N + 1) n) :
    second_order_semiproposition L N n :=
  second_order_predicate_rew_app second_order_predicate_rew_free_last p.

Definition second_order_semiproposition_shift_predicate {L N n}
    (p : second_order_semiproposition L N n) :
    second_order_semiproposition L N n :=
  second_order_predicate_rew_app second_order_predicate_rew_shift p.

Definition second_order_semiproposition_substitute_predicates {L N1 N2 n}
    (Phi : Fin.t N1 -> second_order_semiproposition L N2 1)
    (p : second_order_semiproposition L N1 n) :
    second_order_semiproposition L N2 n :=
  second_order_substitute_predicates Phi p.

(** Embed a formula with no free variables of either sort into arbitrary free
    variable types. *)
Definition second_order_semisentence_embed {L P X N n}
    (p : second_order_semisentence L N n) :
    second_order_semiformula L P X N n :=
  second_order_predicate_rew_app
    (second_order_predicate_rew_emb (fun x : Empty_set => match x with end))
    (second_order_rewrite_terms
      (rew_emb (fun x : Empty_set => match x with end)) p).
