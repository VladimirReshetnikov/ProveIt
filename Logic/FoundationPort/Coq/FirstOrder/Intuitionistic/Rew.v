(** Capture-avoiding rewriting of intuitionistic first-order formulas. *)

From Stdlib Require Import Logic.FunctionalExtensionality Program.Equality
  Vectors.Fin.
From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Intuitionistic Require Import Formula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint ifo_rewrite_aux {L X n} (phi : ifo_semiformula L X n) :
    forall Y m, rew L X n Y m -> ifo_semiformula L Y m :=
  match phi in ifo_semiformula _ _ n0 return
      forall Y m, rew L X n0 Y m -> ifo_semiformula L Y m with
  | IFOFalsum => fun Y m _ => @IFOFalsum L Y m
  | IFORel R v => fun Y m w => IFORel R (fun i => rew_apply w (v i))
  | IFOAnd psi chi => fun Y m w =>
      IFOAnd (@ifo_rewrite_aux L X _ psi Y m w)
        (@ifo_rewrite_aux L X _ chi Y m w)
  | IFOOr psi chi => fun Y m w =>
      IFOOr (@ifo_rewrite_aux L X _ psi Y m w)
        (@ifo_rewrite_aux L X _ chi Y m w)
  | IFOImp psi chi => fun Y m w =>
      IFOImp (@ifo_rewrite_aux L X _ psi Y m w)
        (@ifo_rewrite_aux L X _ chi Y m w)
  | IFOAll psi => fun Y m w =>
      IFOAll (@ifo_rewrite_aux L X _ psi Y (S m) (rew_q w))
  | IFOExs psi => fun Y m w =>
      IFOExs (@ifo_rewrite_aux L X _ psi Y (S m) (rew_q w))
  end.

Definition ifo_rewrite {L X n Y m} (w : rew L X n Y m)
    (phi : ifo_semiformula L X n) : ifo_semiformula L Y m :=
  @ifo_rewrite_aux L X n phi Y m w.

Lemma ifo_rewrite_falsum : forall L X n Y m (w : rew L X n Y m),
  ifo_rewrite w (@IFOFalsum L X n) = @IFOFalsum L Y m.
Proof. reflexivity. Qed.

Lemma ifo_rewrite_rel : forall L X n Y m (w : rew L X n Y m)
    k (R : language_rel L k) v,
  ifo_rewrite w (@IFORel L X n k R v) =
  IFORel R (fun i => rew_apply w (v i)).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_and : forall L X n Y m (w : rew L X n Y m)
    (phi psi : ifo_semiformula L X n),
  ifo_rewrite w (IFOAnd phi psi) =
  IFOAnd (ifo_rewrite w phi) (ifo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_or : forall L X n Y m (w : rew L X n Y m)
    (phi psi : ifo_semiformula L X n),
  ifo_rewrite w (IFOOr phi psi) =
  IFOOr (ifo_rewrite w phi) (ifo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_imp : forall L X n Y m (w : rew L X n Y m)
    (phi psi : ifo_semiformula L X n),
  ifo_rewrite w (IFOImp phi psi) =
  IFOImp (ifo_rewrite w phi) (ifo_rewrite w psi).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_all : forall L X n Y m (w : rew L X n Y m)
    (phi : ifo_semiformula L X (S n)),
  ifo_rewrite w (IFOAll phi) = IFOAll (ifo_rewrite (rew_q w) phi).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_exs : forall L X n Y m (w : rew L X n Y m)
    (phi : ifo_semiformula L X (S n)),
  ifo_rewrite w (IFOExs phi) = IFOExs (ifo_rewrite (rew_q w) phi).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_neg : forall L X n Y m (w : rew L X n Y m)
    (phi : ifo_semiformula L X n),
  ifo_rewrite w (ifo_neg phi) = ifo_neg (ifo_rewrite w phi).
Proof. reflexivity. Qed.

Lemma ifo_rewrite_verum : forall L X n Y m (w : rew L X n Y m),
  ifo_rewrite w (@ifo_verum L X n) = @ifo_verum L Y m.
Proof. reflexivity. Qed.

Lemma ifo_rewrite_ext : forall L X n Y m (w v : rew L X n Y m)
    (phi : ifo_semiformula L X n),
  rew_equiv w v -> ifo_rewrite w phi = ifo_rewrite v phi.
Proof.
  intros L X n Y m w v phi Hwv. revert m w v Hwv.
  induction phi; intros m w v Hwv; simpl; try reflexivity.
  - f_equal. apply functional_extensionality. intro i. apply Hwv.
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - now rewrite (IHphi1 m w v Hwv), (IHphi2 m w v Hwv).
  - f_equal. apply IHphi. now apply rew_q_respects_equiv.
  - f_equal. apply IHphi. now apply rew_q_respects_equiv.
Qed.

Theorem ifo_rewrite_id : forall L X n (phi : ifo_semiformula L X n),
  ifo_rewrite rew_id phi = phi.
Proof.
  intros L X n phi. induction phi; simpl; try congruence.
  - f_equal.
  - f_equal. transitivity (ifo_rewrite (@rew_id L X (S n)) phi).
    + apply ifo_rewrite_ext. intro t. apply rew_q_id_apply.
    + exact IHphi.
  - f_equal. transitivity (ifo_rewrite (@rew_id L X (S n)) phi).
    + apply ifo_rewrite_ext. intro t. apply rew_q_id_apply.
    + exact IHphi.
Qed.

Theorem ifo_rewrite_comp : forall L X n Y m Z o
    (v : rew L Y m Z o) (w : rew L X n Y m)
    (phi : ifo_semiformula L X n),
  ifo_rewrite (rew_comp v w) phi = ifo_rewrite v (ifo_rewrite w phi).
Proof.
  intros L X n Y m Z o v w phi. revert Y m Z o v w.
  induction phi; intros Y m Z o v w; simpl; try congruence.
  - f_equal. transitivity
      (ifo_rewrite (rew_comp (rew_q v) (rew_q w)) phi).
    + apply ifo_rewrite_ext. intro t. apply rew_q_comp_apply.
    + apply IHphi.
  - f_equal. transitivity
      (ifo_rewrite (rew_comp (rew_q v) (rew_q w)) phi).
    + apply ifo_rewrite_ext. intro t. apply rew_q_comp_apply.
    + apply IHphi.
Qed.

Definition ifo_map {L X n Y m} (b : Fin.t n -> Fin.t m) (e : X -> Y)
    (phi : ifo_semiformula L X n) : ifo_semiformula L Y m :=
  ifo_rewrite (rew_map b e) phi.

Definition ifo_bshift {L X n} (phi : ifo_semiformula L X n) :
    ifo_semiformula L X (S n) := ifo_rewrite rew_bshift phi.

Definition ifo_emb {L O X n} (empty : O -> False)
    (phi : ifo_semiformula L O n) : ifo_semiformula L X n :=
  ifo_rewrite (rew_emb empty) phi.

Definition ifo_shift {L n} (phi : ifo_semiproposition L n) :
    ifo_semiproposition L n := ifo_rewrite rew_shift phi.

Definition ifo_free {L n} (phi : ifo_semiproposition L (n + 1)) :
    ifo_semiproposition L n := ifo_rewrite rew_free phi.

Definition ifo_substitute {L X n m}
    (b : Fin.t n -> semiterm L X m) (phi : ifo_semiformula L X n) :
    ifo_semiformula L X m := ifo_rewrite (rew_subst b) phi.

(** Freeing a freshly weakened closed formula is the ordinary shift of its
    free variables.  Keeping this equality at the formula layer avoids
    repeating rewrite-composition arguments in quantified proof systems. *)
Lemma ifo_free_bshift : forall L (phi : ifo_proposition L),
  @ifo_free L 0 (ifo_bshift phi) = ifo_shift phi.
Proof.
  intros L phi. unfold ifo_free, ifo_bshift, ifo_shift.
  rewrite <- ifo_rewrite_comp.
  apply ifo_rewrite_ext, rew_free_bshift_eq_shift.
Qed.

Lemma ifo_free_imp_bshift : forall L (phi : ifo_proposition L)
    (psi : ifo_semiproposition L 1),
  @ifo_free L 0 (IFOImp (ifo_bshift phi) psi) =
  IFOImp (ifo_shift phi) (@ifo_free L 0 psi).
Proof.
  intros L phi psi. unfold ifo_free. simpl. f_equal.
  apply ifo_free_bshift.
Qed.

Lemma ifo_shift_all : forall L (phi : ifo_semiproposition L 1),
  ifo_shift (IFOAll phi) = IFOAll (ifo_shift phi).
Proof.
  intros L phi. unfold ifo_shift. simpl. f_equal.
  apply ifo_rewrite_ext, rew_q_shift.
Qed.

Lemma ifo_shift_double_neg_all : forall L
    (phi : ifo_semiproposition L 1),
  ifo_shift (ifo_neg (ifo_neg (IFOAll phi))) =
  ifo_neg (ifo_neg (IFOAll (ifo_shift phi))).
Proof.
  intros L phi. unfold ifo_shift, ifo_neg. simpl.
  f_equal. f_equal. f_equal.
  apply ifo_rewrite_ext, rew_q_shift.
Qed.

Lemma ifo_substitute_shift_one_eq_free : forall L
    (phi : ifo_semiproposition L 1),
  ifo_substitute (fun _ : Fin.t 1 => Semiterm_fvar 0)
      (ifo_shift phi) = @ifo_free L 0 phi.
Proof.
  intros L phi. unfold ifo_substitute, ifo_shift, ifo_free.
  rewrite <- ifo_rewrite_comp.
  apply ifo_rewrite_ext, rew_equiv_of_variables.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    now subst i.
  - intro x. reflexivity.
Qed.

(** Rewrite laws needed by proof transport through the quantified Hilbert
    constructors. *)
Lemma ifo_rewrite_under_free_free : forall L
    (f : nat -> syntactic_term L) (phi : ifo_semiproposition L 1),
  ifo_rewrite (rew_rewrite (rew_rewrite_under_free f))
      (@ifo_free L 0 phi) =
  @ifo_free L 0 (ifo_rewrite (rew_q (rew_rewrite f)) phi).
Proof.
  intros L f phi. unfold ifo_free.
  rewrite <- !ifo_rewrite_comp.
  apply ifo_rewrite_ext, rew_rewrite_under_free_comp_free.
Qed.

Lemma ifo_rewrite_substitute_one : forall L
    (f : nat -> syntactic_term L) (t : syntactic_term L)
    (phi : ifo_semiproposition L 1),
  ifo_rewrite (rew_rewrite f)
      (ifo_substitute (fun _ : Fin.t 1 => t) phi) =
  ifo_substitute
      (fun _ : Fin.t 1 => rew_apply (rew_rewrite f) t)
      (ifo_rewrite (rew_q (rew_rewrite f)) phi).
Proof.
  intros L f t phi. unfold ifo_substitute.
  rewrite <- !ifo_rewrite_comp.
  apply ifo_rewrite_ext, rew_rewrite_comp_substitute_one.
Qed.

Lemma ifo_rewrite_q_bshift : forall L X n Y m
    (w : rew L X n Y m) (phi : ifo_semiformula L X n),
  ifo_rewrite (rew_q w) (ifo_bshift phi) =
  ifo_bshift (ifo_rewrite w phi).
Proof.
  intros L X n Y m w phi. unfold ifo_bshift.
  rewrite <- !ifo_rewrite_comp.
  apply ifo_rewrite_ext. intro t. apply rew_q_bshift_apply.
Qed.

Lemma ifo_rewrite_all1_shape : forall L
    (f : nat -> syntactic_term L) (phi : ifo_semiproposition L 1)
    (t : syntactic_term L),
  ifo_rewrite (rew_rewrite f)
      (IFOImp (IFOAll phi)
        (ifo_substitute (fun _ : Fin.t 1 => t) phi)) =
  IFOImp (IFOAll (ifo_rewrite (rew_q (rew_rewrite f)) phi))
    (ifo_substitute
      (fun _ : Fin.t 1 => rew_apply (rew_rewrite f) t)
      (ifo_rewrite (rew_q (rew_rewrite f)) phi)).
Proof.
  intros. simpl. f_equal. apply ifo_rewrite_substitute_one.
Qed.

Lemma ifo_rewrite_all2_shape : forall L
    (f : nat -> syntactic_term L) (phi : ifo_proposition L)
    (psi : ifo_semiproposition L 1),
  ifo_rewrite (rew_rewrite f)
      (IFOImp (IFOAll (IFOImp (ifo_bshift phi) psi))
        (IFOImp phi (IFOAll psi))) =
  IFOImp
    (IFOAll (IFOImp (ifo_bshift (ifo_rewrite (rew_rewrite f) phi))
      (ifo_rewrite (rew_q (rew_rewrite f)) psi)))
    (IFOImp (ifo_rewrite (rew_rewrite f) phi)
      (IFOAll (ifo_rewrite (rew_q (rew_rewrite f)) psi))).
Proof.
  intros. simpl. now rewrite ifo_rewrite_q_bshift.
Qed.

Lemma ifo_rewrite_ex1_shape : forall L
    (f : nat -> syntactic_term L) (t : syntactic_term L)
    (phi : ifo_semiproposition L 1),
  ifo_rewrite (rew_rewrite f)
      (IFOImp (ifo_substitute (fun _ : Fin.t 1 => t) phi)
        (IFOExs phi)) =
  IFOImp
    (ifo_substitute
      (fun _ : Fin.t 1 => rew_apply (rew_rewrite f) t)
      (ifo_rewrite (rew_q (rew_rewrite f)) phi))
    (IFOExs (ifo_rewrite (rew_q (rew_rewrite f)) phi)).
Proof.
  intros. simpl. f_equal. apply ifo_rewrite_substitute_one.
Qed.

Lemma ifo_rewrite_ex2_shape : forall L
    (f : nat -> syntactic_term L) (phi : ifo_semiproposition L 1)
    (psi : ifo_proposition L),
  ifo_rewrite (rew_rewrite f)
      (IFOImp (IFOAll (IFOImp phi (ifo_bshift psi)))
        (IFOImp (IFOExs phi) psi)) =
  IFOImp
    (IFOAll (IFOImp (ifo_rewrite (rew_q (rew_rewrite f)) phi)
      (ifo_bshift (ifo_rewrite (rew_rewrite f) psi))))
    (IFOImp (IFOExs (ifo_rewrite (rew_q (rew_rewrite f)) phi))
      (ifo_rewrite (rew_rewrite f) psi)).
Proof.
  intros. simpl. now rewrite ifo_rewrite_q_bshift.
Qed.

Theorem ifo_map_injective : forall (L : language) (X : Type) n
    (Y : Type) m (b : Fin.t n -> Fin.t m) (e : X -> Y),
  (forall i j, b i = b j -> i = j) ->
  (forall x y, e x = e y -> x = y) ->
  forall phi psi : ifo_semiformula L X n,
    ifo_map b e phi = ifo_map b e psi -> phi = psi.
Proof.
  intros L X n Y m b e Hb He phi. revert Y m b e Hb He.
  refine (@ifo_semiformula_rect L X
    (fun n phi => forall (Y : Type) m
      (b : Fin.t n -> Fin.t m) (e : X -> Y),
      (forall i j, b i = b j -> i = j) ->
      (forall x y, e x = e y -> x = y) ->
      forall psi, ifo_map b e phi = ifo_map b e psi -> phi = psi)
    _ _ _ _ _ _ _ n phi); clear phi n.
  - intros n Y m b e Hb He psi H. destruct psi; try discriminate.
    reflexivity.
  - intros n k R v Y m b e Hb He psi H.
    destruct psi as [| n l S w | | | | | ]; try discriminate.
    assert (Hkl : k = l).
    { pose proof (f_equal ifo_outer_rel_payload H) as Hp; simpl in Hp.
      apply option_some_injective in Hp. now injection Hp. }
    subst l. destruct (ifo_rel_injective_same_arity H) as [HRS Hvw].
    subst S. f_equal. apply functional_extensionality. intro i.
    eapply (@rew_map_injective L X n Y m b e Hb He).
    exact (f_equal (fun h => h i) Hvw).
  - intros n a IHa c IHc Y m b e Hb He psi H.
    destruct psi; try discriminate. f_equal.
    + eapply IHa; eauto. now dependent destruction H.
    + eapply IHc; eauto. now dependent destruction H.
  - intros n a IHa c IHc Y m b e Hb He psi H.
    destruct psi; try discriminate. f_equal.
    + eapply IHa; eauto. now dependent destruction H.
    + eapply IHc; eauto. now dependent destruction H.
  - intros n a IHa c IHc Y m b e Hb He psi H.
    destruct psi; try discriminate. f_equal.
    + eapply IHa; eauto. now dependent destruction H.
    + eapply IHc; eauto. now dependent destruction H.
  - intros n a IHa Y m b e Hb He psi H.
    destruct psi; try discriminate. f_equal.
    apply IHa with (Y := Y) (m := S m)
      (b := rew_lift_bound_map b) (e := e).
    + now apply rew_lift_bound_map_injective.
    + exact He.
    + unfold ifo_map.
      rewrite <- (@ifo_rewrite_ext L X (S n) Y (S m) _ _ a
        (rew_q_map_equiv (L := L) b e)).
      rewrite <- (@ifo_rewrite_ext L X (S n) Y (S m) _ _ psi
        (rew_q_map_equiv (L := L) b e)).
      now apply (proj1 (ifo_all_injective _ _)) in H.
  - intros n a IHa Y m b e Hb He psi H.
    destruct psi; try discriminate. f_equal.
    apply IHa with (Y := Y) (m := S m)
      (b := rew_lift_bound_map b) (e := e).
    + now apply rew_lift_bound_map_injective.
    + exact He.
    + unfold ifo_map.
      rewrite <- (@ifo_rewrite_ext L X (S n) Y (S m) _ _ a
        (rew_q_map_equiv (L := L) b e)).
      rewrite <- (@ifo_rewrite_ext L X (S n) Y (S m) _ _ psi
        (rew_q_map_equiv (L := L) b e)).
      now apply (proj1 (ifo_exs_injective _ _)) in H.
Qed.

Theorem ifo_complexity_rewrite : forall L X n Y m
    (w : rew L X n Y m) (phi : ifo_semiformula L X n),
  ifo_complexity (ifo_rewrite w phi) = ifo_complexity phi.
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl; try reflexivity.
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi1 m w), (IHphi2 m w).
  - now rewrite (IHphi (S m) (rew_q w)).
  - now rewrite (IHphi (S m) (rew_q w)).
Qed.

Theorem ifo_negative_rewrite_iff : forall L X n Y m
    (w : rew L X n Y m) (phi : ifo_semiformula L X n),
  ifo_negative m (ifo_rewrite w phi) <-> ifo_negative n phi.
Proof.
  intros L X n Y m w phi. revert m w.
  induction phi; intros m w; simpl.
  - split; intro H; constructor.
  - split; intro H; inversion H.
  - rewrite !ifo_negative_and_iff.
    now rewrite (IHphi1 m w), (IHphi2 m w).
  - split; intro H; inversion H.
  - rewrite !ifo_negative_imp_iff. apply IHphi2.
  - rewrite !ifo_negative_all_iff. apply IHphi.
  - split; intro H; inversion H.
Qed.
