(**
  The normal extensions GL.3 + box^n bottom.

  This module ports the active theorem surface of Foundation's pinned
  [Modal/Logic/GLPoint3OplusBoxBot/Basic.lean].  Extended naturals are
  represented by [option nat]: [Some n] is the least normal-rule closure of
  GL.3 together with [box_iter n Bottom], while [None] is definitionally
  GL.3 itself.

  A useful Coq simplification is the exact deduction theorem below.  The
  added axiom is letterless and implies its own box already in GL, so both
  substitution and necessitation pass through an implication whose
  antecedent is the added axiom.  This lets the finite completeness theorem
  for GL.3 discharge the otherwise lengthy stage-two WeakPoint2 argument.
  The two characteristic GL.2 derivations remain explicit and checked.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.Classical_Prop Logic.ProofIrrelevance.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Root StructuralFrames NormalHilbert
  CanonicalExtensions LogicInfrastructure GLGrzDerivations Boxdot
  CanonicalPoint2 CanonicalGLPoint3 CanonicalTrivVer GLPlusBoxBot.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The option-indexed normal hierarchy *)

Definition GLPoint3PlusBoxBot_axiom (n : nat) : modal_logic_set nat :=
  fun p => p = box_iter n (@Bottom nat).

Definition GLPoint3PlusBoxBot (n : option nat) : modal_logic_set nat :=
  match n with
  | Some k =>
      logic_sum_normal (@GLPoint3_proves nat)
        (GLPoint3PlusBoxBot_axiom k)
  | None => @GLPoint3_proves nat
  end.

Theorem GLPoint3PlusBoxBot_normal :
  forall n, normal_logic (GLPoint3PlusBoxBot n).
Proof.
  intros [n |]; simpl.
  - apply logic_sum_normal_normal_left. exact GLPoint3_normal_logic.
  - exact GLPoint3_normal_logic.
Qed.

Definition GLPoint3PlusBoxBot_classical (n : option nat) :
    classical_logic (GLPoint3PlusBoxBot n) :=
  quasi_classical (normal_quasi (GLPoint3PlusBoxBot_normal n)).

Theorem GLPoint3_weaker_than_GLPoint3PlusBoxBot :
  forall n, logic_subset (@GLPoint3_proves nat)
                         (GLPoint3PlusBoxBot n).
Proof.
  intros [n |] p Hp; simpl.
  - now apply LSN_mem_left.
  - exact Hp.
Qed.

Theorem GLPoint3PlusBoxBot_boxbot :
  forall n,
    GLPoint3PlusBoxBot (Some n) (box_iter n (@Bottom nat)).
Proof. intro n; simpl; apply LSN_mem_right; reflexivity. Qed.

Lemma substitute_GLPoint3PlusBoxBot_axiom :
  forall (sigma : nat -> formula nat) n,
    substitute sigma (box_iter n (@Bottom nat)) =
    box_iter n Bottom.
Proof.
  intros sigma n. rewrite substitute_box_iter. reflexivity.
Qed.

Lemma GLPoint3_proves_boxbot_successor :
  forall n,
    GLPoint3_proves
      (Imp (box_iter n (@Bottom nat))
           (box_iter (S n) Bottom)).
Proof.
  intro n. apply GL_weaker_than_GLPoint3.
  exact (GL_proves_boxbot_successor n).
Qed.

(** Every finite stage proves [box^n p], not merely [box^n bottom]. *)
Theorem GLPoint3PlusBoxBot_axiomNVer :
  forall n (p : formula nat),
    GLPoint3PlusBoxBot (Some n) (box_iter n p).
Proof.
  intros n p.
  pose proof (K_proves_ex_falso p) as Hfalse.
  pose proof (GL_proves_box_iter_regularity n
    (@K_proves_normal schema_L nat _ Hfalse)) as Hiter.
  simpl. eapply LSN_mp.
  - apply LSN_mem_left, GL_weaker_than_GLPoint3. exact Hiter.
  - apply LSN_mem_right. reflexivity.
Qed.

Theorem eq_GLPoint3PlusBoxBot_omega_GLPoint3 :
  GLPoint3PlusBoxBot None = @GLPoint3_proves nat.
Proof. reflexivity. Qed.

(** The exact finite-stage deduction theorem. *)
Theorem iff_provable_GLPoint3PlusBoxBot_provable_GLPoint3 :
  forall n (p : formula nat),
    GLPoint3PlusBoxBot (Some n) p <->
    GLPoint3_proves (Imp (box_iter n Bottom) p).
Proof.
  intros n p; split.
  - intro Hp. simpl in Hp.
    induction Hp as
        [p Hp
        | p Hp
        | p q Hpq IHpq Hp IHp
        | sigma p Hp IH
        | p Hp IH].
    + now apply (logic_imply_intro GLPoint3_classical_logic).
    + unfold GLPoint3PlusBoxBot_axiom in Hp. subst p.
      apply logic_identity. exact GLPoint3_classical_logic.
    + exact (logic_under_mp GLPoint3_classical_logic IHpq IHp).
    + pose proof
        (@normal_proves_substitute GLPoint3_schema
          GLPoint3_schema_substitution_closed nat nat sigma
          (Imp (box_iter n Bottom) p) IH) as Hsub.
      change
        (GLPoint3_proves
          (Imp (substitute sigma (box_iter n Bottom))
               (substitute sigma p))) in Hsub.
      rewrite substitute_GLPoint3PlusBoxBot_axiom in Hsub.
      exact Hsub.
    + pose proof
        (logic_box_regularity GLPoint3_normal_logic IH) as Hbox.
      pose proof (GLPoint3_proves_boxbot_successor n) as Hstep.
      change
        (@GLPoint3_proves nat
          (Imp (box_iter n Bottom) (Box (box_iter n Bottom)))) in Hstep.
      eapply logic_imp_trans; [exact GLPoint3_classical_logic | exact Hstep |].
      exact Hbox.
  - intro Hp. simpl. eapply LSN_mp.
    + apply LSN_mem_left. exact Hp.
    + apply LSN_mem_right. reflexivity.
Qed.

(** * Monotonicity and strictness *)

Theorem GLPoint3PlusBoxBot_weakerThan_succ :
  forall n,
    logic_subset (GLPoint3PlusBoxBot (Some (S n)))
                 (GLPoint3PlusBoxBot (Some n)).
Proof.
  intros n p Hp.
  apply (proj2
    (iff_provable_GLPoint3PlusBoxBot_provable_GLPoint3 n p)).
  eapply logic_imp_trans; [exact GLPoint3_classical_logic | |].
  - exact (GLPoint3_proves_boxbot_successor n).
  - now apply (proj1
      (iff_provable_GLPoint3PlusBoxBot_provable_GLPoint3 (S n) p)).
Qed.

Theorem GLPoint3PlusBoxBot_weakerThan_add :
  forall n k,
    logic_subset (GLPoint3PlusBoxBot (Some (n + k)))
                 (GLPoint3PlusBoxBot (Some n)).
Proof.
  intros n k. induction k as [|k IH].
  - rewrite Nat.add_0_r. intros p Hp; exact Hp.
  - intros p Hp. replace (n + S k) with (S (n + k)) in Hp by lia.
    apply IH. exact (@GLPoint3PlusBoxBot_weakerThan_succ (n + k) p Hp).
Qed.

Theorem GLPoint3PlusBoxBot_weakerThan_lt :
  forall n m,
    n < m ->
    logic_subset (GLPoint3PlusBoxBot (Some m))
                 (GLPoint3PlusBoxBot (Some n)).
Proof.
  intros n m Hlt p Hp. replace m with (n + (m - n)) in Hp by lia.
  exact (@GLPoint3PlusBoxBot_weakerThan_add n (m - n) p Hp).
Qed.

Definition GLPoint3PlusBoxBot_weaker_than_succ :=
  GLPoint3PlusBoxBot_weakerThan_succ.
Definition GLPoint3PlusBoxBot_weaker_than_add :=
  GLPoint3PlusBoxBot_weakerThan_add.
Definition GLPoint3PlusBoxBot_weaker_than_lt :=
  GLPoint3PlusBoxBot_weakerThan_lt.

Lemma fin_lt_connected :
  forall n, frame_connected (fin_lt_frame n).
Proof.
  intros n [x Hx] [y Hy]; simpl.
  destruct (Nat.lt_trichotomy x y) as [Hxy | [Hxy | Hyx]].
  - now left.
  - right; left. subst y. f_equal. apply proof_irrelevance.
  - now right; right.
Qed.

Definition fin_lt_zero (n : nat) : World (fin_lt_frame (S n)) :=
  exist _ 0 (Nat.lt_0_succ n).

Arguments fin_lt_zero n : clear implicits.

Definition fin_lt_point (n k : nat) (Hk : k <= n) :
    World (fin_lt_frame (S n)) :=
  exist _ k (proj2 (Nat.lt_succ_r k n) Hk).

Arguments fin_lt_point n k Hk : clear implicits.

Lemma fin_lt_path_by_distance :
  forall n len (x y : World (fin_lt_frame (S n))),
    proj1_sig x + len = proj1_sig y ->
    rel_iter (Rel (fin_lt_frame (S n))) len x y.
Proof.
  intros n len. induction len as [|len IH]; intros x y Hdistance; simpl.
  - apply eq_sig_hprop.
    + intros z pz qz. apply proof_irrelevance.
    + simpl in Hdistance. lia.
  - assert (Hnext : S (proj1_sig x) < S n).
    { destruct y as [y Hy]; simpl in *. lia. }
    pose (z :=
      (exist _ (S (proj1_sig x)) Hnext : World (fin_lt_frame (S n)))).
    exists z; split.
    + unfold z; simpl. lia.
    + apply IH. unfold z; simpl in *. lia.
Qed.

Lemma fin_lt_zero_to_last_path :
  forall n,
    rel_iter (Rel (fin_lt_frame (S n))) n
      (fin_lt_zero n) (fin_lt_point n n (Nat.le_refl n)).
Proof.
  intro n. apply fin_lt_path_by_distance. simpl. lia.
Qed.

Lemma fin_lt_box_iter_bottom_fails_at_zero :
  forall n (V : valuation nat (fin_lt_frame (S n))),
    ~ satisfies (fin_lt_frame (S n)) V (fin_lt_zero n)
        (box_iter n Bottom).
Proof.
  intros n V Hbox.
  pose proof (proj1 (@satisfies_box_iter nat (fin_lt_frame (S n)) V n
    (fin_lt_zero n) Bottom) Hbox
    (fin_lt_point n n (Nat.le_refl n))
    (fin_lt_zero_to_last_path n)) as Hbottom.
  exact Hbottom.
Qed.

Theorem GLPoint3PlusBoxBot_strictlyWeakerThan_GLPoint3 :
  forall n,
    normal_strictly_weaker (@GLPoint3_proves nat)
      (GLPoint3PlusBoxBot (Some n)).
Proof.
  intro n; split.
  - exact (GLPoint3_weaker_than_GLPoint3PlusBoxBot (Some n)).
  - exists (box_iter n Bottom); split.
    + apply GLPoint3PlusBoxBot_boxbot.
    + intro Hprovable.
      assert (Hframe : GLPoint3_finite_frame_class (fin_lt_frame (S n))).
      {
        repeat split.
        - apply fin_lt_finite.
        - apply fin_lt_transitive.
        - apply fin_lt_irreflexive.
        - apply fin_lt_connected.
      }
      pose proof (@GLPoint3_finite_sound _ Hprovable
        (fin_lt_frame (S n)) Hframe) as Hvalid.
      exact (@fin_lt_box_iter_bottom_fails_at_zero n
        (fun _ _ => True) (Hvalid (fun _ _ => True) (fin_lt_zero n))).
Qed.

Definition GLPoint3PlusBoxBot_strictly_weaker_than_GLPoint3 :=
  GLPoint3PlusBoxBot_strictlyWeakerThan_GLPoint3.

(** * The first two finite stages *)

Theorem eq_GLPoint3PlusBoxBot_0_full :
  GLPoint3PlusBoxBot (Some 0) = @logic_full nat.
Proof.
  apply (proj2 (logic_eq_iff_equiv _ _)); split.
  - apply logic_weaker_full.
  - intros p _. simpl. eapply LSN_mp.
    + apply LSN_mem_left, K_weaker_than_GLPoint3, K_proves_normal.
      apply K_proves_ex_falso.
    + apply LSN_mem_right. reflexivity.
Qed.

Theorem eq_GLPoint3PlusBoxBot_1_Ver :
  GLPoint3PlusBoxBot (Some 1) = @Boxdot.Ver_proves nat.
Proof.
  apply (proj2 (logic_eq_iff_equiv _ _)); split.
  - intros p Hp. simpl in Hp. induction Hp.
    + now apply GLPoint3_weaker_than_Ver.
    + unfold GLPoint3PlusBoxBot_axiom in H. subst p.
      simpl. apply Np_extra. exists Bottom. reflexivity.
    + eapply Np_mp; eauto.
    + now apply normal_proves_substitute; [exact schema_Ver_substitution_closed |].
    + now apply Np_nec.
  - intros p Hp. induction Hp.
    + apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 1))).
      apply Kp_imply_K.
    + apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 1))).
      apply Kp_imply_S.
    + apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 1))).
      apply Kp_elim_contra.
    + apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 1))).
      apply Kp_modal_K.
    + destruct H as [q ->].
      change (GLPoint3PlusBoxBot (Some 1) (box_iter 1 q)).
      apply GLPoint3PlusBoxBot_axiomNVer.
    + eapply LSN_mp; eauto.
    + now apply LSN_nec.
Qed.

(** * GL.2 as Loeb plus WeakPoint2 *)

Definition GLPoint2_schema : modal_axiom_schema :=
  schema_union schema_L schema_WeakPoint2.

Definition GLPoint2_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves GLPoint2_schema AtomType.

Lemma GLPoint2_schema_substitution_closed :
  schema_substitution_closed GLPoint2_schema.
Proof.
  apply schema_union_substitution_closed.
  - exact schema_L_substitution_closed.
  - exact schema_WeakPoint2_substitution_closed.
Qed.

Definition GLPoint2_normal_logic : normal_logic (@GLPoint2_proves nat) :=
  @normal_proves_logic_is_normal
    GLPoint2_schema GLPoint2_schema_substitution_closed.

Definition GLPoint2_classical_logic :
    classical_logic (@GLPoint2_proves nat) :=
  quasi_classical (normal_quasi GLPoint2_normal_logic).

Lemma GL_weaker_than_GLPoint2 :
  forall (AtomType : Type) (p : formula AtomType),
    GL_proves p -> GLPoint2_proves p.
Proof.
  intros AtomType p Hp. eapply normal_proves_weaken; [| exact Hp].
  intros A q Hq. now left.
Qed.

Lemma GLPoint2_proves_L :
  forall p : formula nat, GLPoint2_proves (L p).
Proof. intro p; apply GL_weaker_than_GLPoint2, GL_proves_L. Qed.

Lemma GLPoint2_proves_Four :
  forall p : formula nat, GLPoint2_proves (Four p).
Proof. intro p; apply GL_weaker_than_GLPoint2, GL_proves_Four. Qed.

Lemma GLPoint2_proves_WeakPoint2 :
  forall p q : formula nat, GLPoint2_proves (WeakPoint2 p q).
Proof.
  intros p q. apply Np_extra. right. exists p, q. reflexivity.
Qed.

(** Foundation [GLPoint2.provable_boxboxbot]. *)
Theorem GLPoint2_provable_boxboxbot :
  GLPoint2_proves (box_iter 2 (@Bottom nat)).
Proof.
  set (a := Box (Neg (Box (@Bottom nat)))).
  set (c := Box (Box (@Bottom nat))).
  assert (Hleft : GLPoint2_proves (Imp a c)).
  {
    unfold a, c.
    eapply logic_imp_trans; [exact GLPoint2_classical_logic | |].
    - exact (GLPoint2_proves_L Bottom).
    - exact (GLPoint2_proves_Four Bottom).
  }
  assert (Hdia_step :
    @GLPoint2_proves nat
      (Imp (Dia (Box Bottom))
        (Dia (And (Box (Neg (Box Bottom))) (Box Bottom))))).
  {
    apply normal_proves_of_K_valid.
    intros F V w Hdia.
    destruct (satisfies_dia_elim Hdia) as [y [Rwy Hybox]].
    apply satisfies_dia_intro. exists y; split; [exact Rwy |].
    apply (proj2 (@satisfies_and nat F V y
      (Box (Neg (Box Bottom))) (Box Bottom))). split.
    - intros z Ryz Hzbox. exact (Hybox z Ryz).
    - exact Hybox.
  }
  assert (Hweak :
    @GLPoint2_proves nat
      (Imp (Dia (And (Box (Neg (Box Bottom))) (Box Bottom)))
        (Box (Or (Dia (Neg (Box Bottom))) (Box Bottom))))).
  { exact (GLPoint2_proves_WeakPoint2 (Neg (Box Bottom)) (Box Bottom)). }
  assert (Hrewrite :
    @GLPoint2_proves nat
      (Imp (Box (Or (Dia (Neg (Box Bottom))) (Box Bottom)))
        (Box (Imp (Box (Box Bottom)) (Box Bottom))))).
  {
    apply normal_proves_of_K_valid.
    intros F V w Hbox y Rwy Hboxbox.
    specialize (Hbox y Rwy).
    destruct (proj1 (@satisfies_or nat F V y
      (Dia (Neg (Box Bottom))) (Box Bottom)) Hbox) as [Hdia | Hboxbot].
    - destruct (satisfies_dia_elim Hdia) as [z [Ryz Hzneg]].
      exfalso. apply (proj1 (@satisfies_neg nat F V z (Box Bottom)) Hzneg).
      exact (Hboxbox z Ryz).
    - exact Hboxbot.
  }
  assert (Hright : GLPoint2_proves (Imp (Neg a) c)).
  {
    unfold a, c.
    eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hdia_step |].
    eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hweak |].
    eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hrewrite |].
    exact (GLPoint2_proves_L (Box Bottom)).
  }
  unfold c in Hleft, Hright.
  change (@GLPoint2_proves nat (Box (Box Bottom))).
  eapply normal_proves_K_rule2; [| exact Hleft | exact Hright].
  intros F V w H1 H2.
  unfold a in *. simpl in *. tauto.
Qed.

(** The GL.2 fixed-point consequence used in Foundation's WeakPoint3
    derivation. *)
Lemma GLPoint2_provable_dia_boxdot_implies_box :
  forall p : formula nat,
    GLPoint2_proves (Imp (Dia (Boxdot p)) (Box p)).
Proof.
  intro p.
  set (a := Boxdot p).
  set (inner := And a (Box (Neg a))).
  set (complex :=
    And p (And (Box p) (And (Box (Box p)) (Box (Neg a))))).

  assert (Hfirst :
    @GLPoint2_proves nat (Imp (Dia a) (Dia inner))).
  {
    eapply (@normal_proves_K_rule1 GLPoint2_schema
      (L (Neg a)) (Imp (Dia a) (Dia inner))).
    - intros F V w Hloeb Hdia.
      apply satisfies_dia_intro. apply NNPP. intro Hnone.
      assert (Hante :
        satisfies F V w (Box (Imp (Box (Neg a)) (Neg a)))).
      {
        intros y Rwy Hboxnega.
        apply (proj2 (@satisfies_neg nat F V y a)). intro Ha.
        apply Hnone. exists y; split; [exact Rwy |].
        apply (proj2 (@satisfies_and nat F V y a (Box (Neg a)))).
        now split.
      }
      unfold L, Loeb in Hloeb.
      pose proof (Hloeb Hante) as Hboxnega.
      destruct (satisfies_dia_elim Hdia) as [y [Rwy Ha]].
      exact ((proj1 (@satisfies_neg nat F V y a)
        (Hboxnega y Rwy)) Ha).
    - unfold a. exact (GLPoint2_proves_L (Neg (Boxdot p))).
  }

  assert (Hinner :
    @GLPoint2_proves nat (Imp inner complex)).
  {
    eapply (@normal_proves_K_rule1 GLPoint2_schema
      (Four p) (Imp inner complex)).
    - intros F V w Hfour Hinner.
      unfold inner, complex, a in *.
      destruct (proj1 (@satisfies_and nat F V w
        (Boxdot p) (Box (Neg (Boxdot p)))) Hinner)
        as [Hboxdot Hboxneg].
      destruct (proj1 (@satisfies_and nat F V w p (Box p)) Hboxdot)
        as [Hp Hboxp].
      apply (proj2 (@satisfies_and nat F V w p
        (And (Box p) (And (Box (Box p)) (Box (Neg (Boxdot p))))))).
      split; [exact Hp |].
      apply (proj2 (@satisfies_and nat F V w (Box p)
        (And (Box (Box p)) (Box (Neg (Boxdot p)))))).
      split; [exact Hboxp |].
      apply (proj2 (@satisfies_and nat F V w (Box (Box p))
        (Box (Neg (Boxdot p))))). split.
      + exact (Hfour Hboxp).
      + exact Hboxneg.
    - exact (GLPoint2_proves_Four p).
  }

  assert (Hsecond :
    @GLPoint2_proves nat (Imp (Dia inner) (Dia complex))).
  {
    eapply (@normal_proves_K_rule1 GLPoint2_schema
      (Box (Imp inner complex)) (Imp (Dia inner) (Dia complex))).
    - intros F V w Hboximp Hdia.
      destruct (satisfies_dia_elim Hdia) as [y [Rwy Hy]].
      apply satisfies_dia_intro. exists y; split; [exact Rwy |].
      exact (Hboximp y Rwy Hy).
    - exact (Np_nec Hinner).
  }

  assert (Hthird :
    @GLPoint2_proves nat
      (Imp (Dia complex) (Dia (And (Box Bottom) p)))).
  {
    apply normal_proves_of_K_valid.
    intros F V w Hdia.
    destruct (satisfies_dia_elim Hdia) as [y [Rwy Hcomplex]].
    unfold complex, a in Hcomplex.
    destruct (proj1 (@satisfies_and nat F V y p
      (And (Box p) (And (Box (Box p)) (Box (Neg (Boxdot p))))))
      Hcomplex) as [Hp Hrest].
    destruct (proj1 (@satisfies_and nat F V y (Box p)
      (And (Box (Box p)) (Box (Neg (Boxdot p))))) Hrest)
      as [Hboxp Hrest2].
    destruct (proj1 (@satisfies_and nat F V y (Box (Box p))
      (Box (Neg (Boxdot p)))) Hrest2) as [Hboxboxp Hboxneg].
    apply satisfies_dia_intro. exists y; split; [exact Rwy |].
    apply (proj2 (@satisfies_and nat F V y (Box Bottom) p)). split.
    - intros z Ryz.
      pose proof (Hboxp z Ryz) as Hpz.
      pose proof (Hboxboxp z Ryz) as Hboxpz.
      pose proof (proj1 (@satisfies_neg nat F V z (Boxdot p))
        (Hboxneg z Ryz)) as Hnotboxdot.
      exfalso. apply Hnotboxdot.
      apply (proj2 (@satisfies_and nat F V z p (Box p))). now split.
    - exact Hp.
  }

  assert (Hweak :
    @GLPoint2_proves nat
      (Imp (Dia (And (Box Bottom) p))
        (Box (Or (Dia Bottom) p)))).
  { exact (GLPoint2_proves_WeakPoint2 Bottom p). }

  assert (Hcleanup :
    @GLPoint2_proves nat
      (Imp (Box (Or (Dia Bottom) p)) (Box p))).
  {
    apply normal_proves_of_K_valid.
    intros F V w Hbox y Rwy.
    destruct (proj1 (@satisfies_or nat F V y (Dia Bottom) p)
      (Hbox y Rwy)) as [Hdia | Hp]; [| exact Hp].
    destruct (satisfies_dia_elim Hdia) as [z [_ Hbottom]].
    exfalso. exact Hbottom.
  }

  unfold a in Hfirst; unfold inner in Hfirst, Hsecond.
  unfold complex in Hsecond, Hthird.
  eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hfirst |].
  eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hsecond |].
  eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hthird |].
  eapply logic_imp_trans; [exact GLPoint2_classical_logic | exact Hweak |].
  exact Hcleanup.
Qed.

(** Foundation [GLPoint2.provable_axiomWeakPoint3], strengthened from the
    two displayed atoms to arbitrary formulas. *)
Theorem GLPoint2_provable_WeakPoint3 :
  forall p q : formula nat,
    GLPoint2_proves (WeakPoint3 p q).
Proof.
  intros p q.
  set (r := Imp (Boxdot q) p).
  set (left := Box (Imp (Boxdot p) q)).
  assert (Hcounter :
    @GLPoint2_proves nat (Imp (Neg left) (Dia (Boxdot r)))).
  {
    apply normal_proves_of_K_valid.
    intros F V w Hnotleft.
    apply satisfies_dia_intro. apply NNPP. intro Hnone.
    apply (proj1 (@satisfies_neg nat F V w left) Hnotleft).
    unfold left. intros y Rwy Hboxdotp.
    apply NNPP. intro Hnotq.
    apply Hnone. exists y; split; [exact Rwy |].
    unfold r.
    apply (proj2 (@satisfies_and nat F V y
      (Imp (Boxdot q) p) (Box (Imp (Boxdot q) p)))).
    destruct (proj1 (@satisfies_and nat F V y p (Box p)) Hboxdotp)
      as [Hp Hboxp]. split.
    - intro Hignored. exact Hp.
    - intros z Ryz Hignored. exact (Hboxp z Ryz).
  }
  pose proof (GLPoint2_provable_dia_boxdot_implies_box r) as Hfixed.
  pose proof (logic_imp_trans GLPoint2_classical_logic Hcounter Hfixed)
    as Hresult.
  unfold WeakPoint3, Or. unfold left, r in Hresult.
  exact Hresult.
Qed.

(** * The exact identification of stage two *)

Theorem GLPoint3PlusBoxBot_provable_WeakPoint2_in_2 :
  forall p q : formula nat,
    GLPoint3PlusBoxBot (Some 2) (WeakPoint2 p q).
Proof.
  intros p q.
  apply (proj2
    (iff_provable_GLPoint3PlusBoxBot_provable_GLPoint3 2
      (WeakPoint2 p q))).
  apply GLPoint3_finite_complete.
  intros F [Hfinite [Htrans [Hirr Hconnected]]] V x Hbox2 Hdia.
  destruct (satisfies_dia_elim Hdia) as [y [Rxy Hy]].
  destruct (proj1 (@satisfies_and nat F V y (Box p) q) Hy)
    as [_ Hqy].
  intros z Rxz.
  apply (proj2 (@satisfies_or nat F V z (Dia p) q)).
  destruct (Hconnected y z) as [Ryz | [Hyz | Rzy]].
  - exfalso. exact (Hbox2 y Rxy z Ryz).
  - right. now subst z.
  - exfalso. exact (Hbox2 z Rxz y Rzy).
Qed.

Theorem GLPoint2_weaker_than_GLPoint3PlusBoxBot_2 :
  logic_subset (@GLPoint2_proves nat)
    (GLPoint3PlusBoxBot (Some 2)).
Proof.
  intros p Hp. induction Hp.
  - apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 2))).
    apply Kp_imply_K.
  - apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 2))).
    apply Kp_imply_S.
  - apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 2))).
    apply Kp_elim_contra.
  - apply (normal_logic_contains_K (GLPoint3PlusBoxBot_normal (Some 2))).
    apply Kp_modal_K.
  - destruct H as [HL | Hweak].
    + destruct HL as [q ->]. apply LSN_mem_left.
      apply GL_weaker_than_GLPoint3, GL_proves_L.
    + destruct Hweak as [q [r ->]].
      apply GLPoint3PlusBoxBot_provable_WeakPoint2_in_2.
  - eapply LSN_mp; eauto.
  - now apply LSN_nec.
Qed.

Theorem GLPoint3_weaker_than_GLPoint2 :
  forall p : formula nat, GLPoint3_proves p -> GLPoint2_proves p.
Proof.
  intros p Hp. induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [HL | Hweak].
    + apply Np_extra. now left.
    + destruct Hweak as [q [r ->]].
      apply GLPoint2_provable_WeakPoint3.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Theorem GLPoint3PlusBoxBot_2_weaker_than_GLPoint2 :
  logic_subset (GLPoint3PlusBoxBot (Some 2))
    (@GLPoint2_proves nat).
Proof.
  intros p Hp. simpl in Hp. induction Hp.
  - now apply GLPoint3_weaker_than_GLPoint2.
  - unfold GLPoint3PlusBoxBot_axiom in H. subst p.
    exact GLPoint2_provable_boxboxbot.
  - eapply Np_mp; eauto.
  - now apply normal_proves_substitute;
      [exact GLPoint2_schema_substitution_closed |].
  - now apply Np_nec.
Qed.

Theorem eq_GLPoint3PlusBoxBot_2_GLPoint2 :
  GLPoint3PlusBoxBot (Some 2) = @GLPoint2_proves nat.
Proof.
  apply (proj2 (logic_eq_iff_equiv _ _)); split.
  - exact GLPoint3PlusBoxBot_2_weaker_than_GLPoint2.
  - exact GLPoint2_weaker_than_GLPoint3PlusBoxBot_2.
Qed.

(** Source-facing names retaining Foundation's [Oplus] spelling. *)
Definition GLPoint3OplusBoxBot := GLPoint3PlusBoxBot.
Definition GLPoint3OplusBoxBot_normal := GLPoint3PlusBoxBot_normal.
Definition GLPoint3_weaker_than_GLPoint3OplusBoxBot :=
  GLPoint3_weaker_than_GLPoint3PlusBoxBot.
Definition GLPoint3OplusBoxBot_boxbot := GLPoint3PlusBoxBot_boxbot.
Definition GLPoint3OplusBoxBot_axiomNVer :=
  GLPoint3PlusBoxBot_axiomNVer.
Definition eq_GLPoint3OplusBoxBot_omega_GLPoint3 :=
  eq_GLPoint3PlusBoxBot_omega_GLPoint3.
Definition GLPoint3OplusBoxBot_weakerThan_succ :=
  GLPoint3PlusBoxBot_weakerThan_succ.
Definition GLPoint3OplusBoxBot_weakerThan_add :=
  GLPoint3PlusBoxBot_weakerThan_add.
Definition GLPoint3OplusBoxBot_weakerThan_lt :=
  GLPoint3PlusBoxBot_weakerThan_lt.
Definition GLPoint3OplusBoxBot_strictlyWeakerThan_GLPoint3 :=
  GLPoint3PlusBoxBot_strictlyWeakerThan_GLPoint3.
Definition eq_GLPoint3OplusBoxBot_0_Univ :=
  eq_GLPoint3PlusBoxBot_0_full.
Definition eq_GLPoint3OplusBoxBot_1_Ver :=
  eq_GLPoint3PlusBoxBot_1_Ver.
Definition GLPoint3OplusBoxBot_provable_weakPoint2_in_2 :=
  GLPoint3PlusBoxBot_provable_WeakPoint2_in_2.
Definition GLPoint2_provable_axiomWeakPoint3 :=
  GLPoint2_provable_WeakPoint3.
Definition eq_GLPoint3OplusBoxBot_2_GLPoint2 :=
  eq_GLPoint3PlusBoxBot_2_GLPoint2.
