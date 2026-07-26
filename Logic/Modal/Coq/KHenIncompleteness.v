(**
  Kripke incompleteness of KHen.

  This module ports the proved surface of the pinned Foundation file
  [Modal/Kripke/Logic/KHen.lean].  The fixed Cresswell model is the same
  countable two-column model as in Foundation.  For the one place where the
  Lean proof uses finite/cofinite sets, we use the equivalent and more
  computationally transparent invariant that a truth set is eventually
  constantly true or eventually constantly false in both columns.

  No completeness theorem is used in the incompleteness proof.  Soundness on
  the single Cresswell model refutes Four in KHen, while the atomic
  Henkin/Loeb equivalence shows that every class of frames validating Henkin
  must validate Four.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Logic.Classical_Prop Logic.Classical_Pred_Type.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence Loeb HilbertKSoundness
  NormalHilbert LogicInfrastructure CanonicalExtensions GLGrzDerivations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The Hilbert system KHen *)

Definition schema_Hen : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = Hen q.

Definition KHen_proves {AtomType} : formula AtomType -> Prop :=
  @normal_proves schema_Hen AtomType.

Lemma schema_Hen_substitution_closed :
  schema_substitution_closed schema_Hen.
Proof.
  intros A B sigma p [q ->].
  exists (substitute sigma q). reflexivity.
Qed.

Theorem KHen_proves_substitute :
  forall (A B : Type) (sigma : A -> formula B) (p : formula A),
    @KHen_proves A p ->
    @KHen_proves B (substitute sigma p).
Proof.
  intros A B sigma p Hp.
  exact (@normal_proves_substitute schema_Hen
    schema_Hen_substitution_closed A B sigma p Hp).
Qed.

Definition KHen_normal_logic : normal_logic (@KHen_proves nat) :=
  @normal_proves_logic_is_normal schema_Hen
    schema_Hen_substitution_closed.

Definition KHen_classical_logic : classical_logic (@KHen_proves nat) :=
  quasi_classical (normal_quasi KHen_normal_logic).

Lemma KHen_proves_Hen :
  forall p : formula nat, KHen_proves (Hen p).
Proof. intro p. apply Np_extra. now exists p. Qed.

Lemma K_weaker_than_KHen :
  forall (AtomType : Type) (p : formula AtomType),
    K_normal_proves p -> KHen_proves p.
Proof. intros AtomType p. apply K_weaker_than_normal. Qed.

(** GL derives every Henkin instance, hence contains KHen. *)
Lemma KHen_weaker_than_GL :
  forall p : formula nat, KHen_proves p -> GL_proves p.
Proof.
  intros p Hp. induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - destruct H as [q ->]. now apply GL_proves_Hen.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

(** * Atomic Henkin/Loeb validity *)

Lemma valid_atomic_Hen_of_valid_atomic_Loeb :
  forall (F : frame) (a : nat),
    valid F (Loeb (Atom a)) -> valid F (Hen (Atom a)).
Proof.
  intros F a HL V x Hiff.
  pose proof (HL V x) as HLx.
  unfold Loeb in HLx; simpl in HLx.
  change (forall y, Rel F x y -> V a y).
  apply HLx.
  intros y Rxy Hbox.
  exact (proj1
    (proj1 (@satisfies_iff nat F V y
      (Box (Atom a)) (Atom a)) (Hiff y Rxy)) Hbox).
Qed.

Lemma valid_atomic_Loeb_of_valid_atomic_Hen :
  forall (F : frame) (a : nat),
    valid F (Hen (Atom a)) -> valid F (Loeb (Atom a)).
Proof.
  intros F a HH V x Hstep.
  pose (Vstar := (fun b w =>
    forall n, satisfies F V w (box_iter n (Atom b)))
    : valuation nat F).
  assert (Hfixed :
    satisfies F Vstar x (Box (Iff (Box (Atom a)) (Atom a)))).
  {
    intros y Rxy.
    apply (proj2 (@satisfies_iff nat F Vstar y
      (Box (Atom a)) (Atom a))).
    split.
    - intros Hbox n. destruct n as [|n].
      + apply (Hstep y Rxy). intros z Ryz.
        exact (Hbox z Ryz 0).
      + intros z Ryz. exact (Hbox z Ryz n).
    - intros Hall z Ryz n.
      exact (Hall (S n) z Ryz).
  }
  pose proof (HH Vstar x Hfixed) as Hboxstar.
  intros y Rxy. exact (Hboxstar y Rxy 0).
Qed.

Theorem valid_atomic_Loeb_iff_valid_atomic_Hen :
  forall (F : frame) (a : nat),
    valid F (Loeb (Atom a)) <-> valid F (Hen (Atom a)).
Proof.
  intros F a; split.
  - apply valid_atomic_Hen_of_valid_atomic_Loeb.
  - apply valid_atomic_Loeb_of_valid_atomic_Hen.
Qed.

Lemma valid_atomic_Four_of_valid_atomic_Loeb :
  forall F : frame,
    valid F (Loeb (Atom 0)) -> valid F (Four (Atom 0)).
Proof.
  intros F HL.
  apply valid_Four_of_transitive.
  now apply transitive_of_valid_Loeb_atom.
Qed.

Lemma valid_atomic_Four_of_valid_atomic_Hen :
  forall F : frame,
    valid F (Hen (Atom 0)) -> valid F (Four (Atom 0)).
Proof.
  intros F HH. apply valid_atomic_Four_of_valid_atomic_Loeb.
  now apply valid_atomic_Loeb_of_valid_atomic_Hen.
Qed.

(** * Cresswell's two-column frame and model *)

Definition cresswell_world : Type := nat * bool.

Definition cresswell_sharp (n : nat) : cresswell_world := (n, false).
Definition cresswell_flat (n : nat) : cresswell_world := (n, true).

Definition cresswell_rel (x y : cresswell_world) : Prop :=
  match snd x, snd y with
  | false, false => fst x <= S (fst y)
  | true, true => fst y < fst x
  | false, true => True
  | true, false => False
  end.

Definition cresswell_frame : frame :=
  {| World := cresswell_world; Rel := cresswell_rel |}.

Definition cresswell_valuation (AtomType : Type) :
    valuation AtomType cresswell_frame :=
  fun _ w => w <> cresswell_sharp 0.

Arguments cresswell_valuation AtomType _ _ : clear implicits.

Lemma cresswell_sharp_to_flat :
  forall n m, Rel cresswell_frame (cresswell_sharp n) (cresswell_flat m).
Proof. intros; constructor. Qed.

Lemma cresswell_not_flat_to_sharp :
  forall n m,
    ~ Rel cresswell_frame (cresswell_flat n) (cresswell_sharp m).
Proof. intros n m H. exact H. Qed.

Lemma cresswell_sharp_to_sharp :
  forall n m,
    Rel cresswell_frame (cresswell_sharp n) (cresswell_sharp m) <->
    n <= S m.
Proof. reflexivity. Qed.

Lemma cresswell_flat_to_flat :
  forall n m,
    Rel cresswell_frame (cresswell_flat n) (cresswell_flat m) <->
    m < n.
Proof. reflexivity. Qed.

Lemma cresswell_successor_of_flat :
  forall n x,
    Rel cresswell_frame (cresswell_flat n) x ->
    exists m, x = cresswell_flat m /\ m < n.
Proof.
  intros n [m b] H; destruct b.
  - exists m. split; [reflexivity | exact H].
  - exact (False_rect _ H).
Qed.

Lemma cresswell_rel_trichotomy :
  forall x y : World cresswell_frame,
    Rel cresswell_frame x y \/ x = y \/ Rel cresswell_frame y x.
Proof.
  intros [n b] [m c]; destruct b, c; simpl.
  - destruct (Nat.lt_trichotomy n m) as [H | [-> | H]]; auto; right; right; lia.
  - now right; right.
  - now left.
  - destruct (Nat.le_gt_cases n (S m)) as [H | H]; auto.
    right; right. change (m <= S n). lia.
Qed.

Lemma cresswell_not_satisfies_Four_at_two_sharp :
  forall a : nat,
    ~ satisfies cresswell_frame (cresswell_valuation nat)
        (cresswell_sharp 2) (Four (Atom a)).
Proof.
  intros a Hfour.
  assert (Hbox : satisfies cresswell_frame (cresswell_valuation nat)
    (cresswell_sharp 2) (Box (Atom a))).
  {
    intros [n b] R; destruct b; simpl in *.
    - discriminate.
    - change (2 <= S n) in R.
      intro Heq. injection Heq as Hn. subst n. lia.
  }
  pose proof (Hfour Hbox (cresswell_sharp 1) (le_n 2)) as Hbox1.
  pose proof (Hbox1 (cresswell_sharp 0) (le_n 1)) as Hzero.
  exact (Hzero eq_refl).
Qed.

Lemma cresswell_model_not_valid_Four :
  forall a : nat,
    ~ @model_valid nat cresswell_frame (cresswell_valuation nat)
        (Four (Atom a)).
Proof.
  intros a Hvalid.
  apply (@cresswell_not_satisfies_Four_at_two_sharp a).
  apply Hvalid.
Qed.

(** * Eventual truth-set classification *)

Definition cresswell_eventually_true {AtomType}
    (p : formula AtomType) : Prop :=
  exists N, forall n, N <= n ->
    satisfies cresswell_frame (cresswell_valuation AtomType)
      (cresswell_sharp n) p /\
    satisfies cresswell_frame (cresswell_valuation AtomType)
      (cresswell_flat n) p.

Definition cresswell_eventually_false {AtomType}
    (p : formula AtomType) : Prop :=
  exists N, forall n, N <= n ->
    ~ satisfies cresswell_frame (cresswell_valuation AtomType)
        (cresswell_sharp n) p /\
    ~ satisfies cresswell_frame (cresswell_valuation AtomType)
        (cresswell_flat n) p.

Lemma cresswell_eventually_true_or_false :
  forall (AtomType : Type) (p : formula AtomType),
    cresswell_eventually_true p \/ cresswell_eventually_false p.
Proof.
  intros AtomType p; induction p as [a | | p IHp q IHq | p IHp].
  - left. exists 1. intros n Hn. split; simpl.
    + intro Heq. inversion Heq. lia.
    + discriminate.
  - right. exists 0. intros n _. simpl. tauto.
  - destruct IHp as [[Np Hp] | [Np Hp]];
      destruct IHq as [[Nq Hq] | [Nq Hq]].
    + left. exists (Nat.max Np Nq). intros n Hn. split; intros _;
        apply Hq; lia.
    + right. exists (Nat.max Np Nq). intros n Hn.
      destruct (Hp n) as [Hps Hpf]; [lia |].
      destruct (Hq n) as [Hqs Hqf]; [lia |].
      split; intro Himp.
      * exact (Hqs (Himp Hps)).
      * exact (Hqf (Himp Hpf)).
    + left. exists Np. intros n Hn. split; intro Hante.
      * exfalso. exact ((proj1 (Hp n Hn)) Hante).
      * exfalso. exact ((proj2 (Hp n Hn)) Hante).
    + left. exists Np. intros n Hn. split; intro Hante.
      * exfalso. exact ((proj1 (Hp n Hn)) Hante).
      * exfalso. exact ((proj2 (Hp n Hn)) Hante).
  - destruct (classic (forall n,
      satisfies cresswell_frame (cresswell_valuation AtomType)
        (cresswell_flat n) p)) as [Hall | Hnotall].
    + destruct IHp as [[N Hp] | [N Hp]].
      * left. exists (S N). intros n Hn. split.
        -- intros [m b] R; destruct b; simpl in *.
           ++ apply Hall.
           ++ change (n <= S m) in R.
              destruct (Hp m) as [Hsharp _]; [lia | exact Hsharp].
        -- intros [m b] R; destruct b; simpl in *.
           ++ apply Hall.
           ++ exact (False_rect _ R).
      * exfalso.
        destruct (Hp N (le_n N)) as [_ Hflat].
        exact (Hflat (Hall N)).
    + right.
      apply not_all_ex_not in Hnotall.
      destruct Hnotall as [k Hk].
      exists (S k). intros n Hn. split; intro Hbox.
      * exact (Hk (Hbox (cresswell_flat k)
          (cresswell_sharp_to_flat n k))).
      * exact (Hk (Hbox (cresswell_flat k)
          (Nat.lt_le_trans k (S k) n (Nat.lt_succ_diag_r k) Hn))).
Qed.

(** Elementary bounded-search forms of Foundation's maximum-sharp and
    minimum-flat lemmas. *)
Lemma eventually_true_has_last_counterexample :
  forall (P : nat -> Prop) N,
    (forall n, N <= n -> P n) ->
    (exists n, ~ P n) ->
    exists k, ~ P k /\ forall m, k < m -> P m.
Proof.
  intros P N; induction N as [|N IH]; intros Htail [k Hk].
  - exfalso. exact (Hk (Htail k (Nat.le_0_l k))).
  - destruct (classic (P N)) as [HPN | HnotN].
    + apply IH.
      * intros n HNn. destruct (Nat.eq_dec n N) as [-> | Hne]; auto.
        apply Htail. lia.
      * now exists k.
    + exists N. split; [exact HnotN |].
      intros m HNm. apply Htail. lia.
Qed.

Lemma bounded_counterexample_has_first :
  forall (P : nat -> Prop) N,
    (exists n, n <= N /\ ~ P n) ->
    exists k, ~ P k /\ forall m, m < k -> P m.
Proof.
  intros P N; induction N as [|N IH]; intros Hcounter.
  - destruct Hcounter as [n [Hn Hnot]].
    assert (n = 0) by lia. subst n.
    exists 0. split; [exact Hnot | lia].
  - destruct (classic (exists n, n <= N /\ ~ P n)) as [Hold | Hnone].
    + now apply IH.
    + assert (Hall : forall m, m <= N -> P m).
      { intros m Hm. apply NNPP. intro Hnot.
        apply Hnone. exists m. auto. }
      destruct Hcounter as [n [Hn Hnot]].
      assert (n = S N) by (apply NNPP; intro Hne; apply Hnot, Hall; lia).
      subst n. exists (S N). split; [exact Hnot |].
      intros m Hm. apply Hall. lia.
Qed.

Lemma counterexample_has_first :
  forall P : nat -> Prop,
    (exists n, ~ P n) ->
    exists k, ~ P k /\ forall m, m < k -> P m.
Proof.
  intros P [N HN]. apply (@bounded_counterexample_has_first P N).
  exists N. auto.
Qed.

(** * Henkin validity in the Cresswell model *)

Theorem cresswell_model_valid_Hen :
  forall (AtomType : Type) (p : formula AtomType),
    @model_valid AtomType cresswell_frame
      (cresswell_valuation AtomType) (Hen p).
Proof.
  intros AtomType p x.
  destruct (classic (forall n,
    satisfies cresswell_frame (cresswell_valuation AtomType)
      (cresswell_flat n) p)) as [Hallflat | Hnotallflat].
  - destruct (cresswell_eventually_true_or_false p)
      as [[N Htail] | [N Htail]].
    + destruct (classic (forall w,
        satisfies cresswell_frame (cresswell_valuation AtomType) w p))
        as [Hall | Hnotall].
      * intros _. intros y _. apply Hall.
      * apply not_all_ex_not in Hnotall.
        assert (Hsharp_counter : exists n,
          ~ satisfies cresswell_frame (cresswell_valuation AtomType)
              (cresswell_sharp n) p).
        {
          destruct Hnotall as [[n b] Hfail]. destruct b.
          - exfalso. now apply Hfail, Hallflat.
          - now exists n.
        }
        destruct (@eventually_true_has_last_counterexample
          (fun n => satisfies cresswell_frame
            (cresswell_valuation AtomType) (cresswell_sharp n) p)
          N (fun n Hn => proj1 (Htail n Hn)) Hsharp_counter)
          as [k [Hk Hafter]].
        destruct x as [m b]; destruct b.
        -- intros _. intros y Rmy.
           destruct (cresswell_successor_of_flat Rmy) as [j [-> _]].
           apply Hallflat.
        -- destruct (Nat.le_gt_cases (S (S k)) m) as [Hfar | Hnear].
           ++ intros _. intros [j c] R; destruct c; simpl in *.
              ** apply Hallflat.
              ** change (m <= S j) in R.
                 apply Hafter. lia.
           ++ intro Hante.
              exfalso.
              assert (Rnear : Rel cresswell_frame
                (cresswell_sharp m) (cresswell_sharp (S k))).
              { change (m <= S (S k)). lia. }
              pose proof (Hante (cresswell_sharp (S k)) Rnear) as Hiff.
              apply (proj1 (@satisfies_iff AtomType cresswell_frame
                (cresswell_valuation AtomType) (cresswell_sharp (S k))
                (Box p) p)) in Hiff.
              assert (HpSk : satisfies cresswell_frame
                (cresswell_valuation AtomType) (cresswell_sharp (S k)) p).
              { apply Hafter. lia. }
              pose proof (proj2 Hiff HpSk) as Hbox.
              apply Hk. exact (Hbox (cresswell_sharp k) (le_n (S k))).
    + exfalso.
      destruct (Htail N (le_n N)) as [_ Hflat].
      exact (Hflat (Hallflat N)).
  - apply not_all_ex_not in Hnotallflat.
    destruct (@counterexample_has_first
      (fun n => satisfies cresswell_frame
        (cresswell_valuation AtomType) (cresswell_flat n) p)
      Hnotallflat) as [k [Hk Hbefore]].
    assert (Hboxk : satisfies cresswell_frame
      (cresswell_valuation AtomType) (cresswell_flat k) (Box p)).
    {
      intros y Rky.
      destruct (cresswell_successor_of_flat Rky) as [j [-> Hj]].
      now apply Hbefore.
    }
    assert (Hnotiffk : ~ satisfies cresswell_frame
      (cresswell_valuation AtomType) (cresswell_flat k)
      (Iff (Box p) p)).
    {
      intro Hiff.
      apply (proj1 (@satisfies_iff AtomType cresswell_frame
        (cresswell_valuation AtomType) (cresswell_flat k)
        (Box p) p)) in Hiff.
      exact (Hk (proj1 Hiff Hboxk)).
    }
    destruct x as [m b]; destruct b.
    + destruct (Nat.le_gt_cases m k) as [Hmk | Hkm].
      * intros _. intros y Rmy.
        destruct (cresswell_successor_of_flat Rmy) as [j [-> Hj]].
        apply Hbefore. lia.
      * intro Hante. exfalso.
        exact (Hnotiffk (Hante (cresswell_flat k) Hkm)).
    + intro Hante. exfalso.
      exact (Hnotiffk (Hante (cresswell_flat k)
        (cresswell_sharp_to_flat m k))).
Qed.

(** The fixed-model soundness theorem used to refute Four. *)
Theorem KHen_proves_valid_on_cresswell_model :
  forall p : formula nat,
    KHen_proves p ->
    @model_valid nat cresswell_frame (cresswell_valuation nat) p.
Proof.
  intros p Hp. induction Hp.
  - intros w; apply valid_Hilbert_imply_K.
  - intros w; apply valid_Hilbert_imply_S.
  - intros w; apply valid_Hilbert_elim_contra.
  - intros w; apply valid_K.
  - destruct H as [q ->]. now apply cresswell_model_valid_Hen.
  - intros w. eapply IHHp1; eauto. apply IHHp2.
  - intros w u Rwu. apply IHHp.
Qed.

Theorem KHen_unprovable_atomic_Four :
  forall a : nat, ~ KHen_proves (Four (Atom a)).
Proof.
  intros a Hfour.
  apply (@cresswell_model_not_valid_Four a).
  now apply KHen_proves_valid_on_cresswell_model.
Qed.

(** * Kripke incompleteness and strict hierarchy *)

Theorem KHen_Kripke_incomplete :
  ~ exists C : frame -> Prop,
      forall p : formula nat,
        KHen_proves p <-> normal_valid_on_class C p.
Proof.
  intros [C Hcharacterizes].
  assert (HHen : normal_valid_on_class C (Hen (Atom 0))).
  {
    apply (proj1 (Hcharacterizes (Hen (Atom 0)))).
    apply KHen_proves_Hen.
  }
  assert (HFour : normal_valid_on_class C (Four (Atom 0))).
  {
    intros F HF. apply valid_atomic_Four_of_valid_atomic_Hen.
    exact (HHen F HF).
  }
  apply (@KHen_unprovable_atomic_Four 0).
  apply (proj2 (Hcharacterizes (Four (Atom 0)))). exact HFour.
Qed.

Theorem K_strictly_weaker_KHen :
  normal_strictly_weaker (@K_normal_proves nat) (@KHen_proves nat).
Proof.
  split.
  - apply K_weaker_than_KHen.
  - exists (Hen (Atom 0)). split.
    + apply KHen_proves_Hen.
    + intro HK.
      apply (proj1 (empty_normal_proves_iff_K _)) in HK.
      pose proof (K_proves_sound_on_frame
        (F := reflexive_singleton_frame) HK) as Hvalid.
      specialize (Hvalid (fun _ _ => False) tt).
      unfold Hen, Iff, And, Neg in Hvalid; simpl in Hvalid.
      tauto.
Qed.

Theorem KHen_strictly_weaker_GL :
  normal_strictly_weaker (@KHen_proves nat) (@GL_proves nat).
Proof.
  split.
  - exact KHen_weaker_than_GL.
  - exists (Four (Atom 0)). split.
    + apply GL_proves_Four.
    + apply KHen_unprovable_atomic_Four.
Qed.
