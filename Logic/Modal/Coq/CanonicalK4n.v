(**
  Canonical completeness and the strict hierarchy of the logics K4n.

  This module ports the mathematical surface of the pinned Foundation file
  [Modal/Kripke/Logic/K4n.lean].  The logic [K4n n] is K together with

                 box^n p -> box^(n+1) p,

  and its frames are exactly the weakly [n]-transitive frames.  The main
  point not already supplied by the correspondence layer is canonicality for
  an arbitrary iterate.  It is proved below through a finite-support
  Lindenbaum bridge; no additional axiom is postulated.

  Foundation's final [Infinite] instance is represented explicitly by the
  injectivity and pairwise-inequivalence theorems for the family [K4n].
*)

From Stdlib Require Import Arith.PeanoNat Arith.Compare_dec Lia Lists.List.
From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax Axioms HilbertK Kripke Correspondence CorrespondenceExtensions
  HilbertKSoundness Filtration NormalHilbert CanonicalK CanonicalExtensions
  Boxdot CanonicalTrivVer LogicInfrastructure.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Schema, logic, and frame class *)

Definition schema_FourN (n : nat) : modal_axiom_schema :=
  fun AtomType p => exists q : formula AtomType, p = FourN n q.

Definition K4n_proves (n : nat) {AtomType} : formula AtomType -> Prop :=
  @normal_proves (schema_FourN n) AtomType.

Definition K4n_frame_class (n : nat) (F : frame) : Prop :=
  frame_weakly_transitive F n.

Lemma schema_FourN_substitution_closed :
  forall n, schema_substitution_closed (schema_FourN n).
Proof.
  intros n A B sigma p [q ->].
  exists (substitute sigma q). unfold FourN.
  cbn [substitute].
  now rewrite !substitute_box_iter.
Qed.

Lemma schema_FourN_valid_on_weakly_transitive :
  forall n F,
    frame_weakly_transitive F n ->
    schema_valid_on_frame (schema_FourN n) F.
Proof.
  intros n F Hweak AtomType p [q ->].
  now apply valid_FourN_of_weakly_transitive.
Qed.

Theorem K4n_proves_sound_on_frame :
  forall n (AtomType : Type) (F : frame) (p : formula AtomType),
    K4n_frame_class n F -> K4n_proves n p -> valid F p.
Proof.
  intros n AtomType F p Hweak Hp.
  eapply normal_proves_sound_on_frame; [| exact Hp].
  now apply schema_FourN_valid_on_weakly_transitive.
Qed.

(** The reflexive singleton witnesses consistency uniformly in [n]. *)
Lemma reflexive_singleton_weakly_transitive :
  forall n, frame_weakly_transitive reflexive_singleton_frame n.
Proof.
  intros n [] [] _. induction n as [|n IH]; simpl.
  - reflexivity.
  - exists tt. split; [constructor | exact IH].
Qed.

Theorem K4n_is_consistent :
  forall n AtomType, ~ @K4n_proves n AtomType Bottom.
Proof.
  intros n.
  apply (normal_consistent_of_sound_inhabited_frame
    (Ax := schema_FourN n) (F := reflexive_singleton_frame)).
  - now exists tt.
  - apply schema_FourN_valid_on_weakly_transitive.
    apply reflexive_singleton_weakly_transitive.
Qed.

(** * Finite-support machinery for canonical iterates *)

Fixpoint k4n_list_conj (ps : list (formula nat)) : formula nat :=
  match ps with
  | [] => Top
  | p :: qs => And p (k4n_list_conj qs)
  end.

Fixpoint k4n_list_disj (ps : list (formula nat)) : formula nat :=
  match ps with
  | [] => Bottom
  | p :: qs => Or p (k4n_list_disj qs)
  end.

Lemma satisfies_k4n_list_conj :
  forall F (V : valuation nat F) w ps,
    satisfies F V w (k4n_list_conj ps) <->
    forall p, In p ps -> satisfies F V w p.
Proof.
  intros F V w ps; induction ps as [|p ps IH].
  - cbn [k4n_list_conj]. split.
    + intros _ q Hq. contradiction.
    + intros _. apply satisfies_top.
  - cbn [k4n_list_conj]. split.
    + intro Hsat. destruct (proj1 (@satisfies_and nat F V w p
        (k4n_list_conj ps)) Hsat) as [Hp Hps].
      intros q [-> | Hq]; [exact Hp |].
      exact ((proj1 IH Hps) q Hq).
    + intro Hall. apply (proj2 (@satisfies_and nat F V w p
        (k4n_list_conj ps))). split.
      * apply Hall. now left.
      * apply (proj2 IH). intros q Hq. apply Hall. now right.
Qed.

Lemma satisfies_k4n_list_disj :
  forall F (V : valuation nat F) w ps,
    satisfies F V w (k4n_list_disj ps) <->
    exists p, In p ps /\ satisfies F V w p.
Proof.
  intros F V w ps; induction ps as [|p ps IH].
  - cbn [k4n_list_disj]. split.
    + intro H. exfalso. now apply (@satisfies_bottom nat F V w).
    + intros [q [Hq _]]. contradiction.
  - cbn [k4n_list_disj]. split.
    + intro Hsat. destruct (proj1 (@satisfies_or nat F V w p
        (k4n_list_disj ps)) Hsat) as [Hp | Hps].
      * exists p. split; [now left | exact Hp].
      * destruct (proj1 IH Hps) as [q [Hq Hsatq]].
        exists q. split; [now right | exact Hsatq].
    + intros [q [Hinq Hsatq]]. destruct Hinq as [Heq | Hq].
      * subst q. apply (proj2 (@satisfies_or nat F V w p
          (k4n_list_disj ps))). now left.
      * apply (proj2 (@satisfies_or nat F V w p
          (k4n_list_disj ps))). right. apply (proj2 IH).
        exists q. now split.
Qed.

Lemma k4n_normal_proves_of_valid_on_all_frames :
  forall Ax (p : formula nat),
    valid_on_all_frames p -> normal_proves Ax p.
Proof.
  intros Ax p Hvalid. apply K_proves_normal. now apply K_complete.
Qed.

Lemma k4n_normal_proves_box_and_intro :
  forall Ax (p q : formula nat),
    normal_proves Ax
      (Imp (Box p) (Imp (Box q) (Box (And p q)))).
Proof.
  intros Ax p q. apply k4n_normal_proves_of_valid_on_all_frames.
  intros F V w Hp Hq u Rwu.
  apply (proj2 (@satisfies_and nat F V u p q)). auto.
Qed.

Lemma k4n_normal_mct_box_conj :
  forall Ax (M : normal_maximal_consistent_theory Ax) ps,
    (forall p, In p ps -> normal_mct_mem M (Box p)) ->
    normal_mct_mem M (Box (k4n_list_conj ps)).
Proof.
  intros Ax M ps; induction ps as [|p ps IH]; intro Hmem; simpl.
  - apply normal_mct_derivable_mem. apply ND_theorem. apply Np_nec.
    unfold Top, Neg. apply normal_proves_identity.
  - apply normal_mct_derivable_mem. eapply ND_mp.
    + eapply ND_mp.
      * apply ND_theorem. apply k4n_normal_proves_box_and_intro.
      * apply ND_assumption. apply Hmem. now left.
    + apply ND_assumption. apply IH.
      intros q Hq. apply Hmem. now right.
Qed.

Definition k4n_bridge_theory Ax
    (M N : normal_maximal_consistent_theory Ax) (k : nat)
    : theory nat :=
  fun q =>
    normal_mct_mem M (Box q) \/
    exists p,
      normal_mct_mem N (Neg p) /\ q = Neg (box_iter k p).

(** A finite derivation from the bridge theory uses finitely many unboxed
    formulas from [M] and finitely many negated iterated boxes indexed by
    formulas false at [N]. *)
Lemma k4n_bridge_derivation_finite :
  forall Ax (M N : normal_maximal_consistent_theory Ax) k r,
    normal_derives Ax (k4n_bridge_theory M N k) r ->
    exists left right : list (formula nat),
      (forall p, In p left -> normal_mct_mem M (Box p)) /\
      (forall p, In p right -> normal_mct_mem N (Neg p)) /\
      normal_proves Ax
        (Imp (k4n_list_conj left)
          (Imp (k4n_list_conj
            (map (fun p => Neg (box_iter k p)) right)) r)).
Proof.
  intros Ax M N k r Hder.
  induction Hder as
    [r Hr | r Hr | p q Hpq IHpq Hp IHp].
  - destruct Hr as [HM | [s [HN ->]]].
    + exists [r], []. repeat split.
      * intros t [-> | H]; [exact HM | contradiction].
      * intros t H. contradiction.
      * apply k4n_normal_proves_of_valid_on_all_frames.
        intros F V w Hleft _.
        exact (proj1 (proj1 (@satisfies_and nat F V w r Top) Hleft)).
    + exists [], [s]. repeat split.
      * intros t H. contradiction.
      * intros t [-> | H]; [exact HN | contradiction].
      * apply k4n_normal_proves_of_valid_on_all_frames.
        intros F V w _ Hright.
        exact (proj1 (proj1 (@satisfies_and nat F V w
          (Neg (box_iter k s)) Top) Hright)).
  - exists [], []. repeat split.
    + intros t H. contradiction.
    + intros t H. contradiction.
    + apply normal_proves_imply_intro.
      now apply normal_proves_imply_intro.
  - destruct IHpq as [left1 [right1 [HM1 [HN1 Himp1]]]].
    destruct IHp as [left2 [right2 [HM2 [HN2 Himp2]]]].
    exists (left1 ++ left2), (right1 ++ right2). repeat split.
    + intros t Ht. apply in_app_or in Ht. destruct Ht.
      * now apply HM1.
      * now apply HM2.
    + intros t Ht. apply in_app_or in Ht. destruct Ht.
      * now apply HN1.
      * now apply HN2.
    + assert (Hcombine : normal_proves Ax
        (Imp
          (Imp (k4n_list_conj left1)
            (Imp (k4n_list_conj
              (map (fun p0 => Neg (box_iter k p0)) right1))
              (Imp p q)))
          (Imp
            (Imp (k4n_list_conj left2)
              (Imp (k4n_list_conj
                (map (fun p0 => Neg (box_iter k p0)) right2)) p))
            (Imp (k4n_list_conj (left1 ++ left2))
              (Imp (k4n_list_conj
                (map (fun p0 => Neg (box_iter k p0))
                  (right1 ++ right2))) q))))).
      {
        apply k4n_normal_proves_of_valid_on_all_frames.
        intros F V w Hfirst Hsecond HallLeft HallRight.
        rewrite map_app in HallRight.
        assert (HL1 : satisfies F V w (k4n_list_conj left1)).
        {
          apply (proj2 (@satisfies_k4n_list_conj F V w left1)).
          intros t Ht.
          apply (proj1 (@satisfies_k4n_list_conj
            F V w (left1 ++ left2)) HallLeft).
          apply in_or_app. now left.
        }
        assert (HL2 : satisfies F V w (k4n_list_conj left2)).
        {
          apply (proj2 (@satisfies_k4n_list_conj F V w left2)).
          intros t Ht.
          apply (proj1 (@satisfies_k4n_list_conj
            F V w (left1 ++ left2)) HallLeft).
          apply in_or_app. now right.
        }
        assert (HR1 : satisfies F V w
          (k4n_list_conj
            (map (fun p0 => Neg (box_iter k p0)) right1))).
        {
          apply (proj2 (@satisfies_k4n_list_conj F V w
            (map (fun p0 => Neg (box_iter k p0)) right1))).
          intros t Ht.
          apply (proj1 (@satisfies_k4n_list_conj F V w
            (map (fun p0 => Neg (box_iter k p0)) right1 ++
             map (fun p0 => Neg (box_iter k p0)) right2)) HallRight).
          apply in_or_app. now left.
        }
        assert (HR2 : satisfies F V w
          (k4n_list_conj
            (map (fun p0 => Neg (box_iter k p0)) right2))).
        {
          apply (proj2 (@satisfies_k4n_list_conj F V w
            (map (fun p0 => Neg (box_iter k p0)) right2))).
          intros t Ht.
          apply (proj1 (@satisfies_k4n_list_conj F V w
            (map (fun p0 => Neg (box_iter k p0)) right1 ++
             map (fun p0 => Neg (box_iter k p0)) right2)) HallRight).
          apply in_or_app. now right.
        }
        exact (Hfirst HL1 HR1 (Hsecond HL2 HR2)).
      }
      eapply Np_mp.
      * eapply Np_mp; [exact Hcombine | exact Himp1].
      * exact Himp2.
Qed.

(** The modal tautology that closes the bridge argument.  If [a] is
    incompatible with all the negated [k]-boxes in a finite list, then [a]
    forces the [k]-box of their disjunction. *)
Lemma k4n_bridge_modal_transform :
  forall Ax k (a : formula nat) right,
    normal_proves Ax
      (Imp
        (Imp a
          (Imp (k4n_list_conj
            (map (fun p => Neg (box_iter k p)) right)) Bottom))
        (Imp a (box_iter k (k4n_list_disj right)))).
Proof.
  intros Ax k a right.
  apply k4n_normal_proves_of_valid_on_all_frames.
  intros F V w Hcontra Ha.
  apply (proj2 (@satisfies_box_iter nat F V k w
    (k4n_list_disj right))).
  intros u Hwu.
  apply (proj2 (@satisfies_k4n_list_disj F V u right)).
  apply NNPP. intro Hnone.
  assert (Hnegboxes : satisfies F V w
    (k4n_list_conj
      (map (fun p => Neg (box_iter k p)) right))).
  {
    apply (proj2 (@satisfies_k4n_list_conj F V w
      (map (fun p => Neg (box_iter k p)) right))).
    intros q Hq. apply in_map_iff in Hq.
    destruct Hq as [p [<- Hp]].
    apply (proj2 (@satisfies_neg nat F V w (box_iter k p))).
    intro Hbox.
    pose proof (proj1 (@satisfies_box_iter nat F V k w p)
      Hbox u Hwu) as Hpu.
    apply Hnone. exists p. now split.
  }
  exact (@satisfies_bottom nat F V w (Hcontra Ha Hnegboxes)).
Qed.

Lemma k4n_normal_mct_neg_disj :
  forall Ax (N : normal_maximal_consistent_theory Ax) right,
    (forall p, In p right -> normal_mct_mem N (Neg p)) ->
    normal_mct_mem N (Neg (k4n_list_disj right)).
Proof.
  intros Ax N right Hneg.
  apply (proj2 (@normal_canonical_truth_lemma Ax
    (Neg (k4n_list_disj right)) N)).
  apply (proj2 (@satisfies_neg nat (normal_canonical_frame Ax)
    (@normal_canonical_valuation Ax) N (k4n_list_disj right))).
  intro Hdisj.
  destruct (proj1 (@satisfies_k4n_list_disj
    (normal_canonical_frame Ax) (@normal_canonical_valuation Ax)
    N right) Hdisj) as [p [Hp Hsat]].
  pose proof (proj1 (@normal_canonical_truth_lemma Ax (Neg p) N)
    (Hneg p Hp)) as Hnotsat.
  exact (Hnotsat Hsat).
Qed.

Lemma k4n_bridge_theory_consistent :
  forall Ax (M N : normal_maximal_consistent_theory Ax) k,
    (forall p,
      normal_mct_mem M (Box (box_iter k p)) ->
      normal_mct_mem N p) ->
    normal_theory_consistent Ax (k4n_bridge_theory M N k).
Proof.
  intros Ax M N k Hlink Hbottom.
  destruct (k4n_bridge_derivation_finite Hbottom)
    as [left [right [HM [HN Hcontra]]]].
  assert (HboxLeft : normal_mct_mem M (Box (k4n_list_conj left))).
  { now apply k4n_normal_mct_box_conj. }
  assert (Hstep : normal_proves Ax
    (Imp (k4n_list_conj left)
      (box_iter k (k4n_list_disj right)))).
  {
    eapply Np_mp.
    - apply k4n_bridge_modal_transform.
    - exact Hcontra.
  }
  assert (HboxedStep : normal_proves Ax
    (Imp (Box (k4n_list_conj left))
      (Box (box_iter k (k4n_list_disj right))))).
  {
    eapply Np_mp.
    - apply Np_modal_K.
    - now apply Np_nec.
  }
  assert (HboxDisj : normal_mct_mem M
    (Box (box_iter k (k4n_list_disj right)))).
  {
    apply normal_mct_derivable_mem. eapply ND_mp.
    - apply ND_theorem. exact HboxedStep.
    - apply ND_assumption. exact HboxLeft.
  }
  pose proof (Hlink (k4n_list_disj right) HboxDisj) as Hdisj.
  pose proof (k4n_normal_mct_neg_disj HN) as HnegDisj.
  exact (@normal_mct_not_both Ax N (k4n_list_disj right)
    Hdisj HnegDisj).
Qed.

(** Exact canonical characterization of iterated accessibility. *)
Theorem normal_canonical_rel_iter_iff_box_iter :
  forall Ax n (M N : normal_maximal_consistent_theory Ax),
    rel_iter (@normal_canonical_relation Ax) n M N <->
    forall p,
      normal_mct_mem M (box_iter n p) -> normal_mct_mem N p.
Proof.
  intros Ax n M N; split.
  - revert M N. induction n as [|n IH]; intros M N Hpath p Hbox.
    + simpl in Hpath. now subst N.
    + simpl in Hpath, Hbox.
      destruct Hpath as [P [HMP HPN]].
      apply (IH P N HPN p).
      exact (HMP (box_iter n p) Hbox).
  - revert M N. induction n as [|n IH]; intros M N Hbox.
    + simpl in Hbox. simpl.
      apply normal_mct_eq_of_included. exact Hbox.
    + assert (Hconsistent : normal_theory_consistent Ax
        (k4n_bridge_theory M N n)).
      {
        apply k4n_bridge_theory_consistent.
        intros p Hp. apply Hbox. exact Hp.
      }
      destruct (normal_lindenbaum_extension Hconsistent)
        as [P Hinclude].
      simpl. exists P; split.
      * intros p Hp. apply Hinclude. now left.
      * apply IH. intros p Hp.
        destruct (@normal_mct_complete Ax N p) as [HNp | HNneg].
        -- exact HNp.
        -- exfalso. apply (@normal_mct_not_both Ax P (box_iter n p) Hp).
           apply Hinclude. right. exists p. now split.
Qed.

Theorem normal_canonical_weakly_transitive_of_schema_FourN :
  forall Ax n,
    schema_included (schema_FourN n) Ax ->
    frame_weakly_transitive (normal_canonical_frame Ax) n.
Proof.
  intros Ax n HFour M N Hlong.
  apply (proj2 (@normal_canonical_rel_iter_iff_box_iter Ax n M N)).
  intros p Hbox.
  apply (proj1 (@normal_canonical_rel_iter_iff_box_iter
    Ax (n + 1) M N) Hlong p).
  apply normal_mct_derivable_mem. eapply ND_mp.
  - apply ND_theorem. apply Np_extra. apply HFour.
    exists p. reflexivity.
  - apply ND_assumption. exact Hbox.
Qed.

Lemma K4n_canonical_frame :
  forall n,
    K4n_frame_class n (normal_canonical_frame (schema_FourN n)).
Proof.
  intros n. apply normal_canonical_weakly_transitive_of_schema_FourN.
  intros A p Hp. exact Hp.
Qed.

Theorem K4n_complete :
  forall n (p : formula nat),
    normal_valid_on_class (K4n_frame_class n) p -> K4n_proves n p.
Proof.
  intros n. unfold K4n_proves.
  apply (normal_complete_of_canonical_frame
    (Ax := schema_FourN n) (C := K4n_frame_class n)).
  - exact (@K4n_is_consistent n nat).
  - apply K4n_canonical_frame.
Qed.

Theorem K4n_sound_complete :
  forall n (p : formula nat),
    K4n_proves n p <->
    normal_valid_on_class (K4n_frame_class n) p.
Proof.
  intros n p; split.
  - intros Hp F HF.
    now apply (@K4n_proves_sound_on_frame n nat F p).
  - apply K4n_complete.
Qed.

(** * The zero and one levels *)

Lemma K4n_frame_class_zero_iff_KTc :
  forall F,
    K4n_frame_class 0 F <-> KTc_kripke_frame_class F.
Proof.
  intro F. unfold K4n_frame_class, frame_weakly_transitive,
    KTc_kripke_frame_class, frame_coreflexive.
  split.
  - intros Hweak x y Rxy.
    apply Hweak. now apply (proj2 (rel_iter_one (Rel F) x y)).
  - intros Hcore x y Hxy. simpl.
    apply Hcore. now apply (proj1 (rel_iter_one (Rel F) x y)).
Qed.

Lemma K4n_frame_class_one_iff_transitive :
  forall F,
    K4n_frame_class 1 F <-> frame_transitive F.
Proof.
  intro F. unfold K4n_frame_class, frame_weakly_transitive.
  split.
  - intros Hweak x y z Rxy Ryz.
    apply (proj1 (rel_iter_one (Rel F) x z)).
    apply Hweak. simpl. exists y; split; [exact Rxy |].
    now apply (proj2 (rel_iter_one (Rel F) y z)).
  - intros Htrans x z Hpath.
    destruct Hpath as [y [Rxy Hyz]].
    apply (proj2 (rel_iter_one (Rel F) x z)).
    apply Htrans with (y := y); [exact Rxy |].
    now apply (proj1 (rel_iter_one (Rel F) y z)).
Qed.

Lemma normal_proves_from_provable_axioms :
  forall Ax Ay,
    (forall (AtomType : Type) (p : formula AtomType),
      Ax AtomType p -> normal_proves Ay p) ->
    forall (AtomType : Type) (p : formula AtomType),
      normal_proves Ax p -> normal_proves Ay p.
Proof.
  intros Ax Ay Haxiom AtomType p Hp; induction Hp.
  - apply Np_imply_K.
  - apply Np_imply_S.
  - apply Np_elim_contra.
  - apply Np_modal_K.
  - now apply Haxiom.
  - eapply Np_mp; eauto.
  - now apply Np_nec.
Qed.

Lemma schema_FourN_zero_iff_Tc :
  forall AtomType (p : formula AtomType),
    @schema_FourN 0 AtomType p <-> @schema_Tc AtomType p.
Proof.
  intros AtomType p; split; intros [q ->]; exists q; reflexivity.
Qed.

Lemma schema_FourN_one_iff_Four :
  forall AtomType (p : formula AtomType),
    @schema_FourN 1 AtomType p <-> @schema_Four AtomType p.
Proof.
  intros AtomType p; split; intros [q ->]; exists q; reflexivity.
Qed.

Theorem K4n_zero_iff_KTc_proves :
  forall (AtomType : Type) (p : formula AtomType),
    K4n_proves 0 p <-> KTc_proves p.
Proof.
  intros AtomType p; split; intro Hp.
  - unfold K4n_proves, KTc_proves in *.
    eapply normal_proves_from_provable_axioms; [| exact Hp].
    intros A q Hq. apply Np_extra.
    now apply (proj1 (@schema_FourN_zero_iff_Tc A q)).
  - unfold K4n_proves, KTc_proves in *.
    eapply normal_proves_from_provable_axioms; [| exact Hp].
    intros A q Hq. apply Np_extra.
    now apply (proj2 (@schema_FourN_zero_iff_Tc A q)).
Qed.

Theorem K4n_one_iff_K4_proves :
  forall (AtomType : Type) (p : formula AtomType),
    K4n_proves 1 p <-> K4_proves p.
Proof.
  intros AtomType p; split; intro Hp.
  - unfold K4n_proves, K4_proves in *.
    eapply normal_proves_from_provable_axioms; [| exact Hp].
    intros A q Hq. apply Np_extra.
    now apply (proj1 (@schema_FourN_one_iff_Four A q)).
  - unfold K4n_proves, K4_proves in *.
    eapply normal_proves_from_provable_axioms; [| exact Hp].
    intros A q Hq. apply Np_extra.
    now apply (proj2 (@schema_FourN_one_iff_Four A q)).
Qed.

Theorem K4n_zero_equiv_KTc :
  forall AtomType,
    logic_equiv (@K4n_proves 0 AtomType) (@KTc_proves AtomType).
Proof.
  intros AtomType; split; intros p Hp.
  - now apply (proj1 (@K4n_zero_iff_KTc_proves AtomType p)).
  - now apply (proj2 (@K4n_zero_iff_KTc_proves AtomType p)).
Qed.

Theorem K4n_one_equiv_K4 :
  forall AtomType,
    logic_equiv (@K4n_proves 1 AtomType) (@K4_proves AtomType).
Proof.
  intros AtomType; split; intros p Hp.
  - now apply (proj1 (@K4n_one_iff_K4_proves AtomType p)).
  - now apply (proj2 (@K4n_one_iff_K4_proves AtomType p)).
Qed.

(** * Syntactic hierarchy *)

Lemma K_weaker_than_K4n :
  forall n (AtomType : Type) (p : formula AtomType),
    K_normal_proves p -> K4n_proves n p.
Proof.
  intros n AtomType p Hp. unfold K4n_proves.
  now apply K_weaker_than_normal.
Qed.

Lemma K4n_proves_successor_axiom :
  forall n (AtomType : Type) (p : formula AtomType),
    K4n_proves n (FourN (S n) p).
Proof.
  intros n AtomType p. unfold K4n_proves, FourN.
  replace (S n + 1) with (S (S n)) by lia. simpl.
  eapply Np_mp.
  - apply Np_modal_K.
  - apply Np_nec. apply Np_extra. exists p.
    unfold FourN. replace (n + 1) with (S n) by lia. reflexivity.
Qed.

Lemma K4n_successor_weaker_than :
  forall n (AtomType : Type) (p : formula AtomType),
    K4n_proves (S n) p -> K4n_proves n p.
Proof.
  intros n AtomType p Hp. unfold K4n_proves in *.
  eapply normal_proves_from_provable_axioms; [| exact Hp].
  intros A q [r ->]. apply K4n_proves_successor_axiom.
Qed.

Lemma K4n_weaker_than_of_le :
  forall n m,
    n <= m ->
    forall (AtomType : Type) (p : formula AtomType),
      K4n_proves m p -> K4n_proves n p.
Proof.
  intros n m Hnm. induction Hnm as [|m Hnm IH]; intros AtomType p Hp.
  - exact Hp.
  - apply IH. now apply K4n_successor_weaker_than.
Qed.

(** * Explicit bounded saturating counterframes *)

Definition k4n_counter_world (n : nat) : Type :=
  { i : nat | i <= S n }.

Definition k4n_counterframe (n : nat) : frame :=
  {| World := k4n_counter_world n;
     Rel := fun i j =>
       proj1_sig j = Nat.min (S (proj1_sig i)) (S n) |}.

Definition k4n_counter_zero (n : nat) : World (k4n_counterframe n) :=
  exist _ 0 (Nat.le_0_l (S n)).

Definition k4n_counter_last (n : nat) : World (k4n_counterframe n) :=
  exist _ (S n) (Nat.le_refl (S n)).

Definition k4n_counter_next (n : nat)
    (i : World (k4n_counterframe n))
    : World (k4n_counterframe n) :=
  exist _ (Nat.min (S (proj1_sig i)) (S n))
    (Nat.le_min_r (S (proj1_sig i)) (S n)).

Lemma k4n_saturation_succ :
  forall bound i m,
    i <= bound ->
    Nat.min (Nat.min (S i) bound + m) bound =
    Nat.min (i + S m) bound.
Proof.
  intros bound i m Hib.
  destruct (le_dec (S i) bound) as [Hsucc | Hsucc].
  - rewrite (Nat.min_l _ _ Hsucc).
    replace (i + S m) with (S i + m) by lia. reflexivity.
  - assert (Hbound : bound <= S i) by lia.
    rewrite (Nat.min_r _ _ Hbound).
    rewrite (Nat.min_r (bound + m) bound) by lia.
    rewrite (Nat.min_r (i + S m) bound) by lia.
    reflexivity.
Qed.

Lemma k4n_counter_rel_iter_iff :
  forall n m (i j : World (k4n_counterframe n)),
    rel_iter (Rel (k4n_counterframe n)) m i j <->
    proj1_sig j = Nat.min (proj1_sig i + m) (S n).
Proof.
  intros n m; induction m as [|m IH]; intros i j.
  - simpl. split.
    + intro Hij. subst j.
      rewrite Nat.add_0_r, Nat.min_l; [reflexivity | exact (proj2_sig i)].
    + intro Hij. apply eq_sig_hprop.
      * intros x px py. apply proof_irrelevance.
      * simpl in Hij. rewrite Nat.add_0_r, Nat.min_l in Hij;
          [lia | exact (proj2_sig i)].
  - simpl. split.
    + intros [z [Hiz Hzj]].
      apply (proj1 (IH z j)) in Hzj.
      change (proj1_sig z =
        Nat.min (S (proj1_sig i)) (S n)) in Hiz.
      change (proj1_sig j =
        Nat.min (proj1_sig z + m) (S n)) in Hzj.
      change (proj1_sig j =
        Nat.min (proj1_sig i + S m) (S n)).
      rewrite Hiz in Hzj.
      rewrite k4n_saturation_succ in Hzj; [exact Hzj | exact (proj2_sig i)].
    + intro Hij. exists (@k4n_counter_next n i). split.
      * reflexivity.
      * apply (proj2 (IH (@k4n_counter_next n i) j)).
        change (proj1_sig j =
          Nat.min (Nat.min (S (proj1_sig i)) (S n) + m) (S n)).
        rewrite k4n_saturation_succ; [exact Hij | exact (proj2_sig i)].
Qed.

Lemma k4n_counterframe_weakly_transitive_above :
  forall n m,
    n < m -> frame_weakly_transitive (k4n_counterframe n) m.
Proof.
  intros n m Hnm i j Hlong.
  apply (proj2 (@k4n_counter_rel_iter_iff n m i j)).
  pose proof (proj1 (@k4n_counter_rel_iter_iff n (m + 1) i j)
    Hlong) as Hj.
  rewrite (Nat.min_r (proj1_sig i + (m + 1)) (S n)) in Hj by lia.
  rewrite (Nat.min_r (proj1_sig i + m) (S n)) by lia.
  exact Hj.
Qed.

Lemma k4n_counterframe_not_weakly_transitive :
  forall n, ~ frame_weakly_transitive (k4n_counterframe n) n.
Proof.
  intros n Hweak.
  assert (Hlong : rel_iter (Rel (k4n_counterframe n)) (n + 1)
    (k4n_counter_zero n) (k4n_counter_last n)).
  {
    apply (proj2 (@k4n_counter_rel_iter_iff n (n + 1)
      (k4n_counter_zero n) (k4n_counter_last n))).
    unfold k4n_counter_zero, k4n_counter_last; simpl.
    lia.
  }
  pose proof (Hweak (k4n_counter_zero n) (k4n_counter_last n) Hlong)
    as Hshort.
  apply (proj1 (@k4n_counter_rel_iter_iff n n
    (k4n_counter_zero n) (k4n_counter_last n))) in Hshort.
  unfold k4n_counter_zero, k4n_counter_last in Hshort; simpl in Hshort.
  rewrite Nat.min_l in Hshort by lia. lia.
Qed.

(** * Strictness, inequivalence, and the infinite family *)

Theorem K_strictly_weaker_K4n :
  forall n,
    normal_strictly_weaker (@K_normal_proves nat) (@K4n_proves n nat).
Proof.
  intros n; split.
  - intros p Hp. now apply K_weaker_than_K4n.
  - exists (FourN n (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro HK.
      pose proof (@K_proves_sound_on_frame nat (k4n_counterframe n)
        (FourN n (Atom 0))
        (proj1 (empty_normal_proves_iff_K (FourN n (Atom 0))) HK))
        as Hvalid.
      apply (@k4n_counterframe_not_weakly_transitive n).
      now apply (proj1 (valid_FourN_atom_iff_weakly_transitive
        (k4n_counterframe n) n)).
Qed.

Theorem K4n_strictly_weaker_of_lt :
  forall n m,
    n < m ->
    normal_strictly_weaker (@K4n_proves m nat) (@K4n_proves n nat).
Proof.
  intros n m Hnm; split.
  - intros p Hp.
    exact (@K4n_weaker_than_of_le n m (Nat.lt_le_incl n m Hnm) nat p Hp).
  - exists (FourN n (Atom 0)); split.
    + apply Np_extra. exists (Atom 0). reflexivity.
    + intro Hm.
      pose proof (@K4n_proves_sound_on_frame m nat (k4n_counterframe n)
        (FourN n (Atom 0))
        (k4n_counterframe_weakly_transitive_above Hnm) Hm) as Hvalid.
      apply (@k4n_counterframe_not_weakly_transitive n).
      now apply (proj1 (valid_FourN_atom_iff_weakly_transitive
        (k4n_counterframe n) n)).
Qed.

Corollary K4n_successor_strictly_weaker :
  forall n,
    normal_strictly_weaker
      (@K4n_proves (S n) nat) (@K4n_proves n nat).
Proof. intros n. apply K4n_strictly_weaker_of_lt. lia. Qed.

Corollary K4n_add_strictly_weaker :
  forall n m,
    0 < m ->
    normal_strictly_weaker
      (@K4n_proves (n + m) nat) (@K4n_proves n nat).
Proof. intros n m Hm. apply K4n_strictly_weaker_of_lt. lia. Qed.

Theorem K4n_not_equiv_of_ne :
  forall n m,
    n <> m ->
    ~ logic_equiv (@K4n_proves n nat) (@K4n_proves m nat).
Proof.
  intros n m Hne Hequiv.
  destruct (Nat.lt_trichotomy n m) as [Hlt | [Heq | Hgt]].
  - destruct (K4n_strictly_weaker_of_lt Hlt)
      as [_ [p [Hn Hnotm]]].
    exact (Hnotm ((proj1 Hequiv) p Hn)).
  - contradiction.
  - destruct (K4n_strictly_weaker_of_lt Hgt)
      as [_ [p [Hm Hnotn]]].
    exact (Hnotn ((proj2 Hequiv) p Hm)).
Qed.

Theorem K4n_family_pairwise_inequivalent :
  forall n m,
    n <> m ->
    ~ logic_equiv (@K4n_proves n nat) (@K4n_proves m nat).
Proof. exact K4n_not_equiv_of_ne. Qed.

Theorem K4n_family_injective :
  forall n m,
    (@K4n_proves n nat) = (@K4n_proves m nat) -> n = m.
Proof.
  intros n m Heq. apply NNPP. intro Hne.
  apply (K4n_not_equiv_of_ne Hne). split; intros p Hp.
  - rewrite <- Heq. exact Hp.
  - rewrite Heq. exact Hp.
Qed.

Corollary K4n_one_strictly_weaker_zero :
  normal_strictly_weaker (@K4n_proves 1 nat) (@K4n_proves 0 nat).
Proof. apply K4n_strictly_weaker_of_lt. lia. Qed.

Corollary K4n_two_strictly_weaker_one :
  normal_strictly_weaker (@K4n_proves 2 nat) (@K4n_proves 1 nat).
Proof. apply K4n_strictly_weaker_of_lt. lia. Qed.

Corollary K_strictly_weaker_K4n_two :
  normal_strictly_weaker (@K_normal_proves nat) (@K4n_proves 2 nat).
Proof. apply K_strictly_weaker_K4n. Qed.
