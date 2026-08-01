(**
  Corsi's weak Goedel translation and the VF modal companion.

  This independently ports
  [Foundation/Modal/ModalCompanion/Corsi/VF.lean].  The pinned Lean source
  postulates PLoN soundness and completeness for NP.  Here both facts are
  proved from the existing canonical PLoN construction: seriality of the
  canonical frame follows directly from the P axiom and maximal consistency.

  The two model translations are factored from their truth lemmas.  This
  yields the VF/N/NP equivalences without contraposition or an imported
  semantic axiom.
*)

From Stdlib Require Import Lists.List Logic.Classical_Prop.
From FoundationModal Require Import
  Syntax HilbertK LogicInfrastructure PropositionalFormula PropositionalHilbertVF PropositionalFMT
  PropositionalFMTCompleteness PLoN PLoNCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * The weak Goedel translation *)

Fixpoint corsi_godel_weak (p : pformula nat) : formula nat :=
  match p with
  | PAtom a => Atom a
  | PFalsum => Bottom
  | PAnd q r => And (corsi_godel_weak q) (corsi_godel_weak r)
  | POr q r => Or (corsi_godel_weak q) (corsi_godel_weak r)
  | PImp q r => Box (Imp (corsi_godel_weak q) (corsi_godel_weak r))
  end.

(** A partial inverse makes injectivity and all later relation-index recovery
    one reusable syntactic fact.  The conjunction pattern is checked before
    disjunction; their raw implicational encodings are disjoint. *)
Fixpoint corsi_godel_weak_decode (t : formula nat) : option (pformula nat) :=
  match t with
  | Atom a => Some (PAtom a)
  | Bottom => Some PFalsum
  | Box (Imp a b) =>
      match corsi_godel_weak_decode a, corsi_godel_weak_decode b with
      | Some p, Some q => Some (PImp p q)
      | _, _ => None
      end
  | Imp (Imp a (Imp b Bottom)) Bottom =>
      match corsi_godel_weak_decode a, corsi_godel_weak_decode b with
      | Some p, Some q => Some (PAnd p q)
      | _, _ => None
      end
  | Imp (Imp a Bottom) b =>
      match corsi_godel_weak_decode a, corsi_godel_weak_decode b with
      | Some p, Some q => Some (POr p q)
      | _, _ => None
      end
  | _ => None
  end.

Lemma corsi_godel_weak_decode_roundtrip :
  forall p, corsi_godel_weak_decode (corsi_godel_weak p) = Some p.
Proof.
  intro p; induction p; cbn [corsi_godel_weak And Or Neg].
  - reflexivity.
  - reflexivity.
  - change
      (match corsi_godel_weak_decode (corsi_godel_weak p1),
             corsi_godel_weak_decode (corsi_godel_weak p2) with
       | Some q, Some r => Some (PAnd q r)
       | _, _ => None
       end = Some (PAnd p1 p2)).
    now rewrite IHp1, IHp2.
  - change
      (match corsi_godel_weak_decode (corsi_godel_weak p1),
             corsi_godel_weak_decode (corsi_godel_weak p2) with
       | Some q, Some r => Some (POr q r)
       | _, _ => None
       end = Some (POr p1 p2)).
    now rewrite IHp1, IHp2.
  - change
      (match corsi_godel_weak_decode (corsi_godel_weak p1),
             corsi_godel_weak_decode (corsi_godel_weak p2) with
       | Some q, Some r => Some (PImp q r)
       | _, _ => None
       end = Some (PImp p1 p2)).
    now rewrite IHp1, IHp2.
Qed.

Theorem corsi_godel_weak_injective :
  forall p q, corsi_godel_weak p = corsi_godel_weak q -> p = q.
Proof.
  intros p q H.
  pose proof (f_equal corsi_godel_weak_decode H) as Hd.
  now rewrite !corsi_godel_weak_decode_roundtrip in Hd; injection Hd.
Qed.

(** * NP in formula-indexed PLoN semantics *)

Definition plon_P_axiom : formula nat := Neg (Box Bottom).

Definition plon_NP_axioms : theory nat :=
  fun p => p = plon_P_axiom.

Definition plon_NP_proves (p : formula nat) : Prop :=
  plon_hilbert_proves plon_NP_axioms p.

Definition plon_frame_NP (F : plon_frame) : Prop :=
  forall x, exists y, plon_rel F Bottom x y.

Lemma plon_P_valid_on_NP_frame :
  forall F, plon_frame_NP F -> plon_frame_valid F plon_P_axiom.
Proof.
  intros F Hserial V x Hbox.
  destruct (Hserial x) as [y Rxy].
  exact (@plon_satisfies_bottom (plon_model_on F V) y (Hbox y Rxy)).
Qed.

Theorem plon_NP_sound :
  plon_sound plon_NP_axioms plon_frame_NP.
Proof.
  apply plon_soundness_frameclass.
  intros p -> F HF. exact (plon_P_valid_on_NP_frame HF).
Qed.

Lemma plon_terminal_frame_NP : plon_frame_NP plon_terminal_frame.
Proof. intros []; now exists tt. Qed.

Theorem plon_NP_consistent :
  plon_system_consistent plon_NP_axioms.
Proof.
  eapply (@plon_consistent_of_nonempty_frameclass
    plon_NP_axioms plon_frame_NP).
  - exists plon_terminal_frame. exact plon_terminal_frame_NP.
  - exact plon_NP_sound.
Qed.

Lemma plon_NP_canonical_frame_serial :
  plon_frame_NP
    (@plon_canonical_frame plon_NP_axioms plon_NP_consistent).
Proof.
  intro X.
  exists (@plon_canonical_default plon_NP_axioms plon_NP_consistent).
  split.
  - apply plon_mct_derivable_mem, PD_theorem, PH_axiom. reflexivity.
  - apply (proj2 (plon_mct_neg_iff
      (@plon_canonical_default plon_NP_axioms plon_NP_consistent) Bottom)).
    apply plon_mct_bottom_absent.
Qed.

Theorem plon_NP_complete :
  plon_complete plon_NP_axioms plon_frame_NP.
Proof.
  apply (@plon_complete_of_canonical_frame
    plon_NP_axioms plon_frame_NP plon_NP_consistent).
  exact plon_NP_canonical_frame_serial.
Qed.

Theorem plon_NP_sound_complete :
  forall p, plon_NP_proves p <->
    plon_frame_class_valid plon_frame_NP p.
Proof.
  intro p; split; [apply plon_NP_sound | apply plon_NP_complete].
Qed.

Lemma plon_hilbert_proves_mono :
  forall Ax Bx p,
    theory_included Ax Bx ->
    plon_hilbert_proves Ax p -> plon_hilbert_proves Bx p.
Proof.
  intros Ax Bx p Hinc Hp; induction Hp.
  - apply PH_axiom, Hinc; assumption.
  - apply PH_imply_K.
  - apply PH_imply_S.
  - apply PH_elim_contra.
  - eapply PH_mp; eauto.
  - now apply PH_nec.
Qed.

Lemma plon_N_proves_in_NP :
  forall p, plon_N_proves p -> plon_NP_proves p.
Proof.
  intros p Hp. eapply plon_hilbert_proves_mono; [|exact Hp].
  intros q Hq; contradiction.
Qed.

(** * From a PLoN model to a rooted FMT model *)

Definition corsi_plon_to_fmt_frame (M : plon_model) : fmt_frame.
Proof.
  refine {| fmt_world := unit + plon_world (plon_model_frame M);
            fmt_access := fun p x y =>
              match x, y, p with
              | inr u, inr v, PImp q r =>
                  plon_rel (plon_model_frame M)
                    (Imp (corsi_godel_weak q) (corsi_godel_weak r)) u v
              | inr _, inl _, _ => False
              | _, _, _ => True
              end;
            fmt_root := inl tt |}.
  intros p [|w]; exact I.
Defined.

Definition corsi_plon_to_fmt_model (M : plon_model) : fmt_model :=
  {| fmt_model_frame := corsi_plon_to_fmt_frame M;
     fmt_model_valuation := fun a x =>
       match x with
       | inl _ => True
       | inr w => plon_model_valuation M w a
       end |}.

Lemma corsi_plon_to_fmt_truth :
  forall M (w : plon_world (plon_model_frame M)) p,
    fmt_forces (corsi_plon_to_fmt_model M) (inr w) p <->
    plon_satisfies M w (corsi_godel_weak p).
Proof.
  intros M w p; revert w.
  induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro w.
  all: cbn [corsi_plon_to_fmt_model corsi_plon_to_fmt_frame
      corsi_godel_weak] in *.
  - reflexivity.
  - tauto.
  - rewrite plon_satisfies_and. split; intros [Hp Hq]; split.
    + now apply (proj1 (IHp w)).
    + now apply (proj1 (IHq w)).
    + now apply (proj2 (IHp w)).
    + now apply (proj2 (IHq w)).
  - rewrite plon_satisfies_or. split; intros [Hp | Hq].
    + left. now apply (proj1 (IHp w)).
    + right. now apply (proj1 (IHq w)).
    + left. now apply (proj2 (IHp w)).
    + right. now apply (proj2 (IHq w)).
  - split.
    + intros H v Rwv Hvp.
      apply (proj1 (IHq v)), H with (v := inr v); [exact Rwv |].
      now apply (proj2 (IHp v)).
    + intros H [|v] Rwv Hvp; [contradiction |].
      apply (proj2 (IHq v)), H with (u := v); [exact Rwv |].
      now apply (proj1 (IHp v)).
Qed.

(** * From a rooted FMT model to a serial PLoN model *)

Definition corsi_fmt_to_plon_frame (M : fmt_model) : plon_frame :=
  {| plon_world := fmt_world (fmt_model_frame M);
     plon_rel := fun t x y =>
       match t with
       | Imp a b => exists p q,
           corsi_godel_weak p = a /\ corsi_godel_weak q = b /\
           fmt_access (fmt_model_frame M) (PImp p q) x y
       | _ => True
       end;
     plon_default := fmt_root (fmt_model_frame M) |}.

Definition corsi_fmt_to_plon_model (M : fmt_model) : plon_model :=
  plon_model_on (corsi_fmt_to_plon_frame M)
    (fun w a => @fmt_model_valuation M a w).

Lemma corsi_fmt_to_plon_frame_NP :
  forall M, plon_frame_NP (corsi_fmt_to_plon_frame M).
Proof.
  intros M x. exists (fmt_root (fmt_model_frame M)). exact I.
Qed.

Lemma corsi_fmt_to_plon_truth :
  forall M (w : fmt_world (fmt_model_frame M)) p,
    plon_satisfies (corsi_fmt_to_plon_model M) w (corsi_godel_weak p) <->
    fmt_forces M w p.
Proof.
  intros M w p; revert w.
  induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro w.
  all: cbn [corsi_fmt_to_plon_model corsi_fmt_to_plon_frame
      corsi_godel_weak] in *.
  - reflexivity.
  - tauto.
  - rewrite plon_satisfies_and. split; intros [Hp Hq]; split.
    + now apply (proj1 (IHp w)).
    + now apply (proj1 (IHq w)).
    + now apply (proj2 (IHp w)).
    + now apply (proj2 (IHq w)).
  - rewrite plon_satisfies_or. split; intros [Hp | Hq].
    + left. now apply (proj1 (IHp w)).
    + right. now apply (proj1 (IHq w)).
    + left. now apply (proj2 (IHp w)).
    + right. now apply (proj2 (IHq w)).
  - split.
    + intros H v Rwv Hvp. apply (proj1 (IHq v)), H with (u := v).
      * exists p, q. repeat split; try reflexivity. exact Rwv.
      * now apply (proj2 (IHp v)).
    + intros H v [p' [q' [Hp' [Hq' Rwv]]]] Hvp.
      apply corsi_godel_weak_injective in Hp'.
      apply corsi_godel_weak_injective in Hq'. subst p' q'.
      apply (proj2 (IHq v)), H with (v := v); [exact Rwv |].
      now apply (proj1 (IHp v)).
Qed.

(** * Corsi's modal-companion equivalences *)

Theorem phvf_VF_provable_implies_plon_N_weak :
  forall p,
    phvf_provable (phvf_hilbert_VF nat) p ->
    plon_N_proves (corsi_godel_weak p).
Proof.
  intros p Hp. apply plon_N_complete.
  intros F _ V w.
  set (M := plon_model_on F V).
  apply (proj1 (@corsi_plon_to_fmt_truth M w p)).
  exact (@phvf_VF_fmt_sound p Hp (corsi_plon_to_fmt_frame M) I
    (@fmt_model_valuation (corsi_plon_to_fmt_model M)) (inr w)).
Qed.

Theorem plon_NP_weak_provable_implies_phvf_VF :
  forall p,
    plon_NP_proves (corsi_godel_weak p) ->
    phvf_provable (phvf_hilbert_VF nat) p.
Proof.
  intros p Hp. apply phvf_VF_fmt_complete.
  intros F _ V w.
  set (M := {| fmt_model_frame := F; fmt_model_valuation := V |}).
  apply (proj1 (@corsi_fmt_to_plon_truth M w p)).
  exact (@plon_NP_sound (corsi_godel_weak p) Hp
    (corsi_fmt_to_plon_frame M) (@corsi_fmt_to_plon_frame_NP M)
    (plon_model_valuation (corsi_fmt_to_plon_model M)) w).
Qed.

Theorem phvf_VF_iff_plon_N_weak :
  forall p,
    phvf_provable (phvf_hilbert_VF nat) p <->
    plon_N_proves (corsi_godel_weak p).
Proof.
  intro p; split.
  - apply phvf_VF_provable_implies_plon_N_weak.
  - intro Hp. apply plon_NP_weak_provable_implies_phvf_VF.
    now apply plon_N_proves_in_NP.
Qed.

Theorem phvf_VF_iff_plon_NP_weak :
  forall p,
    phvf_provable (phvf_hilbert_VF nat) p <->
    plon_NP_proves (corsi_godel_weak p).
Proof.
  intro p; split.
  - intro Hp. apply plon_N_proves_in_NP.
    now apply phvf_VF_provable_implies_plon_N_weak.
  - apply plon_NP_weak_provable_implies_phvf_VF.
Qed.

Theorem plon_N_weak_iff_NP_weak :
  forall p,
    plon_N_proves (corsi_godel_weak p) <->
    plon_NP_proves (corsi_godel_weak p).
Proof.
  intro p; rewrite <- phvf_VF_iff_plon_N_weak.
  apply phvf_VF_iff_plon_NP_weak.
Qed.
