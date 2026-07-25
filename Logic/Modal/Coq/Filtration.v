(**
  Filtration and the finite-model property for basic modal logic.

  This file ports the coarsest-filtration construction from
  Foundation/Modal/Kripke/Filtration.lean.  A world of the filtered model is
  a truth profile, over the (finite) list of subformulas of one fixed target,
  which is realised by an original world.  This presents the quotient by
  agreement on the closure without requiring quotient types in Rocq.

  Classical informative excluded middle turns semantic truth into Boolean
  profiles; classical description chooses one representative of each
  realised profile.  Proof irrelevance is used only when enumerating the
  corresponding subtype.  The modal truth lemma itself is otherwise the
  usual structural argument for the coarsest filtration.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Bool.Bool Lists.List.
From Stdlib Require Import Logic.ClassicalDescription.
From Stdlib Require Import Logic.ClassicalEpsilon.
From Stdlib Require Import Logic.ProofIrrelevance.
From FoundationModal Require Import Syntax Kripke.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Finite Boolean profiles *)

Definition truth_bit (P : Prop) : bool :=
  if excluded_middle_informative P then true else false.

Lemma truth_bit_true_iff :
  forall P : Prop, truth_bit P = true <-> P.
Proof.
  intro P; unfold truth_bit.
  destruct (excluded_middle_informative P) as [HP | Hnot]; simpl.
  - split; intro; [exact HP | reflexivity].
  - split; [discriminate | intro HP; now exfalso].
Qed.

Lemma map_pointwise_of_eq :
  forall (A B : Type) (f g : A -> B) (xs : list A),
    map f xs = map g xs ->
    forall x, In x xs -> f x = g x.
Proof.
  intros A B f g xs; induction xs as [|a xs IH]; intros Heq x Hx.
  - contradiction.
  - simpl in Heq. injection Heq as Hhead Htail.
    simpl in Hx. destruct Hx as [<- | Hx].
    + exact Hhead.
    + now apply IH with (x := x).
Qed.

Fixpoint bool_profiles (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S k =>
      map (cons false) (bool_profiles k) ++
      map (cons true) (bool_profiles k)
  end.

Lemma bool_profiles_length :
  forall n, length (bool_profiles n) = 2 ^ n.
Proof.
  induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite length_app, !length_map, IH. lia.
Qed.

Lemma bool_profiles_complete :
  forall n xs, length xs = n -> In xs (bool_profiles n).
Proof.
  induction n as [|n IH]; intros xs Hlen.
  - destruct xs; simpl in *; [auto | discriminate].
  - destruct xs as [|b xs]; simpl in Hlen; [discriminate |].
    apply Nat.succ_inj in Hlen. simpl.
    apply in_app_iff. destruct b.
    + right. apply in_map_iff. exists xs; split; [reflexivity |].
      exact (IH xs Hlen).
    + left. apply in_map_iff. exists xs; split; [reflexivity |].
      exact (IH xs Hlen).
Qed.

Lemma NoDup_map_cons :
  forall (b : bool) (xss : list (list bool)),
    NoDup xss -> NoDup (map (cons b) xss).
Proof.
  intros b xss Hnd; induction Hnd as [|xs xss Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor; [|exact IH].
    intro Hin. apply in_map_iff in Hin.
    destruct Hin as [ys [Heq Hin]]. inversion Heq; subst ys.
    now apply Hnotin.
Qed.

Lemma bool_profiles_nodup :
  forall n, NoDup (bool_profiles n).
Proof.
  induction n as [|n IH]; simpl.
  - repeat constructor; simpl; auto.
  - apply NoDup_app.
    + now apply NoDup_map_cons.
    + now apply NoDup_map_cons.
    + intros xs Hfalse Htrue.
      apply in_map_iff in Hfalse, Htrue.
      destruct Hfalse as [ys [<- Hys]].
      destruct Htrue as [zs [Heq Hzs]]. discriminate.
Qed.

(** Keep precisely the elements of a list satisfying a (classically)
    decidable predicate, retaining the proofs in a subset type. *)
Fixpoint sig_filter {A : Type} (P : A -> Prop)
    (dec : forall x, {P x} + {~ P x}) (xs : list A) : list {x : A | P x} :=
  match xs with
  | [] => []
  | x :: rest =>
      match dec x with
      | left Hx => exist P x Hx :: @sig_filter A P dec rest
      | right _ => @sig_filter A P dec rest
      end
  end.

Lemma sig_filter_length_le :
  forall (A : Type) (P : A -> Prop)
         (dec : forall x, {P x} + {~ P x}) (xs : list A),
    length (@sig_filter A P dec xs) <= length xs.
Proof.
  intros A P dec xs; induction xs as [|x xs IH]; simpl.
  - lia.
  - destruct (dec x); simpl; lia.
Qed.

Lemma sig_filter_complete :
  forall (A : Type) (P : A -> Prop)
         (dec : forall x, {P x} + {~ P x}) (xs : list A)
         (X : {x : A | P x}),
    In (proj1_sig X) xs -> In X (@sig_filter A P dec xs).
Proof.
  intros A P dec xs; induction xs as [|x xs IH]; intros X Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst x. destruct (dec (proj1_sig X)) as [HP | Hnot].
      * left. apply eq_sig_hprop.
        -- intros z p q; apply proof_irrelevance.
        -- reflexivity.
      * exfalso. exact (Hnot (proj2_sig X)).
    + destruct (dec x); simpl; [right |]; now apply IH.
Qed.

Lemma sig_filter_nodup :
  forall (A : Type) (P : A -> Prop)
         (dec : forall x, {P x} + {~ P x}) (xs : list A),
    NoDup xs -> NoDup (@sig_filter A P dec xs).
Proof.
  intros A P dec xs Hnd; induction Hnd as [|x xs Hnotin Hnd IH]; simpl.
  - constructor.
  - destruct (dec x) as [HP | Hnot]; [|exact IH].
    constructor; [|exact IH].
    intro Hin.
    assert (Hproj : In x xs).
    { clear -Hin.
      induction xs as [|y ys IHys]; simpl in *; [contradiction |].
      destruct (dec y) as [Hy | Hny].
      - destruct Hin as [Heq | Hin].
        + left. now injection Heq.
        + right. now apply IHys.
      - right. now apply IHys.
    }
    exact (Hnotin Hproj).
Qed.

(** * Coarsest filtration of one model through one formula *)

Section CoarsestFiltration.

Context {AtomType : Type} (F : frame) (V : valuation AtomType F)
        (target : formula AtomType).

Definition truth_profile (w : World F) : list bool :=
  map (fun p => truth_bit (satisfies F V w p)) (subformulas target).

Lemma truth_profile_length :
  forall w, length (truth_profile w) = length (subformulas target).
Proof. intro w; unfold truth_profile; now rewrite length_map. Qed.

Definition realised_profile (bits : list bool) : Prop :=
  exists w : World F, truth_profile w = bits.

Definition filtered_world : Type :=
  {bits : list bool | realised_profile bits}.

Definition profile_class (w : World F) : filtered_world :=
  exist realised_profile (truth_profile w) (ex_intro _ w eq_refl).

Definition representative (X : filtered_world) : World F :=
  proj1_sig
    (constructive_indefinite_description
       (fun w => truth_profile w = proj1_sig X) (proj2_sig X)).

Lemma representative_spec :
  forall X, truth_profile (representative X) = proj1_sig X.
Proof.
  intro X; unfold representative.
  exact (proj2_sig
    (constructive_indefinite_description
       (fun w => truth_profile w = proj1_sig X) (proj2_sig X))).
Qed.

Lemma profile_class_spec :
  forall w, truth_profile (representative (profile_class w)) = truth_profile w.
Proof. intro w; apply representative_spec. Qed.

Lemma truth_profile_agreement :
  forall x y p,
    truth_profile x = truth_profile y ->
    In p (subformulas target) ->
    (satisfies F V x p <-> satisfies F V y p).
Proof.
  intros x y p Hprofiles Hin.
  unfold truth_profile in Hprofiles.
  pose proof (@map_pointwise_of_eq (formula AtomType) bool
    (fun q => truth_bit (satisfies F V x q))
    (fun q => truth_bit (satisfies F V y q))
    (subformulas target) Hprofiles p Hin) as Hbit.
  split; intro Hp.
  - apply (proj1 (truth_bit_true_iff (satisfies F V y p))).
    rewrite <- Hbit.
    apply (proj2 (truth_bit_true_iff (satisfies F V x p))). exact Hp.
  - apply (proj1 (truth_bit_true_iff (satisfies F V x p))).
    rewrite Hbit.
    apply (proj2 (truth_bit_true_iff (satisfies F V y p))). exact Hp.
Qed.

Definition coarsest_filtered_rel (X Y : filtered_world) : Prop :=
  forall p,
    In (Box p) (subformulas target) ->
    satisfies F V (representative X) (Box p) ->
    satisfies F V (representative Y) p.

Definition coarsest_filtered_frame : frame :=
  {| World := filtered_world;
     Rel := coarsest_filtered_rel |}.

Definition coarsest_filtered_valuation :
    valuation AtomType coarsest_filtered_frame :=
  fun a X => satisfies F V (representative X) (Atom a).

Lemma child_is_target_subformula :
  forall p q,
    In p (subformulas target) ->
    In q (subformulas p) ->
    In q (subformulas target).
Proof. intros; eapply subformulas_trans; eauto. Qed.

Lemma coarsest_filtered_rel_forth :
  forall x y,
    Rel F x y ->
    coarsest_filtered_rel (profile_class x) (profile_class y).
Proof.
  intros x y Rxy p Hp Hbox.
  assert (Hrep_x : satisfies F V x (Box p)).
  { apply (proj1 (truth_profile_agreement
                    (x := representative (profile_class x))
                    (y := x) (p := Box p)
                    (profile_class_spec x) Hp)).
    exact Hbox. }
  assert (Hyp : satisfies F V y p) by exact (Hrep_x y Rxy).
  assert (Hchild : In p (subformulas target)).
  { eapply child_is_target_subformula.
    - exact Hp.
    - simpl; right; apply subformulas_self. }
  apply (proj1 (truth_profile_agreement
                  (x := y) (y := representative (profile_class y))
                  (p := p)
                  (eq_sym (profile_class_spec y)) Hchild)).
  exact Hyp.
Qed.

Lemma coarsest_filtered_rel_to_class :
  forall X y,
    Rel F (representative X) y ->
    coarsest_filtered_rel X (profile_class y).
Proof.
  intros X y Rxy p Hp Hbox.
  assert (Hyp : satisfies F V y p) by exact (Hbox y Rxy).
  assert (Hchild : In p (subformulas target)).
  { eapply child_is_target_subformula.
    - exact Hp.
    - simpl; right; apply subformulas_self. }
  apply (proj1 (truth_profile_agreement
                  (x := y) (y := representative (profile_class y))
                  (p := p)
                  (eq_sym (profile_class_spec y)) Hchild)).
  exact Hyp.
Qed.

Theorem coarsest_filtration_truth :
  forall p,
    In p (subformulas target) ->
    forall X,
      satisfies coarsest_filtered_frame coarsest_filtered_valuation X p <->
      satisfies F V (representative X) p.
Proof.
  intros p; induction p as [a | | p IHp q IHq | p IHp];
    intros Hin X; simpl.
  - reflexivity.
  - tauto.
  - assert (Hp : In p (subformulas target)).
    { eapply child_is_target_subformula; [exact Hin |].
      simpl; right; apply in_or_app; left; apply subformulas_self. }
    assert (Hq : In q (subformulas target)).
    { eapply child_is_target_subformula; [exact Hin |].
      simpl; right; apply in_or_app; right; apply subformulas_self. }
    rewrite IHp by exact Hp. rewrite IHq by exact Hq. reflexivity.
  - assert (Hp : In p (subformulas target)).
    { eapply child_is_target_subformula; [exact Hin |].
      simpl; auto using subformulas_self. }
    split.
    + intros Hbox y Rxy.
      specialize (Hbox (profile_class y)
        (coarsest_filtered_rel_to_class (X := X) (y := y) Rxy)).
      apply (proj1 (truth_profile_agreement
                      (x := representative (profile_class y))
                      (y := y) (p := p)
                      (profile_class_spec y) Hp)).
      apply (proj1 (IHp Hp (profile_class y))). exact Hbox.
    + intros Hbox Y HXY.
      apply (proj2 (IHp Hp Y)).
      exact (HXY p Hin Hbox).
Qed.

Corollary coarsest_filtration_truth_at_class :
  forall p,
    In p (subformulas target) ->
    forall w,
      satisfies coarsest_filtered_frame coarsest_filtered_valuation
                (profile_class w) p <->
      satisfies F V w p.
Proof.
  intros p Hin w.
  rewrite coarsest_filtration_truth by exact Hin.
  apply (truth_profile_agreement
           (x := representative (profile_class w)) (y := w) (p := p));
    [apply profile_class_spec | exact Hin].
Qed.

(** * Explicit finite cover and its exponential bound *)

Definition realised_profile_dec (bits : list bool) :
    {realised_profile bits} + {~ realised_profile bits} :=
  excluded_middle_informative (realised_profile bits).

Definition filtered_world_cover : list filtered_world :=
  @sig_filter (list bool) realised_profile realised_profile_dec
    (bool_profiles (length (subformulas target))).

Theorem filtered_world_cover_bound :
  NoDup filtered_world_cover /\
  (forall X : filtered_world, In X filtered_world_cover) /\
  length filtered_world_cover <= 2 ^ length (subformulas target).
Proof.
  split.
  - unfold filtered_world_cover.
    apply sig_filter_nodup. apply bool_profiles_nodup.
  - split.
    + intro X. unfold filtered_world_cover.
      apply sig_filter_complete.
      apply bool_profiles_complete.
      destruct X as [bits [w Hw]]; simpl in *.
      subst bits. apply truth_profile_length.
    + unfold filtered_world_cover.
      eapply Nat.le_trans; [apply sig_filter_length_le |].
      rewrite bool_profiles_length. lia.
Qed.

Definition finite_frame (G : frame) : Prop :=
  exists cover : list (World G), forall w, In w cover.

Corollary coarsest_filtered_frame_finite :
  finite_frame coarsest_filtered_frame.
Proof.
  exists filtered_world_cover.
  exact (proj1 (proj2 filtered_world_cover_bound)).
Qed.

(** * Countermodels and the semantic finite-model property *)

Theorem finite_countermodel :
  forall w,
    ~ satisfies F V w target ->
    exists (G : frame) (U : valuation AtomType G) (u : World G),
      finite_frame G /\
      (exists cover : list (World G),
          NoDup cover /\
          (forall z, In z cover) /\
          length cover <= 2 ^ length (subformulas target)) /\
      ~ satisfies G U u target.
Proof.
  intros w Hcounter.
  exists coarsest_filtered_frame, coarsest_filtered_valuation,
         (profile_class w).
  split; [apply coarsest_filtered_frame_finite |].
  split.
  - exists filtered_world_cover. apply filtered_world_cover_bound.
  - intro Hfiltered. apply Hcounter.
    apply (proj1 (coarsest_filtration_truth_at_class
                    (p := target) (subformulas_self target) w)).
    exact Hfiltered.
Qed.

End CoarsestFiltration.

Definition valid_on_finite_frames {AtomType} (p : formula AtomType) : Prop :=
  forall F : frame, finite_frame F -> valid F p.

Definition valid_on_all_frames {AtomType} (p : formula AtomType) : Prop :=
  forall F : frame, valid F p.

Theorem modal_finite_model_property :
  forall (AtomType : Type) (p : formula AtomType),
    valid_on_finite_frames p <-> valid_on_all_frames p.
Proof.
  intros AtomType p; split.
  - intros Hfinite F V w.
    pose (G := @coarsest_filtered_frame AtomType F V p).
    pose (U := @coarsest_filtered_valuation AtomType F V p).
    apply (proj1 (@coarsest_filtration_truth_at_class
                    AtomType F V p p (subformulas_self p) w)).
    exact (Hfinite G
             (@coarsest_filtered_frame_finite AtomType F V p)
             U (@profile_class AtomType F V p w)).
  - intros Hall F Hfinite. apply Hall.
Qed.

(** A positive, satisfiability-oriented form of the same filtration result. *)
Definition modal_satisfiable {AtomType} (p : formula AtomType) : Prop :=
  exists (F : frame) (V : valuation AtomType F) (w : World F),
    satisfies F V w p.

Definition finite_modal_satisfiable {AtomType} (p : formula AtomType) : Prop :=
  exists (F : frame) (V : valuation AtomType F) (w : World F),
    finite_frame F /\ satisfies F V w p.

Theorem satisfiable_has_finite_model :
  forall (AtomType : Type) (p : formula AtomType),
    modal_satisfiable p -> finite_modal_satisfiable p.
Proof.
  intros AtomType p [F [V [w Hw]]].
  exists (@coarsest_filtered_frame AtomType F V p),
         (@coarsest_filtered_valuation AtomType F V p),
         (@profile_class AtomType F V p w).
  split.
  - exact (@coarsest_filtered_frame_finite AtomType F V p).
  - apply (proj2 (@coarsest_filtration_truth_at_class
                    AtomType F V p p (subformulas_self p) w)).
    exact Hw.
Qed.

(** The customary countermodel formulation follows immediately. *)
Corollary not_valid_has_finite_countermodel :
  forall (AtomType : Type) (p : formula AtomType),
    ~ valid_on_all_frames p ->
    exists (F : frame) (V : valuation AtomType F) (w : World F),
      finite_frame F /\ ~ satisfies F V w p.
Proof.
  intros AtomType p Hnot.
  apply NNPP; intro Hnone. apply Hnot.
  intros F V w.
  apply NNPP; intro Hcounter.
  destruct (@finite_countermodel AtomType F V p w Hcounter)
    as [G [U [u [Hfinite [_ Hbad]]]]].
  apply Hnone. exists G, U, u. auto.
Qed.
