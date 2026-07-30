(** Finite truth-profile filtrations for intuitionistic propositional models.

    This ports Foundation/Propositional/Kripke/Filtration.lean.  Foundation
    quotients worlds by agreement on a finite subformula-closed set.  We use
    the equivalent type of realised Boolean truth profiles instead: equality
    is concrete, a finite cover is explicit, and atoms remain polymorphic.

    A single filtration interface factors the truth lemma.  It is instantiated
    by the coarsest persistence relation and by the transitive closure of the
    relation induced from the original frame. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Logic.ClassicalDescription.
From Stdlib Require Import Logic.ClassicalEpsilon Logic.ProofIrrelevance.
From FoundationModal Require Import
  Filtration PropositionalFormula PropositionalKripke.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Realised truth profiles *)

Definition pfilter_truth_profile {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (w : pkripke_world (pkripke_model_frame M)) : list bool :=
  map (fun p => truth_bit (pkripke_forces M w p)) T.

Arguments pfilter_truth_profile {Atom} M T w.

Lemma pfilter_truth_profile_length :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) w,
    length (pfilter_truth_profile M T w) = length T.
Proof. intros; unfold pfilter_truth_profile; now rewrite length_map. Qed.

Definition pfilter_realised_profile {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (bits : list bool) : Prop :=
  exists w, pfilter_truth_profile M T w = bits.

Arguments pfilter_realised_profile {Atom} M T bits.

Definition pfilter_world {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) : Type :=
  {bits : list bool | pfilter_realised_profile M T bits}.

Arguments pfilter_world {Atom} M T.

Definition pfilter_class {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (w : pkripke_world (pkripke_model_frame M)) : pfilter_world M T :=
  exist (pfilter_realised_profile M T) (pfilter_truth_profile M T w)
    (ex_intro _ w eq_refl).

Arguments pfilter_class {Atom} M T w.

Definition pfilter_representative {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (X : pfilter_world M T) :
    pkripke_world (pkripke_model_frame M) :=
  proj1_sig
    (constructive_indefinite_description
       (fun w => pfilter_truth_profile M T w = proj1_sig X)
       (proj2_sig X)).

Arguments pfilter_representative {Atom} M T X.

Lemma pfilter_representative_spec :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) (X : pfilter_world M T),
    pfilter_truth_profile M T (pfilter_representative M T X) = proj1_sig X.
Proof.
  intros Atom M T X. unfold pfilter_representative.
  exact (proj2_sig
    (constructive_indefinite_description
      (fun w => pfilter_truth_profile M T w = proj1_sig X)
      (proj2_sig X))).
Qed.

Lemma pfilter_profile_agreement :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) x y p,
    pfilter_truth_profile M T x = pfilter_truth_profile M T y ->
    In p T ->
    (pkripke_forces M x p <-> pkripke_forces M y p).
Proof.
  intros Atom M T x y p Heq Hp.
  unfold pfilter_truth_profile in Heq.
  pose proof (@map_pointwise_of_eq (pformula Atom) bool
    (fun q => truth_bit (pkripke_forces M x q))
    (fun q => truth_bit (pkripke_forces M y q)) T Heq p Hp) as Hbit.
  split; intro H.
  - apply (proj1 (truth_bit_true_iff (pkripke_forces M y p))).
    rewrite <- Hbit.
    now apply (proj2 (truth_bit_true_iff (pkripke_forces M x p))).
  - apply (proj1 (truth_bit_true_iff (pkripke_forces M x p))).
    rewrite Hbit.
    now apply (proj2 (truth_bit_true_iff (pkripke_forces M y p))).
Qed.

Lemma pfilter_class_agreement :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) x p,
    In p T ->
    (pkripke_forces M (pfilter_representative M T (pfilter_class M T x)) p
      <-> pkripke_forces M x p).
Proof.
  intros Atom M T x p Hp.
  eapply pfilter_profile_agreement; [|exact Hp].
  apply pfilter_representative_spec.
Qed.

Lemma pfilter_class_representative_eq :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) (X : pfilter_world M T),
    pfilter_class M T (pfilter_representative M T X) = X.
Proof.
  intros Atom M T [bits Hbits].
  apply eq_sig_hprop.
  - intros; apply proof_irrelevance.
  - simpl. apply pfilter_representative_spec.
Qed.

Lemma pfilter_world_eq_of_agreement :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) (X Y : pfilter_world M T),
    (forall p, In p T ->
      (pkripke_forces M (pfilter_representative M T X) p <->
       pkripke_forces M (pfilter_representative M T Y) p)) ->
    X = Y.
Proof.
  intros Atom M T X Y Hagree.
  apply eq_sig_hprop.
  - intros; apply proof_irrelevance.
  - rewrite <- (@pfilter_representative_spec Atom M T X).
    rewrite <- (@pfilter_representative_spec Atom M T Y).
    unfold pfilter_truth_profile.
    apply map_ext_in. intros p Hp.
    unfold truth_bit.
    destruct (excluded_middle_informative
      (pkripke_forces M (pfilter_representative M T X) p)) as [HX | HX];
    destruct (excluded_middle_informative
      (pkripke_forces M (pfilter_representative M T Y) p)) as [HY | HY];
    try reflexivity.
    + exfalso. apply HY. now apply (proj1 (Hagree p Hp)).
    + exfalso. apply HX. now apply (proj2 (Hagree p Hp)).
Qed.

(** The profile presentation exposes finiteness as data, without requiring
    decidable formula equality. *)
Definition pfilter_world_cover {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) :
    list (pfilter_world M T) :=
  @sig_filter (list bool) (pfilter_realised_profile M T)
    (fun bits => excluded_middle_informative
      (pfilter_realised_profile M T bits))
    (bool_profiles (length T)).

Lemma pfilter_world_cover_complete :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) (X : pfilter_world M T),
    In X (pfilter_world_cover M T).
Proof.
  intros Atom M T [bits [w Hw]].
  apply sig_filter_complete. simpl.
  subst bits. apply bool_profiles_complete.
  apply pfilter_truth_profile_length.
Qed.

Lemma pfilter_world_cover_nodup :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)),
    NoDup (pfilter_world_cover M T).
Proof.
  intros. apply sig_filter_nodup. apply bool_profiles_nodup.
Qed.

Lemma pfilter_world_cover_bound :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)),
    length (pfilter_world_cover M T) <= 2 ^ length T.
Proof.
  intros Atom M T. unfold pfilter_world_cover.
  eapply Nat.le_trans; [apply sig_filter_length_le |].
  rewrite bool_profiles_length. apply Nat.le_refl.
Qed.

(** * A common filtration interface and truth lemma *)

Record pfiltration_data {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) : Type := {
  pfiltration_rel : pfilter_world M T -> pfilter_world M T -> Prop;
  pfiltration_rel_refl : forall X, pfiltration_rel X X;
  pfiltration_rel_trans : forall X Y Z,
    pfiltration_rel X Y -> pfiltration_rel Y Z -> pfiltration_rel X Z;
  pfiltration_atom_value : Atom -> pfilter_world M T -> Prop;
  pfiltration_atom_persistent : forall a X Y,
    pfiltration_rel X Y ->
    pfiltration_atom_value a X -> pfiltration_atom_value a Y;
  pfiltration_rel_forth : forall x y,
    pkripke_access (pkripke_model_frame M) x y ->
    pfiltration_rel (pfilter_class M T x) (pfilter_class M T y);
  pfiltration_rel_back : forall X Y,
    pfiltration_rel X Y -> forall p, In p T ->
    pkripke_forces M (pfilter_representative M T X) p ->
    pkripke_forces M (pfilter_representative M T Y) p;
  pfiltration_atom_spec : forall X a, In (PAtom a) T ->
    (pfiltration_atom_value a X <->
     pkripke_forces M (pfilter_representative M T X) (PAtom a))
}.

Arguments pfiltration_rel {Atom M T} _ _ _.
Arguments pfiltration_atom_value {Atom M T} _ _ _.

Definition pfiltration_frame {Atom : Type}
    {M : pkripke_model Atom} {T : list (pformula Atom)}
    (D : pfiltration_data M T) : pkripke_frame :=
  {| pkripke_world := pfilter_world M T;
     pkripke_access := pfiltration_rel D;
     pkripke_access_refl := @pfiltration_rel_refl Atom M T D;
     pkripke_access_trans := @pfiltration_rel_trans Atom M T D |}.

Definition pfiltration_valuation {Atom : Type}
    {M : pkripke_model Atom} {T : list (pformula Atom)}
    (D : pfiltration_data M T) :
    pkripke_valuation Atom (pfiltration_frame D) :=
  @Build_pkripke_valuation Atom (pfiltration_frame D)
    (pfiltration_atom_value D)
    (@pfiltration_atom_persistent Atom M T D).

Definition pfiltration_model {Atom : Type}
    {M : pkripke_model Atom} {T : list (pformula Atom)}
    (D : pfiltration_data M T) : pkripke_model Atom :=
  {| pkripke_model_frame := pfiltration_frame D;
     pkripke_model_valuation := pfiltration_valuation D |}.

Theorem pfiltration_truth :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)),
    pformula_subformula_closed T ->
    forall (D : pfiltration_data M T) p,
      In p T -> forall x,
      (pkripke_forces M x p <->
       pkripke_forces (pfiltration_model D) (pfilter_class M T x) p).
Proof.
  intros Atom M T HT D p.
  induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros HpT x; cbn.
  - split; intro H.
    + apply (proj2 (@pfiltration_atom_spec Atom M T D
        (pfilter_class M T x) a HpT)).
      apply (proj2 (@pfilter_class_agreement Atom M T x (PAtom a) HpT)). exact H.
    + apply (proj1 (@pfilter_class_agreement Atom M T x (PAtom a) HpT)).
      apply (proj1 (@pfiltration_atom_spec Atom M T D
        (pfilter_class M T x) a HpT)). exact H.
  - tauto.
  - pose proof (HT _ _ HpT (proj1 (pformula_subformulas_left p q))) as Hp.
    pose proof (HT _ _ HpT (proj1 (pformula_subformulas_right p q))) as Hq.
    rewrite (IHp Hp x), (IHq Hq x). tauto.
  - pose proof (HT _ _ HpT (proj1 (proj2 (pformula_subformulas_left p q)))) as Hp.
    pose proof (HT _ _ HpT (proj1 (proj2 (pformula_subformulas_right p q)))) as Hq.
    rewrite (IHp Hp x), (IHq Hq x). tauto.
  - pose proof (HT _ _ HpT (proj2 (proj2 (pformula_subformulas_left p q)))) as Hp.
    pose proof (HT _ _ HpT (proj2 (proj2 (pformula_subformulas_right p q)))) as Hq.
    split.
    + intros Himp Y RXY HYp.
      pose (y := pfilter_representative M T Y).
      assert (HclassY : pfilter_class M T y = Y).
      { unfold y. apply pfilter_class_representative_eq. }
      assert (HYp0 : pkripke_forces M y p).
      { apply (proj2 (IHp Hp y)). rewrite HclassY. exact HYp. }
      assert (HXimp :
        pkripke_forces M
          (pfilter_representative M T (pfilter_class M T x))
          (PImp p q)).
      { apply (proj2 (@pfilter_class_agreement Atom M T x (PImp p q) HpT)).
        exact Himp. }
      assert (HYimp : pkripke_forces M y (PImp p q)).
      { unfold y. eapply pfiltration_rel_back; eauto. }
      assert (HYq0 : pkripke_forces M y q).
      { apply (HYimp y (pkripke_access_refl _ y) HYp0). }
      pose proof (proj1 (IHq Hq y) HYq0) as HYq.
      now rewrite HclassY in HYq.
    + intros Himp y Rxy Hyp.
      apply (proj2 (IHq Hq y)).
      apply (Himp (pfilter_class M T y)).
      * now apply pfiltration_rel_forth.
      * now apply (proj1 (IHp Hp y)).
Qed.

(** * Coarsest filtration *)

Definition pcoarsest_filtration_rel {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (X Y : pfilter_world M T) : Prop :=
  forall p, In p T ->
    pkripke_forces M (pfilter_representative M T X) p ->
    pkripke_forces M (pfilter_representative M T Y) p.

Definition pstandard_filtration_atom {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (a : Atom) (X : pfilter_world M T) : Prop :=
  In (PAtom a) T ->
  pkripke_forces M (pfilter_representative M T X) (PAtom a).

Definition pcoarsest_filtration_data {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) :
    pfiltration_data M T.
Proof.
  refine {| pfiltration_rel := @pcoarsest_filtration_rel Atom M T;
            pfiltration_atom_value := @pstandard_filtration_atom Atom M T |}.
  - intros X p Hp H. exact H.
  - intros X Y Z HXY HYZ p Hp HX. now apply HYZ, HXY.
  - intros a X Y HXY HX Ha.
    apply HXY with (p := PAtom a); [exact Ha | now apply HX].
  - intros x y Rxy p Hp HX.
    apply (proj2 (@pfilter_class_agreement Atom M T y p Hp)).
    eapply pkripke_forces_persistent; [exact Rxy |].
    now apply (proj1 (@pfilter_class_agreement Atom M T x p Hp)).
  - intros X Y HXY. exact HXY.
  - intros X a Ha. split.
    + intro H. now apply H.
    + intros H _. exact H.
Defined.

Lemma pcoarsest_filtration_antisymmetric :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) X Y,
    @pcoarsest_filtration_rel Atom M T X Y ->
    @pcoarsest_filtration_rel Atom M T Y X -> X = Y.
Proof.
  intros Atom M T X Y HXY HYX.
  apply pfilter_world_eq_of_agreement. intros p Hp. split.
  - now apply HXY with (p := p).
  - now apply HYX with (p := p).
Qed.

Definition pcoarsest_filtration_model {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) :
    pkripke_model Atom :=
  pfiltration_model (pcoarsest_filtration_data M T).

Theorem pcoarsest_filtration_truth :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)),
    pformula_subformula_closed T ->
    forall p, In p T -> forall x,
      (pkripke_forces M x p <->
       pkripke_forces (pcoarsest_filtration_model M T)
         (pfilter_class M T x) p).
Proof.
  intros. now apply pfiltration_truth.
Qed.

(** * Finest transitive-closure filtration *)

Definition pfinest_filtration_edge {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom))
    (X Y : pfilter_world M T) : Prop :=
  exists x y,
    X = pfilter_class M T x /\
    Y = pfilter_class M T y /\
    pkripke_access (pkripke_model_frame M) x y.

Inductive pfilter_path {W : Type} (E : W -> W -> Prop) (x : W) : W -> Prop :=
| pfilter_path_refl : pfilter_path E x x
| pfilter_path_snoc : forall y z,
    pfilter_path E x y -> E y z -> pfilter_path E x z.

Arguments pfilter_path_refl {W E x}.
Arguments pfilter_path_snoc {W E x y z} _ _.

Lemma pfilter_path_trans :
  forall (W : Type) (E : W -> W -> Prop) x y z,
    pfilter_path E x y -> pfilter_path E y z -> pfilter_path E x z.
Proof.
  intros W E x y z Hxy Hyz.
  induction Hyz as [|u v Hyu IH Huv].
  - exact Hxy.
  - exact (pfilter_path_snoc IH Huv).
Qed.

Definition pfinest_filtration_rel {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) :
    pfilter_world M T -> pfilter_world M T -> Prop :=
  pfilter_path (@pfinest_filtration_edge Atom M T).

Lemma pfinest_edge_preserves :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) X Y,
    @pfinest_filtration_edge Atom M T X Y -> forall p, In p T ->
    pkripke_forces M (pfilter_representative M T X) p ->
    pkripke_forces M (pfilter_representative M T Y) p.
Proof.
  intros Atom M T X Y [x [y [-> [-> Rxy]]]] p Hp HX.
  apply (proj2 (@pfilter_class_agreement Atom M T y p Hp)).
  eapply pkripke_forces_persistent; [exact Rxy |].
  now apply (proj1 (@pfilter_class_agreement Atom M T x p Hp)).
Qed.

Lemma pfinest_path_preserves :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) X Y,
    @pfinest_filtration_rel Atom M T X Y -> forall p, In p T ->
    pkripke_forces M (pfilter_representative M T X) p ->
    pkripke_forces M (pfilter_representative M T Y) p.
Proof.
  intros Atom M T X Y Hpath. induction Hpath; intros p Hp HX.
  - exact HX.
  - eapply pfinest_edge_preserves; [exact H | exact Hp |].
    now apply IHHpath.
Qed.

Definition pfinest_filtration_data {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) :
    pfiltration_data M T.
Proof.
  refine {| pfiltration_rel := @pfinest_filtration_rel Atom M T;
            pfiltration_atom_value := @pstandard_filtration_atom Atom M T |}.
  - intro X. apply pfilter_path_refl.
  - intros X Y Z. apply pfilter_path_trans.
  - intros a X Y HXY HX Ha.
    eapply pfinest_path_preserves; [exact HXY | exact Ha |].
    now apply HX.
  - intros x y Rxy.
    eapply pfilter_path_snoc; [apply pfilter_path_refl |].
    exists x, y. repeat split; assumption.
  - intros X Y HXY. now apply pfinest_path_preserves.
  - intros X a Ha. split.
    + intro H. now apply H.
    + intros H _. exact H.
Defined.

Definition pfinest_filtration_model {Atom : Type}
    (M : pkripke_model Atom) (T : list (pformula Atom)) :
    pkripke_model Atom :=
  pfiltration_model (pfinest_filtration_data M T).

Theorem pfinest_filtration_truth :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)),
    pformula_subformula_closed T ->
    forall p, In p T -> forall x,
      (pkripke_forces M x p <->
       pkripke_forces (pfinest_filtration_model M T)
         (pfilter_class M T x) p).
Proof.
  intros. now apply pfiltration_truth.
Qed.

Lemma pfinest_filtration_rel_in_coarsest :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) X Y,
    @pfinest_filtration_rel Atom M T X Y ->
    @pcoarsest_filtration_rel Atom M T X Y.
Proof.
  intros Atom M T X Y H p Hp HX.
  eapply pfinest_path_preserves; eauto.
Qed.

Lemma pfinest_filtration_antisymmetric :
  forall (Atom : Type) (M : pkripke_model Atom)
      (T : list (pformula Atom)) X Y,
    @pfinest_filtration_rel Atom M T X Y ->
    @pfinest_filtration_rel Atom M T Y X -> X = Y.
Proof.
  intros Atom M T X Y HXY HYX.
  apply pcoarsest_filtration_antisymmetric.
  - now apply pfinest_filtration_rel_in_coarsest.
  - now apply pfinest_filtration_rel_in_coarsest.
Qed.

(** Target-specialized corollaries use the canonical finite closure. *)
Theorem pcoarsest_subformula_filtration_truth :
  forall (Atom : Type) (M : pkripke_model Atom)
      (target p : pformula Atom),
    pformula_is_subformula p target -> forall x,
      (pkripke_forces M x p <->
       pkripke_forces
         (pcoarsest_filtration_model M (pformula_subformulas target))
         (pfilter_class M (pformula_subformulas target) x) p).
Proof.
  intros. eapply pcoarsest_filtration_truth; eauto.
  apply pformula_subformulas_closed.
Qed.

Theorem pfinest_subformula_filtration_truth :
  forall (Atom : Type) (M : pkripke_model Atom)
      (target p : pformula Atom),
    pformula_is_subformula p target -> forall x,
      (pkripke_forces M x p <->
       pkripke_forces
         (pfinest_filtration_model M (pformula_subformulas target))
         (pfilter_class M (pformula_subformulas target) x) p).
Proof.
  intros. eapply pfinest_filtration_truth; eauto.
  apply pformula_subformulas_closed.
Qed.
