(** Bisimulations, bounded morphisms, and rooted generated models for
    intuitionistic propositional Kripke semantics.

    This ports Foundation's Propositional/Kripke [Preservation] and [Rooted]
    modules.  Atoms are arbitrary and frames are preorders: neither the
    preservation argument nor point generation needs antisymmetry, decidable
    equality, or an inhabited-world field. *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import
  Logic.ClassicalDescription Logic.Classical_Prop Logic.ProofIrrelevance.
From FoundationModal Require Import PropositionalFormula PropositionalKripke.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Bisimulation and formula equivalence *)

Record pkripke_bisimulation {Atom : Type}
    (M1 M2 : pkripke_model Atom) : Type := {
  pkripke_bisimilar :
    pkripke_world (pkripke_model_frame M1) ->
    pkripke_world (pkripke_model_frame M2) -> Prop;
  pkripke_bisimulation_atoms :
    forall x y a, pkripke_bisimilar x y ->
      (pkripke_atom_value (pkripke_model_valuation M1) a x <->
       pkripke_atom_value (pkripke_model_valuation M2) a y);
  pkripke_bisimulation_forth :
    forall x y x', pkripke_bisimilar x y ->
      pkripke_access (pkripke_model_frame M1) x x' ->
      exists y', pkripke_bisimilar x' y' /\
        pkripke_access (pkripke_model_frame M2) y y';
  pkripke_bisimulation_back :
    forall x y y', pkripke_bisimilar x y ->
      pkripke_access (pkripke_model_frame M2) y y' ->
      exists x', pkripke_bisimilar x' y' /\
        pkripke_access (pkripke_model_frame M1) x x'
}.

Arguments pkripke_bisimilar {Atom M1 M2} _ _ _.

Definition pkripke_bisimulation_symmetry {Atom M1 M2}
    (Z : @pkripke_bisimulation Atom M1 M2) :
    @pkripke_bisimulation Atom M2 M1.
Proof.
  refine {| pkripke_bisimilar := fun y x => pkripke_bisimilar Z x y |}.
  - intros y x a Hxy. symmetry.
    exact (@pkripke_bisimulation_atoms Atom M1 M2 Z x y a Hxy).
  - intros y x y' Hxy Ryy'.
    destruct (@pkripke_bisimulation_back Atom M1 M2 Z x y y' Hxy Ryy')
      as [x' [Hx' Rxx']].
    exists x'; auto.
  - intros y x x' Hxy Rxx'.
    destruct (@pkripke_bisimulation_forth Atom M1 M2 Z x y x' Hxy Rxx')
      as [y' [Hy' Ryy']].
    exists y'; auto.
Defined.

Theorem pkripke_bisimulation_invariance :
  forall (Atom : Type) (M1 M2 : pkripke_model Atom)
         (Z : pkripke_bisimulation M1 M2)
         (p : pformula Atom) x y,
    pkripke_bisimilar Z x y ->
    (pkripke_forces M1 x p <-> pkripke_forces M2 y p).
Proof.
  intros Atom M1 M2 Z p.
  induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros x y Hxy; cbn.
  - exact (@pkripke_bisimulation_atoms Atom M1 M2 Z x y a Hxy).
  - tauto.
  - now rewrite (IHp x y Hxy), (IHq x y Hxy).
  - now rewrite (IHp x y Hxy), (IHq x y Hxy).
  - split; intros Himp z Ryz Hzp.
    + destruct (@pkripke_bisimulation_back Atom M1 M2 Z x y z Hxy Ryz)
        as [u [Huz Rxu]].
      apply (proj1 (IHq u z Huz)), Himp with (v := u); auto.
      now apply (proj2 (IHp u z Huz)).
    + destruct (@pkripke_bisimulation_forth Atom M1 M2 Z x y z Hxy Ryz)
        as [u [Hzu Ryu]].
      apply (proj2 (IHq z u Hzu)), Himp with (v := u); auto.
      now apply (proj1 (IHp z u Hzu)).
Qed.

Definition pkripke_equivalent {Atom : Type}
    {M1 : pkripke_model Atom}
    (x : pkripke_world (pkripke_model_frame M1))
    {M2 : pkripke_model Atom}
    (y : pkripke_world (pkripke_model_frame M2)) : Prop :=
  forall p : pformula Atom,
    pkripke_forces M1 x p <-> pkripke_forces M2 y p.

Arguments pkripke_equivalent {Atom M1} x {M2} y.

Lemma pkripke_equivalent_of_bisimilar :
  forall (Atom : Type) (M1 M2 : pkripke_model Atom)
         (Z : pkripke_bisimulation M1 M2) x y,
    pkripke_bisimilar Z x y -> pkripke_equivalent x y.
Proof.
  intros Atom M1 M2 Z x y Hxy p.
  exact (@pkripke_bisimulation_invariance Atom M1 M2 Z p x y Hxy).
Qed.

Lemma pkripke_equivalent_symmetry :
  forall (Atom : Type) (M1 M2 : pkripke_model Atom)
         (x : pkripke_world (pkripke_model_frame M1))
         (y : pkripke_world (pkripke_model_frame M2)),
    pkripke_equivalent x y -> pkripke_equivalent y x.
Proof. intros Atom M1 M2 x y H p; symmetry; apply H. Qed.

(** * Bounded morphisms *)

Record pkripke_frame_p_morphism (F1 F2 : pkripke_frame) : Type := {
  pkripke_pmap : pkripke_world F1 -> pkripke_world F2;
  pkripke_p_morphism_forth : forall x y,
    pkripke_access F1 x y ->
    pkripke_access F2 (pkripke_pmap x) (pkripke_pmap y);
  pkripke_p_morphism_back : forall x z,
    pkripke_access F2 (pkripke_pmap x) z ->
    exists y, pkripke_pmap y = z /\ pkripke_access F1 x y
}.

Arguments pkripke_pmap {F1 F2} _ _.

Definition pkripke_frame_p_morphism_id (F : pkripke_frame) :
    pkripke_frame_p_morphism F F.
Proof. refine {| pkripke_pmap := fun x => x |}; firstorder. Defined.

Definition pkripke_frame_p_morphism_comp {F1 F2 F3}
    (f : pkripke_frame_p_morphism F1 F2)
    (g : pkripke_frame_p_morphism F2 F3) :
    pkripke_frame_p_morphism F1 F3.
Proof.
  refine {| pkripke_pmap := fun x => pkripke_pmap g (pkripke_pmap f x) |}.
  - intros x y Rxy.
    exact (@pkripke_p_morphism_forth F2 F3 g
      (pkripke_pmap f x) (pkripke_pmap f y)
      (@pkripke_p_morphism_forth F1 F2 f x y Rxy)).
  - intros x z Rxz.
    destruct (@pkripke_p_morphism_back F2 F3 g
      (pkripke_pmap f x) z Rxz) as [y [Hy Rfy]].
    destruct (@pkripke_p_morphism_back F1 F2 f x y Rfy)
      as [u [Hu Rxu]].
    exists u; split; [now rewrite Hu, Hy | exact Rxu].
Defined.

Record pkripke_model_p_morphism {Atom : Type}
    (M1 M2 : pkripke_model Atom) : Type := {
  pkripke_model_p_morphism_frame :
    pkripke_frame_p_morphism
      (pkripke_model_frame M1) (pkripke_model_frame M2);
  pkripke_model_p_morphism_atoms : forall a x,
    pkripke_atom_value (pkripke_model_valuation M1) a x <->
    pkripke_atom_value (pkripke_model_valuation M2) a
      (pkripke_pmap pkripke_model_p_morphism_frame x)
}.

Arguments pkripke_model_p_morphism_frame {Atom M1 M2} _.

Definition pkripke_model_pmap {Atom : Type}
    {M1 M2 : pkripke_model Atom}
    (f : pkripke_model_p_morphism M1 M2) :=
  pkripke_pmap (pkripke_model_p_morphism_frame f).

Arguments pkripke_model_pmap {Atom M1 M2} _ _.

Definition pkripke_model_p_morphism_of_atomic {Atom : Type}
    {M1 M2 : pkripke_model Atom}
    (f : pkripke_frame_p_morphism
      (pkripke_model_frame M1) (pkripke_model_frame M2))
    (Hatoms : forall a x,
      pkripke_atom_value (pkripke_model_valuation M1) a x <->
      pkripke_atom_value (pkripke_model_valuation M2) a
        (pkripke_pmap f x)) :
    pkripke_model_p_morphism M1 M2 :=
  {| pkripke_model_p_morphism_frame := f;
     pkripke_model_p_morphism_atoms := Hatoms |}.

Definition pkripke_model_p_morphism_id {Atom : Type}
    (M : pkripke_model Atom) : pkripke_model_p_morphism M M.
Proof.
  refine {| pkripke_model_p_morphism_frame :=
              pkripke_frame_p_morphism_id (pkripke_model_frame M) |}.
  intros; reflexivity.
Defined.

Definition pkripke_model_p_morphism_comp {Atom : Type}
    {M1 M2 M3 : pkripke_model Atom}
    (f : pkripke_model_p_morphism M1 M2)
    (g : pkripke_model_p_morphism M2 M3) :
    pkripke_model_p_morphism M1 M3.
Proof.
  refine {| pkripke_model_p_morphism_frame :=
      pkripke_frame_p_morphism_comp
        (pkripke_model_p_morphism_frame f)
        (pkripke_model_p_morphism_frame g) |}.
  intros a x; simpl.
  transitivity
    (pkripke_atom_value (pkripke_model_valuation M2) a
      (pkripke_model_pmap f x)); apply pkripke_model_p_morphism_atoms.
Defined.

Definition pkripke_model_p_morphism_bisimulation {Atom : Type}
    {M1 M2 : pkripke_model Atom}
    (f : pkripke_model_p_morphism M1 M2) :
    pkripke_bisimulation M1 M2.
Proof.
  refine {| pkripke_bisimilar := fun x y => y = pkripke_model_pmap f x |}.
  - intros x y a ->. apply pkripke_model_p_morphism_atoms.
  - intros x y x' -> Rxx'.
    exists (pkripke_model_pmap f x'); split; [reflexivity |].
    exact (@pkripke_p_morphism_forth
      (pkripke_model_frame M1) (pkripke_model_frame M2)
      (pkripke_model_p_morphism_frame f) x x' Rxx').
  - intros x y y' -> Ryy'.
    destruct (@pkripke_p_morphism_back
      (pkripke_model_frame M1) (pkripke_model_frame M2)
      (pkripke_model_p_morphism_frame f) x y' Ryy')
      as [x' [Hx' Rxx']].
    exists x'; split; [symmetry; exact Hx' | exact Rxx'].
Defined.

Theorem pkripke_model_p_morphism_equivalence :
  forall (Atom : Type) (M1 M2 : pkripke_model Atom)
         (f : pkripke_model_p_morphism M1 M2) x,
    pkripke_equivalent x (pkripke_model_pmap f x).
Proof.
  intros Atom M1 M2 f x.
  apply (@pkripke_equivalent_of_bisimilar Atom M1 M2
    (pkripke_model_p_morphism_bisimulation f)
    x (pkripke_model_pmap f x)).
  reflexivity.
Qed.

(** * Point-generated frames and models *)

Definition pkripke_frame_antisymmetric (F : pkripke_frame) : Prop :=
  forall x y, pkripke_access F x y -> pkripke_access F y x -> x = y.

Definition pkripke_frame_irreflexive (F : pkripke_frame) : Prop :=
  forall x, ~ pkripke_access F x x.

Definition pkripke_frame_finite (F : pkripke_frame) : Prop :=
  exists cover : list (pkripke_world F), forall w, In w cover.

Definition pkripke_frame_root (F : pkripke_frame)
    (r : pkripke_world F) : Prop :=
  forall w, w <> r -> pkripke_access F r w.

Arguments pkripke_frame_root F r : clear implicits.

Definition pkripke_frame_rooted (F : pkripke_frame) : Prop :=
  exists r, pkripke_frame_root F r.

Definition pkripke_point_generated_member (F : pkripke_frame)
    (r x : pkripke_world F) : Prop :=
  x = r \/ pkripke_access F r x.

Arguments pkripke_point_generated_member F r x : clear implicits.

Definition pkripke_point_generated_frame (F : pkripke_frame)
    (r : pkripke_world F) : pkripke_frame :=
  {| pkripke_world := {x : pkripke_world F |
       pkripke_point_generated_member F r x};
     pkripke_access := fun x y =>
       pkripke_access F (proj1_sig x) (proj1_sig y);
     pkripke_access_refl := fun x =>
       pkripke_access_refl F (proj1_sig x);
     pkripke_access_trans := fun x y z =>
       pkripke_access_trans F (proj1_sig x) (proj1_sig y) (proj1_sig z) |}.

Arguments pkripke_point_generated_frame F r : clear implicits.

Definition pkripke_point_generated_root (F : pkripke_frame)
    (r : pkripke_world F) :
    pkripke_world (pkripke_point_generated_frame F r) :=
  exist _ r (or_introl eq_refl).

Arguments pkripke_point_generated_root F r : clear implicits.

Lemma pkripke_point_generated_sig_eq :
  forall F r x (hx hy : pkripke_point_generated_member F r x),
    (exist _ x hx : pkripke_world (pkripke_point_generated_frame F r)) =
    exist _ x hy.
Proof.
  intros F r x hx hy. replace hy with hx by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma pkripke_point_generated_root_is_root :
  forall F r,
    pkripke_frame_root (pkripke_point_generated_frame F r)
      (pkripke_point_generated_root F r).
Proof.
  intros F r [x [-> | Hrx]] Hneq; simpl; [|exact Hrx].
  exfalso. apply Hneq. apply pkripke_point_generated_sig_eq.
Qed.

Theorem pkripke_point_generated_rooted :
  forall F r, pkripke_frame_rooted (pkripke_point_generated_frame F r).
Proof. intros F r; exists (pkripke_point_generated_root F r); apply pkripke_point_generated_root_is_root. Qed.

Fixpoint pkripke_sig_filter {A : Type} (P : A -> Prop)
    (dec : forall x, {P x} + {~ P x}) (xs : list A) :
    list {x : A | P x} :=
  match xs with
  | [] => []
  | x :: rest =>
      match dec x with
      | left Hx => exist P x Hx :: @pkripke_sig_filter A P dec rest
      | right _ => @pkripke_sig_filter A P dec rest
      end
  end.

Lemma pkripke_sig_filter_complete :
  forall (A : Type) (P : A -> Prop)
         (dec : forall x, {P x} + {~ P x}) (xs : list A)
         (X : {x : A | P x}),
    In (proj1_sig X) xs ->
    In X (@pkripke_sig_filter A P dec xs).
Proof.
  intros A P dec xs; induction xs as [|x xs IH]; intros X Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst x. destruct (dec (proj1_sig X)) as [HP | Hnot].
      * left. destruct X as [x HX]; simpl in *.
        replace HP with HX by apply proof_irrelevance. reflexivity.
      * exfalso. exact (Hnot (proj2_sig X)).
    + destruct (dec x); simpl; [right |]; now apply IH.
Qed.

Definition pkripke_point_generated_cover (F : pkripke_frame)
    (r : pkripke_world F) (xs : list (pkripke_world F)) :
    list (pkripke_world (pkripke_point_generated_frame F r)) :=
  @pkripke_sig_filter (pkripke_world F)
    (pkripke_point_generated_member F r)
    (fun x => excluded_middle_informative
      (pkripke_point_generated_member F r x)) xs.

Arguments pkripke_point_generated_cover F r xs : clear implicits.

Theorem pkripke_point_generated_finite :
  forall F r, pkripke_frame_finite F ->
    pkripke_frame_finite (pkripke_point_generated_frame F r).
Proof.
  intros F r [xs Hxs]. exists (pkripke_point_generated_cover F r xs).
  intros x. unfold pkripke_point_generated_cover.
  apply pkripke_sig_filter_complete. apply Hxs.
Qed.

Lemma pkripke_point_generated_antisymmetric :
  forall F r, pkripke_frame_antisymmetric F ->
    pkripke_frame_antisymmetric (pkripke_point_generated_frame F r).
Proof.
  intros F r Hanti [x hx] [y hy] Hxy Hyx; simpl in *.
  assert (x = y) as -> by (eapply Hanti; eauto).
  apply pkripke_point_generated_sig_eq.
Qed.

Lemma pkripke_point_generated_irreflexive :
  forall F r, pkripke_frame_irreflexive F ->
    pkripke_frame_irreflexive (pkripke_point_generated_frame F r).
Proof. intros F r Hirr [x hx]; apply Hirr. Qed.

Definition pkripke_point_generated_p_morphism
    (F : pkripke_frame) (r : pkripke_world F) :
    pkripke_frame_p_morphism (pkripke_point_generated_frame F r) F.
Proof.
  refine {| pkripke_pmap := fun x :
      pkripke_world (pkripke_point_generated_frame F r) => proj1_sig x |}.
  - intros [x hx] [y hy] Hxy; exact Hxy.
  - intros [x [-> | Hrx]] y Hxy.
    + exists (exist _ y (or_intror Hxy)); auto.
    + assert (Hry : pkripke_access F r y) by
        (eapply pkripke_access_trans; eauto).
      exists (exist _ y (or_intror Hry)); auto.
Defined.

Arguments pkripke_point_generated_p_morphism F r : clear implicits.

Definition pkripke_point_generated_valuation {Atom : Type}
    (M : pkripke_model Atom)
    (r : pkripke_world (pkripke_model_frame M)) :
    pkripke_valuation Atom
      (pkripke_point_generated_frame (pkripke_model_frame M) r).
Proof.
  refine {| pkripke_atom_value := fun a
      (x : pkripke_world
        (pkripke_point_generated_frame (pkripke_model_frame M) r)) =>
              pkripke_atom_value (pkripke_model_valuation M) a
                (proj1_sig x) |}.
  intros a [x hx] [y hy] Rxy Ha; simpl in *.
  eapply pkripke_atom_persistent; eauto.
Defined.

Definition pkripke_point_generated_model {Atom : Type}
    (M : pkripke_model Atom)
    (r : pkripke_world (pkripke_model_frame M)) : pkripke_model Atom :=
  {| pkripke_model_frame :=
       pkripke_point_generated_frame (pkripke_model_frame M) r;
     pkripke_model_valuation :=
       @pkripke_point_generated_valuation Atom M r |}.

Arguments pkripke_point_generated_model {Atom} M r.

Definition pkripke_point_generated_model_p_morphism {Atom : Type}
    (M : pkripke_model Atom)
    (r : pkripke_world (pkripke_model_frame M)) :
    pkripke_model_p_morphism (pkripke_point_generated_model M r) M.
Proof.
  apply pkripke_model_p_morphism_of_atomic with
    (f := pkripke_point_generated_p_morphism
      (pkripke_model_frame M) r).
  intros a [x hx]; reflexivity.
Defined.

Arguments pkripke_point_generated_model_p_morphism {Atom} M r.

Definition pkripke_point_generated_bisimulation {Atom : Type}
    (M : pkripke_model Atom)
    (r : pkripke_world (pkripke_model_frame M)) :
    pkripke_bisimulation (pkripke_point_generated_model M r) M :=
  pkripke_model_p_morphism_bisimulation
    (pkripke_point_generated_model_p_morphism M r).

Theorem pkripke_point_generated_equivalent_at_root :
  forall (Atom : Type) (M : pkripke_model Atom)
         (r : pkripke_world (pkripke_model_frame M)),
    @pkripke_equivalent Atom (pkripke_point_generated_model M r)
      (pkripke_point_generated_root (pkripke_model_frame M) r) M r.
Proof.
  intros Atom M r.
  apply pkripke_model_p_morphism_equivalence with
    (f := pkripke_point_generated_model_p_morphism M r).
Qed.
