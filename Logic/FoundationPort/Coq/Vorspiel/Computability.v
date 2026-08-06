(** Executable partial computations and semidecidable predicates.

    The source phrases these results through Mathlib's coding-dependent
    [Partrec] hierarchy.  A step-indexed evaluator is the corresponding
    native Coq interface: it exposes the algorithm, while soundness and
    completeness identify its graph with a proof-relevant partial value.
    Existential projection is generalized from primitive encodings to any
    witness type equipped with a surjective decoder. *)

From Stdlib Require Import Arith.Cantor Bool.Bool.
From Foundation.Vorspiel Require Import Part.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Enumerable witness types *)

Record enumerable_decoder (A : Type) : Type := {
  enumerable_decode : nat -> option A;
  enumerable_decode_surjective : forall a,
    exists code, enumerable_decode code = Some a
}.

Arguments enumerable_decode {A} _ _.

Definition nat_enumerable_decoder : enumerable_decoder nat :=
  {| enumerable_decode := fun n => Some n;
     enumerable_decode_surjective := fun n => ex_intro _ n eq_refl |}.

(** * Partial computations *)

Definition partial_computable {A B} (f : A -> partial_value B) : Prop :=
  exists run : A -> nat -> option B,
    (forall a fuel b, run a fuel = Some b -> partial_member (f a) b) /\
    (forall a b, partial_member (f a) b ->
      exists fuel, run a fuel = Some b).

Definition partial_projection {A B C}
    (f : A -> B -> partial_value C)
    (unif : forall a b1 b2 c1 c2,
      partial_member (f a b1) c1 ->
      partial_member (f a b2) c2 -> c1 = c2)
    (a : A) : partial_value C.
Proof.
  refine {| partial_member := fun c =>
    exists b, partial_member (f a b) c |}.
  intros c1 c2 [b1 H1] [b2 H2]. exact (unif a b1 b2 c1 c2 H1 H2).
Defined.

Lemma partial_projection_member_iff : forall A B C
    (f : A -> B -> partial_value C) unif a c,
  partial_member (@partial_projection A B C f unif a) c <->
  exists b, partial_member (f a b) c.
Proof. reflexivity. Qed.

Theorem partial_computable_projection : forall A B C
    (E : enumerable_decoder B) (f : A -> B -> partial_value C)
    (unif : forall a b1 b2 c1 c2,
      partial_member (f a b1) c1 ->
      partial_member (f a b2) c2 -> c1 = c2),
  partial_computable (fun ab : A * B => f (fst ab) (snd ab)) ->
  partial_computable (@partial_projection A B C f unif).
Proof.
  intros A B C E f unif [run [Hsound Hcomplete]].
  exists (fun a code =>
    let '(witness_code, fuel) := Cantor.of_nat code in
    match enumerable_decode E witness_code with
    | Some b => run (a, b) fuel
    | None => None
    end).
  split.
  - intros a code c Hrun.
    destruct (Cantor.of_nat code) as [witness_code fuel] eqn:Hcode.
    destruct (enumerable_decode E witness_code) as [b|] eqn:Hdecode;
      [|discriminate].
    exists b. exact (Hsound (a, b) fuel c Hrun).
  - intros a c [b Hb].
    destruct (enumerable_decode_surjective E b) as [witness_code Hdecode].
    destruct (Hcomplete (a, b) c Hb) as [fuel Hrun].
    exists (Cantor.to_nat (witness_code, fuel)).
    rewrite Cantor.cancel_of_to. simpl. now rewrite Hdecode.
Qed.

(** * Semidecidable predicates *)

Definition semidecidable {A} (p : A -> Prop) : Prop :=
  exists recognize : A -> nat -> bool,
    forall a, p a <-> exists fuel, recognize a fuel = true.

Lemma semidecidable_true : forall A,
  @semidecidable A (fun _ => True).
Proof.
  intro A. exists (fun _ _ => true). intro a. split.
  - intro. now exists 0.
  - intro. exact I.
Qed.

Lemma semidecidable_false : forall A,
  @semidecidable A (fun _ => False).
Proof.
  intro A. exists (fun _ _ => false). intro a. split.
  - contradiction.
  - intros [fuel H]. discriminate.
Qed.

Lemma semidecidable_const : forall A (p : Prop),
  {p} + {~ p} -> @semidecidable A (fun _ => p).
Proof.
  intros A p [Hp|Hp].
  - exists (fun _ _ => true). intro a. split; intro.
    + now exists 0.
    + exact Hp.
  - exists (fun _ _ => false). intro a. split.
    + contradiction.
    + intros [fuel H]. discriminate.
Qed.

Theorem semidecidable_iff_partial_computable_unit : forall A (p : A -> Prop),
  semidecidable p <->
  exists f : A -> partial_value unit,
    partial_computable f /\
    forall a, p a <-> partial_dom (f a).
Proof.
  intros A p. split.
  - intros [recognize Hrecognize].
    exists (fun a =>
      {| partial_member := fun _ => p a;
         partial_member_unique := fun x y _ _ =>
           match x, y with tt, tt => eq_refl end |}).
    split.
    + exists (fun a fuel =>
        if recognize a fuel then Some tt else None).
      split.
      * intros a fuel u Hrun. destruct u.
        destruct (recognize a fuel) eqn:Hfuel; [|discriminate].
        apply (proj2 (Hrecognize a)). now exists fuel.
      * intros a u Hu. destruct u.
        destruct (proj1 (Hrecognize a) Hu) as [fuel Hfuel].
        exists fuel. now rewrite Hfuel.
    + intro a. split.
      * intro Hp. now exists tt.
      * intros [u Hu]. exact Hu.
  - intros [f [[run [Hsound Hcomplete]] Hdom]].
    exists (fun a fuel =>
      match run a fuel with
      | Some _ => true
      | None => false
      end).
    intro a. split.
    + intro Hp.
      destruct (Hdom a) as [Hto _].
      destruct (Hto Hp) as [u Hu].
      destruct (Hcomplete a u Hu) as [fuel Hfuel].
      exists fuel. now rewrite Hfuel.
    + intros [fuel Hfuel].
      destruct (run a fuel) as [u|] eqn:Hrun; [|discriminate].
      apply (proj2 (Hdom a)). exists u. exact (Hsound a fuel u Hrun).
Qed.

Lemma semidecidable_and : forall A (p q : A -> Prop),
  semidecidable p -> semidecidable q ->
  semidecidable (fun a => p a /\ q a).
Proof.
  intros A p q [rp Hp] [rq Hq].
  exists (fun a code =>
    let '(pfuel, qfuel) := Cantor.of_nat code in
    andb (rp a pfuel) (rq a qfuel)).
  intro a. split.
  - intros [Hpa Hqa].
    destruct (proj1 (Hp a) Hpa) as [pfuel Hpfuel].
    destruct (proj1 (Hq a) Hqa) as [qfuel Hqfuel].
    exists (Cantor.to_nat (pfuel, qfuel)).
    rewrite Cantor.cancel_of_to. simpl. now rewrite Hpfuel, Hqfuel.
  - intros [code Hcode].
    destruct (Cantor.of_nat code) as [pfuel qfuel] eqn:Hfuel.
    apply Bool.andb_true_iff in Hcode. destruct Hcode as [Hp' Hq'].
    split.
    + apply (proj2 (Hp a)). now exists pfuel.
    + apply (proj2 (Hq a)). now exists qfuel.
Qed.

Lemma semidecidable_or : forall A (p q : A -> Prop),
  semidecidable p -> semidecidable q ->
  semidecidable (fun a => p a \/ q a).
Proof.
  intros A p q [rp Hp] [rq Hq].
  exists (fun a code =>
    let '(pfuel, qfuel) := Cantor.of_nat code in
    orb (rp a pfuel) (rq a qfuel)).
  intro a. split.
  - intros [Hpa|Hqa].
    + destruct (proj1 (Hp a) Hpa) as [pfuel Hpfuel].
      exists (Cantor.to_nat (pfuel, 0)).
      rewrite Cantor.cancel_of_to. simpl. now rewrite Hpfuel.
    + destruct (proj1 (Hq a) Hqa) as [qfuel Hqfuel].
      exists (Cantor.to_nat (0, qfuel)).
      rewrite Cantor.cancel_of_to. simpl. now rewrite Hqfuel, Bool.orb_true_r.
  - intros [code Hcode].
    destruct (Cantor.of_nat code) as [pfuel qfuel] eqn:Hfuel.
    apply Bool.orb_true_iff in Hcode. destruct Hcode as [Hp'|Hq'].
    + left. apply (proj2 (Hp a)). now exists pfuel.
    + right. apply (proj2 (Hq a)). now exists qfuel.
Qed.

Theorem semidecidable_projection : forall A B
    (E : enumerable_decoder B) (p : A * B -> Prop),
  semidecidable p ->
  semidecidable (fun a => exists b, p (a, b)).
Proof.
  intros A B E p [recognize Hrecognize].
  exists (fun a code =>
    let '(witness_code, fuel) := Cantor.of_nat code in
    match enumerable_decode E witness_code with
    | Some b => recognize (a, b) fuel
    | None => false
    end).
  intro a. split.
  - intros [b Hab].
    destruct (enumerable_decode_surjective E b) as [witness_code Hdecode].
    destruct (proj1 (Hrecognize (a, b)) Hab) as [fuel Hfuel].
    exists (Cantor.to_nat (witness_code, fuel)).
    rewrite Cantor.cancel_of_to. simpl. now rewrite Hdecode.
  - intros [code Hcode].
    destruct (Cantor.of_nat code) as [witness_code fuel] eqn:Hfuel.
    destruct (enumerable_decode E witness_code) as [b|] eqn:Hdecode;
      [|discriminate].
    exists b. apply (proj2 (Hrecognize (a, b))). now exists fuel.
Qed.

Lemma semidecidable_comp : forall A B (f : A -> B) (p : B -> Prop),
  semidecidable p -> semidecidable (fun a => p (f a)).
Proof.
  intros A B f p [recognize Hrecognize].
  exists (fun a fuel => recognize (f a) fuel).
  intro a. apply Hrecognize.
Qed.

(** * Decidable predicates *)

Definition decidable_predicate {A} (p : A -> Prop) : Type :=
  forall a, {p a} + {~ p a}.

Lemma decidable_predicate_semidecidable : forall A (p : A -> Prop),
  decidable_predicate p -> semidecidable p.
Proof.
  intros A p decide.
  exists (fun a _ => if decide a then true else false).
  intro a. destruct (decide a) as [Hp|Hp]; simpl.
  - split; intro; [now exists 0 | exact Hp].
  - split; [contradiction | intros [fuel H]; discriminate].
Qed.

Lemma decidable_predicate_const : forall A (p : Prop),
  {p} + {~ p} -> @decidable_predicate A (fun _ => p).
Proof. intros A p Hp a. exact Hp. Qed.

Lemma decidable_predicate_and : forall A (p q : A -> Prop),
  decidable_predicate p -> decidable_predicate q ->
  decidable_predicate (fun a => p a /\ q a).
Proof.
  intros A p q Hp Hq a. destruct (Hp a), (Hq a); firstorder.
Qed.

Lemma decidable_predicate_or : forall A (p q : A -> Prop),
  decidable_predicate p -> decidable_predicate q ->
  decidable_predicate (fun a => p a \/ q a).
Proof.
  intros A p q Hp Hq a. destruct (Hp a), (Hq a); firstorder.
Qed.
