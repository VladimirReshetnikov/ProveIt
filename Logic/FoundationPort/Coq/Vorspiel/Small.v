(** Explicit small-universe encodings and injective preimages. *)

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Section ExplicitSmallness.

Universe small_universe large_universe.
Constraint small_universe < large_universe.

Record predicate_small {A : Type@{large_universe}} (s : A -> Prop) := {
  small_code : Type@{small_universe};
  small_encode : forall x, s x -> small_code;
  small_encode_injective : forall x y (Hx : s x) (Hy : s y),
    @small_encode x Hx = @small_encode y Hy -> x = y
}.

Arguments small_code {A s} _.
Arguments small_encode {A s} _ _ _.

Definition predicate_preimage {A B} (f : A -> B) (s : B -> Prop) :
    A -> Prop :=
  fun x => s (f x).

Theorem small_preimage_of_injective :
  forall (A : Type@{large_universe}) (B : Type@{large_universe})
    (f : A -> B),
  (forall x y, f x = f y -> x = y) ->
  forall (s : B -> Prop),
  predicate_small s -> predicate_small (predicate_preimage f s).
Proof.
  intros A B f Hf s S.
  refine {|
    small_code := small_code S;
    small_encode := fun x Hx => small_encode S (f x) Hx
  |}.
  intros x y Hx Hy Heq. apply Hf.
  exact (@small_encode_injective B s S (f x) (f y) Hx Hy Heq).
Defined.

End ExplicitSmallness.
