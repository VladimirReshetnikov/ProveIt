(**
  Executable enumerations of modal and negation-normal formulas over [nat].

  Foundation obtains these enumerations through Lean's [Encodable]
  instances.  The Coq presentation exposes the Cantor codes and fuelled
  decoders directly, which makes the surjectivity theorem available to the
  Lindenbaum construction without typeclass machinery or choice.
*)

From Stdlib Require Import Arith.PeanoNat Cantor Lia.
From FoundationModal Require Import Syntax NNFormula.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Encoding over an arbitrary explicit atom codec

    Lean packages the corresponding data in an [Encodable] instance.  Keeping
    the atom encoder, decoder, and round-trip law explicit makes the actual
    dependency visible and lets callers use any injective natural coding. *)

Fixpoint nnformula_encode_with {AtomType}
    (encode_atom : AtomType -> nat) (p : nnformula AtomType) : nat :=
  match p with
  | NAtom a => Cantor.to_nat (0, encode_atom a)
  | NNegAtom a => Cantor.to_nat (1, encode_atom a)
  | NBottom => Cantor.to_nat (2, 0)
  | NTop => Cantor.to_nat (3, 0)
  | NOr q r => Cantor.to_nat
      (4, Cantor.to_nat
        (nnformula_encode_with encode_atom q,
         nnformula_encode_with encode_atom r))
  | NAnd q r => Cantor.to_nat
      (5, Cantor.to_nat
        (nnformula_encode_with encode_atom q,
         nnformula_encode_with encode_atom r))
  | NBox q => Cantor.to_nat (6, nnformula_encode_with encode_atom q)
  | NDia q => Cantor.to_nat (7, nnformula_encode_with encode_atom q)
  end.

Fixpoint nnformula_decode_with {AtomType}
    (decode_atom : nat -> option AtomType) (fuel code : nat)
    : option (nnformula AtomType) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      let tag := fst (Cantor.of_nat code) in
      let payload := snd (Cantor.of_nat code) in
      match tag with
      | 0 =>
          match decode_atom payload with
          | Some a => Some (NAtom a)
          | None => None
          end
      | 1 =>
          match decode_atom payload with
          | Some a => Some (NNegAtom a)
          | None => None
          end
      | 2 => Some NBottom
      | 3 => Some NTop
      | 4 =>
          match
            nnformula_decode_with decode_atom fuel'
              (fst (Cantor.of_nat payload)),
            nnformula_decode_with decode_atom fuel'
              (snd (Cantor.of_nat payload))
          with
          | Some q, Some r => Some (NOr q r)
          | _, _ => None
          end
      | 5 =>
          match
            nnformula_decode_with decode_atom fuel'
              (fst (Cantor.of_nat payload)),
            nnformula_decode_with decode_atom fuel'
              (snd (Cantor.of_nat payload))
          with
          | Some q, Some r => Some (NAnd q r)
          | _, _ => None
          end
      | 6 =>
          match nnformula_decode_with decode_atom fuel' payload with
          | Some q => Some (NBox q)
          | None => None
          end
      | 7 =>
          match nnformula_decode_with decode_atom fuel' payload with
          | Some q => Some (NDia q)
          | None => None
          end
      | _ => None
      end
  end.

Theorem nnformula_decode_encode_with :
  forall (AtomType : Type) (encode_atom : AtomType -> nat)
    (decode_atom : nat -> option AtomType),
    (forall a, decode_atom (encode_atom a) = Some a) ->
    forall (p : nnformula AtomType) fuel,
      nnformula_encode_with encode_atom p < fuel ->
      nnformula_decode_with decode_atom fuel
        (nnformula_encode_with encode_atom p) = Some p.
Proof.
  intros AtomType encode_atom decode_atom Hatom p.
  induction p as
    [a | a | | | p IHp q IHq | p IHp q IHq | p IHp | p IHp];
    intros fuel Hfuel; destruct fuel as [|fuel'];
    try (cbn [nnformula_encode_with] in Hfuel; lia).
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite Hatom. reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite Hatom. reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd]. reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd]. reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_encode_with] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 4
        (Cantor.to_nat
          (nnformula_encode_with encode_atom p,
           nnformula_encode_with encode_atom q))) as Houter.
    pose proof
      (Cantor.to_nat_non_decreasing
        (nnformula_encode_with encode_atom p)
        (nnformula_encode_with encode_atom q)) as Hinner.
    rewrite (IHp fuel' ltac:(lia)), (IHq fuel' ltac:(lia)). reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_encode_with] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 5
        (Cantor.to_nat
          (nnformula_encode_with encode_atom p,
           nnformula_encode_with encode_atom q))) as Houter.
    pose proof
      (Cantor.to_nat_non_decreasing
        (nnformula_encode_with encode_atom p)
        (nnformula_encode_with encode_atom q)) as Hinner.
    rewrite (IHp fuel' ltac:(lia)), (IHq fuel' ltac:(lia)). reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_encode_with] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 6
        (nnformula_encode_with encode_atom p)) as Houter.
    rewrite (IHp fuel' ltac:(lia)). reflexivity.
  - cbn [nnformula_decode_with nnformula_encode_with].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_encode_with] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 7
        (nnformula_encode_with encode_atom p)) as Houter.
    rewrite (IHp fuel' ltac:(lia)). reflexivity.
Qed.

Definition nnformula_enum_with {AtomType}
    (decode_atom : nat -> option AtomType) (n : nat)
    : option (nnformula AtomType) :=
  nnformula_decode_with decode_atom (S n) n.

Corollary nnformula_enum_with_surjective :
  forall (AtomType : Type) (encode_atom : AtomType -> nat)
    (decode_atom : nat -> option AtomType),
    (forall a, decode_atom (encode_atom a) = Some a) ->
    forall p : nnformula AtomType,
      exists n, nnformula_enum_with decode_atom n = Some p.
Proof.
  intros AtomType encode_atom decode_atom Hatom p.
  exists (nnformula_encode_with encode_atom p).
  unfold nnformula_enum_with. eapply nnformula_decode_encode_with.
  - exact Hatom.
  - lia.
Qed.

(** * Primitive modal formulas *)

Fixpoint modal_formula_code (p : formula nat) : nat :=
  match p with
  | Atom a => Cantor.to_nat (0, a)
  | Bottom => Cantor.to_nat (1, 0)
  | Imp q r =>
      Cantor.to_nat
        (2, Cantor.to_nat (modal_formula_code q, modal_formula_code r))
  | Box q => Cantor.to_nat (3, modal_formula_code q)
  end.

Fixpoint modal_formula_decode (fuel code : nat) : formula nat :=
  match fuel with
  | 0 => Bottom
  | S fuel' =>
      let tag := fst (Cantor.of_nat code) in
      let payload := snd (Cantor.of_nat code) in
      match tag with
      | 0 => Atom payload
      | 1 => Bottom
      | 2 =>
          Imp
            (modal_formula_decode fuel' (fst (Cantor.of_nat payload)))
            (modal_formula_decode fuel' (snd (Cantor.of_nat payload)))
      | 3 => Box (modal_formula_decode fuel' payload)
      | _ => Bottom
      end
  end.

Theorem modal_formula_decode_code :
  forall (p : formula nat) fuel,
    modal_formula_code p < fuel ->
    modal_formula_decode fuel (modal_formula_code p) = p.
Proof.
  induction p as [a | | p IHp q IHq | p IHp];
    intros fuel Hfuel; destruct fuel as [|fuel'];
    try (cbn [modal_formula_code] in Hfuel; lia).
  - cbn [modal_formula_decode modal_formula_code].
    rewrite !Cantor.cancel_of_to. reflexivity.
  - cbn [modal_formula_decode modal_formula_code].
    rewrite !Cantor.cancel_of_to. reflexivity.
  - cbn [modal_formula_decode modal_formula_code].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [modal_formula_code] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 2
        (Cantor.to_nat (modal_formula_code p, modal_formula_code q)))
      as Houter.
    pose proof
      (Cantor.to_nat_non_decreasing
        (modal_formula_code p) (modal_formula_code q)) as Hinner.
    rewrite (IHp fuel' ltac:(lia)), (IHq fuel' ltac:(lia)).
    reflexivity.
  - cbn [modal_formula_decode modal_formula_code].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [modal_formula_code] in Hfuel.
    pose proof (Cantor.to_nat_non_decreasing 3 (modal_formula_code p))
      as Houter.
    rewrite (IHp fuel' ltac:(lia)). reflexivity.
Qed.

Definition modal_formula_enum (n : nat) : formula nat :=
  modal_formula_decode (S n) n.

Theorem modal_formula_enum_surjective :
  forall p : formula nat, exists n, modal_formula_enum n = p.
Proof.
  intro p. exists (modal_formula_code p).
  unfold modal_formula_enum. apply modal_formula_decode_code. lia.
Qed.

(** * Negation-normal formulas *)

Definition nnformula_code (p : nnformula nat) : nat :=
  nnformula_encode_with (fun a => a) p.

Definition nnformula_decode (fuel code : nat) : nnformula nat :=
  match nnformula_decode_with (fun a => Some a) fuel code with
  | Some p => p
  | None => NBottom
  end.

Theorem nnformula_decode_code :
  forall (p : nnformula nat) fuel,
    nnformula_code p < fuel ->
    nnformula_decode fuel (nnformula_code p) = p.
Proof.
  intros p fuel Hfuel. unfold nnformula_code, nnformula_decode.
  pose proof
    (@nnformula_decode_encode_with nat
      (fun a => a) (fun a => Some a) (fun a => eq_refl)
      p fuel Hfuel) as Hdecode.
  now rewrite Hdecode.
Qed.

Definition nnformula_enum (n : nat) : nnformula nat :=
  nnformula_decode (S n) n.

Theorem nnformula_enum_surjective :
  forall p : nnformula nat, exists n, nnformula_enum n = p.
Proof.
  intro p. exists (nnformula_code p).
  unfold nnformula_enum. apply nnformula_decode_code. lia.
Qed.
