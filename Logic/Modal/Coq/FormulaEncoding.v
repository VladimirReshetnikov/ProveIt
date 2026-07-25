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

Fixpoint nnformula_code (p : nnformula nat) : nat :=
  match p with
  | NAtom a => Cantor.to_nat (0, a)
  | NNegAtom a => Cantor.to_nat (1, a)
  | NBottom => Cantor.to_nat (2, 0)
  | NTop => Cantor.to_nat (3, 0)
  | NOr q r =>
      Cantor.to_nat (4, Cantor.to_nat (nnformula_code q, nnformula_code r))
  | NAnd q r =>
      Cantor.to_nat (5, Cantor.to_nat (nnformula_code q, nnformula_code r))
  | NBox q => Cantor.to_nat (6, nnformula_code q)
  | NDia q => Cantor.to_nat (7, nnformula_code q)
  end.

Fixpoint nnformula_decode (fuel code : nat) : nnformula nat :=
  match fuel with
  | 0 => NBottom
  | S fuel' =>
      let tag := fst (Cantor.of_nat code) in
      let payload := snd (Cantor.of_nat code) in
      match tag with
      | 0 => NAtom payload
      | 1 => NNegAtom payload
      | 2 => NBottom
      | 3 => NTop
      | 4 =>
          NOr
            (nnformula_decode fuel' (fst (Cantor.of_nat payload)))
            (nnformula_decode fuel' (snd (Cantor.of_nat payload)))
      | 5 =>
          NAnd
            (nnformula_decode fuel' (fst (Cantor.of_nat payload)))
            (nnformula_decode fuel' (snd (Cantor.of_nat payload)))
      | 6 => NBox (nnformula_decode fuel' payload)
      | 7 => NDia (nnformula_decode fuel' payload)
      | _ => NBottom
      end
  end.

Theorem nnformula_decode_code :
  forall (p : nnformula nat) fuel,
    nnformula_code p < fuel ->
    nnformula_decode fuel (nnformula_code p) = p.
Proof.
  induction p as
    [a | a | | | p IHp q IHq | p IHp q IHq | p IHp | p IHp];
    intros fuel Hfuel; destruct fuel as [|fuel'];
    try (cbn [nnformula_code] in Hfuel; lia).
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_code] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 4
        (Cantor.to_nat (nnformula_code p, nnformula_code q))) as Houter.
    pose proof
      (Cantor.to_nat_non_decreasing (nnformula_code p) (nnformula_code q))
      as Hinner.
    rewrite (IHp fuel' ltac:(lia)), (IHq fuel' ltac:(lia)).
    reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_code] in Hfuel.
    pose proof
      (Cantor.to_nat_non_decreasing 5
        (Cantor.to_nat (nnformula_code p, nnformula_code q))) as Houter.
    pose proof
      (Cantor.to_nat_non_decreasing (nnformula_code p) (nnformula_code q))
      as Hinner.
    rewrite (IHp fuel' ltac:(lia)), (IHq fuel' ltac:(lia)).
    reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_code] in Hfuel.
    pose proof (Cantor.to_nat_non_decreasing 6 (nnformula_code p))
      as Houter.
    rewrite (IHp fuel' ltac:(lia)). reflexivity.
  - cbn [nnformula_decode nnformula_code].
    rewrite !Cantor.cancel_of_to. cbn [fst snd].
    cbn [nnformula_code] in Hfuel.
    pose proof (Cantor.to_nat_non_decreasing 7 (nnformula_code p))
      as Houter.
    rewrite (IHp fuel' ltac:(lia)). reflexivity.
Qed.

Definition nnformula_enum (n : nat) : nnformula nat :=
  nnformula_decode (S n) n.

Theorem nnformula_enum_surjective :
  forall p : nnformula nat, exists n, nnformula_enum n = p.
Proof.
  intro p. exists (nnformula_code p).
  unfold nnformula_enum. apply nnformula_decode_code. lia.
Qed.
