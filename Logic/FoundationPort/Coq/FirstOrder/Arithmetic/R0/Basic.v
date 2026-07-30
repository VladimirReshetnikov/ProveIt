(**
  Semantic core of Cobham's arithmetic theory R0.

  The source presents four first-order axiom schemes and then repeatedly uses
  only their consequences in a model.  Packaging those consequences directly
  keeps downstream reductions independent of a particular proof calculus while
  retaining the exact numeral arithmetic and finite-interval content.
*)

From Stdlib Require Import Arith.PeanoNat Lia Vectors.Fin.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record r0_laws {M : Type} (O : oring_carrier M) : Prop := {
  r0_numeral_add : forall n m,
    oring_add O (oring_numeral O n) (oring_numeral O m) =
    oring_numeral O (n + m);
  r0_numeral_mul : forall n m,
    oring_mul O (oring_numeral O n) (oring_numeral O m) =
    oring_numeral O (n * m);
  r0_numeral_ne : forall n m,
    n <> m -> oring_numeral O n <> oring_numeral O m;
  r0_lt_numeral : forall n x,
    oring_lt O x (oring_numeral O n) <->
    exists i, i < n /\ x = oring_numeral O i
}.

Lemma r0_numeral_eq_iff : forall M (O : oring_carrier M),
  r0_laws O -> forall n m,
  oring_numeral O n = oring_numeral O m <-> n = m.
Proof.
  intros M O H n m. split.
  - intro Heq. destruct (Nat.eq_dec n m); [assumption|].
    exfalso. exact (@r0_numeral_ne M O H n m n0 Heq).
  - now intros ->.
Qed.

Lemma r0_numeral_lt_iff : forall M (O : oring_carrier M),
  r0_laws O -> forall n m,
  oring_lt O (oring_numeral O n) (oring_numeral O m) <-> n < m.
Proof.
  intros M O H n m. split.
  - intro Hlt.
    destruct (proj1 (@r0_lt_numeral M O H m (oring_numeral O n)) Hlt)
      as [i [Him Hni]].
    apply (proj1 (r0_numeral_eq_iff H n i)) in Hni.
    now subst i.
  - intro Hnm. apply (proj2 (@r0_lt_numeral M O H m
      (oring_numeral O n))).
    exists n. now split.
Qed.

Lemma r0_lt_numeral_fin_iff : forall M (O : oring_carrier M),
  r0_laws O -> forall n x,
  oring_lt O x (oring_numeral O n) <->
  exists i : Fin.t n,
    x = oring_numeral O (proj1_sig (Fin.to_nat i)).
Proof.
  intros M O H n x. rewrite (@r0_lt_numeral M O H n x).
  split.
  - intros [i [Hin Hx]]. exists (Fin.of_nat_lt Hin).
    rewrite Fin.to_nat_of_nat. exact Hx.
  - intros [i Hx]. exists (proj1_sig (Fin.to_nat i)). split.
    + exact (proj2_sig (Fin.to_nat i)).
    + exact Hx.
Qed.

Definition nat_r0_laws : r0_laws nat_oring_carrier.
Proof.
  constructor.
  - intros n m. rewrite !nat_oring_numeral. reflexivity.
  - intros n m. rewrite !nat_oring_numeral. reflexivity.
  - intros n m Hne. rewrite !nat_oring_numeral. exact Hne.
  - intros n x. rewrite !nat_oring_numeral.
    cbn [nat_oring_carrier]. split.
    + intro Hx. exists x. split.
      * exact Hx.
      * symmetry. apply nat_oring_numeral.
    + intros [i [Hin ->]]. rewrite nat_oring_numeral.
      change (i < n). exact Hin.
Defined.
