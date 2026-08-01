From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import SexticSparsePolynomials
  SexticSparseResolvents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Transparent enumeration of elementary-symmetric certificates.  MathComp's
    [countType] encoding of integer sparse polynomials is used only as a
    surjective enumeration; candidate verification is the extensional Boolean
    checker from [SexticSparsePolynomials]. *)
Module PolynomialFormulasSexticSparseSymmetricSearch.

Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticSparseResolvents.

Definition sparse_candidate (n : nat) : sparse_polynomial :=
  odflt sparse_zero (unpickle n).

Definition elementary_certificateb (p : sparse_polynomial) (n : nat) : bool :=
  sparse_equivalentb (substitute_esymm (sparse_candidate n)) p.

Definition has_elementary_certificate_up_to
    (p : sparse_polynomial) (fuel : nat) : bool :=
  has (elementary_certificateb p) (iota 0 fuel).

Lemma sparse_candidate_pickle q : sparse_candidate (pickle q) = q.
Proof. by rewrite /sparse_candidate pickleK. Qed.

Lemma elementary_certificatebP p n :
  reflect
    (forall d,
      sparse_coefficient (substitute_esymm (sparse_candidate n)) d =
      sparse_coefficient p d)
    (elementary_certificateb p n).
Proof. exact: sparse_equivalentbP. Qed.

Lemma elementary_certificate_eval p n values :
  elementary_certificateb p n ->
  sparse_eval values p =
    sparse_eval
      [tuple sparse_eval values (esymm_sparse i) | i < 6]
      (sparse_candidate n).
Proof.
move=> hcert.
have heval := sparse_equivalentb_eval values hcert.
rewrite sparse_eval_substitute_esymm in heval.
exact: esym heval.
Qed.

Lemma elementary_certificate_exists_of_expression p q :
  sparse_equivalentb (substitute_esymm q) p ->
  exists n, elementary_certificateb p n.
Proof.
move=> hq; exists (pickle q).
by rewrite /elementary_certificateb sparse_candidate_pickle.
Qed.

Lemma has_elementary_certificate_up_toP p fuel :
  reflect
    (exists n, (n < fuel)%N /\ elementary_certificateb p n)
    (has_elementary_certificate_up_to p fuel).
Proof.
apply: (iffP hasP).
- move=> [n].
  rewrite mem_iota add0n => hn hcert.
  by exists n.
- move=> [n [hn hcert]].
  exists n => //.
  by rewrite mem_iota add0n.
Qed.

Lemma elementary_certificate_eventually p :
  (exists q, sparse_equivalentb (substitute_esymm q) p) ->
  exists fuel, has_elementary_certificate_up_to p fuel.
Proof.
move=> [q hq].
have [n hn] := elementary_certificate_exists_of_expression hq.
exists n.+1; apply/has_elementary_certificate_up_toP.
by exists n; rewrite ltnSn.
Qed.

End PolynomialFormulasSexticSparseSymmetricSearch.
