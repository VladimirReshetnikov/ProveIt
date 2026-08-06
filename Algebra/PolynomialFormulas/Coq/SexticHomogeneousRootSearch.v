From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  SexticRecursiveCore SexticRationalRootSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** An arithmetic-only version of the bounded rational-root test.

    The earlier search evaluates a rational number [u / v].  This equivalent
    Boolean clears the denominator and therefore uses only integer addition,
    multiplication, powers, equality, and bounded finite search.  That is the
    form consumed by the direct Mu-recursive certificate. *)
Module PolynomialFormulasSexticHomogeneousRootSearch.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticRationalRootSearch.

Definition bounded_homogeneous_rootb (cs : seq int) : bool :=
  if constant_coefficient cs == 0 then true else
  has (fun u => has (fun v => homogeneous_eval cs u v == 0)
    (denominator_candidates cs)) (numerator_candidates cs).

Lemma homogeneous_eval_ratE cs u v :
  v != 0 ->
  (homogeneous_eval cs u v)%:~R =
    coefficient_list_eval_rat cs (u%:~R / v%:~R) *
      (v%:~R : rat) ^+ (size cs).-1.
Proof.
move=> hv.
elim: cs=> [|a cs ih] /=.
- by rewrite mul0r.
case: cs ih=> [|b cs] ih /=.
- by rewrite expr0 !mulr1 !mulr0 !addr0.
- rewrite !rmorphD !rmorphM !rmorphXn /= ih //.
  have hvQ : (v%:~R : rat) != 0 by rewrite intr_eq0.
  rewrite exprS /= [RHS]mulrDl.
  congr (_ + _).
  rewrite [RHS]mulrACA divfK //.
Qed.

Lemma positive_interval_nonzero R v :
  v \in positive_interval R -> v != 0.
Proof.
rewrite /positive_interval.
move/mapP=> [n].
rewrite mem_iota=> /andP [hn _] ->.
case: n hn=> [|n] hn; last by [].
by move: hn; rewrite ltnn.
Qed.

Lemma homogeneous_eval_zero_iff cs u v :
  v != 0 ->
  (homogeneous_eval cs u v == 0) =
    (coefficient_list_eval_rat cs (u%:~R / v%:~R) == 0).
Proof.
move=> hv.
apply/eqP/eqP.
- move=> hhom.
  have hcast : ((homogeneous_eval cs u v)%:~R : rat) = 0 by rewrite hhom.
  rewrite homogeneous_eval_ratE // in hcast.
  have hvQ : (v%:~R : rat) != 0 by rewrite intr_eq0.
  have hvpow : (v%:~R : rat) ^+ (size cs).-1 != 0 by rewrite expf_neq0.
  apply/eqP.
  move/eqP: hcast.
  by rewrite mulf_eq0 (negPf hvpow) orbF.
- move=> heval.
  apply: (@intr_inj rat).
  rewrite homogeneous_eval_ratE // heval mul0r.
all: done.
Qed.

Theorem bounded_homogeneous_rootbE cs :
  bounded_homogeneous_rootb cs = bounded_rational_rootb cs.
Proof.
rewrite /bounded_homogeneous_rootb /bounded_rational_rootb.
case: (constant_coefficient cs == 0)=> //.
apply/idP/idP.
- move/hasP=> [u hu /hasP [v hv hroot]].
  apply/hasP; exists u=> //; apply/hasP; exists v=> //.
  move: hroot.
  by rewrite homogeneous_eval_zero_iff //; exact: positive_interval_nonzero hv.
- move/hasP=> [u hu /hasP [v hv hroot]].
  apply/hasP; exists u=> //; apply/hasP; exists v=> //.
  move: hroot.
  by rewrite -homogeneous_eval_zero_iff //; exact: positive_interval_nonzero hv.
Qed.

Theorem homogeneous_rational_rootP cs :
  reflect (has_rational_root cs) (bounded_homogeneous_rootb cs).
Proof. by rewrite bounded_homogeneous_rootbE; exact: rational_rootP. Qed.

End PolynomialFormulasSexticHomogeneousRootSearch.
