From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import AbelRuffini.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

(** A kernel-checked semantic bridge for the external decision argument in
    [../Decidability.md].  MathComp-Abel reflects solvability by radicals to
    solvability of the finite Galois group of a chosen splitting field.  The
    second reflection below composes that result with [solvable_formula], so
    its proposition says exactly that every algebraic-closure root has an
    [algterm rat] expression.

    This file deliberately does not identify the opaque [numfield]
    construction with a Turing program.  The recursive realization is supplied
    by the external coefficient argument in [Decidability.md], using Dummit's
    sextic resolvent (with Landau--Miller as a stronger alternative).  Thus the
    formal reflector establishes the semantic endpoint, while the accompanying
    mathematical proof separately establishes effectivity. *)

Module PolynomialFormulasQuinticRadicalDecidability.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Definition galois_solvableb (p : {poly rat}) : bool :=
  solvable 'Gal({: numfield p} / 1).

Lemma galois_solvableP (p : {poly rat}) :
  reflect (solvable_by_radical_poly p) (galois_solvableb p).
Proof. exact: AbelGaloisPolyRat. Qed.

Lemma every_root_has_radical_expressionP (p : {poly rat})
    (p_neq0 : p != 0) :
  reflect (radical_formula_solves p) (galois_solvableb p).
Proof.
apply: (equivP (galois_solvableP p)).
exact: radical_formula_solvesP p_neq0.
Qed.

(** A degree-five polynomial is nonzero, so the rootwise reflector applies
    without a separate nonzeroness input.  MathComp polynomial degree is
    represented by [size p - 1], hence quintics have size six. *)
Lemma quintic_every_root_has_radical_expressionP (p : {poly rat})
    (p_quintic : size p = 6%N) :
  reflect (radical_formula_solves p) (galois_solvableb p).
Proof.
apply: every_root_has_radical_expressionP.
apply/eqP=> p_eq0.
by move: p_quintic; rewrite p_eq0 size_poly0.
Qed.

Definition int_to_rat_poly (p : {poly int}) : {poly rat} :=
  map_poly (intr : int -> rat) p.

(** The exact integer-coefficient predicate from the decision problem. *)
Definition all_roots_radical_int (p : {poly int}) : Prop :=
  {in root (map_poly ratrC (int_to_rat_poly p)), forall x,
    exists f : algterm rat, algT_eval ratrC f = x}.

(** Boolean reflection through the finite Galois group of the rational image. *)
Definition integer_radical_decision (p : {poly int}) : bool :=
  galois_solvableb (int_to_rat_poly p).

Lemma integer_radical_decisionP (p : {poly int})
    (p_quintic : size p = 6%N) :
  reflect (all_roots_radical_int p) (integer_radical_decision p).
Proof.
have p_neq0 : p != 0 by rewrite -size_poly_eq0 p_quintic.
have q_neq0 : int_to_rat_poly p != 0.
  rewrite /int_to_rat_poly -(@map_poly0 int rat (intr : int -> rat)).
  rewrite (inj_eq (map_inj_poly (@intr_inj rat) (rmorph0 (intr : int -> rat)))).
  exact: p_neq0.
apply: (equivP (AbelGaloisPolyRat (int_to_rat_poly p))).
exact: solvable_formula q_neq0.
Qed.

(** A characteristic function on natural-number codes.  Malformed codes and
    polynomials whose degree is not five are rejected. *)
Definition quintic_radical_decision_code (n : nat) : bool :=
  if (unpickle n : option {poly int}) is Some p
  then (size p == 6%N) && integer_radical_decision p
  else false.

Lemma quintic_radical_decision_codeK (p : {poly int}) :
  quintic_radical_decision_code (pickle p) =
    (size p == 6%N) && integer_radical_decision p.
Proof. by rewrite /quintic_radical_decision_code pickleK. Qed.

Definition encoded_quintic_radical (n : nat) : Prop :=
  exists p : {poly int},
    unpickle n = Some p /\ size p = 6%N /\ all_roots_radical_int p.

Lemma quintic_radical_decision_codeP n :
  reflect (encoded_quintic_radical n) (quintic_radical_decision_code n).
Proof.
rewrite /quintic_radical_decision_code /encoded_quintic_radical.
case E: (unpickle n) => [p|].
- apply: (iffP andP).
  + move=> [/eqP hp hdec].
    exists p; split=> //; split=> //.
    exact: (elimT (@integer_radical_decisionP p hp) hdec).
  + move=> [q [Eq [hq hrad]]].
    case: Eq => ->.
    split; first exact/eqP.
    exact: (introT (@integer_radical_decisionP q hq) hrad).
- constructor=> [[q [Eq _]]].
  by discriminate Eq.
Qed.

End PolynomialFormulasQuinticRadicalDecidability.
