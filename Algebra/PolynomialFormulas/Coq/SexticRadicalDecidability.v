From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

(** Semantic endpoint for the sextic recursive decision.

    The executable coefficient algorithm is developed separately: for an
    irreducible sextic it tests the two block-system resolvents of degrees ten
    and fifteen, and for a reducible sextic it invokes the already verified
    lower-degree decisions.  This file establishes the exact MathComp-Abel
    proposition that that algorithm must reflect. *)
Module PolynomialFormulasSexticRadicalDecidability.

Import LeanProofs.PolynomialFormulasAbelRuffini.
Import PolynomialFormulasQuinticRadicalDecidability.

(** A size-seven rational polynomial is nonzero, so the general
    MathComp-Abel rootwise reflector applies. *)
Lemma sextic_every_root_has_radical_expressionP (p : {poly rat})
    (p_sextic : size p = 7%N) :
  reflect (radical_formula_solves p) (galois_solvableb p).
Proof.
apply: every_root_has_radical_expressionP.
apply/eqP=> p_eq0.
by move: p_sextic; rewrite p_eq0 size_poly0.
Qed.

(** The exact integer-coefficient predicate, reused from the degree-five
    semantic bridge, does not itself depend on the degree. *)
Definition all_roots_radical_sextic_int := all_roots_radical_int.

Definition sextic_integer_radical_semantic_decision (p : {poly int}) : bool :=
  integer_radical_decision p.

Lemma sextic_integer_radical_semantic_decisionP (p : {poly int})
    (p_sextic : size p = 7%N) :
  reflect (all_roots_radical_sextic_int p)
    (sextic_integer_radical_semantic_decision p).
Proof.
have p_neq0 : p != 0 by rewrite -size_poly_eq0 p_sextic.
have q_neq0 : int_to_rat_poly p != 0.
  rewrite /int_to_rat_poly -(@map_poly0 int rat (intr : int -> rat)).
  rewrite (inj_eq (map_inj_poly (@intr_inj rat) (rmorph0 (intr : int -> rat)))).
  exact: p_neq0.
apply: (equivP (AbelGaloisPolyRat (int_to_rat_poly p))).
exact: solvable_formula q_neq0.
Qed.

(** Constructive decidability in Coq's standard [sumbool] sense.  This
    theorem is deliberately named [semantic]: its Boolean is the reflected
    MathComp-Abel Galois-group test above, not the transparent bounded
    coefficient search from [SexticRecursiveCore]. *)
Definition all_roots_radical_sextic_int_semantic_decidable
    (p : {poly int}) (p_sextic : size p = 7%N) :
    {all_roots_radical_sextic_int p} +
    {~ all_roots_radical_sextic_int p}.
Proof.
case E: (sextic_integer_radical_semantic_decision p).
- left.
  exact: (elimT (@sextic_integer_radical_semantic_decisionP p p_sextic) E).
- right=> hrad.
  have := introT (@sextic_integer_radical_semantic_decisionP p p_sextic) hrad.
  by rewrite E.
Defined.

(** Natural-number coding of the semantic reflector.  This is the endpoint to
    which the later structurally recursive resolvent Boolean is related; no
    extraction claim about MathComp-Abel's classical [numfield] is made here. *)
Definition sextic_radical_semantic_code (n : nat) : bool :=
  if (unpickle n : option {poly int}) is Some p
  then (size p == 7%N) && sextic_integer_radical_semantic_decision p
  else false.

Definition encoded_sextic_radical (n : nat) : Prop :=
  exists p : {poly int},
    unpickle n = Some p /\ size p = 7%N /\
      all_roots_radical_sextic_int p.

Lemma sextic_radical_semantic_codeK (p : {poly int}) :
  sextic_radical_semantic_code (pickle p) =
    (size p == 7%N) && sextic_integer_radical_semantic_decision p.
Proof. by rewrite /sextic_radical_semantic_code pickleK. Qed.

Lemma sextic_radical_semantic_codeP n :
  reflect (encoded_sextic_radical n) (sextic_radical_semantic_code n).
Proof.
rewrite /sextic_radical_semantic_code /encoded_sextic_radical.
case E: (unpickle n) => [p|].
- apply: (iffP andP).
  + move=> [/eqP hp hdec].
    exists p; split=> //; split=> //.
    exact: (elimT (@sextic_integer_radical_semantic_decisionP p hp) hdec).
  + move=> [q [Eq [hq hrad]]].
    case: Eq => ->.
    split; first exact/eqP.
    exact: (introT (@sextic_integer_radical_semantic_decisionP q hq) hrad).
- constructor=> [[q [Eq _]]].
  by discriminate Eq.
Qed.

End PolynomialFormulasSexticRadicalDecidability.
