From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticRootProjectionI LazardQuinticQuadratic
  LazardQuinticFourierNumerators
  LazardQuinticRootFourierNumeratorCommon
  LazardQuinticRootFourierNumeratorP2Common
  SexticSparsePolynomials SexticNewtonPowerSums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A memory-bounded sparse certificate language for the root-specialized
    P2 numerator.  It deliberately reuses the six-coordinate sparse
    polynomial semantics used by the sextic development.  Coordinates
    0--3 are the independent depressed roots; coordinates 4 and 5 are
    unused.  The fifth root is represented by [-x0-x1-x2-x3]. *)
Module PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticFourierNumerators.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module C := PolynomialFormulasLazardQuinticRootFourierNumeratorCommon.
Module P2C := PolynomialFormulasLazardQuinticRootFourierNumeratorP2Common.
Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SN := PolynomialFormulasSexticNewtonPowerSums.
Local Open Scope ring_scope.

(** The checker never asks Rocq's reflective [ring] tactic to normalize the
    30,282-term source identity.  Instead it maintains a sorted sparse list.
    [sparse_insert] combines one coefficient at a time, and the generated
    certificates expose five independent, bounded [vm_compute] leaves. *)

Definition exponent_lex_lt
    (a b : SP.sparse_exponent) : bool :=
  let a0 := tnth a ord0 in let b0 := tnth b ord0 in
  let a1 := tnth a (inord 1) in let b1 := tnth b (inord 1) in
  let a2 := tnth a (inord 2) in let b2 := tnth b (inord 2) in
  let a3 := tnth a (inord 3) in let b3 := tnth b (inord 3) in
  let a4 := tnth a (inord 4) in let b4 := tnth b (inord 4) in
  let a5 := tnth a (inord 5) in let b5 := tnth b (inord 5) in
  (a0 < b0)%N || ((a0 == b0) &&
  ((a1 < b1)%N || ((a1 == b1) &&
  ((a2 < b2)%N || ((a2 == b2) &&
  ((a3 < b3)%N || ((a3 == b3) &&
  ((a4 < b4)%N || ((a4 == b4) && (a5 < b5)%N))))))))).

Fixpoint sparse_insert (t : SP.sparse_term)
    (p : SP.sparse_polynomial) : SP.sparse_polynomial :=
  if p is u :: p' then
    if t.2 == u.2 then
      let coefficient := t.1 + u.1 in
      if coefficient == 0 then p'
      else (coefficient, t.2) :: p'
    else if exponent_lex_lt t.2 u.2 then t :: p
    else u :: sparse_insert t p'
  else if t.1 == 0 then [::] else [:: t].

Fixpoint sparse_insert_all (source accumulator : SP.sparse_polynomial) :
    SP.sparse_polynomial :=
  if source is t :: source' then
    sparse_insert_all source' (sparse_insert t accumulator)
  else accumulator.

Definition sparse_canonical_zero : SP.sparse_polynomial := [::].

Definition sparse_canonical_const (z : int) : SP.sparse_polynomial :=
  if z == 0 then [::] else [:: (z, SP.exponent_zero)].

Definition sparse_canonical_add
    (p q : SP.sparse_polynomial) : SP.sparse_polynomial :=
  sparse_insert_all q p.

Definition sparse_canonical_neg (p : SP.sparse_polynomial) :
    SP.sparse_polynomial := map SP.term_neg p.

Definition sparse_canonical_sub
    (p q : SP.sparse_polynomial) : SP.sparse_polynomial :=
  sparse_canonical_add p (sparse_canonical_neg q).

Definition sparse_term_scale (z : int) (t : SP.sparse_term) :
    SP.sparse_term := (z * t.1, t.2).

Definition sparse_canonical_scale (z : int) (p : SP.sparse_polynomial) :
    SP.sparse_polynomial :=
  if z == 0 then [::] else map (sparse_term_scale z) p.

Fixpoint sparse_canonical_mul_acc
    (p q accumulator : SP.sparse_polynomial) : SP.sparse_polynomial :=
  if p is t :: p' then
    sparse_canonical_mul_acc p' q
      (sparse_insert_all (map (SP.term_mul t) q) accumulator)
  else accumulator.

Definition sparse_canonical_mul
    (p q : SP.sparse_polynomial) : SP.sparse_polynomial :=
  sparse_canonical_mul_acc p q [::].

Fixpoint sparse_canonical_pow
    (p : SP.sparse_polynomial) (n : nat) : SP.sparse_polynomial :=
  if n is n'.+1 then
    sparse_canonical_mul p (sparse_canonical_pow p n')
  else sparse_canonical_const 1.

Section CanonicalEvaluation.
Variable R : comPzRingType.

Definition sparse_term_eval_ring (values : 6.-tuple R)
    (t : SP.sparse_term) : R :=
  (t.1)%:~R * SN.exponent_value_ring values t.2.

Lemma sparse_eval_ring_cons values t p :
  SN.sparse_eval_ring values (t :: p) =
    sparse_term_eval_ring values t + SN.sparse_eval_ring values p.
Proof. by rewrite /SN.sparse_eval_ring big_cons. Qed.

Lemma sparse_term_eval_ring_add_coefficient values a b exponent :
  sparse_term_eval_ring values (a + b, exponent) =
    sparse_term_eval_ring values (a, exponent) +
      sparse_term_eval_ring values (b, exponent).
Proof. by rewrite /sparse_term_eval_ring /= intrD mulrDl. Qed.

Lemma sparse_term_eval_ring_zero_coefficient values exponent :
  sparse_term_eval_ring values (0, exponent) = 0.
Proof. by rewrite /sparse_term_eval_ring rmorph0 mul0r. Qed.

Lemma sparse_insert_eval values t p :
  SN.sparse_eval_ring values (sparse_insert t p) =
    sparse_term_eval_ring values t + SN.sparse_eval_ring values p.
Proof.
elim: p => [|[b exponent] p ih] /=.
- case ht: (t.1 == 0).
  + move/eqP: ht=> ht.
    case: t ht=> coefficient exponent /= ->.
    rewrite sparse_term_eval_ring_zero_coefficient.
    by rewrite SN.sparse_eval_ring_zero addr0.
  + by rewrite sparse_eval_ring_cons SN.sparse_eval_ring_zero addr0.
- case heq: (t.2 == exponent).
  + move/eqP: heq=> heq; subst exponent.
    case hcoefficient: (t.1 + b == 0).
    * move/eqP: hcoefficient=> hcoefficient.
      rewrite sparse_eval_ring_cons.
      have hsum : sparse_term_eval_ring values t +
          sparse_term_eval_ring values (b, t.2) = 0.
        rewrite -sparse_term_eval_ring_add_coefficient hcoefficient.
        exact: sparse_term_eval_ring_zero_coefficient.
      by rewrite addrA hsum add0r.
    * rewrite !sparse_eval_ring_cons.
      by rewrite sparse_term_eval_ring_add_coefficient addrA.
  + case hlt: (exponent_lex_lt t.2 exponent).
    * by rewrite !sparse_eval_ring_cons.
    * rewrite !sparse_eval_ring_cons ih.
      by rewrite addrCA.
Qed.

Lemma sparse_insert_all_eval (values : 6.-tuple R)
    (source accumulator : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_insert_all source accumulator) =
    SN.sparse_eval_ring values source +
      SN.sparse_eval_ring values accumulator.
Proof.
elim: source accumulator => [|t source ih] accumulator /=.
- by rewrite !SN.sparse_eval_ring_zero add0r.
- rewrite ih sparse_insert_eval !sparse_eval_ring_cons.
  by rewrite addrCA addrA.
Qed.

Lemma sparse_canonical_const_eval (values : 6.-tuple R) (z : int) :
  SN.sparse_eval_ring values (sparse_canonical_const z) = z%:~R.
Proof.
rewrite /sparse_canonical_const.
case hz: (z == 0).
- move/eqP: hz=> ->; by rewrite SN.sparse_eval_ring_zero rmorph0.
- exact: SN.sparse_eval_ring_const.
Qed.

Lemma sparse_canonical_add_eval (values : 6.-tuple R)
    (p q : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_canonical_add p q) =
    SN.sparse_eval_ring values p + SN.sparse_eval_ring values q.
Proof.
rewrite /sparse_canonical_add sparse_insert_all_eval.
exact: addrC.
Qed.

Lemma sparse_canonical_neg_eval (values : 6.-tuple R)
    (p : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_canonical_neg p) =
    - SN.sparse_eval_ring values p.
Proof. exact: SN.sparse_eval_ring_neg. Qed.

Lemma sparse_canonical_sub_eval (values : 6.-tuple R)
    (p q : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_canonical_sub p q) =
    SN.sparse_eval_ring values p - SN.sparse_eval_ring values q.
Proof.
by rewrite /sparse_canonical_sub sparse_canonical_add_eval
  sparse_canonical_neg_eval.
Qed.

Lemma sparse_canonical_scale_eval (values : 6.-tuple R) (z : int)
    (p : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_canonical_scale z p) =
    z%:~R * SN.sparse_eval_ring values p.
Proof.
rewrite /sparse_canonical_scale.
case hz: (z == 0).
- move/eqP: hz=> ->.
  by rewrite SN.sparse_eval_ring_zero rmorph0 mul0r.
- rewrite /SN.sparse_eval_ring big_map /= big_distrr.
  apply: eq_bigr=> t ht.
  by rewrite /sparse_term_scale /= rmorphM mulrA.
Qed.

Lemma sparse_eval_ring_map_term_mul (values : 6.-tuple R)
    (t : SP.sparse_term) (q : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (map (SP.term_mul t) q) =
    sparse_term_eval_ring values t * SN.sparse_eval_ring values q.
Proof.
rewrite /SN.sparse_eval_ring big_map /= big_distrr.
apply: eq_bigr=> u hu.
rewrite /SP.term_mul /sparse_term_eval_ring /=
  rmorphM SN.exponent_value_ring_add.
by rewrite mulrACA.
Qed.

Lemma sparse_canonical_mul_acc_eval (values : 6.-tuple R)
    (p q accumulator : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_canonical_mul_acc p q accumulator) =
    SN.sparse_eval_ring values p * SN.sparse_eval_ring values q +
      SN.sparse_eval_ring values accumulator.
Proof.
elim: p accumulator => [|t p ih] accumulator /=.
- by rewrite SN.sparse_eval_ring_zero mul0r add0r.
- rewrite ih sparse_insert_all_eval sparse_eval_ring_map_term_mul
    !sparse_eval_ring_cons.
  by rewrite mulrDl addrCA addrA.
Qed.

Lemma sparse_canonical_mul_eval (values : 6.-tuple R)
    (p q : SP.sparse_polynomial) :
  SN.sparse_eval_ring values (sparse_canonical_mul p q) =
    SN.sparse_eval_ring values p * SN.sparse_eval_ring values q.
Proof.
by rewrite /sparse_canonical_mul sparse_canonical_mul_acc_eval
  SN.sparse_eval_ring_zero addr0.
Qed.

Lemma sparse_canonical_pow_eval (values : 6.-tuple R)
    (p : SP.sparse_polynomial) (n : nat) :
  SN.sparse_eval_ring values (sparse_canonical_pow p n) =
    SN.sparse_eval_ring values p ^+ n.
Proof.
elim: n => [|n ih] /=.
- by rewrite sparse_canonical_const_eval.
- by rewrite sparse_canonical_mul_eval ih exprS.
Qed.

End CanonicalEvaluation.

(** Four independent root coordinates and the depressed fifth root. *)
Definition sx0 : SP.sparse_polynomial := SP.sparse_var ord0.
Definition sx1 : SP.sparse_polynomial := SP.sparse_var (inord 1).
Definition sx2 : SP.sparse_polynomial := SP.sparse_var (inord 2).
Definition sx3 : SP.sparse_polynomial := SP.sparse_var (inord 3).
Definition sx4 : SP.sparse_polynomial :=
  sparse_canonical_neg
    (sparse_canonical_add
      (sparse_canonical_add (sparse_canonical_add sx0 sx1) sx2) sx3).

Definition sparse_root_values {F : fieldType}
    (roots : 5.-tuple F) : 6.-tuple F :=
  [tuple tnth roots o0; tnth roots o1; tnth roots o2;
    tnth roots o3; 0; 0].

Section RootEvaluation.
Variable F : fieldType.
Variable roots : 5.-tuple F.
Let values := sparse_root_values roots.

Lemma sx0_eval : SN.sparse_eval_ring values sx0 = tnth roots o0.
Proof. by rewrite /sx0 SN.sparse_eval_ring_var /values /sparse_root_values. Qed.
Lemma sx1_eval : SN.sparse_eval_ring values sx1 = tnth roots o1.
Proof. by rewrite /sx1 SN.sparse_eval_ring_var /values /sparse_root_values
  (tnth_nth 0) inordK. Qed.
Lemma sx2_eval : SN.sparse_eval_ring values sx2 = tnth roots o2.
Proof. by rewrite /sx2 SN.sparse_eval_ring_var /values /sparse_root_values
  (tnth_nth 0) inordK. Qed.
Lemma sx3_eval : SN.sparse_eval_ring values sx3 = tnth roots o3.
Proof. by rewrite /sx3 SN.sparse_eval_ring_var /values /sparse_root_values
  (tnth_nth 0) inordK. Qed.

Lemma sx4_eval (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sx4 = tnth roots o4.
Proof.
have hx4 := lazard_root_sum_zero_last hsum.
rewrite /sx4 sparse_canonical_neg_eval !sparse_canonical_add_eval
  sx0_eval sx1_eval sx2_eval sx3_eval.
exact: esym hx4.
Qed.

End RootEvaluation.

(** Root-level sparse expressions.  They intentionally mirror the public
    root definitions rather than importing a computer-algebra result as an
    axiom. *)

Definition ssum (ps : seq SP.sparse_polynomial) : SP.sparse_polynomial :=
  foldr sparse_canonical_add sparse_canonical_zero ps.

Definition sproduct (ps : seq SP.sparse_polynomial) : SP.sparse_polynomial :=
  foldr sparse_canonical_mul (sparse_canonical_const 1) ps.

Definition sroot_esymm2 : SP.sparse_polynomial := ssum [::
  sparse_canonical_mul sx0 sx1; sparse_canonical_mul sx0 sx2;
  sparse_canonical_mul sx0 sx3; sparse_canonical_mul sx0 sx4;
  sparse_canonical_mul sx1 sx2; sparse_canonical_mul sx1 sx3;
  sparse_canonical_mul sx1 sx4; sparse_canonical_mul sx2 sx3;
  sparse_canonical_mul sx2 sx4; sparse_canonical_mul sx3 sx4].

Definition sroot_esymm3 : SP.sparse_polynomial := ssum [::
  sproduct [:: sx0; sx1; sx2]; sproduct [:: sx0; sx1; sx3];
  sproduct [:: sx0; sx1; sx4]; sproduct [:: sx0; sx2; sx3];
  sproduct [:: sx0; sx2; sx4]; sproduct [:: sx0; sx3; sx4];
  sproduct [:: sx1; sx2; sx3]; sproduct [:: sx1; sx2; sx4];
  sproduct [:: sx1; sx3; sx4]; sproduct [:: sx2; sx3; sx4]].

Definition sroot_esymm4 : SP.sparse_polynomial := ssum [::
  sproduct [:: sx0; sx1; sx2; sx3];
  sproduct [:: sx0; sx1; sx2; sx4];
  sproduct [:: sx0; sx1; sx3; sx4];
  sproduct [:: sx0; sx2; sx3; sx4];
  sproduct [:: sx1; sx2; sx3; sx4]].

Definition sroot_esymm5 : SP.sparse_polynomial :=
  sproduct [:: sx0; sx1; sx2; sx3; sx4].

Definition sp : SP.sparse_polynomial := sroot_esymm2.
Definition sq : SP.sparse_polynomial := sparse_canonical_neg sroot_esymm3.
Definition sr : SP.sparse_polynomial := sroot_esymm4.
Definition ss : SP.sparse_polynomial := sparse_canonical_neg sroot_esymm5.

Definition sroot_orbit_formula (a b : nat) : SP.sparse_polynomial :=
  ssum [::
    sproduct [:: sparse_canonical_pow sx0 a; sparse_canonical_pow sx1 b;
      sparse_canonical_pow sx4 b];
    sproduct [:: sparse_canonical_pow sx0 a; sparse_canonical_pow sx2 b;
      sparse_canonical_pow sx3 b];
    sproduct [:: sparse_canonical_pow sx1 a; sparse_canonical_pow sx0 b;
      sparse_canonical_pow sx2 b];
    sproduct [:: sparse_canonical_pow sx1 a; sparse_canonical_pow sx3 b;
      sparse_canonical_pow sx4 b];
    sproduct [:: sparse_canonical_pow sx2 a; sparse_canonical_pow sx0 b;
      sparse_canonical_pow sx4 b];
    sproduct [:: sparse_canonical_pow sx2 a; sparse_canonical_pow sx1 b;
      sparse_canonical_pow sx3 b];
    sproduct [:: sparse_canonical_pow sx3 a; sparse_canonical_pow sx0 b;
      sparse_canonical_pow sx1 b];
    sproduct [:: sparse_canonical_pow sx3 a; sparse_canonical_pow sx2 b;
      sparse_canonical_pow sx4 b];
    sproduct [:: sparse_canonical_pow sx4 a; sparse_canonical_pow sx0 b;
      sparse_canonical_pow sx3 b];
    sproduct [:: sparse_canonical_pow sx4 a; sparse_canonical_pow sx1 b;
      sparse_canonical_pow sx2 b]].

Definition si4 := sroot_orbit_formula 2 1.
Definition si5 := sroot_orbit_formula 3 1.
Definition si6 := sroot_orbit_formula 4 1.
Definition si7 := sroot_orbit_formula 3 2.
Definition si8 := sroot_orbit_formula 4 2.

Definition st_prime : SP.sparse_polynomial := sproduct [::
  sparse_canonical_sub sx0 sx1; sparse_canonical_sub sx1 sx2;
  sparse_canonical_sub sx2 sx3; sparse_canonical_sub sx3 sx4;
  sparse_canonical_sub sx4 sx0].

Definition su_prime : SP.sparse_polynomial := sproduct [::
  sparse_canonical_sub sx0 sx2; sparse_canonical_sub sx1 sx3;
  sparse_canonical_sub sx2 sx4; sparse_canonical_sub sx3 sx0;
  sparse_canonical_sub sx4 sx1].

Definition sepsilon_product : SP.sparse_polynomial := sproduct [::
  sparse_canonical_add
    (sparse_canonical_sub (sparse_canonical_sub sx1 sx2) sx3) sx4;
  sparse_canonical_add
    (sparse_canonical_sub (sparse_canonical_sub sx2 sx3) sx4) sx0;
  sparse_canonical_add
    (sparse_canonical_sub (sparse_canonical_sub sx3 sx4) sx0) sx1;
  sparse_canonical_add
    (sparse_canonical_sub (sparse_canonical_sub sx4 sx0) sx1) sx2;
  sparse_canonical_add
    (sparse_canonical_sub (sparse_canonical_sub sx0 sx1) sx2) sx3].

Definition sroot_E : SP.sparse_polynomial :=
  sparse_canonical_neg
    (sparse_canonical_add (sparse_canonical_pow st_prime 2)
      (sparse_canonical_pow su_prime 2)).

Definition sp21 : SP.sparse_polynomial :=
  sparse_canonical_scale 5%:Z (ssum [::
    sparse_canonical_scale 3%:Z si4;
    sparse_canonical_scale 2%:Z (sparse_canonical_pow sp 2);
    sparse_canonical_scale (- 16%:Z) sr]).

Definition sp22 : SP.sparse_polynomial :=
  sparse_canonical_scale 25%:Z (ssum [::
    sparse_canonical_scale (- 10%:Z) (sparse_canonical_mul sq si6);
    sparse_canonical_mul
      (sparse_canonical_sub
        (sparse_canonical_scale 8%:Z (sparse_canonical_pow sp 2))
        (sparse_canonical_scale 50%:Z sr)) si5;
    sparse_canonical_mul
      (sparse_canonical_sub
        (sparse_canonical_scale (- 2%:Z) (sparse_canonical_mul sp sq))
        (sparse_canonical_scale 25%:Z ss)) si4;
    sparse_canonical_scale 8%:Z
      (sproduct [:: sparse_canonical_pow sp 3; sq]);
    sparse_canonical_scale 70%:Z (sparse_canonical_pow sq 3);
    sparse_canonical_scale (- 20%:Z)
      (sproduct [:: sparse_canonical_pow sp 2; ss]);
    sparse_canonical_scale (- 26%:Z) (sproduct [:: sp; sq; sr]);
    sparse_canonical_scale 50%:Z (sparse_canonical_mul sr ss)]).

Definition sp23 : SP.sparse_polynomial :=
  sparse_canonical_scale 25%:Z (ssum [::
    sparse_canonical_scale (- 4%:Z) (sparse_canonical_mul sp si7);
    sparse_canonical_neg (sparse_canonical_mul sq si6);
    sparse_canonical_scale 4%:Z (sparse_canonical_mul sr si5);
    sparse_canonical_mul
      (sparse_canonical_add
        (sparse_canonical_scale (- 3%:Z) (sparse_canonical_mul sp sq))
        (sparse_canonical_scale 15%:Z ss)) si4;
    sparse_canonical_scale 26%:Z
      (sproduct [:: sparse_canonical_pow sp 2; ss]);
    sparse_canonical_scale (- 26%:Z) (sproduct [:: sp; sq; sr]);
    sparse_canonical_scale 7%:Z (sparse_canonical_pow sq 3);
    sparse_canonical_scale (- 40%:Z) (sparse_canonical_mul sr ss)]).

Definition sp24 : SP.sparse_polynomial :=
  sparse_canonical_scale 25%:Z (ssum [::
    sparse_canonical_scale 3%:Z (sparse_canonical_mul sp si7);
    sparse_canonical_scale (- 18%:Z) (sparse_canonical_mul sq si6);
    sparse_canonical_scale 22%:Z (sparse_canonical_mul sr si5);
    sparse_canonical_mul
      (sparse_canonical_add
        (sparse_canonical_scale (- 14%:Z) (sparse_canonical_mul sp sq))
        (sparse_canonical_scale 20%:Z ss)) si4;
    sparse_canonical_scale 18%:Z
      (sproduct [:: sparse_canonical_pow sp 2; ss]);
    sparse_canonical_scale (- 33%:Z) (sproduct [:: sp; sq; sr]);
    sparse_canonical_scale 21%:Z (sparse_canonical_pow sq 3);
    sparse_canonical_scale 30%:Z (sparse_canonical_mul sr ss)]).

(** Five-coordinate cyclic convolution over canonical sparse polynomials. *)
Record SparseCyclicFive := {
  sparse_cyclic0 : SP.sparse_polynomial;
  sparse_cyclic1 : SP.sparse_polynomial;
  sparse_cyclic2 : SP.sparse_polynomial;
  sparse_cyclic3 : SP.sparse_polynomial;
  sparse_cyclic4 : SP.sparse_polynomial
}.

Definition sparse_cyclic_add (a b : SparseCyclicFive) : SparseCyclicFive :=
  {| sparse_cyclic0 := sparse_canonical_add (sparse_cyclic0 a) (sparse_cyclic0 b);
     sparse_cyclic1 := sparse_canonical_add (sparse_cyclic1 a) (sparse_cyclic1 b);
     sparse_cyclic2 := sparse_canonical_add (sparse_cyclic2 a) (sparse_cyclic2 b);
     sparse_cyclic3 := sparse_canonical_add (sparse_cyclic3 a) (sparse_cyclic3 b);
     sparse_cyclic4 := sparse_canonical_add (sparse_cyclic4 a) (sparse_cyclic4 b) |}.

Definition sparse_cyclic_neg (a : SparseCyclicFive) : SparseCyclicFive :=
  {| sparse_cyclic0 := sparse_canonical_neg (sparse_cyclic0 a);
     sparse_cyclic1 := sparse_canonical_neg (sparse_cyclic1 a);
     sparse_cyclic2 := sparse_canonical_neg (sparse_cyclic2 a);
     sparse_cyclic3 := sparse_canonical_neg (sparse_cyclic3 a);
     sparse_cyclic4 := sparse_canonical_neg (sparse_cyclic4 a) |}.

Definition sparse_cyclic_sub (a b : SparseCyclicFive) : SparseCyclicFive :=
  sparse_cyclic_add a (sparse_cyclic_neg b).

Definition sparse_cyclic_scale
    (c : SP.sparse_polynomial) (a : SparseCyclicFive) : SparseCyclicFive :=
  {| sparse_cyclic0 := sparse_canonical_mul c (sparse_cyclic0 a);
     sparse_cyclic1 := sparse_canonical_mul c (sparse_cyclic1 a);
     sparse_cyclic2 := sparse_canonical_mul c (sparse_cyclic2 a);
     sparse_cyclic3 := sparse_canonical_mul c (sparse_cyclic3 a);
     sparse_cyclic4 := sparse_canonical_mul c (sparse_cyclic4 a) |}.

Definition sparse_cyclic_mul (a b : SparseCyclicFive) : SparseCyclicFive :=
  {| sparse_cyclic0 := ssum [::
       sparse_canonical_mul (sparse_cyclic0 a) (sparse_cyclic0 b);
       sparse_canonical_mul (sparse_cyclic1 a) (sparse_cyclic4 b);
       sparse_canonical_mul (sparse_cyclic2 a) (sparse_cyclic3 b);
       sparse_canonical_mul (sparse_cyclic3 a) (sparse_cyclic2 b);
       sparse_canonical_mul (sparse_cyclic4 a) (sparse_cyclic1 b)];
     sparse_cyclic1 := ssum [::
       sparse_canonical_mul (sparse_cyclic0 a) (sparse_cyclic1 b);
       sparse_canonical_mul (sparse_cyclic1 a) (sparse_cyclic0 b);
       sparse_canonical_mul (sparse_cyclic2 a) (sparse_cyclic4 b);
       sparse_canonical_mul (sparse_cyclic3 a) (sparse_cyclic3 b);
       sparse_canonical_mul (sparse_cyclic4 a) (sparse_cyclic2 b)];
     sparse_cyclic2 := ssum [::
       sparse_canonical_mul (sparse_cyclic0 a) (sparse_cyclic2 b);
       sparse_canonical_mul (sparse_cyclic1 a) (sparse_cyclic1 b);
       sparse_canonical_mul (sparse_cyclic2 a) (sparse_cyclic0 b);
       sparse_canonical_mul (sparse_cyclic3 a) (sparse_cyclic4 b);
       sparse_canonical_mul (sparse_cyclic4 a) (sparse_cyclic3 b)];
     sparse_cyclic3 := ssum [::
       sparse_canonical_mul (sparse_cyclic0 a) (sparse_cyclic3 b);
       sparse_canonical_mul (sparse_cyclic1 a) (sparse_cyclic2 b);
       sparse_canonical_mul (sparse_cyclic2 a) (sparse_cyclic1 b);
       sparse_canonical_mul (sparse_cyclic3 a) (sparse_cyclic0 b);
       sparse_canonical_mul (sparse_cyclic4 a) (sparse_cyclic4 b)];
     sparse_cyclic4 := ssum [::
       sparse_canonical_mul (sparse_cyclic0 a) (sparse_cyclic4 b);
       sparse_canonical_mul (sparse_cyclic1 a) (sparse_cyclic3 b);
       sparse_canonical_mul (sparse_cyclic2 a) (sparse_cyclic2 b);
       sparse_canonical_mul (sparse_cyclic3 a) (sparse_cyclic1 b);
       sparse_canonical_mul (sparse_cyclic4 a) (sparse_cyclic0 b)] |}.

Definition sparse_cyclic_constant (p : SP.sparse_polynomial) :
    SparseCyclicFive :=
  {| sparse_cyclic0 := p;
     sparse_cyclic1 := sparse_canonical_zero;
     sparse_cyclic2 := sparse_canonical_zero;
     sparse_cyclic3 := sparse_canonical_zero;
     sparse_cyclic4 := sparse_canonical_zero |}.

Definition sparse_cyclic_discriminant : SparseCyclicFive :=
  {| sparse_cyclic0 := sparse_canonical_zero;
     sparse_cyclic1 := sparse_canonical_const 1;
     sparse_cyclic2 := sparse_canonical_const (-1);
     sparse_cyclic3 := sparse_canonical_const (-1);
     sparse_cyclic4 := sparse_canonical_const 1 |}.

Definition sparse_cyclic_A : SparseCyclicFive :=
  {| sparse_cyclic0 := sparse_canonical_zero;
     sparse_cyclic1 := sparse_canonical_const 1;
     sparse_cyclic2 := sparse_canonical_zero;
     sparse_cyclic3 := sparse_canonical_zero;
     sparse_cyclic4 := sparse_canonical_const (-1) |}.

Definition sparse_cyclic_B : SparseCyclicFive :=
  {| sparse_cyclic0 := sparse_canonical_zero;
     sparse_cyclic1 := sparse_canonical_zero;
     sparse_cyclic2 := sparse_canonical_const 1;
     sparse_cyclic3 := sparse_canonical_const (-1);
     sparse_cyclic4 := sparse_canonical_zero |}.

Definition sparse_cyclic_epsilon : SparseCyclicFive :=
  sparse_cyclic_scale sepsilon_product sparse_cyclic_discriminant.

Definition sparse_cyclic_T : SparseCyclicFive :=
  sparse_cyclic_add
    (sparse_cyclic_scale st_prime sparse_cyclic_A)
    (sparse_cyclic_scale su_prime sparse_cyclic_B).

Definition sparse_cyclic_formula_U : SparseCyclicFive :=
  sparse_cyclic_sub
    (sparse_cyclic_scale su_prime sparse_cyclic_A)
    (sparse_cyclic_scale st_prime sparse_cyclic_B).

Definition sparse_cyclic_fourier_P1 : SparseCyclicFive :=
  {| sparse_cyclic0 := sx0; sparse_cyclic1 := sx1;
     sparse_cyclic2 := sx2; sparse_cyclic3 := sx3;
     sparse_cyclic4 := sx4 |}.

Definition sparse_cyclic_fourier_P2 : SparseCyclicFive :=
  {| sparse_cyclic0 := sx0; sparse_cyclic1 := sx3;
     sparse_cyclic2 := sx1; sparse_cyclic3 := sx4;
     sparse_cyclic4 := sx2 |}.

Definition sparse_p2_numerator_left : SparseCyclicFive :=
  sparse_cyclic_add
    (sparse_cyclic_scale
      (sparse_canonical_mul
        (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp21)
      sparse_cyclic_epsilon)
    (sparse_cyclic_add
      (sparse_cyclic_constant
        (sparse_canonical_mul
          (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp22))
      (sparse_cyclic_scale (sparse_canonical_const 2)
        (sparse_cyclic_mul sparse_cyclic_epsilon
          (sparse_cyclic_add
            (sparse_cyclic_scale sp23 sparse_cyclic_T)
            (sparse_cyclic_scale sp24 sparse_cyclic_formula_U))))).

Definition sparse_p2_numerator_right : SparseCyclicFive :=
  sparse_cyclic_scale
    (sparse_canonical_scale 20%:Z sroot_E)
    (sparse_cyclic_mul sparse_cyclic_epsilon
      (sparse_cyclic_mul
        (sparse_cyclic_mul
          (sparse_cyclic_mul sparse_cyclic_fourier_P1
            sparse_cyclic_fourier_P1)
          sparse_cyclic_fourier_P1)
        sparse_cyclic_fourier_P2)).

Definition sparse_p2_numerator_difference : SparseCyclicFive :=
  sparse_cyclic_sub sparse_p2_numerator_left sparse_p2_numerator_right.

(** Semantic bridge to the public field-valued definitions. *)
Section SemanticBridge.
Variable F : fieldType.
Variable roots : 5.-tuple F.
Let values := sparse_root_values roots.

Definition eval_sparse_cyclic (a : SparseCyclicFive) : LazardCyclicFive F :=
  {| lazard_cyclic0 := SN.sparse_eval_ring values (sparse_cyclic0 a);
     lazard_cyclic1 := SN.sparse_eval_ring values (sparse_cyclic1 a);
     lazard_cyclic2 := SN.sparse_eval_ring values (sparse_cyclic2 a);
     lazard_cyclic3 := SN.sparse_eval_ring values (sparse_cyclic3 a);
     lazard_cyclic4 := SN.sparse_eval_ring values (sparse_cyclic4 a) |}.

Lemma eval_ssum ps :
  SN.sparse_eval_ring values (ssum ps) =
    \sum_(p <- ps) SN.sparse_eval_ring values p.
Proof.
elim: ps => [|p ps ih] /=.
- by rewrite SN.sparse_eval_ring_zero big_nil.
- by rewrite sparse_canonical_add_eval ih big_cons.
Qed.

Lemma eval_sproduct ps :
  SN.sparse_eval_ring values (sproduct ps) =
    \prod_(p <- ps) SN.sparse_eval_ring values p.
Proof.
elim: ps => [|p ps ih] /=.
- by rewrite sparse_canonical_const_eval big_nil.
- by rewrite sparse_canonical_mul_eval ih big_cons.
Qed.

Lemma eval_slinear4 a b c d :
  SN.sparse_eval_ring values
      (sparse_canonical_add
        (sparse_canonical_sub (sparse_canonical_sub a b) c) d) =
    (SN.sparse_eval_ring values a - SN.sparse_eval_ring values b -
      SN.sparse_eval_ring values c) + SN.sparse_eval_ring values d.
Proof.
rewrite sparse_canonical_add_eval.
rewrite sparse_canonical_sub_eval.
by rewrite sparse_canonical_sub_eval.
Qed.

(** Keep the signed integer casts and the two association shapes used by
    the P2 atoms out of their individual semantic proofs. *)
Lemma sparse_canonical_scale_nat_eval n p :
  SN.sparse_eval_ring values (sparse_canonical_scale n%:Z p) =
    n%:R * SN.sparse_eval_ring values p.
Proof. exact: sparse_canonical_scale_eval. Qed.

Lemma sparse_canonical_scale_neg_nat_eval n p :
  SN.sparse_eval_ring values (sparse_canonical_scale (- n%:Z) p) =
    - (n%:R * SN.sparse_eval_ring values p).
Proof.
by rewrite sparse_canonical_scale_eval intrN mulNr.
Qed.

Lemma add3_right_assoc (a b c : F) :
  (a + b) + c = a + (b + c).
Proof. by rewrite addrA. Qed.

Lemma add8_right_assoc (a b c d e f g h : F) :
  (((((((a + b) + c) + d) + e) + f) + g) + h) =
    a + (b + (c + (d + (e + (f + (g + h)))))).
Proof. by rewrite !addrA. Qed.

Ltac normalize_sparse_semantics :=
  repeat first
    [ rewrite eval_ssum
    | rewrite eval_sproduct
    | rewrite big_cons
    | rewrite big_nil
    | rewrite sparse_canonical_scale_neg_nat_eval
    | rewrite sparse_canonical_scale_nat_eval
    | rewrite sparse_canonical_add_eval
    | rewrite sparse_canonical_sub_eval
    | rewrite sparse_canonical_neg_eval
    | rewrite sparse_canonical_mul_eval
    | rewrite sparse_canonical_pow_eval
    | rewrite addr0
    | rewrite mulr1 ].

Lemma eval_sparse_cyclic_add a b :
  eval_sparse_cyclic (sparse_cyclic_add a b) =
    lazard_cyclic_add (eval_sparse_cyclic a) (eval_sparse_cyclic b).
Proof.
by case: a=> a0 a1 a2 a3 a4; case: b=> b0 b1 b2 b3 b4;
  rewrite /eval_sparse_cyclic /sparse_cyclic_add /lazard_cyclic_add /=
    !sparse_canonical_add_eval.
Qed.

Lemma eval_sparse_cyclic_neg a :
  eval_sparse_cyclic (sparse_cyclic_neg a) =
    lazard_cyclic_neg (eval_sparse_cyclic a).
Proof.
by case: a=> a0 a1 a2 a3 a4;
  rewrite /eval_sparse_cyclic /sparse_cyclic_neg /lazard_cyclic_neg /=
    !sparse_canonical_neg_eval.
Qed.

Lemma eval_sparse_cyclic_sub a b :
  eval_sparse_cyclic (sparse_cyclic_sub a b) =
    lazard_cyclic_sub (eval_sparse_cyclic a) (eval_sparse_cyclic b).
Proof.
by rewrite /sparse_cyclic_sub /lazard_cyclic_sub
  eval_sparse_cyclic_add eval_sparse_cyclic_neg.
Qed.

Lemma eval_sparse_cyclic_scale c a :
  eval_sparse_cyclic (sparse_cyclic_scale c a) =
    lazard_cyclic_scale (SN.sparse_eval_ring values c)
      (eval_sparse_cyclic a).
Proof.
by case: a=> a0 a1 a2 a3 a4;
  rewrite /eval_sparse_cyclic /sparse_cyclic_scale /lazard_cyclic_scale /=
    !sparse_canonical_mul_eval.
Qed.

Lemma eval_sparse_cyclic_mul a b :
  eval_sparse_cyclic (sparse_cyclic_mul a b) =
    lazard_cyclic_mul (eval_sparse_cyclic a) (eval_sparse_cyclic b).
Proof.
case: a=> a0 a1 a2 a3 a4; case: b=> b0 b1 b2 b3 b4.
rewrite /eval_sparse_cyclic /sparse_cyclic_mul /lazard_cyclic_mul /=.
by rewrite !sparse_canonical_add_eval !sparse_canonical_mul_eval !addrA.
Qed.

Lemma eval_sparse_cyclic_constant p :
  eval_sparse_cyclic (sparse_cyclic_constant p) =
    C.lazard_cyclic_constant (SN.sparse_eval_ring values p).
Proof.
by rewrite /eval_sparse_cyclic /sparse_cyclic_constant
  /C.lazard_cyclic_constant /= !SN.sparse_eval_ring_zero.
Qed.

Lemma eval_sroot_esymm2 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sroot_esymm2 = lazard_root_esymm2 roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /sroot_esymm2 /lazard_root_esymm2.
rewrite eval_ssum /= !big_cons !big_nil !sparse_canonical_mul_eval.
rewrite hx0 hx1 hx2 hx3 hx4 !addr0.
by rewrite !addrA.
Qed.

Lemma eval_sroot_esymm3 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sroot_esymm3 = lazard_root_esymm3 roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /sroot_esymm3 /lazard_root_esymm3.
rewrite eval_ssum /= !big_cons !big_nil !sparse_canonical_mul_eval.
rewrite hx0 hx1 hx2 hx3 hx4 !sparse_canonical_const_eval !mulr1 !addr0.
by rewrite !mulrA !addrA.
Qed.

Lemma eval_sroot_esymm4 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sroot_esymm4 = lazard_root_esymm4 roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /sroot_esymm4 /lazard_root_esymm4.
rewrite eval_ssum /= !big_cons !big_nil !sparse_canonical_mul_eval.
rewrite hx0 hx1 hx2 hx3 hx4 !sparse_canonical_const_eval !mulr1 !addr0.
by rewrite !mulrA !addrA.
Qed.

Lemma eval_sroot_esymm5 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sroot_esymm5 = lazard_root_esymm5 roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /sroot_esymm5 /lazard_root_esymm5.
rewrite eval_sproduct /= !big_cons !big_nil.
rewrite hx0 hx1 hx2 hx3 hx4 !mulr1.
by rewrite !mulrA.
Qed.

Lemma eval_root_atoms (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp = lazard_root_p (lazard_depressed_of_roots roots) /\
  SN.sparse_eval_ring values sq = lazard_root_q (lazard_depressed_of_roots roots) /\
  SN.sparse_eval_ring values sr = lazard_root_r (lazard_depressed_of_roots roots) /\
  SN.sparse_eval_ring values ss = lazard_root_s (lazard_depressed_of_roots roots).
Proof.
have he2 := eval_sroot_esymm2 hsum.
have he3 := eval_sroot_esymm3 hsum.
have he4 := eval_sroot_esymm4 hsum.
have he5 := eval_sroot_esymm5 hsum.
rewrite /sp /sq /sr /ss !sparse_canonical_neg_eval he2 he3 he4 he5.
rewrite /lazard_depressed_of_roots.
by repeat split.
Qed.

Lemma eval_root_orbit a b (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values (sroot_orbit_formula a b) =
    lazard_root_orbit_formula a b roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /sroot_orbit_formula /lazard_root_orbit_formula.
rewrite eval_ssum /= !big_cons !big_nil !sparse_canonical_mul_eval
  !sparse_canonical_pow_eval.
rewrite hx0 hx1 hx2 hx3 hx4
  !sparse_canonical_const_eval !mulr1 !addr0.
by rewrite !mulrA !addrA.
Qed.

Lemma eval_invariant_atoms (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values si4 = lazard_root_i4 (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values si5 = lazard_root_i5 (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values si6 = lazard_root_i6 (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values si7 = lazard_root_i7 (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values si8 = lazard_root_i8 (lazard_root_invariants roots).
Proof.
repeat split.
- rewrite /si4; exact: eval_root_orbit hsum.
- rewrite /si5; exact: eval_root_orbit hsum.
- rewrite /si6; exact: eval_root_orbit hsum.
- rewrite /si7; exact: eval_root_orbit hsum.
- rewrite /si8; exact: eval_root_orbit hsum.
Qed.

Lemma eval_root_T_prime (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values st_prime = RR.lazard_root_T_prime roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /st_prime /RR.lazard_root_T_prime.
rewrite eval_sproduct /= !big_cons !big_nil !sparse_canonical_sub_eval.
rewrite hx0 hx1 hx2 hx3 hx4 !mulr1.
by rewrite !mulrA.
Qed.

Lemma eval_root_U_prime (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values su_prime = RR.lazard_root_U_prime roots.
Proof.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /su_prime /RR.lazard_root_U_prime.
rewrite eval_sproduct /= !big_cons !big_nil !sparse_canonical_sub_eval.
rewrite hx0 hx1 hx2 hx3 hx4 !mulr1.
by rewrite !mulrA.
Qed.

Lemma eval_sepsilon_factor0 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (sparse_canonical_add
        (sparse_canonical_sub (sparse_canonical_sub sx1 sx2) sx3) sx4) =
    (tnth roots o1 - tnth roots o2 - tnth roots o3) + tnth roots o4.
Proof.
transitivity
  ((SN.sparse_eval_ring values sx1 - SN.sparse_eval_ring values sx2 -
      SN.sparse_eval_ring values sx3) + SN.sparse_eval_ring values sx4).
- exact: eval_slinear4.
- by rewrite (sx1_eval roots) (sx2_eval roots) (sx3_eval roots)
    (sx4_eval hsum).
Qed.

Lemma eval_sepsilon_factor1 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (sparse_canonical_add
        (sparse_canonical_sub (sparse_canonical_sub sx2 sx3) sx4) sx0) =
    (tnth roots o2 - tnth roots o3 - tnth roots o4) + tnth roots o0.
Proof.
transitivity
  ((SN.sparse_eval_ring values sx2 - SN.sparse_eval_ring values sx3 -
      SN.sparse_eval_ring values sx4) + SN.sparse_eval_ring values sx0).
- exact: eval_slinear4.
- by rewrite (sx0_eval roots) (sx2_eval roots) (sx3_eval roots)
    (sx4_eval hsum).
Qed.

Lemma eval_sepsilon_factor2 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (sparse_canonical_add
        (sparse_canonical_sub (sparse_canonical_sub sx3 sx4) sx0) sx1) =
    (tnth roots o3 - tnth roots o4 - tnth roots o0) + tnth roots o1.
Proof.
transitivity
  ((SN.sparse_eval_ring values sx3 - SN.sparse_eval_ring values sx4 -
      SN.sparse_eval_ring values sx0) + SN.sparse_eval_ring values sx1).
- exact: eval_slinear4.
- by rewrite (sx0_eval roots) (sx1_eval roots) (sx3_eval roots)
    (sx4_eval hsum).
Qed.

Lemma eval_sepsilon_factor3 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (sparse_canonical_add
        (sparse_canonical_sub (sparse_canonical_sub sx4 sx0) sx1) sx2) =
    (tnth roots o4 - tnth roots o0 - tnth roots o1) + tnth roots o2.
Proof.
transitivity
  ((SN.sparse_eval_ring values sx4 - SN.sparse_eval_ring values sx0 -
      SN.sparse_eval_ring values sx1) + SN.sparse_eval_ring values sx2).
- exact: eval_slinear4.
- by rewrite (sx0_eval roots) (sx1_eval roots) (sx2_eval roots)
    (sx4_eval hsum).
Qed.

Lemma eval_sepsilon_factor4 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values
      (sparse_canonical_add
        (sparse_canonical_sub (sparse_canonical_sub sx0 sx1) sx2) sx3) =
    (tnth roots o0 - tnth roots o1 - tnth roots o2) + tnth roots o3.
Proof.
transitivity
  ((SN.sparse_eval_ring values sx0 - SN.sparse_eval_ring values sx1 -
      SN.sparse_eval_ring values sx2) + SN.sparse_eval_ring values sx3).
- exact: eval_slinear4.
- by rewrite (sx0_eval roots) (sx1_eval roots) (sx2_eval roots)
    (sx3_eval roots).
Qed.

Lemma eval_root_epsilon_product
    (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sepsilon_product =
    lazard_root_epsilon_product roots.
Proof.
rewrite /sepsilon_product /lazard_root_epsilon_product.
rewrite eval_sproduct /= !big_cons !big_nil.
rewrite (eval_sepsilon_factor0 hsum) (eval_sepsilon_factor1 hsum)
  (eval_sepsilon_factor2 hsum) (eval_sepsilon_factor3 hsum)
  (eval_sepsilon_factor4 hsum) !mulr1.
by rewrite !mulrA.
Qed.

Lemma eval_root_E (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots.
Proof.
have ht := eval_root_T_prime hsum.
have hu := eval_root_U_prime hsum.
by rewrite /sroot_E /Q.lazard_root_E sparse_canonical_neg_eval
  sparse_canonical_add_eval !sparse_canonical_pow_eval ht hu.
Qed.

Lemma eval_tu_epsilon_E (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values st_prime = RR.lazard_root_T_prime roots /\
  SN.sparse_eval_ring values su_prime = RR.lazard_root_U_prime roots /\
  SN.sparse_eval_ring values sepsilon_product =
    lazard_root_epsilon_product roots /\
  SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots.
Proof.
repeat split.
- exact: eval_root_T_prime hsum.
- exact: eval_root_U_prime hsum.
- exact: eval_root_epsilon_product hsum.
- exact: eval_root_E hsum.
Qed.

Opaque sp sq sr ss si4 si5 si6 si7 si8.

Lemma eval_sp21_i4_term :
  SN.sparse_eval_ring values (sparse_canonical_scale 3%:Z si4) =
    3%:R * SN.sparse_eval_ring values si4.
Proof. by rewrite [LHS]sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp21_p_square_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 2%:Z (sparse_canonical_pow sp 2)) =
    2%:R * SN.sparse_eval_ring values sp ^+ 2.
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
congr (_ * _).
exact: sparse_canonical_pow_eval.
Qed.

Lemma eval_sp21_r_term :
  SN.sparse_eval_ring values (sparse_canonical_scale (- 16%:Z) sr) =
    - (16%:R * SN.sparse_eval_ring values sr).
Proof. by rewrite [LHS]sparse_canonical_scale_neg_nat_eval. Qed.

Lemma eval_sp21_structure :
  SN.sparse_eval_ring values sp21 =
    5%:R *
      (3%:R * SN.sparse_eval_ring values si4 +
        (2%:R * SN.sparse_eval_ring values sp ^+ 2 +
          - (16%:R * SN.sparse_eval_ring values sr))).
Proof.
rewrite /sp21 [LHS]sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite eval_ssum !big_cons !big_nil.
rewrite eval_sp21_i4_term eval_sp21_p_square_term eval_sp21_r_term.
by rewrite addr0.
Qed.

Lemma eval_p21_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values sp = lazard_root_p c)
    (hr : SN.sparse_eval_ring values sr = lazard_root_r c)
    (hi4 : SN.sparse_eval_ring values si4 = lazard_root_i4 i) :
  SN.sparse_eval_ring values sp21 = lazard_p21 c i.
Proof.
rewrite eval_sp21_structure hp hr hi4 /lazard_p21.
by rewrite add3_right_assoc.
Qed.

(** Closed atom composites used by the P22--P24 summand certificates. *)
Lemma eval_sp_square_atom :
  SN.sparse_eval_ring values (sparse_canonical_pow sp 2) =
    SN.sparse_eval_ring values sp ^+ 2.
Proof. exact: sparse_canonical_pow_eval. Qed.

Lemma eval_sp_cube_atom :
  SN.sparse_eval_ring values (sparse_canonical_pow sp 3) =
    SN.sparse_eval_ring values sp ^+ 3.
Proof. exact: sparse_canonical_pow_eval. Qed.

Lemma eval_sq_cube_atom :
  SN.sparse_eval_ring values (sparse_canonical_pow sq 3) =
    SN.sparse_eval_ring values sq ^+ 3.
Proof. exact: sparse_canonical_pow_eval. Qed.

Lemma eval_sp_sq_mul_atom :
  SN.sparse_eval_ring values (sparse_canonical_mul sp sq) =
    SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq.
Proof. exact: sparse_canonical_mul_eval. Qed.

Lemma eval_sq_si6_mul_atom :
  SN.sparse_eval_ring values (sparse_canonical_mul sq si6) =
    SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6.
Proof. exact: sparse_canonical_mul_eval. Qed.

Lemma eval_sp_si7_mul_atom :
  SN.sparse_eval_ring values (sparse_canonical_mul sp si7) =
    SN.sparse_eval_ring values sp * SN.sparse_eval_ring values si7.
Proof. exact: sparse_canonical_mul_eval. Qed.

Lemma eval_sr_si5_mul_atom :
  SN.sparse_eval_ring values (sparse_canonical_mul sr si5) =
    SN.sparse_eval_ring values sr * SN.sparse_eval_ring values si5.
Proof. exact: sparse_canonical_mul_eval. Qed.

Lemma eval_sr_ss_mul_atom :
  SN.sparse_eval_ring values (sparse_canonical_mul sr ss) =
    SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss.
Proof. exact: sparse_canonical_mul_eval. Qed.

Lemma eval_sp_cube_q_product_atom :
  SN.sparse_eval_ring values
      (sproduct [:: sparse_canonical_pow sp 3; sq]) =
    SN.sparse_eval_ring values sp ^+ 3 * SN.sparse_eval_ring values sq.
Proof.
rewrite [LHS]eval_sproduct !big_cons !big_nil eval_sp_cube_atom.
by rewrite mulr1.
Qed.

Lemma eval_sp_square_ss_product_atom :
  SN.sparse_eval_ring values
      (sproduct [:: sparse_canonical_pow sp 2; ss]) =
    SN.sparse_eval_ring values sp ^+ 2 * SN.sparse_eval_ring values ss.
Proof.
rewrite [LHS]eval_sproduct !big_cons !big_nil eval_sp_square_atom.
by rewrite mulr1.
Qed.

Lemma eval_sp_sq_sr_product_atom :
  SN.sparse_eval_ring values (sproduct [:: sp; sq; sr]) =
    SN.sparse_eval_ring values sp *
      (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values sr).
Proof.
rewrite [LHS]eval_sproduct !big_cons !big_nil.
by rewrite mulr1.
Qed.

Lemma eval_sp22_i5_left_atom :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 8%:Z (sparse_canonical_pow sp 2)) =
    8%:R * SN.sparse_eval_ring values sp ^+ 2.
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sp_square_atom.
Qed.

Lemma eval_sp22_i5_right_atom :
  SN.sparse_eval_ring values (sparse_canonical_scale 50%:Z sr) =
    50%:R * SN.sparse_eval_ring values sr.
Proof. by rewrite [LHS]sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp22_i4_left_atom :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 2%:Z) (sparse_canonical_mul sp sq)) =
    - (2%:R *
      (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_sq_mul_atom.
Qed.

Lemma eval_sp22_i4_right_atom :
  SN.sparse_eval_ring values (sparse_canonical_scale 25%:Z ss) =
    25%:R * SN.sparse_eval_ring values ss.
Proof. by rewrite [LHS]sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp23_i4_left_atom :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 3%:Z) (sparse_canonical_mul sp sq)) =
    - (3%:R *
      (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_sq_mul_atom.
Qed.

Lemma eval_sp23_i4_right_atom :
  SN.sparse_eval_ring values (sparse_canonical_scale 15%:Z ss) =
    15%:R * SN.sparse_eval_ring values ss.
Proof. by rewrite [LHS]sparse_canonical_scale_nat_eval. Qed.

Lemma eval_sp24_i4_left_atom :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 14%:Z) (sparse_canonical_mul sp sq)) =
    - (14%:R *
      (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_sq_mul_atom.
Qed.

Lemma eval_sp24_i4_right_atom :
  SN.sparse_eval_ring values (sparse_canonical_scale 20%:Z ss) =
    20%:R * SN.sparse_eval_ring values ss.
Proof. by rewrite [LHS]sparse_canonical_scale_nat_eval. Qed.

(** The eight closed P22 summands. *)
Lemma eval_sp22_q_i6_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 10%:Z) (sparse_canonical_mul sq si6)) =
    - (10%:R *
      (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sq_si6_mul_atom.
Qed.

Lemma eval_sp22_i5_term :
  SN.sparse_eval_ring values
      (sparse_canonical_mul
        (sparse_canonical_sub
          (sparse_canonical_scale 8%:Z (sparse_canonical_pow sp 2))
          (sparse_canonical_scale 50%:Z sr)) si5) =
    (8%:R * SN.sparse_eval_ring values sp ^+ 2 -
      50%:R * SN.sparse_eval_ring values sr) *
      SN.sparse_eval_ring values si5.
Proof.
rewrite [LHS]sparse_canonical_mul_eval.
rewrite sparse_canonical_sub_eval
  eval_sp22_i5_left_atom eval_sp22_i5_right_atom.
reflexivity.
Qed.

Lemma eval_sp22_i4_term :
  SN.sparse_eval_ring values
      (sparse_canonical_mul
        (sparse_canonical_sub
          (sparse_canonical_scale (- 2%:Z) (sparse_canonical_mul sp sq))
          (sparse_canonical_scale 25%:Z ss)) si4) =
    (- (2%:R *
        (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)) -
      25%:R * SN.sparse_eval_ring values ss) *
      SN.sparse_eval_ring values si4.
Proof.
rewrite [LHS]sparse_canonical_mul_eval.
rewrite sparse_canonical_sub_eval
  eval_sp22_i4_left_atom eval_sp22_i4_right_atom.
reflexivity.
Qed.

Lemma eval_sp22_p_cube_q_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 8%:Z
        (sproduct [:: sparse_canonical_pow sp 3; sq])) =
    8%:R *
      (SN.sparse_eval_ring values sp ^+ 3 * SN.sparse_eval_ring values sq).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sp_cube_q_product_atom.
Qed.

Lemma eval_sp22_q_cube_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 70%:Z (sparse_canonical_pow sq 3)) =
    70%:R * SN.sparse_eval_ring values sq ^+ 3.
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sq_cube_atom.
Qed.

Lemma eval_sp22_p_square_s_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 20%:Z)
        (sproduct [:: sparse_canonical_pow sp 2; ss])) =
    - (20%:R *
      (SN.sparse_eval_ring values sp ^+ 2 * SN.sparse_eval_ring values ss)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_square_ss_product_atom.
Qed.

Lemma eval_sp22_p_q_r_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 26%:Z) (sproduct [:: sp; sq; sr])) =
    - (26%:R *
      (SN.sparse_eval_ring values sp *
        (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values sr))).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_sq_sr_product_atom.
Qed.

Lemma eval_sp22_r_s_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 50%:Z (sparse_canonical_mul sr ss)) =
    50%:R *
      (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sr_ss_mul_atom.
Qed.

(** The seven new P23 summands; its sixth summand reuses P22's triple. *)
Lemma eval_sp23_p_i7_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 4%:Z) (sparse_canonical_mul sp si7)) =
    - (4%:R *
      (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values si7)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_si7_mul_atom.
Qed.

Lemma eval_sp23_q_i6_term :
  SN.sparse_eval_ring values
      (sparse_canonical_neg (sparse_canonical_mul sq si6)) =
    - (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6).
Proof.
rewrite [LHS]sparse_canonical_neg_eval.
by rewrite eval_sq_si6_mul_atom.
Qed.

Lemma eval_sp23_r_i5_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 4%:Z (sparse_canonical_mul sr si5)) =
    4%:R *
      (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values si5).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sr_si5_mul_atom.
Qed.

Lemma eval_sp23_i4_term :
  SN.sparse_eval_ring values
      (sparse_canonical_mul
        (sparse_canonical_add
          (sparse_canonical_scale (- 3%:Z) (sparse_canonical_mul sp sq))
          (sparse_canonical_scale 15%:Z ss)) si4) =
    (- (3%:R *
        (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)) +
      15%:R * SN.sparse_eval_ring values ss) *
      SN.sparse_eval_ring values si4.
Proof.
rewrite [LHS]sparse_canonical_mul_eval.
rewrite sparse_canonical_add_eval
  eval_sp23_i4_left_atom eval_sp23_i4_right_atom.
reflexivity.
Qed.

Lemma eval_sp23_p_square_s_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 26%:Z
        (sproduct [:: sparse_canonical_pow sp 2; ss])) =
    26%:R *
      (SN.sparse_eval_ring values sp ^+ 2 * SN.sparse_eval_ring values ss).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sp_square_ss_product_atom.
Qed.

Lemma eval_sp23_q_cube_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 7%:Z (sparse_canonical_pow sq 3)) =
    7%:R * SN.sparse_eval_ring values sq ^+ 3.
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sq_cube_atom.
Qed.

Lemma eval_sp23_r_s_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 40%:Z) (sparse_canonical_mul sr ss)) =
    - (40%:R *
      (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sr_ss_mul_atom.
Qed.

(** The eight closed P24 summands. *)
Lemma eval_sp24_p_i7_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 3%:Z (sparse_canonical_mul sp si7)) =
    3%:R *
      (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values si7).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sp_si7_mul_atom.
Qed.

Lemma eval_sp24_q_i6_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 18%:Z) (sparse_canonical_mul sq si6)) =
    - (18%:R *
      (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6)).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sq_si6_mul_atom.
Qed.

Lemma eval_sp24_r_i5_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 22%:Z (sparse_canonical_mul sr si5)) =
    22%:R *
      (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values si5).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sr_si5_mul_atom.
Qed.

Lemma eval_sp24_i4_term :
  SN.sparse_eval_ring values
      (sparse_canonical_mul
        (sparse_canonical_add
          (sparse_canonical_scale (- 14%:Z) (sparse_canonical_mul sp sq))
          (sparse_canonical_scale 20%:Z ss)) si4) =
    (- (14%:R *
        (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)) +
      20%:R * SN.sparse_eval_ring values ss) *
      SN.sparse_eval_ring values si4.
Proof.
rewrite [LHS]sparse_canonical_mul_eval.
rewrite sparse_canonical_add_eval
  eval_sp24_i4_left_atom eval_sp24_i4_right_atom.
reflexivity.
Qed.

Lemma eval_sp24_p_square_s_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 18%:Z
        (sproduct [:: sparse_canonical_pow sp 2; ss])) =
    18%:R *
      (SN.sparse_eval_ring values sp ^+ 2 * SN.sparse_eval_ring values ss).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sp_square_ss_product_atom.
Qed.

Lemma eval_sp24_p_q_r_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale (- 33%:Z) (sproduct [:: sp; sq; sr])) =
    - (33%:R *
      (SN.sparse_eval_ring values sp *
        (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values sr))).
Proof.
rewrite [LHS]sparse_canonical_scale_neg_nat_eval.
by rewrite eval_sp_sq_sr_product_atom.
Qed.

Lemma eval_sp24_q_cube_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 21%:Z (sparse_canonical_pow sq 3)) =
    21%:R * SN.sparse_eval_ring values sq ^+ 3.
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sq_cube_atom.
Qed.

Lemma eval_sp24_r_s_term :
  SN.sparse_eval_ring values
      (sparse_canonical_scale 30%:Z (sparse_canonical_mul sr ss)) =
    30%:R *
      (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss).
Proof.
rewrite [LHS]sparse_canonical_scale_nat_eval.
by rewrite eval_sr_ss_mul_atom.
Qed.

(** Fold-right structure of the three eight-summand P2 coefficients. *)
Lemma eval_sp22_structure :
  SN.sparse_eval_ring values sp22 =
    25%:R *
      (- (10%:R *
          (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6)) +
      ((8%:R * SN.sparse_eval_ring values sp ^+ 2 -
          50%:R * SN.sparse_eval_ring values sr) *
          SN.sparse_eval_ring values si5 +
      ((- (2%:R *
            (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)) -
          25%:R * SN.sparse_eval_ring values ss) *
          SN.sparse_eval_ring values si4 +
      (8%:R *
          (SN.sparse_eval_ring values sp ^+ 3 *
            SN.sparse_eval_ring values sq) +
      (70%:R * SN.sparse_eval_ring values sq ^+ 3 +
      (- (20%:R *
          (SN.sparse_eval_ring values sp ^+ 2 *
            SN.sparse_eval_ring values ss)) +
      (- (26%:R *
          (SN.sparse_eval_ring values sp *
            (SN.sparse_eval_ring values sq *
              SN.sparse_eval_ring values sr))) +
      50%:R *
        (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss)))))))).
Proof.
rewrite /sp22 [LHS]sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite eval_ssum !big_cons !big_nil.
rewrite eval_sp22_q_i6_term eval_sp22_i5_term eval_sp22_i4_term
  eval_sp22_p_cube_q_term eval_sp22_q_cube_term
  eval_sp22_p_square_s_term eval_sp22_p_q_r_term eval_sp22_r_s_term.
by rewrite addr0.
Qed.

Lemma eval_sp23_structure :
  SN.sparse_eval_ring values sp23 =
    25%:R *
      (- (4%:R *
          (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values si7)) +
      (- (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6) +
      (4%:R *
          (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values si5) +
      ((- (3%:R *
            (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)) +
          15%:R * SN.sparse_eval_ring values ss) *
          SN.sparse_eval_ring values si4 +
      (26%:R *
          (SN.sparse_eval_ring values sp ^+ 2 *
            SN.sparse_eval_ring values ss) +
      (- (26%:R *
          (SN.sparse_eval_ring values sp *
            (SN.sparse_eval_ring values sq *
              SN.sparse_eval_ring values sr))) +
      (7%:R * SN.sparse_eval_ring values sq ^+ 3 +
      - (40%:R *
        (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss))))))))).
Proof.
rewrite /sp23 [LHS]sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite eval_ssum !big_cons !big_nil.
rewrite eval_sp23_p_i7_term eval_sp23_q_i6_term eval_sp23_r_i5_term
  eval_sp23_i4_term eval_sp23_p_square_s_term eval_sp22_p_q_r_term
  eval_sp23_q_cube_term eval_sp23_r_s_term.
by rewrite addr0.
Qed.

Lemma eval_sp24_structure :
  SN.sparse_eval_ring values sp24 =
    25%:R *
      (3%:R *
          (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values si7) +
      (- (18%:R *
          (SN.sparse_eval_ring values sq * SN.sparse_eval_ring values si6)) +
      (22%:R *
          (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values si5) +
      ((- (14%:R *
            (SN.sparse_eval_ring values sp * SN.sparse_eval_ring values sq)) +
          20%:R * SN.sparse_eval_ring values ss) *
          SN.sparse_eval_ring values si4 +
      (18%:R *
          (SN.sparse_eval_ring values sp ^+ 2 *
            SN.sparse_eval_ring values ss) +
      (- (33%:R *
          (SN.sparse_eval_ring values sp *
            (SN.sparse_eval_ring values sq *
              SN.sparse_eval_ring values sr))) +
      (21%:R * SN.sparse_eval_ring values sq ^+ 3 +
      30%:R *
        (SN.sparse_eval_ring values sr * SN.sparse_eval_ring values ss)))))))).
Proof.
rewrite /sp24 [LHS]sparse_canonical_scale_nat_eval.
congr (_ * _).
rewrite eval_ssum !big_cons !big_nil.
rewrite eval_sp24_p_i7_term eval_sp24_q_i6_term eval_sp24_r_i5_term
  eval_sp24_i4_term eval_sp24_p_square_s_term eval_sp24_p_q_r_term
  eval_sp24_q_cube_term eval_sp24_r_s_term.
by rewrite addr0.
Qed.

Lemma eval_p22_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values sp = lazard_root_p c)
    (hq : SN.sparse_eval_ring values sq = lazard_root_q c)
    (hr : SN.sparse_eval_ring values sr = lazard_root_r c)
    (hs : SN.sparse_eval_ring values ss = lazard_root_s c)
    (hi4 : SN.sparse_eval_ring values si4 = lazard_root_i4 i)
    (hi5 : SN.sparse_eval_ring values si5 = lazard_root_i5 i)
    (hi6 : SN.sparse_eval_ring values si6 = lazard_root_i6 i) :
  SN.sparse_eval_ring values sp22 = lazard_p22 c i.
Proof.
rewrite eval_sp22_structure hp hq hr hs hi4 hi5 hi6 /lazard_p22.
by rewrite !mulNr !mulrA add8_right_assoc.
Qed.

Lemma eval_p23_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values sp = lazard_root_p c)
    (hq : SN.sparse_eval_ring values sq = lazard_root_q c)
    (hr : SN.sparse_eval_ring values sr = lazard_root_r c)
    (hs : SN.sparse_eval_ring values ss = lazard_root_s c)
    (hi4 : SN.sparse_eval_ring values si4 = lazard_root_i4 i)
    (hi5 : SN.sparse_eval_ring values si5 = lazard_root_i5 i)
    (hi6 : SN.sparse_eval_ring values si6 = lazard_root_i6 i)
    (hi7 : SN.sparse_eval_ring values si7 = lazard_root_i7 i) :
  SN.sparse_eval_ring values sp23 = lazard_p23 c i.
Proof.
rewrite eval_sp23_structure hp hq hr hs hi4 hi5 hi6 hi7 /lazard_p23.
by rewrite !mulNr !mulrA add8_right_assoc.
Qed.

Lemma eval_p24_from_atoms
    (c : LazardDepressedRootCoefficients F) (i : LazardRootInvariants F)
    (hp : SN.sparse_eval_ring values sp = lazard_root_p c)
    (hq : SN.sparse_eval_ring values sq = lazard_root_q c)
    (hr : SN.sparse_eval_ring values sr = lazard_root_r c)
    (hs : SN.sparse_eval_ring values ss = lazard_root_s c)
    (hi4 : SN.sparse_eval_ring values si4 = lazard_root_i4 i)
    (hi5 : SN.sparse_eval_ring values si5 = lazard_root_i5 i)
    (hi6 : SN.sparse_eval_ring values si6 = lazard_root_i6 i)
    (hi7 : SN.sparse_eval_ring values si7 = lazard_root_i7 i) :
  SN.sparse_eval_ring values sp24 = lazard_p24 c i.
Proof.
rewrite eval_sp24_structure hp hq hr hs hi4 hi5 hi6 hi7 /lazard_p24.
by rewrite !mulNr !mulrA add8_right_assoc.
Qed.

Transparent sp sq sr ss si4 si5 si6 si7 si8.

Lemma eval_p21 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp21 =
    lazard_p21 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [_ [hr _]]] := eval_root_atoms hsum.
have [hi4 _] := eval_invariant_atoms hsum.
exact: eval_p21_from_atoms hp hr hi4.
Qed.

Lemma eval_p22 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp22 =
    lazard_p22 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [hq [hr hs]]] := eval_root_atoms hsum.
have [hi4 [hi5 [hi6 _]]] := eval_invariant_atoms hsum.
exact: eval_p22_from_atoms hp hq hr hs hi4 hi5 hi6.
Qed.

Lemma eval_p23 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp23 =
    lazard_p23 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [hq [hr hs]]] := eval_root_atoms hsum.
have [hi4 [hi5 [hi6 [hi7 _]]]] := eval_invariant_atoms hsum.
exact: eval_p23_from_atoms hp hq hr hs hi4 hi5 hi6 hi7.
Qed.

Lemma eval_p24 (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp24 =
    lazard_p24 (lazard_depressed_of_roots roots)
      (lazard_root_invariants roots).
Proof.
have [hp [hq [hr hs]]] := eval_root_atoms hsum.
have [hi4 [hi5 [hi6 [hi7 _]]]] := eval_invariant_atoms hsum.
exact: eval_p24_from_atoms hp hq hr hs hi4 hi5 hi6 hi7.
Qed.

Lemma eval_p2_atoms (hsum : lazard_root_esymm1 roots = 0) :
  SN.sparse_eval_ring values sp21 =
      lazard_p21 (lazard_depressed_of_roots roots) (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values sp22 =
      lazard_p22 (lazard_depressed_of_roots roots) (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots) (lazard_root_invariants roots) /\
  SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots) (lazard_root_invariants roots).
Proof.
repeat split.
- exact: eval_p21 hsum.
- exact: eval_p22 hsum.
- exact: eval_p23 hsum.
- exact: eval_p24 hsum.
Qed.

Lemma eval_sparse_structural_atoms
    (hsum : lazard_root_esymm1 roots = 0) :
  eval_sparse_cyclic sparse_cyclic_epsilon = C.lazard_cyclic_root_epsilon roots /\
  eval_sparse_cyclic sparse_cyclic_T = C.lazard_cyclic_root_T roots /\
  eval_sparse_cyclic sparse_cyclic_formula_U = C.lazard_cyclic_root_formula_U roots /\
  eval_sparse_cyclic sparse_cyclic_fourier_P1 = lazard_cyclic_fourier_P1 roots /\
  eval_sparse_cyclic sparse_cyclic_fourier_P2 = lazard_cyclic_fourier_P2 roots.
Proof.
have [ht [hu [he hE]]] := eval_tu_epsilon_E hsum.
have hx0 := sx0_eval roots.
have hx1 := sx1_eval roots.
have hx2 := sx2_eval roots.
have hx3 := sx3_eval roots.
have hx4 := sx4_eval hsum.
rewrite /sparse_cyclic_epsilon /sparse_cyclic_T /sparse_cyclic_formula_U
  eval_sparse_cyclic_sub eval_sparse_cyclic_scale !eval_sparse_cyclic_add
  !eval_sparse_cyclic_scale
  /sparse_cyclic_discriminant /sparse_cyclic_A /sparse_cyclic_B
  /C.lazard_cyclic_root_epsilon /C.lazard_cyclic_root_T
  /C.lazard_cyclic_root_formula_U
  /PolynomialFormulasLazardQuinticRootProjectionI.lazard_cyclic_discriminant
  /C.lazard_cyclic_fifth_root_A /C.lazard_cyclic_fifth_root_B.
rewrite he ht hu.
rewrite /eval_sparse_cyclic /= !sparse_canonical_const_eval
  !SN.sparse_eval_ring_zero.
rewrite /sparse_cyclic_fourier_P1 /sparse_cyclic_fourier_P2
  /eval_sparse_cyclic /lazard_cyclic_fourier_P1
  /lazard_cyclic_fourier_P2 /= hx0 hx1 hx2 hx3 hx4.
by repeat split.
Qed.

Lemma eval_p2_left_p21_scalar
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hp21 : SN.sparse_eval_ring values sp21 =
      lazard_p21 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots)) :
  SN.sparse_eval_ring values
      (sparse_canonical_mul
        (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp21) =
    5%:R * Q.lazard_root_E roots *
      lazard_p21 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots).
Proof.
rewrite [LHS]sparse_canonical_mul_eval hp21.
rewrite sparse_canonical_mul_eval hE.
by rewrite sparse_canonical_const_eval.
Qed.

Lemma eval_p2_left_p22_scalar
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hp22 : SN.sparse_eval_ring values sp22 =
      lazard_p22 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots)) :
  SN.sparse_eval_ring values
      (sparse_canonical_mul
        (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp22) =
    5%:R * Q.lazard_root_E roots *
      lazard_p22 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots).
Proof.
rewrite [LHS]sparse_canonical_mul_eval hp22.
rewrite sparse_canonical_mul_eval hE.
by rewrite sparse_canonical_const_eval.
Qed.

Lemma eval_p2_sp23_T
    (hp23 : SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hT : eval_sparse_cyclic sparse_cyclic_T =
      C.lazard_cyclic_root_T roots) :
  eval_sparse_cyclic (sparse_cyclic_scale sp23 sparse_cyclic_T) =
    lazard_cyclic_scale
      (lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
      (C.lazard_cyclic_root_T roots).
Proof.
by rewrite [LHS]eval_sparse_cyclic_scale hp23 hT.
Qed.

Lemma eval_p2_sp24_formula_U
    (hp24 : SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hformula : eval_sparse_cyclic sparse_cyclic_formula_U =
      C.lazard_cyclic_root_formula_U roots) :
  eval_sparse_cyclic
      (sparse_cyclic_scale sp24 sparse_cyclic_formula_U) =
    lazard_cyclic_scale
      (lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
      (C.lazard_cyclic_root_formula_U roots).
Proof.
by rewrite [LHS]eval_sparse_cyclic_scale hp24 hformula.
Qed.

Lemma eval_p2_sp23_T_add_sp24_formula_U
    (hp23 : SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp24 : SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hT : eval_sparse_cyclic sparse_cyclic_T =
      C.lazard_cyclic_root_T roots)
    (hformula : eval_sparse_cyclic sparse_cyclic_formula_U =
      C.lazard_cyclic_root_formula_U roots) :
  eval_sparse_cyclic
      (sparse_cyclic_add
        (sparse_cyclic_scale sp23 sparse_cyclic_T)
        (sparse_cyclic_scale sp24 sparse_cyclic_formula_U)) =
    lazard_cyclic_add
      (lazard_cyclic_scale
        (lazard_p23 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots))
        (C.lazard_cyclic_root_T roots))
      (lazard_cyclic_scale
        (lazard_p24 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots))
        (C.lazard_cyclic_root_formula_U roots)).
Proof.
rewrite [LHS]eval_sparse_cyclic_add.
rewrite (eval_p2_sp23_T hp23 hT) (eval_p2_sp24_formula_U hp24 hformula).
reflexivity.
Qed.

Lemma eval_p2_epsilon_mul_TU
    (hp23 : SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp24 : SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots)
    (hT : eval_sparse_cyclic sparse_cyclic_T =
      C.lazard_cyclic_root_T roots)
    (hformula : eval_sparse_cyclic sparse_cyclic_formula_U =
      C.lazard_cyclic_root_formula_U roots) :
  eval_sparse_cyclic
      (sparse_cyclic_mul sparse_cyclic_epsilon
        (sparse_cyclic_add
          (sparse_cyclic_scale sp23 sparse_cyclic_T)
          (sparse_cyclic_scale sp24 sparse_cyclic_formula_U))) =
    lazard_cyclic_mul (C.lazard_cyclic_root_epsilon roots)
      (lazard_cyclic_add
        (lazard_cyclic_scale
          (lazard_p23 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots))
          (C.lazard_cyclic_root_T roots))
        (lazard_cyclic_scale
          (lazard_p24 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots))
          (C.lazard_cyclic_root_formula_U roots))).
Proof.
rewrite [LHS]eval_sparse_cyclic_mul hepsilon.
rewrite (eval_p2_sp23_T_add_sp24_formula_U hp23 hp24 hT hformula).
reflexivity.
Qed.

Lemma eval_p2_scale_two_epsilon_TU
    (hp23 : SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp24 : SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots)
    (hT : eval_sparse_cyclic sparse_cyclic_T =
      C.lazard_cyclic_root_T roots)
    (hformula : eval_sparse_cyclic sparse_cyclic_formula_U =
      C.lazard_cyclic_root_formula_U roots) :
  eval_sparse_cyclic
      (sparse_cyclic_scale (sparse_canonical_const 2)
        (sparse_cyclic_mul sparse_cyclic_epsilon
          (sparse_cyclic_add
            (sparse_cyclic_scale sp23 sparse_cyclic_T)
            (sparse_cyclic_scale sp24 sparse_cyclic_formula_U)))) =
    lazard_cyclic_scale 2%:R
      (lazard_cyclic_mul (C.lazard_cyclic_root_epsilon roots)
        (lazard_cyclic_add
          (lazard_cyclic_scale
            (lazard_p23 (lazard_depressed_of_roots roots)
              (lazard_root_invariants roots))
            (C.lazard_cyclic_root_T roots))
          (lazard_cyclic_scale
            (lazard_p24 (lazard_depressed_of_roots roots)
              (lazard_root_invariants roots))
            (C.lazard_cyclic_root_formula_U roots)))).
Proof.
rewrite [LHS]eval_sparse_cyclic_scale sparse_canonical_const_eval.
rewrite (eval_p2_epsilon_mul_TU hp23 hp24 hepsilon hT hformula).
reflexivity.
Qed.

Lemma eval_p2_left_constant_p22
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hp22 : SN.sparse_eval_ring values sp22 =
      lazard_p22 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots)) :
  eval_sparse_cyclic
      (sparse_cyclic_constant
        (sparse_canonical_mul
          (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp22)) =
    C.lazard_cyclic_constant
      (5%:R * Q.lazard_root_E roots *
        lazard_p22 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots)).
Proof.
rewrite [LHS]eval_sparse_cyclic_constant.
by rewrite (eval_p2_left_p22_scalar hE hp22).
Qed.

Lemma eval_p2_left_epsilon_p21
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hp21 : SN.sparse_eval_ring values sp21 =
      lazard_p21 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots) :
  eval_sparse_cyclic
      (sparse_cyclic_scale
        (sparse_canonical_mul
          (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp21)
        sparse_cyclic_epsilon) =
    lazard_cyclic_scale
      (5%:R * Q.lazard_root_E roots *
        lazard_p21 (lazard_depressed_of_roots roots)
          (lazard_root_invariants roots))
      (C.lazard_cyclic_root_epsilon roots).
Proof.
rewrite [LHS]eval_sparse_cyclic_scale.
by rewrite (eval_p2_left_p21_scalar hE hp21) hepsilon.
Qed.

Lemma eval_p2_left_tail
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hp22 : SN.sparse_eval_ring values sp22 =
      lazard_p22 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp23 : SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp24 : SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots)
    (hT : eval_sparse_cyclic sparse_cyclic_T =
      C.lazard_cyclic_root_T roots)
    (hformula : eval_sparse_cyclic sparse_cyclic_formula_U =
      C.lazard_cyclic_root_formula_U roots) :
  eval_sparse_cyclic
      (sparse_cyclic_add
        (sparse_cyclic_constant
          (sparse_canonical_mul
            (sparse_canonical_mul (sparse_canonical_const 5) sroot_E) sp22))
        (sparse_cyclic_scale (sparse_canonical_const 2)
          (sparse_cyclic_mul sparse_cyclic_epsilon
            (sparse_cyclic_add
              (sparse_cyclic_scale sp23 sparse_cyclic_T)
              (sparse_cyclic_scale sp24 sparse_cyclic_formula_U))))) =
    lazard_cyclic_add
      (C.lazard_cyclic_constant
        (5%:R * Q.lazard_root_E roots *
          lazard_p22 (lazard_depressed_of_roots roots)
            (lazard_root_invariants roots)))
      (lazard_cyclic_scale 2%:R
        (lazard_cyclic_mul (C.lazard_cyclic_root_epsilon roots)
          (lazard_cyclic_add
            (lazard_cyclic_scale
              (lazard_p23 (lazard_depressed_of_roots roots)
                (lazard_root_invariants roots))
              (C.lazard_cyclic_root_T roots))
            (lazard_cyclic_scale
              (lazard_p24 (lazard_depressed_of_roots roots)
                (lazard_root_invariants roots))
              (C.lazard_cyclic_root_formula_U roots))))).
Proof.
rewrite [LHS]eval_sparse_cyclic_add.
rewrite (eval_p2_left_constant_p22 hE hp22).
rewrite (eval_p2_scale_two_epsilon_TU hp23 hp24 hepsilon hT hformula).
reflexivity.
Qed.

Lemma eval_sparse_p2_numerator_left_closed
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hp21 : SN.sparse_eval_ring values sp21 =
      lazard_p21 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp22 : SN.sparse_eval_ring values sp22 =
      lazard_p22 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp23 : SN.sparse_eval_ring values sp23 =
      lazard_p23 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hp24 : SN.sparse_eval_ring values sp24 =
      lazard_p24 (lazard_depressed_of_roots roots)
        (lazard_root_invariants roots))
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots)
    (hT : eval_sparse_cyclic sparse_cyclic_T =
      C.lazard_cyclic_root_T roots)
    (hformula : eval_sparse_cyclic sparse_cyclic_formula_U =
      C.lazard_cyclic_root_formula_U roots) :
  eval_sparse_cyclic sparse_p2_numerator_left =
    P2C.lazard_cyclic_p2_numerator_left roots.
Proof.
rewrite /sparse_p2_numerator_left
  /P2C.lazard_cyclic_p2_numerator_left.
rewrite [LHS]eval_sparse_cyclic_add.
rewrite (eval_p2_left_epsilon_p21 hE hp21 hepsilon).
rewrite (eval_p2_left_tail hE hp22 hp23 hp24 hepsilon hT hformula).
reflexivity.
Qed.

Lemma eval_p2_P1_square
    (hP1 : eval_sparse_cyclic sparse_cyclic_fourier_P1 =
      lazard_cyclic_fourier_P1 roots) :
  eval_sparse_cyclic
      (sparse_cyclic_mul sparse_cyclic_fourier_P1
        sparse_cyclic_fourier_P1) =
    lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
      (lazard_cyclic_fourier_P1 roots).
Proof.
by rewrite [LHS]eval_sparse_cyclic_mul hP1.
Qed.

Lemma eval_p2_P1_cube
    (hP1 : eval_sparse_cyclic sparse_cyclic_fourier_P1 =
      lazard_cyclic_fourier_P1 roots) :
  eval_sparse_cyclic
      (sparse_cyclic_mul
        (sparse_cyclic_mul sparse_cyclic_fourier_P1
          sparse_cyclic_fourier_P1)
        sparse_cyclic_fourier_P1) =
    lazard_cyclic_mul
      (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
        (lazard_cyclic_fourier_P1 roots))
      (lazard_cyclic_fourier_P1 roots).
Proof.
rewrite [LHS]eval_sparse_cyclic_mul (eval_p2_P1_square hP1) hP1.
reflexivity.
Qed.

Lemma eval_p2_P1_cube_mul_P2
    (hP1 : eval_sparse_cyclic sparse_cyclic_fourier_P1 =
      lazard_cyclic_fourier_P1 roots)
    (hP2 : eval_sparse_cyclic sparse_cyclic_fourier_P2 =
      lazard_cyclic_fourier_P2 roots) :
  eval_sparse_cyclic
      (sparse_cyclic_mul
        (sparse_cyclic_mul
          (sparse_cyclic_mul sparse_cyclic_fourier_P1
            sparse_cyclic_fourier_P1)
          sparse_cyclic_fourier_P1)
        sparse_cyclic_fourier_P2) =
    lazard_cyclic_mul
      (lazard_cyclic_mul
        (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
          (lazard_cyclic_fourier_P1 roots))
        (lazard_cyclic_fourier_P1 roots))
      (lazard_cyclic_fourier_P2 roots).
Proof.
rewrite [LHS]eval_sparse_cyclic_mul (eval_p2_P1_cube hP1) hP2.
reflexivity.
Qed.

Lemma eval_p2_epsilon_mul_P1_cube_P2
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots)
    (hP1 : eval_sparse_cyclic sparse_cyclic_fourier_P1 =
      lazard_cyclic_fourier_P1 roots)
    (hP2 : eval_sparse_cyclic sparse_cyclic_fourier_P2 =
      lazard_cyclic_fourier_P2 roots) :
  eval_sparse_cyclic
      (sparse_cyclic_mul sparse_cyclic_epsilon
        (sparse_cyclic_mul
          (sparse_cyclic_mul
            (sparse_cyclic_mul sparse_cyclic_fourier_P1
              sparse_cyclic_fourier_P1)
            sparse_cyclic_fourier_P1)
          sparse_cyclic_fourier_P2)) =
    lazard_cyclic_mul (C.lazard_cyclic_root_epsilon roots)
      (lazard_cyclic_mul
        (lazard_cyclic_mul
          (lazard_cyclic_mul (lazard_cyclic_fourier_P1 roots)
            (lazard_cyclic_fourier_P1 roots))
          (lazard_cyclic_fourier_P1 roots))
        (lazard_cyclic_fourier_P2 roots)).
Proof.
rewrite [LHS]eval_sparse_cyclic_mul hepsilon.
rewrite (eval_p2_P1_cube_mul_P2 hP1 hP2).
reflexivity.
Qed.

Lemma eval_sparse_p2_numerator_right_closed
    (hE : SN.sparse_eval_ring values sroot_E = Q.lazard_root_E roots)
    (hepsilon : eval_sparse_cyclic sparse_cyclic_epsilon =
      C.lazard_cyclic_root_epsilon roots)
    (hP1 : eval_sparse_cyclic sparse_cyclic_fourier_P1 =
      lazard_cyclic_fourier_P1 roots)
    (hP2 : eval_sparse_cyclic sparse_cyclic_fourier_P2 =
      lazard_cyclic_fourier_P2 roots) :
  eval_sparse_cyclic sparse_p2_numerator_right =
    P2C.lazard_cyclic_p2_numerator_right roots.
Proof.
rewrite /sparse_p2_numerator_right
  /P2C.lazard_cyclic_p2_numerator_right.
rewrite [LHS]eval_sparse_cyclic_scale.
rewrite sparse_canonical_scale_nat_eval hE.
rewrite (eval_p2_epsilon_mul_P1_cube_P2 hepsilon hP1 hP2).
reflexivity.
Qed.

Theorem eval_sparse_p2_numerator_difference
    (hsum : lazard_root_esymm1 roots = 0) :
  eval_sparse_cyclic sparse_p2_numerator_difference =
    P2C.lazard_cyclic_p2_numerator_difference roots.
Proof.
have [hp21 [hp22 [hp23 hp24]]] := eval_p2_atoms hsum.
have [ht [hu [hformula [hP1 hP2]]]] :=
  eval_sparse_structural_atoms hsum.
have [_ [_ [_ hE]]] := eval_tu_epsilon_E hsum.
rewrite /sparse_p2_numerator_difference
  /P2C.lazard_cyclic_p2_numerator_difference.
rewrite [LHS]eval_sparse_cyclic_sub.
rewrite (eval_sparse_p2_numerator_left_closed
  hE hp21 hp22 hp23 hp24 ht hu hformula).
rewrite (eval_sparse_p2_numerator_right_closed hE ht hP1 hP2).
reflexivity.
Qed.

End SemanticBridge.

End PolynomialFormulasLazardQuinticRootFourierNumeratorP2Sparse.
