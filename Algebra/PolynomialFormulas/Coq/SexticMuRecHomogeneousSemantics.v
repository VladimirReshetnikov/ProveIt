From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From Undecidability.Shared.Libs.DLW Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util Require Import recomp.
From PolynomialFormulas Require Import
  SexticMuRecComputability
  SexticSparsePolynomials SexticSparseResolvents SexticNewtonPowerSums
  SexticMuRecSparseEvaluator SexticMuRecCollisionEvaluator
  SexticMuRecCollisionSemantics SexticMuRecDescriptorSemantics
  SexticMuRecResolventRootEvaluator
  SexticMuRecMixedRadixSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecHomogeneousSemantics.
Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SR := PolynomialFormulasSexticSparseResolvents.
Module NPS := PolynomialFormulasSexticNewtonPowerSums.
Module SE := PolynomialFormulasSexticMuRecSparseEvaluator.
Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.
Module CS := PolynomialFormulasSexticMuRecCollisionSemantics.
Module DS := PolynomialFormulasSexticMuRecDescriptorSemantics.
Module RE := PolynomialFormulasSexticMuRecResolventRootEvaluator.
Module MRX := PolynomialFormulasSexticMuRecMixedRadixSemantics.

Definition sparse_term_one : SP.sparse_term := (1, SP.exponent_zero).

Lemma exponent_add0_left exponent :
  SP.exponent_add SP.exponent_zero exponent = exponent.
Proof.
apply: eq_from_tnth=> index.
rewrite SP.tnth_exponent_addE SP.tnth_exponent_zeroE.
reflexivity.
Qed.

Lemma exponent_add0_right exponent :
  SP.exponent_add exponent SP.exponent_zero = exponent.
Proof.
apply: eq_from_tnth=> index.
rewrite SP.tnth_exponent_addE SP.tnth_exponent_zeroE.
exact: addn0.
Qed.

Lemma exponent_add_assoc left middle right :
  SP.exponent_add left (SP.exponent_add middle right) =
  SP.exponent_add (SP.exponent_add left middle) right.
Proof.
apply: eq_from_tnth=> index.
rewrite !SP.tnth_exponent_addE.
exact: addnA.
Qed.

Lemma sparse_term_mul1_left term :
  SP.term_mul sparse_term_one term = term.
Proof.
case: term=> coefficient exponent.
rewrite /SP.term_mul /sparse_term_one /= mul1r exponent_add0_left.
reflexivity.
Qed.

Lemma sparse_term_mul1_right term :
  SP.term_mul term sparse_term_one = term.
Proof.
case: term=> coefficient exponent.
rewrite /SP.term_mul /sparse_term_one /= mulr1 exponent_add0_right.
reflexivity.
Qed.

Lemma sparse_term_mul_assoc left middle right :
  SP.term_mul left (SP.term_mul middle right) =
  SP.term_mul (SP.term_mul left middle) right.
Proof.
case: left=> left_coefficient left_exponent.
case: middle=> middle_coefficient middle_exponent.
case: right=> right_coefficient right_exponent.
rewrite /SP.term_mul /=.
congr (_, _).
- exact: mulrA.
- exact: exponent_add_assoc.
Qed.

Lemma sparse_term_mul_comm left right :
  SP.term_mul left right = SP.term_mul right left.
Proof.
case: left=> left_coefficient left_exponent.
case: right=> right_coefficient right_exponent.
rewrite /SP.term_mul /= mulrC.
congr (_, _).
apply: eq_from_tnth=> index.
rewrite !SP.tnth_exponent_addE.
exact: addnC.
Qed.

Lemma sparse_term_mul_nth left right coordinate :
  (coordinate < 6)%N ->
  nth 0%N (SP.term_mul left right).2 coordinate =
  (nth 0%N left.2 coordinate + nth 0%N right.2 coordinate)%N.
Proof.
move=> hcoordinate.
pose ordinal : 'I_6 := @Ordinal 6 coordinate hcoordinate.
change
  (nth 0%N (SP.exponent_add left.2 right.2) ordinal =
    nth 0%N left.2 ordinal + nth 0%N right.2 ordinal)%N.
rewrite -(tnth_nth 0%N) SP.tnth_exponent_addE.
by rewrite (@tnth_nth 6 nat 0%N left.2 ordinal)
  (@tnth_nth 6 nat 0%N right.2 ordinal).
Qed.

Definition homogeneous_digit_term
    (descriptor_term : nat -> nat -> SP.sparse_term)
    (numerator denominator : int) (partition digit : nat) :
    SP.sparse_term :=
  match digit with
  | 0%nat => (numerator, SP.exponent_zero)
  | S descriptor_digit =>
      SP.term_mul (- denominator, SP.exponent_zero)
        (descriptor_term partition descriptor_digit)
  end.

Local Notation descriptor_sparse_term := DS.descriptor_sparse_term.

Definition homogeneous_sparse_term
    (coefficient_value : nat -> nat -> nat -> int)
    (exponent_value : nat -> nat -> nat -> nat)
    (x0 x1 : nat) (numerator denominator : int)
    (partition digit : nat) : SP.sparse_term :=
  homogeneous_digit_term
    (fun partition_value descriptor_digit =>
      descriptor_sparse_term coefficient_value exponent_value
        x0 x1 partition_value descriptor_digit)
    numerator denominator partition digit.

Definition homogeneous_state_factor_term
    (coefficient_value : nat -> nat -> nat -> int)
    (exponent_value : nat -> nat -> nat -> nat)
    (x0 x1 : nat) (numerator denominator : int)
    (descriptor_terms factor remaining : nat) : SP.sparse_term :=
  homogeneous_sparse_term coefficient_value exponent_value
    x0 x1 numerator denominator factor
    (gcd.rem remaining (S descriptor_terms)).

Local Notation recursive_descriptor_coefficient_correct :=
  DS.recursive_descriptor_coefficient_correct.
Local Notation recursive_descriptor_exponent_correct :=
  DS.recursive_descriptor_exponent_correct.

Lemma eval_recursive_succ {arity}
    (expression : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (SE.RecSucc expression) values =
  S (SE.eval_recursive_expression expression values).
Proof. reflexivity. Qed.

Lemma eval_recursive_plus {arity}
    (left right : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (SE.RecPlus left right) values =
  (SE.eval_recursive_expression left values +
    SE.eval_recursive_expression right values)%N.
Proof. reflexivity. Qed.

Lemma eval_recursive_div_succ {arity}
    (dividend : SE.recursive_expression arity) divisor values :
  SE.eval_recursive_expression (SE.RecDivSucc dividend divisor) values =
  gcd.div (SE.eval_recursive_expression dividend values) (S divisor).
Proof. reflexivity. Qed.

Lemma eval_recursive_rem_succ {arity}
    (dividend : SE.recursive_expression arity) divisor values :
  SE.eval_recursive_expression (SE.RecRemSucc dividend divisor) values =
  gcd.rem (SE.eval_recursive_expression dividend values) (S divisor).
Proof. reflexivity. Qed.

Lemma gcd_div_succ_mathcomp value divisor :
  gcd.div value (S divisor) = (value %/ S divisor)%N.
Proof.
exact: (DS.gcd_div_rem_mathcomp value (Nat.neq_succ_0 divisor)).1.
Qed.

Lemma gcd_rem_succ_mathcomp value divisor :
  gcd.rem value (S divisor) = (value %% S divisor)%N.
Proof.
exact: (DS.gcd_div_rem_mathcomp value (Nat.neq_succ_0 divisor)).2.
Qed.

Lemma big_sum_list_an_ord_from (term : nat -> int) start count :
  \sum_(index <- list_an start count) term index =
  \sum_(index < count) term (start + index).
Proof.
elim: count start => [|count ih] start.
- by rewrite /= big_nil big_ord0.
- rewrite list_an_S big_cons big_ord_recl /= ih.
  f_equal.
  + apply f_equal.
    exact: esym (PeanoNat.Nat.add_0_r start).
  + apply: eq_bigr=> index _.
    apply f_equal.
    change (S start + val index = start + S (val index)).
    exact: Nat.add_succ_comm.
Qed.

Lemma big_sum_list_an_ord (term : nat -> int) count :
  \sum_(index <- list_an 0 count) term index =
  \sum_(index < count) term index.
Proof.
rewrite big_sum_list_an_ord_from.
apply: eq_bigr=> index _.
reflexivity.
Qed.

Lemma cartesian_terms_sparse_product factors :
  MRX.cartesian_terms sparse_term_one SP.term_mul factors =
  SP.sparse_product factors.
Proof.
elim: factors=> [|factor factors ih].
- reflexivity.
- by rewrite /= ih /SP.sparse_mul.
Qed.

Lemma newton_symmetrize_observer_sum elementary polynomial :
  \sum_(term <- polynomial)
    term.1 *
      NPS.sparse_eval_ring elementary
        (NPS.newton_mobius_orbit term.2) =
  NPS.sparse_eval_ring elementary (NPS.newton_symmetrize polynomial).
Proof.
rewrite /NPS.newton_symmetrize NPS.sparse_eval_ring_sum big_map.
apply: eq_bigr=> term _.
rewrite /NPS.newton_symmetrize_term NPS.sparse_eval_ring_mul
  NPS.sparse_eval_ring_const intz.
reflexivity.
Qed.

Lemma homogeneous_negative_descriptor_term denominator descriptor_term :
  SP.term_mul (- denominator, SP.exponent_zero) descriptor_term =
  SP.term_neg
    (SP.term_mul (denominator, SP.exponent_zero) descriptor_term).
Proof.
case: descriptor_term=> coefficient exponent.
rewrite /SP.term_mul /SP.term_neg /= mulNr.
reflexivity.
Qed.

Lemma homogeneous_factor_observer_sum
    descriptor_terms coefficient_value exponent_value
    x0 x1 numerator denominator partition descriptor_polynomial :
  (forall target : SP.sparse_term -> int,
    \sum_(digit < descriptor_terms)
      target
        (descriptor_sparse_term coefficient_value exponent_value
          x0 x1 partition digit) =
    \sum_(term <- descriptor_polynomial) target term) ->
  forall target : SP.sparse_term -> int,
    \sum_(digit < S descriptor_terms)
      target
        (homogeneous_sparse_term coefficient_value exponent_value
          x0 x1 numerator denominator partition digit) =
    \sum_(term <-
      SP.sparse_sub (SP.sparse_const numerator)
        (SP.sparse_mul (SP.sparse_const denominator)
          descriptor_polynomial)) target term.
Proof.
move=> hdescriptor target.
rewrite big_ord_recl /=
  /homogeneous_sparse_term /homogeneous_digit_term.
rewrite /SP.sparse_sub /SP.sparse_add /SP.sparse_const
  /SP.sparse_neg /SP.sparse_mul /=.
rewrite big_cons big_map big_cat big_nil big_map.
cbn.
rewrite (hdescriptor
  (fun descriptor_term =>
    target
      (SP.term_mul (- denominator, SP.exponent_zero) descriptor_term))).
apply f_equal.
rewrite intZmod.addzC intZmod.add0z.
apply: eq_bigr=> descriptor_term _.
by rewrite homogeneous_negative_descriptor_term.
Qed.

Lemma descriptor_sparse_term_nth coefficient_value exponent_value
    x0 x1 partition digit coordinate :
  (coordinate < 6)%N ->
  nth 0%N
    (descriptor_sparse_term coefficient_value exponent_value
      x0 x1 partition digit).2 coordinate =
  exponent_value partition digit coordinate.
Proof.
move=> hcoordinate.
rewrite /descriptor_sparse_term.
pose ordinal : 'I_6 := @Ordinal 6 coordinate hcoordinate.
change
  (nth 0%N
    [tuple exponent_value partition digit (val i) | i < 6]
    ordinal = exponent_value partition digit coordinate).
by rewrite nth_mktuple /ordinal.
Qed.

Lemma eval_resolvent_homogeneous_factor_coefficient_from
    descriptor_coefficient coefficient_value exponent_value arity
    (partition digit x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity) values :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  CS.eval_mathcomp_recursive_signed_expression
      (RE.resolvent_homogeneous_factor_coefficient_from
        descriptor_coefficient digit x0 x1 denominator numerator) values =
  (homogeneous_sparse_term coefficient_value exponent_value
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (CS.eval_mathcomp_recursive_signed_expression numerator values)
    (SE.eval_recursive_expression denominator values)%:Z
    (SE.eval_recursive_expression partition values)
    (SE.eval_recursive_expression digit values)).1.
Proof.
move=> hcoefficient.
rewrite /RE.resolvent_homogeneous_factor_coefficient_from.
rewrite CS.eval_mathcomp_recursive_signed_if_zero.
case hdigit: (SE.eval_recursive_expression digit values)=> [|descriptor_digit].
- reflexivity.
- rewrite CS.eval_mathcomp_recursive_signed_mult
    CS.eval_mathcomp_recursive_signed_negate
    CS.eval_mathcomp_recursive_signed_of_nat.
  rewrite /recursive_descriptor_coefficient_correct in hcoefficient.
  rewrite hcoefficient.
  rewrite /homogeneous_sparse_term /homogeneous_digit_term
    /descriptor_sparse_term /SP.term_mul /=.
  rewrite hdigit subn1.
  reflexivity.
Qed.

Lemma eval_resolvent_homogeneous_factor_exponent_from
    descriptor_exponent exponent_value coefficient_value arity
    (partition digit x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity)
    coordinate values :
  (coordinate < 6)%N ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  SE.eval_recursive_expression
      (RE.resolvent_homogeneous_factor_exponent_from
        descriptor_exponent partition digit coordinate) values =
  nth 0%N
    (homogeneous_sparse_term coefficient_value exponent_value
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      (CS.eval_mathcomp_recursive_signed_expression numerator values)
      (SE.eval_recursive_expression denominator values)%:Z
      (SE.eval_recursive_expression partition values)
      (SE.eval_recursive_expression digit values)).2 coordinate.
Proof.
move=> hcoordinate hexponent.
rewrite /RE.resolvent_homogeneous_factor_exponent_from
  CS.eval_recursive_if_zero.
case hdigit: (SE.eval_recursive_expression digit values)=> [|descriptor_digit].
- rewrite /homogeneous_sparse_term /homogeneous_digit_term /=
    /SP.exponent_zero.
  pose ordinal : 'I_6 := @Ordinal 6 coordinate hcoordinate.
  change (0%N = nth 0%N [tuple 0%N | _ < 6] ordinal).
  by rewrite nth_mktuple.
- rewrite /recursive_descriptor_exponent_correct in hexponent.
  rewrite hexponent /homogeneous_sparse_term /homogeneous_digit_term /=.
  rewrite hdigit subn1.
  change
    (exponent_value (SE.eval_recursive_expression partition values)
        descriptor_digit coordinate =
      nth 0%N
        (SP.exponent_add SP.exponent_zero
          (descriptor_sparse_term coefficient_value exponent_value
            (SE.eval_recursive_expression x0 values)
            (SE.eval_recursive_expression x1 values)
            (SE.eval_recursive_expression partition values)
            descriptor_digit).2) coordinate).
  rewrite exponent_add0_left.
  exact: esym (@descriptor_sparse_term_nth
    coefficient_value exponent_value
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (SE.eval_recursive_expression partition values)
    descriptor_digit coordinate hcoordinate).
Qed.

Lemma eval_resolvent_homogeneous_next_coefficient_from
    descriptor_terms descriptor_coefficient coefficient_value exponent_value
    arity (state x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity)
    values factor remaining term :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  vec_pos
      (project 9 (SE.eval_recursive_expression state values)) pos0 = factor ->
  vec_pos
      (project 9 (SE.eval_recursive_expression state values)) pos1 = remaining ->
  mathcomp_zigzag_decode
      (vec_pos (project 9 (SE.eval_recursive_expression state values)) pos2) =
    term.1 ->
  mathcomp_zigzag_decode
      (SE.eval_recursive_expression
        (SE.recursive_signed_code
          (SE.recursive_signed_mult
            (SE.recursive_signed_decode (CE.recursive_project9 pos2 state))
            (RE.resolvent_homogeneous_factor_coefficient_from
              descriptor_coefficient
              (SE.RecRemSucc
                (CE.recursive_project9 pos1 state) descriptor_terms)
              x0 x1 denominator numerator))) values) =
  (SP.term_mul term
    (homogeneous_state_factor_term coefficient_value exponent_value
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      (CS.eval_mathcomp_recursive_signed_expression numerator values)
      (SE.eval_recursive_expression denominator values)%:Z
      descriptor_terms factor remaining)).1.
Proof.
move=> hcoefficient hfactor hremaining hterm.
rewrite CS.decode_eval_recursive_signed_code_mathcomp
  CS.eval_mathcomp_recursive_signed_mult
  CS.eval_mathcomp_recursive_signed_decode
  CS.eval_recursive_project9 hterm.
rewrite (@eval_resolvent_homogeneous_factor_coefficient_from
  descriptor_coefficient coefficient_value exponent_value arity
  (CE.recursive_project9 pos0 state)
  (SE.RecRemSucc (CE.recursive_project9 pos1 state) descriptor_terms)
  x0 x1 denominator numerator values hcoefficient).
rewrite CS.eval_recursive_project9 hfactor
  eval_recursive_rem_succ CS.eval_recursive_project9 hremaining.
reflexivity.
Qed.

Lemma eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value
    (coefficient_value : nat -> nat -> nat -> int)
    arity (state x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity)
    (position : pos 9) coordinate values factor remaining
    (term : SP.sparse_term) :
  (coordinate < 6)%N ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  vec_pos
      (project 9 (SE.eval_recursive_expression state values)) pos0 = factor ->
  vec_pos
      (project 9 (SE.eval_recursive_expression state values)) pos1 = remaining ->
  vec_pos
      (project 9 (SE.eval_recursive_expression state values)) position =
    nth 0%N term.2 coordinate ->
  SE.eval_recursive_expression
      (SE.RecPlus (CE.recursive_project9 position state)
        (RE.resolvent_homogeneous_factor_exponent_from descriptor_exponent
          (CE.recursive_project9 pos0 state)
          (SE.RecRemSucc
            (CE.recursive_project9 pos1 state) descriptor_terms)
          coordinate)) values =
  nth 0%N
    (SP.term_mul term
      (homogeneous_state_factor_term coefficient_value exponent_value
        (SE.eval_recursive_expression x0 values)
        (SE.eval_recursive_expression x1 values)
        (CS.eval_mathcomp_recursive_signed_expression numerator values)
        (SE.eval_recursive_expression denominator values)%:Z
        descriptor_terms factor remaining)).2 coordinate.
Proof.
move=> hcoordinate hexponent hfactor hremaining hterm.
rewrite eval_recursive_plus CS.eval_recursive_project9 hterm.
rewrite (@eval_resolvent_homogeneous_factor_exponent_from
  descriptor_exponent exponent_value coefficient_value arity
  (CE.recursive_project9 pos0 state)
  (SE.RecRemSucc (CE.recursive_project9 pos1 state) descriptor_terms)
  x0 x1 denominator numerator coordinate values hcoordinate hexponent).
rewrite CS.eval_recursive_project9 hfactor
  eval_recursive_rem_succ CS.eval_recursive_project9 hremaining.
exact: esym (@sparse_term_mul_nth term
  (homogeneous_state_factor_term coefficient_value exponent_value
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (CS.eval_mathcomp_recursive_signed_expression numerator values)
    (SE.eval_recursive_expression denominator values)%:Z
    descriptor_terms factor remaining)
  coordinate hcoordinate).
Qed.

Definition homogeneous_state_semantics
    (state factor remaining : nat) (term : SP.sparse_term) : Prop :=
  vec_pos (project 9 state) pos0 = factor /\
  vec_pos (project 9 state) pos1 = remaining /\
  mathcomp_zigzag_decode (vec_pos (project 9 state) pos2) = term.1 /\
  vec_pos (project 9 state) pos3 = nth 0%N term.2 0 /\
  vec_pos (project 9 state) pos4 = nth 0%N term.2 1 /\
  vec_pos (project 9 state) pos5 = nth 0%N term.2 2 /\
  vec_pos (project 9 state) pos6 = nth 0%N term.2 3 /\
  vec_pos (project 9 state) pos7 = nth 0%N term.2 4 /\
  vec_pos (project 9 state) pos8 = nth 0%N term.2 5.

Lemma homogeneous_state_recursive_sparse_exponent
    arity state factor remaining term (values : Vector.t nat arity) :
  homogeneous_state_semantics state factor remaining term ->
  CS.recursive_sparse_exponent
    (CE.recursive_project9 pos3 (@SE.RecVar (S arity) pos0))
    (CE.recursive_project9 pos4 (@SE.RecVar (S arity) pos0))
    (CE.recursive_project9 pos5 (@SE.RecVar (S arity) pos0))
    (CE.recursive_project9 pos6 (@SE.RecVar (S arity) pos0))
    (CE.recursive_project9 pos7 (@SE.RecVar (S arity) pos0))
    (CE.recursive_project9 pos8 (@SE.RecVar (S arity) pos0))
    (state ## values) = term.2.
Proof.
move=> [_ [_ [_ [hexponent0 [hexponent1 [hexponent2
  [hexponent3 [hexponent4 hexponent5]]]]]]]].
apply: eq_from_tnth=> coordinate.
rewrite /CS.recursive_sparse_exponent.
case: coordinate=> coordinate hcoordinate.
case: coordinate hcoordinate=> [|coordinate] hcoordinate.
- rewrite !(tnth_nth 0%N) /=.
  change (vec_pos (project 9 state) pos3 = nth 0%N term.2 0).
  exact hexponent0.
case: coordinate hcoordinate=> [|coordinate] hcoordinate.
- rewrite !(tnth_nth 0%N) /=.
  change (vec_pos (project 9 state) pos4 = nth 0%N term.2 1).
  exact hexponent1.
case: coordinate hcoordinate=> [|coordinate] hcoordinate.
- rewrite !(tnth_nth 0%N) /=.
  change (vec_pos (project 9 state) pos5 = nth 0%N term.2 2).
  exact hexponent2.
case: coordinate hcoordinate=> [|coordinate] hcoordinate.
- rewrite !(tnth_nth 0%N) /=.
  change (vec_pos (project 9 state) pos6 = nth 0%N term.2 3).
  exact hexponent3.
case: coordinate hcoordinate=> [|coordinate] hcoordinate.
- rewrite !(tnth_nth 0%N) /=.
  change (vec_pos (project 9 state) pos7 = nth 0%N term.2 4).
  exact hexponent4.
case: coordinate hcoordinate=> [|coordinate] hcoordinate.
- rewrite !(tnth_nth 0%N) /=.
  change (vec_pos (project 9 state) pos8 = nth 0%N term.2 5).
  exact hexponent5.
by [].
Qed.

Lemma homogeneous_state_initial term_index :
  homogeneous_state_semantics
    (inject
      (0 ## term_index ## mathcomp_zigzag_encode 1 ##
       0 ## 0 ## 0 ## 0 ## 0 ## 0 ## vec_nil))
    0 term_index sparse_term_one.
Proof.
rewrite /homogeneous_state_semantics /sparse_term_one !project_inject /=.
rewrite /SP.exponent_zero /=.
repeat split.
- change (mathcomp_zigzag_decode (mathcomp_zigzag_encode 1) = 1).
  exact: mathcomp_zigzag_decode_encode.
all: by rewrite (nth_map ord0) ?size_enum_ord.
Qed.

Lemma eval_resolvent_homogeneous_state_step_from
    descriptor_terms descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity
    (state x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity)
    values factor remaining term :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  homogeneous_state_semantics
      (SE.eval_recursive_expression state values) factor remaining term ->
  homogeneous_state_semantics
    (SE.eval_recursive_expression
      (RE.resolvent_homogeneous_state_step_from descriptor_terms
        descriptor_coefficient descriptor_exponent
        state x0 x1 denominator numerator) values)
    (S factor) (gcd.div remaining (S descriptor_terms))
    (SP.term_mul term
      (homogeneous_state_factor_term coefficient_value exponent_value
        (SE.eval_recursive_expression x0 values)
        (SE.eval_recursive_expression x1 values)
        (CS.eval_mathcomp_recursive_signed_expression numerator values)
        (SE.eval_recursive_expression denominator values)%:Z
        descriptor_terms factor remaining)).
Proof.
move=> hcoefficient hexponent.
move=> [hfactor [hremaining [hterm
  [hexponent0 [hexponent1 [hexponent2
  [hexponent3 [hexponent4 hexponent5]]]]]]]].
rewrite /homogeneous_state_semantics
  /RE.resolvent_homogeneous_state_step_from
  !CS.eval_recursive_inject9 !project_inject.
repeat split.
- by rewrite eval_recursive_succ CS.eval_recursive_project9 hfactor.
- by rewrite eval_recursive_div_succ CS.eval_recursive_project9 hremaining.
- exact: (@eval_resolvent_homogeneous_next_coefficient_from
    descriptor_terms descriptor_coefficient coefficient_value exponent_value
    arity state x0 x1 denominator numerator values factor remaining term
    hcoefficient hfactor hremaining hterm).
- exact: (@eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value coefficient_value
    arity state x0 x1 denominator numerator pos3 0 values
    factor remaining term erefl hexponent hfactor hremaining hexponent0).
- exact: (@eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value coefficient_value
    arity state x0 x1 denominator numerator pos4 1 values
    factor remaining term erefl hexponent hfactor hremaining hexponent1).
- exact: (@eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value coefficient_value
    arity state x0 x1 denominator numerator pos5 2 values
    factor remaining term erefl hexponent hfactor hremaining hexponent2).
- exact: (@eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value coefficient_value
    arity state x0 x1 denominator numerator pos6 3 values
    factor remaining term erefl hexponent hfactor hremaining hexponent3).
- exact: (@eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value coefficient_value
    arity state x0 x1 denominator numerator pos7 4 values
    factor remaining term erefl hexponent hfactor hremaining hexponent4).
- exact: (@eval_resolvent_homogeneous_next_exponent_from
    descriptor_terms descriptor_exponent exponent_value coefficient_value
    arity state x0 x1 denominator numerator pos8 5 values
    factor remaining term erefl hexponent hfactor hremaining hexponent5).
Qed.

Lemma eval_resolvent_homogeneous_state_iter_from
    descriptor_terms descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity
    (x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity)
    values iterations state factor remaining term :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  homogeneous_state_semantics state factor remaining term ->
  homogeneous_state_semantics
    (prim_min.iter
      (fun encoded_state =>
        SE.eval_recursive_expression
          (RE.resolvent_homogeneous_state_step_from descriptor_terms
            descriptor_coefficient descriptor_exponent
            (SE.RecVar pos0) (CE.recursive_weaken x0)
            (CE.recursive_weaken x1) (CE.recursive_weaken denominator)
            (CE.recursive_signed_weaken numerator))
          (encoded_state ## values))
      iterations state)
    (factor + iterations)
    (remaining %/ ((S descriptor_terms) ^ iterations))
    (SP.term_mul term
      (MRX.mixed_radix_term_from sparse_term_one SP.term_mul
        (fun partition digit =>
          homogeneous_sparse_term coefficient_value exponent_value
            (SE.eval_recursive_expression x0 values)
            (SE.eval_recursive_expression x1 values)
            (CS.eval_mathcomp_recursive_signed_expression numerator values)
            (SE.eval_recursive_expression denominator values)%:Z
            partition digit)
        (S descriptor_terms) factor iterations remaining)).
Proof.
move=> hcoefficient hexponent.
elim: iterations state factor remaining term =>
    [|iterations ih] state factor remaining term hstate.
- by rewrite /= addn0 expn0 divn1 sparse_term_mul1_right.
- rewrite prim_min.iter_S.
  have hstep :=
    (@eval_resolvent_homogeneous_state_step_from
      descriptor_terms descriptor_coefficient coefficient_value
      descriptor_exponent exponent_value (S arity)
      (SE.RecVar pos0) (CE.recursive_weaken x0)
      (CE.recursive_weaken x1) (CE.recursive_weaken denominator)
      (CE.recursive_signed_weaken numerator) (state ## values)
      factor remaining term hcoefficient hexponent hstate).
  rewrite (CS.eval_recursive_weaken x0 state values)
    (CS.eval_recursive_weaken x1 state values)
    (CS.eval_recursive_weaken denominator state values)
    (CS.eval_recursive_signed_weaken numerator state values)
    /homogeneous_state_factor_term
    (gcd_div_succ_mathcomp remaining descriptor_terms)
    (gcd_rem_succ_mathcomp remaining descriptor_terms) in hstep.
  have htail := ih _ _ _ _ hstep.
  rewrite addnS expnS divnMA.
  cbn [MRX.mixed_radix_term_from].
  rewrite addSn -sparse_term_mul_assoc in htail.
  exact htail.
Qed.

Lemma eval_resolvent_homogeneous_term_state_from
    descriptor_terms partition_count
    descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity
    (term_index x0 x1 denominator : SE.recursive_expression arity)
    (numerator : SE.recursive_signed_expression arity) values :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  homogeneous_state_semantics
    (SE.eval_recursive_expression
      (RE.resolvent_homogeneous_term_state_from
        descriptor_terms partition_count
        descriptor_coefficient descriptor_exponent
        term_index x0 x1 denominator numerator) values)
    partition_count
    (SE.eval_recursive_expression term_index values %/
      ((S descriptor_terms) ^ partition_count))
    (MRX.mixed_radix_term_from sparse_term_one SP.term_mul
      (fun partition digit =>
        homogeneous_sparse_term coefficient_value exponent_value
          (SE.eval_recursive_expression x0 values)
          (SE.eval_recursive_expression x1 values)
          (CS.eval_mathcomp_recursive_signed_expression numerator values)
          (SE.eval_recursive_expression denominator values)%:Z
          partition digit)
      (S descriptor_terms) 0 partition_count
      (SE.eval_recursive_expression term_index values)).
Proof.
move=> hcoefficient hexponent.
rewrite /RE.resolvent_homogeneous_term_state_from CS.eval_recursive_iter
  CS.eval_recursive_inject9 CS.eval_recursive_signed_code_mathcomp
  /CE.recursive_signed_one CS.eval_mathcomp_recursive_signed_nat.
have hinitial :=
  homogeneous_state_initial (SE.eval_recursive_expression term_index values).
have hiter :=
  (@eval_resolvent_homogeneous_state_iter_from
    descriptor_terms descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity x0 x1 denominator numerator
    values partition_count
    (inject
      (0 ## SE.eval_recursive_expression term_index values ##
       mathcomp_zigzag_encode 1 ##
       0 ## 0 ## 0 ## 0 ## 0 ## 0 ## vec_nil))
    0 (SE.eval_recursive_expression term_index values) sparse_term_one
    hcoefficient hexponent hinitial).
move: hiter.
by rewrite add0n sparse_term_mul1_left.
Qed.

Lemma eval_resolvent_homogeneous_term_count_from
    descriptor_terms partition_count arity
    (values : Vector.t nat arity) :
  SE.eval_recursive_expression
      (@RE.resolvent_homogeneous_term_count_from arity
        descriptor_terms partition_count) values =
  ((S descriptor_terms) ^ partition_count)%N.
Proof.
rewrite /RE.resolvent_homogeneous_term_count_from CS.eval_recursive_iter /=.
elim: partition_count => [|partition_count ih] //=.
by rewrite ih expnS mulnC.
Qed.

Lemma eval_recursive_iter_one {arity}
    (initial : SE.recursive_expression arity)
    (step : SE.recursive_expression (S arity)) values :
  SE.eval_recursive_expression
      (SE.RecIter (SE.RecConst 1) initial step) values =
  SE.eval_recursive_expression step
    (SE.eval_recursive_expression initial values ## values).
Proof.
rewrite CS.eval_recursive_iter CS.eval_recursive_const prim_min.iter_S.
reflexivity.
Qed.

Lemma eval_resolvent_homogeneous_term_code_from
    descriptor_terms partition_count
    descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity
    (term_index x0 x1 denominator : SE.recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      SE.recursive_signed_expression arity) values :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  CS.eval_mathcomp_recursive_signed_expression
    (SE.recursive_signed_decode
      (RE.resolvent_homogeneous_term_code_from
        descriptor_terms partition_count
        descriptor_coefficient descriptor_exponent
        term_index x0 x1 denominator numerator
        e1 e2 e3 e4 e5 e6)) values =
  let term :=
    MRX.mixed_radix_term_from sparse_term_one SP.term_mul
      (fun partition digit =>
        homogeneous_sparse_term coefficient_value exponent_value
          (SE.eval_recursive_expression x0 values)
          (SE.eval_recursive_expression x1 values)
          (CS.eval_mathcomp_recursive_signed_expression numerator values)
          (SE.eval_recursive_expression denominator values)%:Z
          partition digit)
      (S descriptor_terms) 0 partition_count
      (SE.eval_recursive_expression term_index values) in
  term.1 *
    NPS.sparse_eval_ring
      (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      (NPS.newton_mobius_orbit term.2).
Proof.
move=> hcoefficient hexponent.
have hstate :=
  (@eval_resolvent_homogeneous_term_state_from
    descriptor_terms partition_count
    descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity
    term_index x0 x1 denominator numerator values
    hcoefficient hexponent).
have hstate_copy := hstate.
move: hstate => [_ [_ [hterm _]]].
have hterm_exponent :=
  homogeneous_state_recursive_sparse_exponent values hstate_copy.
rewrite CS.eval_mathcomp_recursive_signed_decode
  /RE.resolvent_homogeneous_term_code_from eval_recursive_iter_one.
rewrite CS.decode_eval_recursive_signed_code_mathcomp
  CS.eval_mathcomp_recursive_signed_mult
  CS.eval_mathcomp_recursive_signed_decode
  CS.eval_recursive_project9 hterm.
rewrite CS.eval_recursive_newton_mobius_from
  CS.recursive_elementary_values_weakened hterm_exponent.
reflexivity.
Qed.

Lemma eval_resolvent_scaled_homogeneous_from
    descriptor_terms partition_count
    descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value arity
    (x0 x1 denominator : SE.recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      SE.recursive_signed_expression arity) values :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  CS.eval_mathcomp_recursive_signed_expression
    (RE.resolvent_scaled_homogeneous_from
      descriptor_terms partition_count
      descriptor_coefficient descriptor_exponent
      x0 x1 denominator numerator e1 e2 e3 e4 e5 e6) values =
  \sum_(code < (S descriptor_terms) ^ partition_count)
    let term :=
      MRX.mixed_radix_term_from sparse_term_one SP.term_mul
        (fun partition digit =>
          homogeneous_sparse_term coefficient_value exponent_value
            (SE.eval_recursive_expression x0 values)
            (SE.eval_recursive_expression x1 values)
            (CS.eval_mathcomp_recursive_signed_expression numerator values)
            (SE.eval_recursive_expression denominator values)%:Z
            partition digit)
        (S descriptor_terms) 0 partition_count code in
    term.1 *
      NPS.sparse_eval_ring
        (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
        (NPS.newton_mobius_orbit term.2).
Proof.
move=> hcoefficient hexponent.
rewrite /RE.resolvent_scaled_homogeneous_from
  CS.eval_mathcomp_recursive_signed_bounded_sum
  eval_resolvent_homogeneous_term_count_from
  big_sum_list_an_ord.
apply: eq_bigr=> code _.
rewrite (@eval_resolvent_homogeneous_term_code_from
  descriptor_terms partition_count
  descriptor_coefficient coefficient_value descriptor_exponent exponent_value
  (S arity) (SE.RecVar pos0)
  (CE.recursive_weaken x0) (CE.recursive_weaken x1)
  (CE.recursive_weaken denominator) (CE.recursive_signed_weaken numerator)
  (CE.recursive_signed_weaken e1) (CE.recursive_signed_weaken e2)
  (CE.recursive_signed_weaken e3) (CE.recursive_signed_weaken e4)
  (CE.recursive_signed_weaken e5) (CE.recursive_signed_weaken e6)
  (val code ## values) hcoefficient hexponent).
rewrite /= !CS.eval_recursive_weaken !CS.eval_recursive_signed_weaken
  CS.recursive_elementary_values_weakened.
reflexivity.
Qed.

Lemma eval_resolvent_scaled_homogeneous_product_from
    descriptor_terms partition_count
    descriptor_coefficient coefficient_value
    descriptor_exponent exponent_value
    (factor_terms : nat -> SP.sparse_polynomial)
    arity (x0 x1 denominator : SE.recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      SE.recursive_signed_expression arity) values :
  recursive_descriptor_coefficient_correct
      descriptor_coefficient coefficient_value ->
  recursive_descriptor_exponent_correct descriptor_exponent exponent_value ->
  (forall partition (target : SP.sparse_term -> int),
    \sum_(digit < S descriptor_terms)
      target
        (homogeneous_sparse_term coefficient_value exponent_value
          (SE.eval_recursive_expression x0 values)
          (SE.eval_recursive_expression x1 values)
          (CS.eval_mathcomp_recursive_signed_expression numerator values)
          (SE.eval_recursive_expression denominator values)%:Z
          partition digit) =
    \sum_(term <- factor_terms partition) target term) ->
  CS.eval_mathcomp_recursive_signed_expression
    (RE.resolvent_scaled_homogeneous_from
      descriptor_terms partition_count
      descriptor_coefficient descriptor_exponent
      x0 x1 denominator numerator e1 e2 e3 e4 e5 e6) values =
  NPS.sparse_eval_ring
    (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    (NPS.newton_symmetrize
      (SP.sparse_product
        [seq factor_terms partition
          | partition <- iota 0 partition_count])).
Proof.
move=> hcoefficient hexponent hfactor.
rewrite (@eval_resolvent_scaled_homogeneous_from
  descriptor_terms partition_count
  descriptor_coefficient coefficient_value
  descriptor_exponent exponent_value arity
  x0 x1 denominator numerator e1 e2 e3 e4 e5 e6 values
  hcoefficient hexponent).
rewrite (MRX.mixed_radix_cartesian_observer_sum
  sparse_term_one SP.term_mul
  (factor_terms:=factor_terms)
  (fun term =>
    term.1 *
      NPS.sparse_eval_ring
        (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
        (NPS.newton_mobius_orbit term.2)) 0 partition_count).
- rewrite cartesian_terms_sparse_product.
  exact: newton_symmetrize_observer_sum.
- done.
- exact: hfactor.
Qed.

(* --------------------------------------------------------------------- *)
(* Concrete pair/triple instances.                                      *)

Definition pair_sparse_homogeneous_product
    (u v : int) (x : SR.parameter) : SP.sparse_polynomial :=
  SP.sparse_product
    [seq SP.sparse_sub (SP.sparse_const u)
      (SP.sparse_mul (SP.sparse_const v)
        (SR.pair_sparse_descriptor_value x p))
    | p <- enum SR.pair_partition].

Definition triple_sparse_homogeneous_product
    (u v : int) (x : SR.parameter) : SP.sparse_polynomial :=
  SP.sparse_product
    [seq SP.sparse_sub (SP.sparse_const u)
      (SP.sparse_mul (SP.sparse_const v)
        (SR.triple_sparse_descriptor_value x p))
    | p <- enum SR.triple_partition].

Definition pair_homogeneous_factor_terms
    (x0 x1 : nat) (numerator denominator : int) partition :
    SP.sparse_polynomial :=
  if (partition < 15)%N then
    SP.sparse_sub (SP.sparse_const numerator)
      (SP.sparse_mul (SP.sparse_const denominator)
        (SR.pair_sparse_descriptor_value [tuple x0; x1]
          (inord partition)))
  else
    [seq homogeneous_sparse_term
      DS.pair_descriptor_coefficient_value
      DS.pair_descriptor_exponent_value
      x0 x1 numerator denominator partition (val digit)
    | digit <- index_enum 'I_126].

Definition triple_homogeneous_factor_terms
    (x0 x1 : nat) (numerator denominator : int) partition :
    SP.sparse_polynomial :=
  if (partition < 10)%N then
    SP.sparse_sub (SP.sparse_const numerator)
      (SP.sparse_mul (SP.sparse_const denominator)
        (SR.triple_sparse_descriptor_value [tuple x0; x1]
          (inord partition)))
  else
    [seq homogeneous_sparse_term
      DS.triple_descriptor_coefficient_value
      DS.triple_descriptor_exponent_value
      x0 x1 numerator denominator partition (val digit)
    | digit <- index_enum 'I_82].

Lemma pair_homogeneous_factor_observer_sum x0 x1 numerator denominator
    partition (target : SP.sparse_term -> int) :
  \sum_(digit < 126)
    target
      (homogeneous_sparse_term
        DS.pair_descriptor_coefficient_value
        DS.pair_descriptor_exponent_value
        x0 x1 numerator denominator partition digit) =
  \sum_(term <- pair_homogeneous_factor_terms
      x0 x1 numerator denominator partition) target term.
Proof.
rewrite /pair_homogeneous_factor_terms.
case hpartition: (partition < 15)%N.
- have hp : (partition < 15)%N by rewrite hpartition.
  have hinord : inord partition = @Ordinal 15 partition hp.
    apply: val_inj.
    exact: inordK hp.
  rewrite hinord.
  apply: homogeneous_factor_observer_sum=> descriptor_target.
  rewrite /DS.pair_descriptor_term.
  exact: (DS.pair_descriptor_observer_sum hp x0 x1 descriptor_target).
- by rewrite big_map.
Qed.

Lemma triple_homogeneous_factor_observer_sum x0 x1 numerator denominator
    partition (target : SP.sparse_term -> int) :
  \sum_(digit < 82)
    target
      (homogeneous_sparse_term
        DS.triple_descriptor_coefficient_value
        DS.triple_descriptor_exponent_value
        x0 x1 numerator denominator partition digit) =
  \sum_(term <- triple_homogeneous_factor_terms
      x0 x1 numerator denominator partition) target term.
Proof.
rewrite /triple_homogeneous_factor_terms.
case hpartition: (partition < 10)%N.
- have hp : (partition < 10)%N by rewrite hpartition.
  have hinord : inord partition = @Ordinal 10 partition hp.
    apply: val_inj.
    exact: inordK hp.
  rewrite hinord.
  apply: homogeneous_factor_observer_sum=> descriptor_target.
  rewrite /DS.triple_descriptor_term.
  exact: (DS.triple_descriptor_observer_sum hp x0 x1 descriptor_target).
- by rewrite big_map.
Qed.

Lemma pair_homogeneous_factor_product x0 x1 numerator denominator :
  SP.sparse_product
      [seq pair_homogeneous_factor_terms x0 x1 numerator denominator partition
        | partition <- iota 0 15] =
  pair_sparse_homogeneous_product numerator denominator [tuple x0; x1].
Proof.
rewrite /pair_sparse_homogeneous_product.
apply f_equal.
rewrite -val_enum_ord -map_comp.
apply: eq_map=> partition.
by rewrite /comp /pair_homogeneous_factor_terms ltn_ord inord_val.
Qed.

Lemma triple_homogeneous_factor_product x0 x1 numerator denominator :
  SP.sparse_product
      [seq triple_homogeneous_factor_terms x0 x1 numerator denominator partition
        | partition <- iota 0 10] =
  triple_sparse_homogeneous_product numerator denominator [tuple x0; x1].
Proof.
rewrite /triple_sparse_homogeneous_product.
apply f_equal.
rewrite -val_enum_ord -map_comp.
apply: eq_map=> partition.
by rewrite /comp /triple_homogeneous_factor_terms ltn_ord inord_val.
Qed.

Theorem eval_pair_scaled_homogeneous_from arity
    (x0 x1 denominator : SE.recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      SE.recursive_signed_expression arity) values :
  CS.eval_mathcomp_recursive_signed_expression
      (@RE.pair_scaled_homogeneous_from arity
        x0 x1 denominator numerator e1 e2 e3 e4 e5 e6) values =
  NPS.sparse_eval_ring
    (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    (NPS.newton_symmetrize
      (pair_sparse_homogeneous_product
        (CS.eval_mathcomp_recursive_signed_expression numerator values)
        (SE.eval_recursive_expression denominator values)%:Z
        [tuple SE.eval_recursive_expression x0 values;
               SE.eval_recursive_expression x1 values])).
Proof.
rewrite /RE.pair_scaled_homogeneous_from.
rewrite (@eval_resolvent_scaled_homogeneous_product_from
  125 15 (@CE.pair_descriptor_coefficient_from)
  DS.pair_descriptor_coefficient_value
  (@CE.pair_descriptor_exponent_from) DS.pair_descriptor_exponent_value
  (pair_homogeneous_factor_terms
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (CS.eval_mathcomp_recursive_signed_expression numerator values)
    (SE.eval_recursive_expression denominator values)%:Z)
  arity x0 x1 denominator numerator e1 e2 e3 e4 e5 e6 values
  DS.pair_descriptor_coefficient_from_correct
  DS.pair_descriptor_exponent_from_correct
  (@pair_homogeneous_factor_observer_sum
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (CS.eval_mathcomp_recursive_signed_expression numerator values)
    (SE.eval_recursive_expression denominator values)%:Z)).
by rewrite pair_homogeneous_factor_product.
Qed.

Theorem eval_triple_scaled_homogeneous_from arity
    (x0 x1 denominator : SE.recursive_expression arity)
    (numerator e1 e2 e3 e4 e5 e6 :
      SE.recursive_signed_expression arity) values :
  CS.eval_mathcomp_recursive_signed_expression
      (@RE.triple_scaled_homogeneous_from arity
        x0 x1 denominator numerator e1 e2 e3 e4 e5 e6) values =
  NPS.sparse_eval_ring
    (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
    (NPS.newton_symmetrize
      (triple_sparse_homogeneous_product
        (CS.eval_mathcomp_recursive_signed_expression numerator values)
        (SE.eval_recursive_expression denominator values)%:Z
        [tuple SE.eval_recursive_expression x0 values;
               SE.eval_recursive_expression x1 values])).
Proof.
rewrite /RE.triple_scaled_homogeneous_from.
rewrite (@eval_resolvent_scaled_homogeneous_product_from
  81 10 (@CE.triple_descriptor_coefficient_from)
  DS.triple_descriptor_coefficient_value
  (@CE.triple_descriptor_exponent_from) DS.triple_descriptor_exponent_value
  (triple_homogeneous_factor_terms
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (CS.eval_mathcomp_recursive_signed_expression numerator values)
    (SE.eval_recursive_expression denominator values)%:Z)
  arity x0 x1 denominator numerator e1 e2 e3 e4 e5 e6 values
  DS.triple_descriptor_coefficient_from_correct
  DS.triple_descriptor_exponent_from_correct
  (@triple_homogeneous_factor_observer_sum
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (CS.eval_mathcomp_recursive_signed_expression numerator values)
    (SE.eval_recursive_expression denominator values)%:Z)).
by rewrite triple_homogeneous_factor_product.
Qed.

End PolynomialFormulasSexticMuRecHomogeneousSemantics.
