(* ===================================================================== *)
(*  Closed semantic contracts for the concrete sextic MuRec cores.      *)
(*                                                                       *)
(*  The heavy evaluator semantics stay independent of the final         *)
(*  irreducible assembly.  This downstream module converts their raw    *)
(*  integer equalities into the four Boolean exactness contracts used by *)
(*  [SexticMuRecConcreteDecision].                                      *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia List Vector ZArith.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From Undecidability.Shared.Libs.DLW
  Require Import utils_nat utils_list pos vec.
From Undecidability.MuRec.Util Require Import recomp ra_utils.

From PolynomialFormulas Require Import
  SexticSparsePolynomials SexticSparseResolvents SexticNewtonPowerSums
  SexticComputedResolvents
  SexticSeparatingSearch SexticMuRecSeparatingInstance
  SexticMuRecComputability SexticMuRecFactorDecision SexticMuRecSparseEvaluator
  SexticMuRecCollisionEvaluator
  SexticMuRecCollisionSemantics SexticMuRecResolventRootEvaluator
  SexticMuRecMixedRadixSemantics SexticMuRecDescriptorSemantics
  SexticMuRecIrreducibleAssembly SexticMuRecConcreteDecision
  SexticMuRecHomogeneousSemantics SexticMuRecResolventRootSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecCoreExactness.

Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.
Module CS := PolynomialFormulasSexticMuRecCollisionSemantics.
Module SE := PolynomialFormulasSexticMuRecSparseEvaluator.
Module SP := PolynomialFormulasSexticSparsePolynomials.
Module SR := PolynomialFormulasSexticSparseResolvents.
Module NPS := PolynomialFormulasSexticNewtonPowerSums.
Module MRX := PolynomialFormulasSexticMuRecMixedRadixSemantics.
Module DS := PolynomialFormulasSexticMuRecDescriptorSemantics.
Module RE := PolynomialFormulasSexticMuRecResolventRootEvaluator.
Module HS := PolynomialFormulasSexticMuRecHomogeneousSemantics.
Module RS := PolynomialFormulasSexticMuRecResolventRootSemantics.
Module SS := PolynomialFormulasSexticSeparatingSearch.
Module CR := PolynomialFormulasSexticComputedResolvents.
Module MSI := PolynomialFormulasSexticMuRecSeparatingInstance.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module IA := PolynomialFormulasSexticMuRecIrreducibleAssembly.
Module CC := PolynomialFormulasSexticMuRecConcreteDecision.

(* --------------------------------------------------------------------- *)
(* Shared masked-grid expansion used by both collision evaluators.       *)

(** The evaluator visits the row-major [n x n] grid.  A diagonal slot
    contributes the multiplicative unit and consumes no mixed-radix digit;
    an off-diagonal slot consumes one digit. *)
Definition masked_grid_diagonalb n slot : bool :=
  Nat.eqb ((slot %/ n)%N) ((slot %% n)%N).

Fixpoint masked_grid_offdiag_count n slot iterations : nat :=
  match iterations with
  | 0%N => 0%N
  | iterations'.+1 =>
      if masked_grid_diagonalb n slot
      then masked_grid_offdiag_count n slot.+1 iterations'
      else (masked_grid_offdiag_count n slot.+1 iterations').+1
  end.

Fixpoint masked_grid_acc (T : Type) (one : T) (mul : T -> T -> T)
    (digit_term : nat -> nat -> T) n radix slot iterations code
    (accumulator : T) : T :=
  match iterations with
  | 0%N => accumulator
  | iterations'.+1 =>
      if masked_grid_diagonalb n slot
      then masked_grid_acc one mul digit_term n radix slot.+1 iterations'
        code accumulator
      else masked_grid_acc one mul digit_term n radix slot.+1 iterations'
        ((code %/ radix)%N)
        (mul accumulator (digit_term slot ((code %% radix)%N)))
  end.

Fixpoint masked_grid_remaining n radix slot iterations code : nat :=
  match iterations with
  | 0%N => code
  | iterations'.+1 =>
      if masked_grid_diagonalb n slot
      then masked_grid_remaining n radix slot.+1 iterations' code
      else masked_grid_remaining n radix slot.+1 iterations'
        ((code %/ radix)%N)
  end.

Fixpoint masked_grid_factor_lists (T : Type) (one : T)
    (factor_terms : nat -> seq T) n slot iterations : seq (seq T) :=
  match iterations with
  | 0%N => [::]
  | iterations'.+1 =>
      (if masked_grid_diagonalb n slot then [:: one]
       else factor_terms slot) ::
      masked_grid_factor_lists one factor_terms n slot.+1 iterations'
  end.

Section MaskedGridObserver.

Variables T : Type.
Variable R : comSemiRingType.
Variables (one : T) (mul : T -> T -> T).
Variable digit_term : nat -> nat -> T.
Variable factor_terms : nat -> seq T.
Variables n radix : nat.

Variable mul_one_left : forall term, mul one term = term.
Variable mul_one_right : forall term, mul term one = term.
Variable mul_assoc : forall left middle right,
  mul (mul left middle) right = mul left (mul middle right).
Variable factor_observer_sum : forall slot (target : T -> R),
  (slot < n * n)%N ->
  masked_grid_diagonalb n slot = false ->
  \sum_(digit < radix) target (digit_term slot digit) =
  \sum_(term <- factor_terms slot) target term.

(** This is the variable-mask analogue of
    [mixed_radix_cartesian_observer_sum].  Generalizing over the accumulator
    makes its induction match the checked state machine exactly. *)
Lemma masked_grid_acc_observer_sum slot iterations accumulator
    (observe : T -> R) :
  (0 < radix)%N ->
  (slot + iterations <= n * n)%N ->
  \sum_(code < radix ^ masked_grid_offdiag_count n slot iterations)
    observe
      (masked_grid_acc one mul digit_term n radix slot iterations
        code accumulator) =
  \sum_(term <- MRX.cartesian_terms one mul
      (masked_grid_factor_lists one factor_terms n slot iterations))
    observe (mul accumulator term).
Proof.
move=> hradix.
elim: iterations slot accumulator observe =>
    [|iterations ih] slot accumulator observe hbound.
- by rewrite /= expn0 big_ord1 big_seq1 mul_one_right.
- rewrite /=.
  have hslot_lt : (slot + 0 < slot + iterations.+1)%N.
    by rewrite ltn_add2l.
  have hslot0 : (slot + 0 < n * n)%N := leq_trans hslot_lt hbound.
  have hslot : (slot < n * n)%N.
    by move: hslot0; rewrite addn0.
  have htail : (slot.+1 + iterations <= n * n)%N.
    by move: hbound; rewrite addSn addnS.
  case hdiagonal: (masked_grid_diagonalb n slot).
  + rewrite (ih slot.+1 accumulator observe htail).
    rewrite /= cats0 big_map.
    apply: eq_bigr=> term _.
    by rewrite mul_one_left.
  + rewrite expnS.
    rewrite (reindex (@MRX.radix_join radix
      (radix ^ masked_grid_offdiag_count n slot.+1 iterations))) /=;
      last first.
        apply: onW_bij.
        exact: (@MRX.radix_join_bijective radix
          (radix ^ masked_grid_offdiag_count n slot.+1 iterations) hradix).
    rewrite -(@pair_bigA R 0 +%R ('I_radix)
      ('I_(radix ^ masked_grid_offdiag_count n slot.+1 iterations))
      (fun digit rest =>
        observe
          (masked_grid_acc one mul digit_term n radix slot.+1 iterations
            (((rest * radix + digit)%N %/ radix)%N)
            (mul accumulator
              (digit_term slot
                (((rest * radix + digit)%N %% radix)%N)))))) /=.
    under eq_bigr => digit _ do
      under eq_bigr => rest _ do
        rewrite (MRX.radix_join_mod_digit digit rest)
          (MRX.radix_join_div_rest hradix digit rest).
    under eq_bigr => digit _ do
      rewrite (ih slot.+1
        (mul accumulator (digit_term slot digit))
        (fun term => observe term) htail).
    rewrite (@factor_observer_sum slot
      (fun selected =>
        \sum_(tail <- MRX.cartesian_terms one mul
            (masked_grid_factor_lists one factor_terms n slot.+1 iterations))
          observe (mul (mul accumulator selected) tail)) hslot hdiagonal).
    rewrite /= big_flatten big_map.
    apply: eq_bigr=> selected _.
    rewrite big_map.
    apply: eq_bigr=> tail _.
    by rewrite mul_assoc.
Qed.

End MaskedGridObserver.

(* Regrouping a row-major cartesian expansion changes only the
   parenthesization of [mul].  Stating the bridge for an arbitrary observer
   lets the collision proof compare the flat evaluator grid with the nested
   sparse product without asking the intentionally unnormalised polynomial
   representation to be syntactically equal. *)
Section CartesianRowObserver.

Variables T : Type.
Variable R : comSemiRingType.
Variables (one : T) (mul : T -> T -> T).

Variable mul_one_left : forall term, mul one term = term.
Variable mul_assoc : forall left middle right,
  mul (mul left middle) right = mul left (mul middle right).

Lemma cartesian_terms_cat_observer_sum left right (observe : T -> R) :
  \sum_(term <- MRX.cartesian_terms one mul (left ++ right)) observe term =
  \sum_(left_term <- MRX.cartesian_terms one mul left)
    \sum_(right_term <- MRX.cartesian_terms one mul right)
      observe (mul left_term right_term).
Proof.
elim: left observe => [|factor left ih] observe.
- rewrite /= big_seq1.
  apply: eq_bigr=> term _.
  by rewrite mul_one_left.
- rewrite /= !big_flatten !big_map.
  apply: eq_bigr=> selected _.
  rewrite !big_map.
  rewrite (ih (fun tail => observe (mul selected tail))).
  apply: eq_bigr=> left_term _.
  apply: eq_bigr=> right_term _.
  by rewrite -mul_assoc.
Qed.

Lemma cartesian_terms_flatten_observer_sum rows (observe : T -> R) :
  \sum_(term <- MRX.cartesian_terms one mul (flatten rows)) observe term =
  \sum_(term <- MRX.cartesian_terms one mul
      [seq MRX.cartesian_terms one mul row | row <- rows]) observe term.
Proof.
elim: rows observe => [|row rows ih] observe //=.
rewrite (cartesian_terms_cat_observer_sum row (flatten rows) observe)
  !big_flatten !big_map.
apply: eq_bigr=> row_term _.
rewrite big_map.
exact: ih (fun tail => observe (mul row_term tail)).
Qed.

End CartesianRowObserver.

Lemma masked_grid_factor_lists_iota T (one : T)
    (factor_terms : nat -> seq T) n slot iterations :
  masked_grid_factor_lists one factor_terms n slot iterations =
  [seq if masked_grid_diagonalb n position then [:: one]
       else factor_terms position
    | position <- iota slot iterations].
Proof.
elim: iterations slot => [|iterations ih] slot //=.
by rewrite ih.
Qed.

Lemma pair_masked_grid_offdiag_count :
  masked_grid_offdiag_count 15 0 225 = 210%N.
Proof. vm_compute; reflexivity. Qed.

Lemma triple_masked_grid_offdiag_count :
  masked_grid_offdiag_count 10 0 100 = 90%N.
Proof. vm_compute; reflexivity. Qed.

(* --------------------------------------------------------------------- *)
(* Pair/triple factor expansions at one off-diagonal grid slot.          *)

Definition pair_descriptor_polynomial_at x partition :
    SP.sparse_polynomial :=
  nth [::]
    [seq SR.pair_sparse_descriptor_value x p
      | p <- enum SR.pair_partition] partition.

Definition triple_descriptor_polynomial_at x partition :
    SP.sparse_polynomial :=
  nth [::]
    [seq SR.triple_sparse_descriptor_value x p
      | p <- enum SR.triple_partition] partition.

Lemma pair_descriptor_polynomial_atE x partition
    (hpartition : (partition < 15)%N) :
  pair_descriptor_polynomial_at x partition =
  SR.pair_sparse_descriptor_value x (@Ordinal 15 partition hpartition).
Proof.
rewrite /pair_descriptor_polynomial_at
  (nth_map ord0) ?size_enum_ord //.
congr (SR.pair_sparse_descriptor_value x _).
apply: val_inj.
exact: nth_enum_ord hpartition.
Qed.

Lemma triple_descriptor_polynomial_atE x partition
    (hpartition : (partition < 10)%N) :
  triple_descriptor_polynomial_at x partition =
  SR.triple_sparse_descriptor_value x (@Ordinal 10 partition hpartition).
Proof.
rewrite /triple_descriptor_polynomial_at
  (nth_map ord0) ?size_enum_ord //.
congr (SR.triple_sparse_descriptor_value x _).
apply: val_inj.
exact: nth_enum_ord hpartition.
Qed.

Definition pair_collision_digit_term_from x0 x1 left right digit :
    SP.sparse_term :=
  if (digit < 125)%N
  then DS.pair_descriptor_term left digit x0 x1
  else SP.term_neg
    (DS.pair_descriptor_term right (digit - 125) x0 x1).

Definition triple_collision_digit_term_from x0 x1 left right digit :
    SP.sparse_term :=
  if (digit < 81)%N
  then DS.triple_descriptor_term left digit x0 x1
  else SP.term_neg
    (DS.triple_descriptor_term right (digit - 81) x0 x1).

Definition pair_collision_digit_term x0 x1 slot digit : SP.sparse_term :=
  pair_collision_digit_term_from x0 x1
    (slot %/ 15) (slot %% 15) digit.

Definition triple_collision_digit_term x0 x1 slot digit : SP.sparse_term :=
  triple_collision_digit_term_from x0 x1
    (slot %/ 10) (slot %% 10) digit.

Definition pair_collision_factor_terms x0 x1 slot :
    SP.sparse_polynomial :=
  SP.sparse_sub
    (pair_descriptor_polynomial_at [tuple x0; x1] (slot %/ 15))
    (pair_descriptor_polynomial_at [tuple x0; x1] (slot %% 15)).

Definition triple_collision_factor_terms x0 x1 slot :
    SP.sparse_polynomial :=
  SP.sparse_sub
    (triple_descriptor_polynomial_at [tuple x0; x1] (slot %/ 10))
    (triple_descriptor_polynomial_at [tuple x0; x1] (slot %% 10)).

Section DoubleOrdinalSum.

Variable R : comSemiRingType.

Lemma big_ord_double n (left right : nat -> R) :
  \sum_(digit < n + n)
    (if (digit < n)%N then left digit else right (digit - n)%N) =
  \sum_(digit < n) left digit + \sum_(digit < n) right digit.
Proof.
rewrite (reindex (@unsplit n n)) /=;
  last first.
    apply: onW_bij.
    exact: (@Bijective _ _ (@unsplit n n) (@split n n)
      (@unsplitK n n) (@splitK n n)).
rewrite big_sumType.
congr (_ + _); apply: eq_bigr=> digit _.
- by rewrite /unsplit /= ltn_ord.
- rewrite /unsplit /= ltnNge leq_addr addKn.
  reflexivity.
Qed.

End DoubleOrdinalSum.

Lemma pair_collision_factor_observer_sum x0 x1 slot
    (target : SP.sparse_term -> int) :
  (slot < 15 * 15)%N ->
  masked_grid_diagonalb 15 slot = false ->
  \sum_(digit < 250)
    target (pair_collision_digit_term x0 x1 slot digit) =
  \sum_(term <- pair_collision_factor_terms x0 x1 slot) target term.
Proof.
move=> hslot _.
have hleft : (slot %/ 15 < 15)%N.
  by rewrite ltn_divLR //; exact hslot.
have hright : (slot %% 15 < 15)%N by rewrite ltn_mod.
rewrite /pair_collision_digit_term /pair_collision_digit_term_from.
change 250%N with (125 + 125)%N.
under eq_bigr => digit _ do rewrite fun_if.
transitivity
  ((\sum_(digit < 125)
      target (DS.pair_descriptor_term (slot %/ 15) digit x0 x1)) +
   (\sum_(digit < 125)
      target (SP.term_neg
        (DS.pair_descriptor_term (slot %% 15) digit x0 x1)))).
- exact: (@big_ord_double _ 125
    (fun digit =>
      target (DS.pair_descriptor_term (slot %/ 15) digit x0 x1))
    (fun digit =>
      target (SP.term_neg
        (DS.pair_descriptor_term (slot %% 15) digit x0 x1)))).
rewrite (DS.pair_descriptor_observer_sum hleft x0 x1 target).
rewrite (DS.pair_descriptor_observer_sum hright x0 x1
  (fun term => target (SP.term_neg term))).
rewrite /pair_collision_factor_terms /SP.sparse_sub /SP.sparse_add
  /SP.sparse_neg big_cat big_map.
by rewrite !pair_descriptor_polynomial_atE.
Qed.

Lemma triple_collision_factor_observer_sum x0 x1 slot
    (target : SP.sparse_term -> int) :
  (slot < 10 * 10)%N ->
  masked_grid_diagonalb 10 slot = false ->
  \sum_(digit < 162)
    target (triple_collision_digit_term x0 x1 slot digit) =
  \sum_(term <- triple_collision_factor_terms x0 x1 slot) target term.
Proof.
move=> hslot _.
have hleft : (slot %/ 10 < 10)%N.
  by rewrite ltn_divLR //; exact hslot.
have hright : (slot %% 10 < 10)%N by rewrite ltn_mod.
rewrite /triple_collision_digit_term /triple_collision_digit_term_from.
change 162%N with (81 + 81)%N.
under eq_bigr => digit _ do rewrite fun_if.
transitivity
  ((\sum_(digit < 81)
      target (DS.triple_descriptor_term (slot %/ 10) digit x0 x1)) +
   (\sum_(digit < 81)
      target (SP.term_neg
        (DS.triple_descriptor_term (slot %% 10) digit x0 x1)))).
- exact: (@big_ord_double _ 81
    (fun digit =>
      target (DS.triple_descriptor_term (slot %/ 10) digit x0 x1))
    (fun digit =>
      target (SP.term_neg
        (DS.triple_descriptor_term (slot %% 10) digit x0 x1)))).
rewrite (DS.triple_descriptor_observer_sum hleft x0 x1 target).
rewrite (DS.triple_descriptor_observer_sum hright x0 x1
  (fun term => target (SP.term_neg term))).
rewrite /triple_collision_factor_terms /SP.sparse_sub /SP.sparse_add
  /SP.sparse_neg big_cat big_map.
by rewrite !triple_descriptor_polynomial_atE.
Qed.

(* Fixed row-major presentations of the two masked grids. *)
Definition pair_grid_factor x0 x1 slot : SP.sparse_polynomial :=
  if masked_grid_diagonalb 15 slot
  then [:: HS.sparse_term_one]
  else pair_collision_factor_terms x0 x1 slot.

Definition triple_grid_factor x0 x1 slot : SP.sparse_polynomial :=
  if masked_grid_diagonalb 10 slot
  then [:: HS.sparse_term_one]
  else triple_collision_factor_terms x0 x1 slot.

Definition pair_slot_rows : seq (seq nat) :=
  [seq [seq (row_index * 15 + column_index)%N
          | column_index <- iota 0 15]
    | row_index <- iota 0 15].

Definition triple_slot_rows : seq (seq nat) :=
  [seq [seq (row_index * 10 + column_index)%N
          | column_index <- iota 0 10]
    | row_index <- iota 0 10].

Lemma pair_slot_rowsE : flatten pair_slot_rows = iota 0 225.
Proof. vm_compute; reflexivity. Qed.

Lemma triple_slot_rowsE : flatten triple_slot_rows = iota 0 100.
Proof. vm_compute; reflexivity. Qed.

Definition pair_collision_factor_rows x0 x1 :
    seq (seq SP.sparse_polynomial) :=
  [seq
    [seq if row_index == column_index then SP.sparse_const 1 else
      SP.sparse_sub
        (SR.pair_sparse_descriptor_value [tuple x0; x1] row_index)
        (SR.pair_sparse_descriptor_value [tuple x0; x1] column_index)
      | column_index <- enum SR.pair_partition]
    | row_index <- enum SR.pair_partition].

Definition triple_collision_factor_rows x0 x1 :
    seq (seq SP.sparse_polynomial) :=
  [seq
    [seq if row_index == column_index then SP.sparse_const 1 else
      SP.sparse_sub
        (SR.triple_sparse_descriptor_value [tuple x0; x1] row_index)
        (SR.triple_sparse_descriptor_value [tuple x0; x1] column_index)
      | column_index <- enum SR.triple_partition]
    | row_index <- enum SR.triple_partition].

Lemma pair_grid_factorE x0 x1
    (left right : SR.pair_partition) :
  pair_grid_factor x0 x1 (left * 15 + right)%N =
    if left == right then SP.sparse_const 1 else
      SP.sparse_sub
        (SR.pair_sparse_descriptor_value [tuple x0; x1] left)
        (SR.pair_sparse_descriptor_value [tuple x0; x1] right).
Proof.
rewrite /pair_grid_factor /masked_grid_diagonalb
  modnMDl modn_small // divnMDl // divn_small ?addn0 //.
case hequal: (left == right).
- move/eqP: hequal=> ->.
  rewrite Nat.eqb_refl /HS.sparse_term_one /SP.sparse_const.
  reflexivity.
- have hneq : val left <> val right.
    move=> hval.
    have hlr : left = right by exact: val_inj hval.
    by move: hequal; rewrite hlr eqxx.
  have hneqb : Nat.eqb (val left) (val right) = false.
    exact: (Nat.eqb_neq _ _).2 hneq.
  rewrite hneqb /=
    /pair_collision_factor_terms
    divnMDl // divn_small ?addn0 // modnMDl modn_small //.
  rewrite (pair_descriptor_polynomial_atE [tuple x0; x1] (valP left))
    (pair_descriptor_polynomial_atE [tuple x0; x1] (valP right)).
  reflexivity.
Qed.

Lemma triple_grid_factorE x0 x1
    (left right : SR.triple_partition) :
  triple_grid_factor x0 x1 (left * 10 + right)%N =
    if left == right then SP.sparse_const 1 else
      SP.sparse_sub
        (SR.triple_sparse_descriptor_value [tuple x0; x1] left)
        (SR.triple_sparse_descriptor_value [tuple x0; x1] right).
Proof.
rewrite /triple_grid_factor /masked_grid_diagonalb
  modnMDl modn_small // divnMDl // divn_small ?addn0 //.
case hequal: (left == right).
- move/eqP: hequal=> ->.
  rewrite Nat.eqb_refl /HS.sparse_term_one /SP.sparse_const.
  reflexivity.
- have hneq : val left <> val right.
    move=> hval.
    have hlr : left = right by exact: val_inj hval.
    by move: hequal; rewrite hlr eqxx.
  have hneqb : Nat.eqb (val left) (val right) = false.
    exact: (Nat.eqb_neq _ _).2 hneq.
  rewrite hneqb /=
    /triple_collision_factor_terms
    divnMDl // divn_small ?addn0 // modnMDl modn_small //.
  rewrite (triple_descriptor_polynomial_atE [tuple x0; x1] (valP left))
    (triple_descriptor_polynomial_atE [tuple x0; x1] (valP right)).
  reflexivity.
Qed.

Lemma pair_masked_grid_factor_listsE x0 x1 :
  masked_grid_factor_lists HS.sparse_term_one
      (pair_collision_factor_terms x0 x1) 15 0 225 =
    flatten (pair_collision_factor_rows x0 x1).
Proof.
rewrite masked_grid_factor_lists_iota.
change ([seq pair_grid_factor x0 x1 slot | slot <- iota 0 225] =
  flatten (pair_collision_factor_rows x0 x1)).
rewrite -pair_slot_rowsE map_flatten
  /pair_slot_rows /pair_collision_factor_rows -!val_enum_ord -!map_comp.
congr (flatten _).
apply/eq_in_map=> left _.
rewrite /= -!map_comp.
apply/eq_in_map=> right _.
rewrite /=.
exact: pair_grid_factorE.
Qed.

Lemma triple_masked_grid_factor_listsE x0 x1 :
  masked_grid_factor_lists HS.sparse_term_one
      (triple_collision_factor_terms x0 x1) 10 0 100 =
    flatten (triple_collision_factor_rows x0 x1).
Proof.
rewrite masked_grid_factor_lists_iota.
change ([seq triple_grid_factor x0 x1 slot | slot <- iota 0 100] =
  flatten (triple_collision_factor_rows x0 x1)).
rewrite -triple_slot_rowsE map_flatten
  /triple_slot_rows /triple_collision_factor_rows -!val_enum_ord -!map_comp.
congr (flatten _).
apply/eq_in_map=> left _.
rewrite /= -!map_comp.
apply/eq_in_map=> right _.
rewrite /=.
exact: triple_grid_factorE.
Qed.

Lemma pair_descriptor_term_nth partition digit x0 x1 coordinate :
  (coordinate < 6)%N ->
  nth 0%N (DS.pair_descriptor_term partition digit x0 x1).2 coordinate =
  DS.pair_descriptor_exponent_value partition digit coordinate.
Proof.
move=> hcoordinate.
rewrite /DS.pair_descriptor_term /DS.descriptor_sparse_term /=.
pose ordinal : 'I_6 := @Ordinal 6 coordinate hcoordinate.
change
  (nth 0%N
      [tuple DS.pair_descriptor_exponent_value partition digit (val i)
        | i < 6] ordinal =
    DS.pair_descriptor_exponent_value partition digit coordinate).
by rewrite nth_mktuple /ordinal.
Qed.

Lemma triple_descriptor_term_nth partition digit x0 x1 coordinate :
  (coordinate < 6)%N ->
  nth 0%N (DS.triple_descriptor_term partition digit x0 x1).2 coordinate =
  DS.triple_descriptor_exponent_value partition digit coordinate.
Proof.
move=> hcoordinate.
rewrite /DS.triple_descriptor_term /DS.descriptor_sparse_term /=.
pose ordinal : 'I_6 := @Ordinal 6 coordinate hcoordinate.
change
  (nth 0%N
      [tuple DS.triple_descriptor_exponent_value partition digit (val i)
        | i < 6] ordinal =
    DS.triple_descriptor_exponent_value partition digit coordinate).
by rewrite nth_mktuple /ordinal.
Qed.

Lemma eval_pair_collision_factor_coefficient_from {arity}
    (left right digit x0 x1 : SE.recursive_expression arity) values :
  (SE.eval_recursive_expression digit values < 250)%N ->
  CS.eval_mathcomp_recursive_signed_expression
      (CE.pair_collision_factor_coefficient_from
        left right digit x0 x1) values =
  (pair_collision_digit_term_from
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (SE.eval_recursive_expression left values)
    (SE.eval_recursive_expression right values)
    (SE.eval_recursive_expression digit values)).1.
Proof.
move=> hdigit.
rewrite /CE.pair_collision_factor_coefficient_from
  CS.eval_mathcomp_recursive_signed_if_zero
  CS.eval_recursive_minus CS.eval_recursive_const.
case hcutoff: (SE.eval_recursive_expression digit values < 125)%N.
- have hpositive :
      (0 < 125 - SE.eval_recursive_expression digit values)%N.
    by rewrite subn_gt0 hcutoff.
  case hdifference:
      (125 - SE.eval_recursive_expression digit values)%N => [|difference].
  + by rewrite hdifference in hpositive.
  + rewrite /= DS.pair_descriptor_coefficient_from_correct.
    rewrite /pair_collision_digit_term_from hcutoff
      /DS.pair_descriptor_term /DS.descriptor_sparse_term /=.
    reflexivity.
- have hle :
      (125 <= SE.eval_recursive_expression digit values)%N.
    by rewrite leqNgt hcutoff.
  have hzero :
      (125 - SE.eval_recursive_expression digit values)%N = 0%N.
    by apply/eqP; rewrite subn_eq0.
  rewrite hzero /= CS.eval_mathcomp_recursive_signed_negate
    DS.pair_descriptor_coefficient_from_correct.
  rewrite /pair_collision_digit_term_from hcutoff /SP.term_neg
    /DS.pair_descriptor_term /DS.descriptor_sparse_term /=.
  reflexivity.
Qed.

Lemma eval_triple_collision_factor_coefficient_from {arity}
    (left right digit x0 x1 : SE.recursive_expression arity) values :
  (SE.eval_recursive_expression digit values < 162)%N ->
  CS.eval_mathcomp_recursive_signed_expression
      (CE.triple_collision_factor_coefficient_from
        left right digit x0 x1) values =
  (triple_collision_digit_term_from
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    (SE.eval_recursive_expression left values)
    (SE.eval_recursive_expression right values)
    (SE.eval_recursive_expression digit values)).1.
Proof.
move=> hdigit.
rewrite /CE.triple_collision_factor_coefficient_from
  CS.eval_mathcomp_recursive_signed_if_zero
  CS.eval_recursive_minus CS.eval_recursive_const.
case hcutoff: (SE.eval_recursive_expression digit values < 81)%N.
- have hpositive :
      (0 < 81 - SE.eval_recursive_expression digit values)%N.
    by rewrite subn_gt0 hcutoff.
  case hdifference:
      (81 - SE.eval_recursive_expression digit values)%N => [|difference].
  + by rewrite hdifference in hpositive.
  + rewrite /= DS.triple_descriptor_coefficient_from_correct.
    rewrite /triple_collision_digit_term_from hcutoff
      /DS.triple_descriptor_term /DS.descriptor_sparse_term /=.
    reflexivity.
- have hle :
      (81 <= SE.eval_recursive_expression digit values)%N.
    by rewrite leqNgt hcutoff.
  have hzero :
      (81 - SE.eval_recursive_expression digit values)%N = 0%N.
    by apply/eqP; rewrite subn_eq0.
  rewrite hzero /= CS.eval_mathcomp_recursive_signed_negate
    DS.triple_descriptor_coefficient_from_correct.
  rewrite /triple_collision_digit_term_from hcutoff /SP.term_neg
    /DS.triple_descriptor_term /DS.descriptor_sparse_term /=.
  reflexivity.
Qed.

Lemma eval_pair_collision_factor_exponent_from {arity}
    (left right digit : SE.recursive_expression arity)
    x0 x1 coordinate values :
  (coordinate < 6)%N ->
  (SE.eval_recursive_expression digit values < 250)%N ->
  SE.eval_recursive_expression
      (CE.pair_collision_factor_exponent_from
        left right digit coordinate) values =
  nth 0%N
    (pair_collision_digit_term_from x0 x1
      (SE.eval_recursive_expression left values)
      (SE.eval_recursive_expression right values)
      (SE.eval_recursive_expression digit values)).2 coordinate.
Proof.
move=> hcoordinate hdigit.
rewrite /CE.pair_collision_factor_exponent_from
  CS.eval_recursive_if_zero CS.eval_recursive_minus CS.eval_recursive_const.
case hcutoff: (SE.eval_recursive_expression digit values < 125)%N.
- have hpositive :
      (0 < 125 - SE.eval_recursive_expression digit values)%N.
    by rewrite subn_gt0 hcutoff.
  case hdifference:
      (125 - SE.eval_recursive_expression digit values)%N => [|difference].
  + by rewrite hdifference in hpositive.
  + rewrite DS.pair_descriptor_exponent_from_correct.
    rewrite /pair_collision_digit_term_from hcutoff.
    exact: esym (@pair_descriptor_term_nth
      (SE.eval_recursive_expression left values)
      (SE.eval_recursive_expression digit values)
      x0 x1 coordinate hcoordinate).
- have hle :
      (125 <= SE.eval_recursive_expression digit values)%N.
    by rewrite leqNgt hcutoff.
  have hzero :
      (125 - SE.eval_recursive_expression digit values)%N = 0%N.
    by apply/eqP; rewrite subn_eq0.
  rewrite hzero DS.pair_descriptor_exponent_from_correct.
  rewrite /pair_collision_digit_term_from hcutoff /SP.term_neg.
  exact: esym (@pair_descriptor_term_nth
    (SE.eval_recursive_expression right values)
    (SE.eval_recursive_expression digit values - 125)%N
    x0 x1 coordinate hcoordinate).
Qed.

Lemma eval_triple_collision_factor_exponent_from {arity}
    (left right digit : SE.recursive_expression arity)
    x0 x1 coordinate values :
  (coordinate < 6)%N ->
  (SE.eval_recursive_expression digit values < 162)%N ->
  SE.eval_recursive_expression
      (CE.triple_collision_factor_exponent_from
        left right digit coordinate) values =
  nth 0%N
    (triple_collision_digit_term_from x0 x1
      (SE.eval_recursive_expression left values)
      (SE.eval_recursive_expression right values)
      (SE.eval_recursive_expression digit values)).2 coordinate.
Proof.
move=> hcoordinate hdigit.
rewrite /CE.triple_collision_factor_exponent_from
  CS.eval_recursive_if_zero CS.eval_recursive_minus CS.eval_recursive_const.
case hcutoff: (SE.eval_recursive_expression digit values < 81)%N.
- have hpositive :
      (0 < 81 - SE.eval_recursive_expression digit values)%N.
    by rewrite subn_gt0 hcutoff.
  case hdifference:
      (81 - SE.eval_recursive_expression digit values)%N => [|difference].
  + by rewrite hdifference in hpositive.
  + rewrite DS.triple_descriptor_exponent_from_correct.
    rewrite /triple_collision_digit_term_from hcutoff.
    exact: esym (@triple_descriptor_term_nth
      (SE.eval_recursive_expression left values)
      (SE.eval_recursive_expression digit values)
      x0 x1 coordinate hcoordinate).
- have hle :
      (81 <= SE.eval_recursive_expression digit values)%N.
    by rewrite leqNgt hcutoff.
  have hzero :
      (81 - SE.eval_recursive_expression digit values)%N = 0%N.
    by apply/eqP; rewrite subn_eq0.
  rewrite hzero DS.triple_descriptor_exponent_from_correct.
  rewrite /triple_collision_digit_term_from hcutoff /SP.term_neg.
  exact: esym (@triple_descriptor_term_nth
    (SE.eval_recursive_expression right values)
    (SE.eval_recursive_expression digit values - 81)%N
    x0 x1 coordinate hcoordinate).
Qed.

Lemma eval_recursive_equal_distance {arity}
    (left right : SE.recursive_expression arity) values :
  SE.eval_recursive_expression (CE.recursive_equal_distance left right) values =
  ((SE.eval_recursive_expression left values -
      SE.eval_recursive_expression right values) +
    (SE.eval_recursive_expression right values -
      SE.eval_recursive_expression left values))%N.
Proof. reflexivity. Qed.

Lemma equal_distance_eq0 left right :
  ((left - right) + (right - left) = 0)%N <-> left = right.
Proof.
split.
- move=> hsum.
  have hzero : ((left - right) + (right - left) == 0)%N by exact/eqP.
  move: hzero; rewrite addn_eq0 !subn_eq0.
  move/andP=> [hle hge].
  apply/eqP.
  by rewrite eqn_leq hle hge.
- move=> ->.
  by rewrite subnn addn0.
Qed.

Definition pair_masked_grid_term x0 x1 slot iterations code accumulator :=
  masked_grid_acc HS.sparse_term_one SP.term_mul
    (pair_collision_digit_term x0 x1) 15 250 slot iterations code accumulator.

Definition triple_masked_grid_term x0 x1 slot iterations code accumulator :=
  masked_grid_acc HS.sparse_term_one SP.term_mul
    (triple_collision_digit_term x0 x1) 10 162 slot iterations code accumulator.

Definition pair_masked_grid_remaining slot iterations code :=
  masked_grid_remaining 15 250 slot iterations code.

Definition triple_masked_grid_remaining slot iterations code :=
  masked_grid_remaining 10 162 slot iterations code.

(** One-step fusion laws keep the iterator induction from unfolding the
    complete evaluator state.  They are definitionally small: only the
    current diagonal test is inspected. *)
Lemma pair_masked_grid_remaining_succ slot iterations code :
  pair_masked_grid_remaining slot iterations.+1 code =
  pair_masked_grid_remaining slot.+1 iterations
    (pair_masked_grid_remaining slot 1 code).
Proof.
rewrite /pair_masked_grid_remaining /=.
by case: (masked_grid_diagonalb 15 slot).
Qed.

Lemma pair_masked_grid_term_succ x0 x1 slot iterations code accumulator :
  pair_masked_grid_term x0 x1 slot iterations.+1 code accumulator =
  pair_masked_grid_term x0 x1 slot.+1 iterations
    (pair_masked_grid_remaining slot 1 code)
    (pair_masked_grid_term x0 x1 slot 1 code accumulator).
Proof.
rewrite /pair_masked_grid_term /pair_masked_grid_remaining /=.
by case: (masked_grid_diagonalb 15 slot).
Qed.

Lemma triple_masked_grid_remaining_succ slot iterations code :
  triple_masked_grid_remaining slot iterations.+1 code =
  triple_masked_grid_remaining slot.+1 iterations
    (triple_masked_grid_remaining slot 1 code).
Proof.
rewrite /triple_masked_grid_remaining /=.
by case: (masked_grid_diagonalb 10 slot).
Qed.

Lemma triple_masked_grid_term_succ x0 x1 slot iterations code accumulator :
  triple_masked_grid_term x0 x1 slot iterations.+1 code accumulator =
  triple_masked_grid_term x0 x1 slot.+1 iterations
    (triple_masked_grid_remaining slot 1 code)
    (triple_masked_grid_term x0 x1 slot 1 code accumulator).
Proof.
rewrite /triple_masked_grid_term /triple_masked_grid_remaining /=.
by case: (masked_grid_diagonalb 10 slot).
Qed.

Lemma eval_pair_collision_next_coefficient {arity}
    (state x0 x1 : SE.recursive_expression arity)
    values factor remaining term :
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos0 = factor ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos1 = remaining ->
  mathcomp_zigzag_decode
      (vec_pos (project 9 (SE.eval_recursive_expression state values)) pos2) =
    term.1 ->
  mathcomp_zigzag_decode
    (SE.eval_recursive_expression
      (SE.recursive_signed_code
        (SE.recursive_signed_mult
          (SE.recursive_signed_decode (CE.recursive_project9 pos2 state))
          (CE.pair_collision_factor_coefficient_from
            (SE.RecDivSucc (CE.recursive_project9 pos0 state) 14)
            (SE.RecRemSucc (CE.recursive_project9 pos0 state) 14)
            (SE.RecRemSucc (CE.recursive_project9 pos1 state) 249)
            x0 x1))) values) =
  (SP.term_mul term
    (pair_collision_digit_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor (remaining %% 250))).1.
Proof.
move=> hfactor hremaining hterm.
rewrite CS.decode_eval_recursive_signed_code_mathcomp
  CS.eval_mathcomp_recursive_signed_mult
  CS.eval_mathcomp_recursive_signed_decode
  CS.eval_recursive_project9 hterm.
rewrite (@eval_pair_collision_factor_coefficient_from arity
  (SE.RecDivSucc (CE.recursive_project9 pos0 state) 14)
  (SE.RecRemSucc (CE.recursive_project9 pos0 state) 14)
  (SE.RecRemSucc (CE.recursive_project9 pos1 state) 249)
  x0 x1 values).
- rewrite !HS.eval_recursive_div_succ !HS.eval_recursive_rem_succ
    !CS.eval_recursive_project9 hfactor hremaining
    !HS.gcd_div_succ_mathcomp !HS.gcd_rem_succ_mathcomp.
  reflexivity.
- rewrite HS.eval_recursive_rem_succ CS.eval_recursive_project9 hremaining
    HS.gcd_rem_succ_mathcomp.
  exact: ltn_mod.
Qed.

Lemma eval_pair_collision_next_exponent {arity}
    (state x0 x1 : SE.recursive_expression arity) (position : pos 9)
    coordinate values factor remaining (term : SP.sparse_term) :
  (coordinate < 6)%N ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos0 = factor ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos1 = remaining ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) position =
    nth 0%N term.2 coordinate ->
  SE.eval_recursive_expression
    (SE.RecPlus (CE.recursive_project9 position state)
      (CE.pair_collision_factor_exponent_from
        (SE.RecDivSucc (CE.recursive_project9 pos0 state) 14)
        (SE.RecRemSucc (CE.recursive_project9 pos0 state) 14)
        (SE.RecRemSucc (CE.recursive_project9 pos1 state) 249)
        coordinate)) values =
  nth 0%N
    (SP.term_mul term
      (pair_collision_digit_term
        (SE.eval_recursive_expression x0 values)
        (SE.eval_recursive_expression x1 values)
        factor (remaining %% 250))).2
    coordinate.
Proof.
move=> hcoordinate hfactor hremaining hterm.
rewrite HS.eval_recursive_plus CS.eval_recursive_project9 hterm.
rewrite (@eval_pair_collision_factor_exponent_from arity
  (SE.RecDivSucc (CE.recursive_project9 pos0 state) 14)
  (SE.RecRemSucc (CE.recursive_project9 pos0 state) 14)
  (SE.RecRemSucc (CE.recursive_project9 pos1 state) 249)
  (SE.eval_recursive_expression x0 values)
  (SE.eval_recursive_expression x1 values)
  coordinate values hcoordinate).
  - rewrite !HS.eval_recursive_div_succ !HS.eval_recursive_rem_succ
    !CS.eval_recursive_project9 hfactor hremaining
    !HS.gcd_div_succ_mathcomp !HS.gcd_rem_succ_mathcomp.
  exact: esym (@HS.sparse_term_mul_nth term
    (pair_collision_digit_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor (remaining %% 250)) coordinate hcoordinate).
- rewrite HS.eval_recursive_rem_succ CS.eval_recursive_project9 hremaining
    HS.gcd_rem_succ_mathcomp.
  exact: ltn_mod.
Qed.

Lemma eval_pair_collision_state_step_from {arity}
    (state x0 x1 : SE.recursive_expression arity)
    values factor remaining term :
  HS.homogeneous_state_semantics
      (SE.eval_recursive_expression state values) factor remaining term ->
  HS.homogeneous_state_semantics
    (SE.eval_recursive_expression
      (CE.pair_collision_state_step_from state x0 x1) values)
    factor.+1
    (pair_masked_grid_remaining factor 1 remaining)
    (pair_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor 1 remaining term).
Proof.
move=> [hfactor [hremaining [hterm
  [hexponent0 [hexponent1 [hexponent2
  [hexponent3 [hexponent4 hexponent5]]]]]]]].
rewrite /CE.pair_collision_state_step_from CS.eval_recursive_if_zero.
rewrite eval_recursive_equal_distance
  !HS.eval_recursive_div_succ !HS.eval_recursive_rem_succ
  !CS.eval_recursive_project9 hfactor
  !HS.gcd_div_succ_mathcomp !HS.gcd_rem_succ_mathcomp.
case hdistance:
    (((factor %/ 15) - (factor %% 15)) +
      ((factor %% 15) - (factor %/ 15)))%N => [|distance].
- have hequal : (factor %/ 15)%N = (factor %% 15)%N.
    apply equal_distance_eq0.
    exact hdistance.
  have hdiagonal : masked_grid_diagonalb 15 factor = true.
    apply Nat.eqb_eq.
    exact hequal.
  rewrite /pair_masked_grid_remaining /pair_masked_grid_term
    /masked_grid_remaining /masked_grid_acc hdiagonal.
  rewrite /HS.homogeneous_state_semantics CS.eval_recursive_inject9
    !project_inject.
  repeat split.
  + by rewrite HS.eval_recursive_succ CS.eval_recursive_project9 hfactor.
  + exact hremaining.
  + exact hterm.
  + exact hexponent0.
  + exact hexponent1.
  + exact hexponent2.
  + exact hexponent3.
  + exact hexponent4.
  + exact hexponent5.
- have hnequal : (factor %/ 15)%N <> (factor %% 15)%N.
    move=> hequal.
    have hzero :
        (((factor %/ 15) - (factor %% 15)) +
          ((factor %% 15) - (factor %/ 15)) = 0)%N :=
      (proj2 (equal_distance_eq0 _ _) hequal).
    rewrite hzero in hdistance.
    discriminate.
  have hdiagonal : masked_grid_diagonalb 15 factor = false.
    apply Nat.eqb_neq.
    exact hnequal.
  rewrite /pair_masked_grid_remaining /pair_masked_grid_term
    /masked_grid_remaining /masked_grid_acc hdiagonal.
  rewrite /HS.homogeneous_state_semantics CS.eval_recursive_inject9
    !project_inject.
  repeat split.
  + by rewrite HS.eval_recursive_succ CS.eval_recursive_project9 hfactor.
  + rewrite HS.eval_recursive_div_succ CS.eval_recursive_project9 hremaining
      HS.gcd_div_succ_mathcomp.
    reflexivity.
  + exact: eval_pair_collision_next_coefficient hfactor hremaining hterm.
  + exact: (@eval_pair_collision_next_exponent arity state x0 x1 pos3 0
      values factor remaining term erefl hfactor hremaining hexponent0).
  + exact: (@eval_pair_collision_next_exponent arity state x0 x1 pos4 1
      values factor remaining term erefl hfactor hremaining hexponent1).
  + exact: (@eval_pair_collision_next_exponent arity state x0 x1 pos5 2
      values factor remaining term erefl hfactor hremaining hexponent2).
  + exact: (@eval_pair_collision_next_exponent arity state x0 x1 pos6 3
      values factor remaining term erefl hfactor hremaining hexponent3).
  + exact: (@eval_pair_collision_next_exponent arity state x0 x1 pos7 4
      values factor remaining term erefl hfactor hremaining hexponent4).
  + exact: (@eval_pair_collision_next_exponent arity state x0 x1 pos8 5
      values factor remaining term erefl hfactor hremaining hexponent5).
Qed.

Lemma eval_triple_collision_next_coefficient {arity}
    (state x0 x1 : SE.recursive_expression arity)
    values factor remaining term :
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos0 = factor ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos1 = remaining ->
  mathcomp_zigzag_decode
      (vec_pos (project 9 (SE.eval_recursive_expression state values)) pos2) =
    term.1 ->
  mathcomp_zigzag_decode
    (SE.eval_recursive_expression
      (SE.recursive_signed_code
        (SE.recursive_signed_mult
          (SE.recursive_signed_decode (CE.recursive_project9 pos2 state))
          (CE.triple_collision_factor_coefficient_from
            (SE.RecDivSucc (CE.recursive_project9 pos0 state) 9)
            (SE.RecRemSucc (CE.recursive_project9 pos0 state) 9)
            (SE.RecRemSucc (CE.recursive_project9 pos1 state) 161)
            x0 x1))) values) =
  (SP.term_mul term
    (triple_collision_digit_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor (remaining %% 162))).1.
Proof.
move=> hfactor hremaining hterm.
rewrite CS.decode_eval_recursive_signed_code_mathcomp
  CS.eval_mathcomp_recursive_signed_mult
  CS.eval_mathcomp_recursive_signed_decode
  CS.eval_recursive_project9 hterm.
rewrite (@eval_triple_collision_factor_coefficient_from arity
  (SE.RecDivSucc (CE.recursive_project9 pos0 state) 9)
  (SE.RecRemSucc (CE.recursive_project9 pos0 state) 9)
  (SE.RecRemSucc (CE.recursive_project9 pos1 state) 161)
  x0 x1 values).
- rewrite !HS.eval_recursive_div_succ !HS.eval_recursive_rem_succ
    !CS.eval_recursive_project9 hfactor hremaining
    !HS.gcd_div_succ_mathcomp !HS.gcd_rem_succ_mathcomp.
  reflexivity.
- rewrite HS.eval_recursive_rem_succ CS.eval_recursive_project9 hremaining
    HS.gcd_rem_succ_mathcomp.
  exact: ltn_mod.
Qed.

Lemma eval_triple_collision_next_exponent {arity}
    (state x0 x1 : SE.recursive_expression arity) (position : pos 9)
    coordinate values factor remaining (term : SP.sparse_term) :
  (coordinate < 6)%N ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos0 = factor ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) pos1 = remaining ->
  vec_pos (project 9 (SE.eval_recursive_expression state values)) position =
    nth 0%N term.2 coordinate ->
  SE.eval_recursive_expression
    (SE.RecPlus (CE.recursive_project9 position state)
      (CE.triple_collision_factor_exponent_from
        (SE.RecDivSucc (CE.recursive_project9 pos0 state) 9)
        (SE.RecRemSucc (CE.recursive_project9 pos0 state) 9)
        (SE.RecRemSucc (CE.recursive_project9 pos1 state) 161)
        coordinate)) values =
  nth 0%N
    (SP.term_mul term
      (triple_collision_digit_term
        (SE.eval_recursive_expression x0 values)
        (SE.eval_recursive_expression x1 values)
        factor (remaining %% 162))).2
    coordinate.
Proof.
move=> hcoordinate hfactor hremaining hterm.
rewrite HS.eval_recursive_plus CS.eval_recursive_project9 hterm.
rewrite (@eval_triple_collision_factor_exponent_from arity
  (SE.RecDivSucc (CE.recursive_project9 pos0 state) 9)
  (SE.RecRemSucc (CE.recursive_project9 pos0 state) 9)
  (SE.RecRemSucc (CE.recursive_project9 pos1 state) 161)
  (SE.eval_recursive_expression x0 values)
  (SE.eval_recursive_expression x1 values)
  coordinate values hcoordinate).
  - rewrite !HS.eval_recursive_div_succ !HS.eval_recursive_rem_succ
    !CS.eval_recursive_project9 hfactor hremaining
    !HS.gcd_div_succ_mathcomp !HS.gcd_rem_succ_mathcomp.
  exact: esym (@HS.sparse_term_mul_nth term
    (triple_collision_digit_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor (remaining %% 162)) coordinate hcoordinate).
- rewrite HS.eval_recursive_rem_succ CS.eval_recursive_project9 hremaining
    HS.gcd_rem_succ_mathcomp.
  exact: ltn_mod.
Qed.

Lemma eval_triple_collision_state_step_from {arity}
    (state x0 x1 : SE.recursive_expression arity)
    values factor remaining term :
  HS.homogeneous_state_semantics
      (SE.eval_recursive_expression state values) factor remaining term ->
  HS.homogeneous_state_semantics
    (SE.eval_recursive_expression
      (CE.triple_collision_state_step_from state x0 x1) values)
    factor.+1
    (triple_masked_grid_remaining factor 1 remaining)
    (triple_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor 1 remaining term).
Proof.
move=> [hfactor [hremaining [hterm
  [hexponent0 [hexponent1 [hexponent2
  [hexponent3 [hexponent4 hexponent5]]]]]]]].
rewrite /CE.triple_collision_state_step_from CS.eval_recursive_if_zero.
rewrite eval_recursive_equal_distance
  !HS.eval_recursive_div_succ !HS.eval_recursive_rem_succ
  !CS.eval_recursive_project9 hfactor
  !HS.gcd_div_succ_mathcomp !HS.gcd_rem_succ_mathcomp.
case hdistance:
    (((factor %/ 10) - (factor %% 10)) +
      ((factor %% 10) - (factor %/ 10)))%N => [|distance].
- have hequal : (factor %/ 10)%N = (factor %% 10)%N.
    apply equal_distance_eq0.
    exact hdistance.
  have hdiagonal : masked_grid_diagonalb 10 factor = true.
    apply Nat.eqb_eq.
    exact hequal.
  rewrite /triple_masked_grid_remaining /triple_masked_grid_term
    /masked_grid_remaining /masked_grid_acc hdiagonal.
  rewrite /HS.homogeneous_state_semantics CS.eval_recursive_inject9
    !project_inject.
  repeat split.
  + by rewrite HS.eval_recursive_succ CS.eval_recursive_project9 hfactor.
  + exact hremaining.
  + exact hterm.
  + exact hexponent0.
  + exact hexponent1.
  + exact hexponent2.
  + exact hexponent3.
  + exact hexponent4.
  + exact hexponent5.
- have hnequal : (factor %/ 10)%N <> (factor %% 10)%N.
    move=> hequal.
    have hzero :
        (((factor %/ 10) - (factor %% 10)) +
          ((factor %% 10) - (factor %/ 10)) = 0)%N :=
      (proj2 (equal_distance_eq0 _ _) hequal).
    rewrite hzero in hdistance.
    discriminate.
  have hdiagonal : masked_grid_diagonalb 10 factor = false.
    apply Nat.eqb_neq.
    exact hnequal.
  rewrite /triple_masked_grid_remaining /triple_masked_grid_term
    /masked_grid_remaining /masked_grid_acc hdiagonal.
  rewrite /HS.homogeneous_state_semantics CS.eval_recursive_inject9
    !project_inject.
  repeat split.
  + by rewrite HS.eval_recursive_succ CS.eval_recursive_project9 hfactor.
  + rewrite HS.eval_recursive_div_succ CS.eval_recursive_project9 hremaining
      HS.gcd_div_succ_mathcomp.
    reflexivity.
  + exact: eval_triple_collision_next_coefficient hfactor hremaining hterm.
  + exact: (@eval_triple_collision_next_exponent arity state x0 x1 pos3 0
      values factor remaining term erefl hfactor hremaining hexponent0).
  + exact: (@eval_triple_collision_next_exponent arity state x0 x1 pos4 1
      values factor remaining term erefl hfactor hremaining hexponent1).
  + exact: (@eval_triple_collision_next_exponent arity state x0 x1 pos5 2
      values factor remaining term erefl hfactor hremaining hexponent2).
  + exact: (@eval_triple_collision_next_exponent arity state x0 x1 pos6 3
      values factor remaining term erefl hfactor hremaining hexponent3).
  + exact: (@eval_triple_collision_next_exponent arity state x0 x1 pos7 4
      values factor remaining term erefl hfactor hremaining hexponent4).
  + exact: (@eval_triple_collision_next_exponent arity state x0 x1 pos8 5
      values factor remaining term erefl hfactor hremaining hexponent5).
Qed.

(** Normalize the extended-variable one-step theorem once, behind an opaque
    boundary, instead of traversing its large conclusion at every iterator
    induction step. *)
Lemma eval_pair_collision_state_step_weakened_from {arity}
    (x0 x1 : SE.recursive_expression arity) values
    state factor remaining term :
  HS.homogeneous_state_semantics state factor remaining term ->
  HS.homogeneous_state_semantics
    (SE.eval_recursive_expression
      (CE.pair_collision_state_step_from (SE.RecVar pos0)
        (CE.recursive_weaken x0) (CE.recursive_weaken x1))
      (state ## values))
    factor.+1
    (pair_masked_grid_remaining factor 1 remaining)
    (pair_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor 1 remaining term).
Proof.
move=> hstate.
have hstep :=
  (@eval_pair_collision_state_step_from (S arity)
    (SE.RecVar pos0) (CE.recursive_weaken x0)
    (CE.recursive_weaken x1) (state ## values)
    factor remaining term hstate).
move: hstep.
by rewrite !CS.eval_recursive_weaken.
Qed.

Lemma eval_triple_collision_state_step_weakened_from {arity}
    (x0 x1 : SE.recursive_expression arity) values
    state factor remaining term :
  HS.homogeneous_state_semantics state factor remaining term ->
  HS.homogeneous_state_semantics
    (SE.eval_recursive_expression
      (CE.triple_collision_state_step_from (SE.RecVar pos0)
        (CE.recursive_weaken x0) (CE.recursive_weaken x1))
      (state ## values))
    factor.+1
    (triple_masked_grid_remaining factor 1 remaining)
    (triple_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor 1 remaining term).
Proof.
move=> hstate.
have hstep :=
  (@eval_triple_collision_state_step_from (S arity)
    (SE.RecVar pos0) (CE.recursive_weaken x0)
    (CE.recursive_weaken x1) (state ## values)
    factor remaining term hstate).
move: hstep.
by rewrite !CS.eval_recursive_weaken.
Qed.

Lemma iter_succ_add factor iterations :
  prim_min.iter S iterations factor = (factor + iterations)%N.
Proof.
elim: iterations factor => [|iterations ih] factor.
- by rewrite /= addn0.
- rewrite prim_min.iter_S ih.
  by rewrite addSn addnS.
Qed.

Lemma eval_pair_collision_state_iter_raw_from {arity}
    (x0 x1 : SE.recursive_expression arity) values
    iterations state factor remaining term :
  HS.homogeneous_state_semantics state factor remaining term ->
  HS.homogeneous_state_semantics
    (prim_min.iter
      (fun encoded_state =>
        SE.eval_recursive_expression
          (CE.pair_collision_state_step_from (SE.RecVar pos0)
            (CE.recursive_weaken x0) (CE.recursive_weaken x1))
          (encoded_state ## values))
      iterations state)
    (prim_min.iter S iterations factor)
    (pair_masked_grid_remaining factor iterations remaining)
    (pair_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor iterations remaining term).
Proof.
elim: iterations state factor remaining term =>
    [|iterations ih] state factor remaining term hstate.
- by rewrite /= /pair_masked_grid_remaining
    /pair_masked_grid_term /masked_grid_remaining /masked_grid_acc.
- rewrite !prim_min.iter_S.
  have hstep :=
    (@eval_pair_collision_state_step_weakened_from arity x0 x1 values
      state factor remaining term hstate).
  have htail := ih _ _ _ _ hstep.
  rewrite pair_masked_grid_remaining_succ pair_masked_grid_term_succ.
  exact htail.
Qed.

Lemma eval_triple_collision_state_iter_raw_from {arity}
    (x0 x1 : SE.recursive_expression arity) values
    iterations state factor remaining term :
  HS.homogeneous_state_semantics state factor remaining term ->
  HS.homogeneous_state_semantics
    (prim_min.iter
      (fun encoded_state =>
        SE.eval_recursive_expression
          (CE.triple_collision_state_step_from (SE.RecVar pos0)
            (CE.recursive_weaken x0) (CE.recursive_weaken x1))
          (encoded_state ## values))
      iterations state)
    (prim_min.iter S iterations factor)
    (triple_masked_grid_remaining factor iterations remaining)
    (triple_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      factor iterations remaining term).
Proof.
elim: iterations state factor remaining term =>
    [|iterations ih] state factor remaining term hstate.
- by rewrite /= /triple_masked_grid_remaining
    /triple_masked_grid_term /masked_grid_remaining /masked_grid_acc.
- rewrite !prim_min.iter_S.
  have hstep :=
    (@eval_triple_collision_state_step_weakened_from arity x0 x1 values
      state factor remaining term hstate).
  have htail := ih _ _ _ _ hstep.
  rewrite triple_masked_grid_remaining_succ triple_masked_grid_term_succ.
  exact htail.
Qed.

Lemma eval_pair_collision_term_state_from {arity}
    (term_index x0 x1 : SE.recursive_expression arity) values :
  HS.homogeneous_state_semantics
    (SE.eval_recursive_expression
      (CE.pair_collision_term_state_from term_index x0 x1) values)
    225
    (pair_masked_grid_remaining 0 225
      (SE.eval_recursive_expression term_index values))
    (pair_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      0 225 (SE.eval_recursive_expression term_index values)
      HS.sparse_term_one).
Proof.
rewrite /CE.pair_collision_term_state_from CS.eval_recursive_iter
  CS.eval_recursive_inject9 CS.eval_recursive_signed_code_mathcomp
  /CE.recursive_signed_one CS.eval_mathcomp_recursive_signed_nat.
have hinitial :=
  HS.homogeneous_state_initial (SE.eval_recursive_expression term_index values).
have hiter :=
  (@eval_pair_collision_state_iter_raw_from arity x0 x1 values 225
    (inject
      (0 ## SE.eval_recursive_expression term_index values ##
       mathcomp_zigzag_encode 1 ##
       0 ## 0 ## 0 ## 0 ## 0 ## 0 ## vec_nil))
    0 (SE.eval_recursive_expression term_index values)
    HS.sparse_term_one hinitial).
move: hiter.
by rewrite iter_succ_add add0n.
Qed.

Lemma eval_triple_collision_term_state_from {arity}
    (term_index x0 x1 : SE.recursive_expression arity) values :
  HS.homogeneous_state_semantics
    (SE.eval_recursive_expression
      (CE.triple_collision_term_state_from term_index x0 x1) values)
    100
    (triple_masked_grid_remaining 0 100
      (SE.eval_recursive_expression term_index values))
    (triple_masked_grid_term
      (SE.eval_recursive_expression x0 values)
      (SE.eval_recursive_expression x1 values)
      0 100 (SE.eval_recursive_expression term_index values)
      HS.sparse_term_one).
Proof.
rewrite /CE.triple_collision_term_state_from CS.eval_recursive_iter
  CS.eval_recursive_inject9 CS.eval_recursive_signed_code_mathcomp
  /CE.recursive_signed_one CS.eval_mathcomp_recursive_signed_nat.
have hinitial :=
  HS.homogeneous_state_initial (SE.eval_recursive_expression term_index values).
have hiter :=
  (@eval_triple_collision_state_iter_raw_from arity x0 x1 values 100
    (inject
      (0 ## SE.eval_recursive_expression term_index values ##
       mathcomp_zigzag_encode 1 ##
       0 ## 0 ## 0 ## 0 ## 0 ## 0 ## vec_nil))
    0 (SE.eval_recursive_expression term_index values)
    HS.sparse_term_one hinitial).
move: hiter.
by rewrite iter_succ_add add0n.
Qed.

Lemma eval_pair_collision_term_code_from {arity}
    (term_index x0 x1 : SE.recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  CS.eval_mathcomp_recursive_signed_expression
    (SE.recursive_signed_decode
      (CE.pair_collision_term_code_from term_index x0 x1
        e1 e2 e3 e4 e5 e6)) values =
  let term := pair_masked_grid_term
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    0 225 (SE.eval_recursive_expression term_index values)
    HS.sparse_term_one in
  term.1 *
    NPS.sparse_eval_ring
      (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      (NPS.newton_mobius_orbit term.2).
Proof.
set state_expression :=
  CE.pair_collision_term_state_from term_index x0 x1.
set state := SE.eval_recursive_expression state_expression values.
set term := pair_masked_grid_term
  (SE.eval_recursive_expression x0 values)
  (SE.eval_recursive_expression x1 values)
  0 225 (SE.eval_recursive_expression term_index values)
  HS.sparse_term_one.
have hstate : HS.homogeneous_state_semantics state 225
    (pair_masked_grid_remaining 0 225
      (SE.eval_recursive_expression term_index values)) term.
  rewrite /state /state_expression /term.
  exact: eval_pair_collision_term_state_from.
have hstate_copy := hstate.
move: hstate=> [_ [_ [hterm _]]].
have hterm_exponent :=
  HS.homogeneous_state_recursive_sparse_exponent values hstate_copy.
rewrite CS.eval_mathcomp_recursive_signed_decode
  /CE.pair_collision_term_code_from HS.eval_recursive_iter_one -/state.
rewrite CS.decode_eval_recursive_signed_code_mathcomp
  CS.eval_mathcomp_recursive_signed_mult
  CS.eval_mathcomp_recursive_signed_decode
  CS.eval_recursive_project9 hterm.
rewrite CS.eval_recursive_newton_mobius_from
  CS.recursive_elementary_values_weakened hterm_exponent.
reflexivity.
Qed.

Lemma eval_triple_collision_term_code_from {arity}
    (term_index x0 x1 : SE.recursive_expression arity)
    (e1 e2 e3 e4 e5 e6 : SE.recursive_signed_expression arity) values :
  CS.eval_mathcomp_recursive_signed_expression
    (SE.recursive_signed_decode
      (CE.triple_collision_term_code_from term_index x0 x1
        e1 e2 e3 e4 e5 e6)) values =
  let term := triple_masked_grid_term
    (SE.eval_recursive_expression x0 values)
    (SE.eval_recursive_expression x1 values)
    0 100 (SE.eval_recursive_expression term_index values)
    HS.sparse_term_one in
  term.1 *
    NPS.sparse_eval_ring
      (CS.recursive_elementary_values e1 e2 e3 e4 e5 e6 values)
      (NPS.newton_mobius_orbit term.2).
Proof.
set state_expression :=
  CE.triple_collision_term_state_from term_index x0 x1.
set state := SE.eval_recursive_expression state_expression values.
set term := triple_masked_grid_term
  (SE.eval_recursive_expression x0 values)
  (SE.eval_recursive_expression x1 values)
  0 100 (SE.eval_recursive_expression term_index values)
  HS.sparse_term_one.
have hstate : HS.homogeneous_state_semantics state 100
    (triple_masked_grid_remaining 0 100
      (SE.eval_recursive_expression term_index values)) term.
  rewrite /state /state_expression /term.
  exact: eval_triple_collision_term_state_from.
have hstate_copy := hstate.
move: hstate=> [_ [_ [hterm _]]].
have hterm_exponent :=
  HS.homogeneous_state_recursive_sparse_exponent values hstate_copy.
rewrite CS.eval_mathcomp_recursive_signed_decode
  /CE.triple_collision_term_code_from HS.eval_recursive_iter_one -/state.
rewrite CS.decode_eval_recursive_signed_code_mathcomp
  CS.eval_mathcomp_recursive_signed_mult
  CS.eval_mathcomp_recursive_signed_decode
  CS.eval_recursive_project9 hterm.
rewrite CS.eval_recursive_newton_mobius_from
  CS.recursive_elementary_values_weakened hterm_exponent.
reflexivity.
Qed.

Lemma iter_mult_pow (base count : nat) :
  prim_min.iter (fun state => (state * base)%N) count 1 = (base ^ count)%N.
Proof.
elim: count=> [|count ih] //=.
by rewrite ih expnS mulnC.
Qed.

Lemma eval_pair_collision_term_count_from {arity}
    (values : Vector.t nat arity) :
  SE.eval_recursive_expression (@CE.pair_collision_term_count_from arity)
    values = (250 ^ 210)%N.
Proof.
rewrite /CE.pair_collision_term_count_from CS.eval_recursive_iter.
change (prim_min.iter (fun state => (state * 250)%N) 210 1 =
  (250 ^ 210)%N).
exact (iter_mult_pow 250 210).
Qed.

Lemma eval_triple_collision_term_count_from {arity}
    (values : Vector.t nat arity) :
  SE.eval_recursive_expression (@CE.triple_collision_term_count_from arity)
    values = (162 ^ 90)%N.
Proof.
rewrite /CE.triple_collision_term_count_from CS.eval_recursive_iter.
change (prim_min.iter (fun state => (state * 162)%N) 90 1 =
  (162 ^ 90)%N).
exact (iter_mult_pow 162 90).
Qed.

Definition collision_recursive_elementary_values (values : Vector.t nat 8) :=
  CS.recursive_elementary_values
    (SE.recursive_signed_negate (SE.recursive_signed_input pos5))
    (SE.recursive_signed_input pos4)
    (SE.recursive_signed_negate (SE.recursive_signed_input pos3))
    (SE.recursive_signed_input pos2)
    (SE.recursive_signed_negate (SE.recursive_signed_input pos1))
    (SE.recursive_signed_input pos0) values.

Lemma eval_pair_scaled_collision_signed_expression values :
  CS.eval_mathcomp_recursive_signed_expression
      CE.pair_scaled_collision_signed_expression values =
  \sum_(code < (250 ^ 210)%N)
    let term := pair_masked_grid_term
      (vec_pos values pos6) (vec_pos values pos7)
      0 225 code HS.sparse_term_one in
    term.1 *
      NPS.sparse_eval_ring (collision_recursive_elementary_values values)
        (NPS.newton_mobius_orbit term.2).
Proof.
rewrite /CE.pair_scaled_collision_signed_expression
  CS.eval_mathcomp_recursive_signed_bounded_sum
  eval_pair_collision_term_count_from HS.big_sum_list_an_ord.
apply: eq_bigr=> code _.
rewrite (@eval_pair_collision_term_code_from 9
  (SE.RecVar pos0) (SE.RecVar pos7) (SE.RecVar pos8)
  (SE.recursive_signed_negate (SE.recursive_signed_input pos6))
  (SE.recursive_signed_input pos5)
  (SE.recursive_signed_negate (SE.recursive_signed_input pos4))
  (SE.recursive_signed_input pos3)
  (SE.recursive_signed_negate (SE.recursive_signed_input pos2))
  (SE.recursive_signed_input pos1) (val code ## values)).
reflexivity.
Qed.

Lemma eval_triple_scaled_collision_signed_expression values :
  CS.eval_mathcomp_recursive_signed_expression
      CE.triple_scaled_collision_signed_expression values =
  \sum_(code < (162 ^ 90)%N)
    let term := triple_masked_grid_term
      (vec_pos values pos6) (vec_pos values pos7)
      0 100 code HS.sparse_term_one in
    term.1 *
      NPS.sparse_eval_ring (collision_recursive_elementary_values values)
        (NPS.newton_mobius_orbit term.2).
Proof.
rewrite /CE.triple_scaled_collision_signed_expression
  CS.eval_mathcomp_recursive_signed_bounded_sum
  eval_triple_collision_term_count_from HS.big_sum_list_an_ord.
apply: eq_bigr=> code _.
rewrite (@eval_triple_collision_term_code_from 9
  (SE.RecVar pos0) (SE.RecVar pos7) (SE.RecVar pos8)
  (SE.recursive_signed_negate (SE.recursive_signed_input pos6))
  (SE.recursive_signed_input pos5)
  (SE.recursive_signed_negate (SE.recursive_signed_input pos4))
  (SE.recursive_signed_input pos3)
  (SE.recursive_signed_negate (SE.recursive_signed_input pos2))
  (SE.recursive_signed_input pos1) (val code ## values)).
reflexivity.
Qed.

Definition pair_flat_collision_polynomial x0 x1 : SP.sparse_polynomial :=
  SP.sparse_product
    (masked_grid_factor_lists HS.sparse_term_one
      (pair_collision_factor_terms x0 x1) 15 0 225).

Definition triple_flat_collision_polynomial x0 x1 : SP.sparse_polynomial :=
  SP.sparse_product
    (masked_grid_factor_lists HS.sparse_term_one
      (triple_collision_factor_terms x0 x1) 10 0 100).

Lemma sparse_term_mul_assoc_forward
    (left middle right : SP.sparse_term) :
  SP.term_mul (SP.term_mul left middle) right =
    SP.term_mul left (SP.term_mul middle right).
Proof.
exact (esym (HS.sparse_term_mul_assoc left middle right)).
Qed.

Lemma eval_pair_scaled_collision_flat values :
  CS.eval_mathcomp_recursive_signed_expression
      CE.pair_scaled_collision_signed_expression values =
  NPS.sparse_eval_ring (collision_recursive_elementary_values values)
    (NPS.newton_symmetrize
      (pair_flat_collision_polynomial
        (vec_pos values pos6) (vec_pos values pos7))).
Proof.
rewrite eval_pair_scaled_collision_signed_expression
  -pair_masked_grid_offdiag_count /pair_masked_grid_term.
rewrite (@masked_grid_acc_observer_sum
  SP.sparse_term int HS.sparse_term_one SP.term_mul
  (pair_collision_digit_term (vec_pos values pos6) (vec_pos values pos7))
  (pair_collision_factor_terms (vec_pos values pos6) (vec_pos values pos7))
  15 250
  HS.sparse_term_mul1_left HS.sparse_term_mul1_right
  sparse_term_mul_assoc_forward
  (pair_collision_factor_observer_sum
    (vec_pos values pos6) (vec_pos values pos7))
  0 225 HS.sparse_term_one
  (fun term =>
    term.1 *
      NPS.sparse_eval_ring (collision_recursive_elementary_values values)
        (NPS.newton_mobius_orbit term.2))) //.
- under eq_bigr do rewrite HS.sparse_term_mul1_left.
  rewrite HS.cartesian_terms_sparse_product
    /pair_flat_collision_polynomial.
  exact: HS.newton_symmetrize_observer_sum.
Qed.

Lemma eval_triple_scaled_collision_flat values :
  CS.eval_mathcomp_recursive_signed_expression
      CE.triple_scaled_collision_signed_expression values =
  NPS.sparse_eval_ring (collision_recursive_elementary_values values)
    (NPS.newton_symmetrize
      (triple_flat_collision_polynomial
        (vec_pos values pos6) (vec_pos values pos7))).
Proof.
rewrite eval_triple_scaled_collision_signed_expression
  -triple_masked_grid_offdiag_count /triple_masked_grid_term.
rewrite (@masked_grid_acc_observer_sum
  SP.sparse_term int HS.sparse_term_one SP.term_mul
  (triple_collision_digit_term (vec_pos values pos6) (vec_pos values pos7))
  (triple_collision_factor_terms (vec_pos values pos6) (vec_pos values pos7))
  10 162
  HS.sparse_term_mul1_left HS.sparse_term_mul1_right
  sparse_term_mul_assoc_forward
  (triple_collision_factor_observer_sum
    (vec_pos values pos6) (vec_pos values pos7))
  0 100 HS.sparse_term_one
  (fun term =>
    term.1 *
      NPS.sparse_eval_ring (collision_recursive_elementary_values values)
        (NPS.newton_mobius_orbit term.2))) //.
- under eq_bigr do rewrite HS.sparse_term_mul1_left.
  rewrite HS.cartesian_terms_sparse_product
    /triple_flat_collision_polynomial.
  exact: HS.newton_symmetrize_observer_sum.
Qed.

Lemma sparse_product_flatten_newton_eval
    (elementary : 6.-tuple int) rows :
  NPS.sparse_eval_ring elementary
      (NPS.newton_symmetrize (SP.sparse_product (flatten rows))) =
  NPS.sparse_eval_ring elementary
      (NPS.newton_symmetrize
        (SP.sparse_product [seq SP.sparse_product row | row <- rows])).
Proof.
rewrite -(HS.newton_symmetrize_observer_sum elementary
    (SP.sparse_product (flatten rows)))
  -(HS.newton_symmetrize_observer_sum elementary
    (SP.sparse_product [seq SP.sparse_product row | row <- rows]))
  -(HS.cartesian_terms_sparse_product (flatten rows))
  -(HS.cartesian_terms_sparse_product
    [seq SP.sparse_product row | row <- rows]).
have hrows :
    [seq SP.sparse_product row | row <- rows] =
    [seq MRX.cartesian_terms HS.sparse_term_one SP.term_mul row
      | row <- rows].
  apply/eq_in_map=> row _.
  exact: esym (HS.cartesian_terms_sparse_product row).
rewrite hrows.
apply: (@cartesian_terms_flatten_observer_sum
  SP.sparse_term int HS.sparse_term_one SP.term_mul).
- exact: HS.sparse_term_mul1_left.
- move=> left middle right.
  exact: sparse_term_mul_assoc_forward.
Qed.

Lemma eval_pair_scaled_collision_projected f index :
  CS.eval_mathcomp_recursive_signed_expression
      CE.pair_scaled_collision_signed_expression
      (RS.projected_core_values f index) =
    SS.pair_scaled_collision_value f (MSI.projected_parameter index).
Proof.
rewrite eval_pair_scaled_collision_flat
  /collision_recursive_elementary_values
  RS.projected_core_recursive_elementary_values
  /pair_flat_collision_polynomial pair_masked_grid_factor_listsE
  sparse_product_flatten_newton_eval.
have hparameter := RS.projected_core_recursive_parameter_values f index.
change
  ([tuple
    vec_pos (RS.projected_core_values f index) pos6;
    vec_pos (RS.projected_core_values f index) pos7] =
  MSI.projected_parameter index) in hparameter.
rewrite /pair_collision_factor_rows hparameter
  /SS.pair_scaled_collision_value /CR.scaled_symmetric_value
  /SS.pair_sparse_collision.
rewrite -map_comp.
reflexivity.
Qed.

Lemma eval_triple_scaled_collision_projected f index :
  CS.eval_mathcomp_recursive_signed_expression
      CE.triple_scaled_collision_signed_expression
      (RS.projected_core_values f index) =
    SS.triple_scaled_collision_value f (MSI.projected_parameter index).
Proof.
rewrite eval_triple_scaled_collision_flat
  /collision_recursive_elementary_values
  RS.projected_core_recursive_elementary_values
  /triple_flat_collision_polynomial triple_masked_grid_factor_listsE
  sparse_product_flatten_newton_eval.
have hparameter := RS.projected_core_recursive_parameter_values f index.
change
  ([tuple
    vec_pos (RS.projected_core_values f index) pos6;
    vec_pos (RS.projected_core_values f index) pos7] =
  MSI.projected_parameter index) in hparameter.
rewrite /triple_collision_factor_rows hparameter
  /SS.triple_scaled_collision_value /CR.scaled_symmetric_value
  /SS.triple_sparse_collision.
rewrite -map_comp.
reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* A normalized signed code is nonzero exactly when its integer is.      *)

Lemma zigzag_collision_indicatorE value :
  Nat.eqb (ite_rel (mathcomp_zigzag_encode value) 0 1) 1 =
  (value != 0).
Proof.
case: value=> magnitude; case: magnitude=> //=.
Qed.

(* --------------------------------------------------------------------- *)
(* Raw signed-value semantics imply the projected Boolean contracts.     *)

Lemma pair_collision_projected_core_from f index
    (hvalue :
      CS.eval_mathcomp_recursive_signed_expression
          CE.pair_scaled_collision_signed_expression
          (RS.projected_core_values f index) =
        SS.pair_scaled_collision_value f (MSI.projected_parameter index)) :
  CC.pair_collision_core (RS.projected_core_values f index) =
  MSI.pair_projected_collisionb f index.
Proof.
rewrite /CC.pair_collision_core /CE.encoded_pair_collision_test
  /CE.encoded_pair_scaled_collision_value
  /CE.pair_scaled_collision_code_expression
  CS.eval_recursive_signed_code_mathcomp hvalue
  /MSI.pair_projected_collisionb /SS.pair_separatesb.
exact: zigzag_collision_indicatorE.
Qed.

Lemma triple_collision_projected_core_from f index
    (hvalue :
      CS.eval_mathcomp_recursive_signed_expression
          CE.triple_scaled_collision_signed_expression
          (RS.projected_core_values f index) =
        SS.triple_scaled_collision_value f (MSI.projected_parameter index)) :
  CC.triple_collision_core (RS.projected_core_values f index) =
  MSI.triple_projected_collisionb f index.
Proof.
rewrite /CC.triple_collision_core /CE.encoded_triple_collision_test
  /CE.encoded_triple_scaled_collision_value
  /CE.triple_scaled_collision_code_expression
  CS.eval_recursive_signed_code_mathcomp hvalue
  /MSI.triple_projected_collisionb /SS.triple_separatesb.
exact: zigzag_collision_indicatorE.
Qed.

Theorem encoded_pair_collision_core_exact_from
    (hvalue : forall f index,
      CS.eval_mathcomp_recursive_signed_expression
          CE.pair_scaled_collision_signed_expression
          (RS.projected_core_values f index) =
        SS.pair_scaled_collision_value f (MSI.projected_parameter index)) :
  IA.pair_collision_core_exact CC.pair_collision_core.
Proof.
move=> f index _.
change
  (CC.pair_collision_core (RS.projected_core_values f index) =
    MSI.pair_projected_collisionb f index).
exact: pair_collision_projected_core_from.
Qed.

Theorem encoded_triple_collision_core_exact_from
    (hvalue : forall f index,
      CS.eval_mathcomp_recursive_signed_expression
          CE.triple_scaled_collision_signed_expression
          (RS.projected_core_values f index) =
        SS.triple_scaled_collision_value f (MSI.projected_parameter index)) :
  IA.triple_collision_core_exact CC.triple_collision_core.
Proof.
move=> f index _.
change
  (CC.triple_collision_core (RS.projected_core_values f index) =
    MSI.triple_projected_collisionb f index).
exact: triple_collision_projected_core_from.
Qed.

Theorem encoded_pair_collision_core_exact :
  IA.pair_collision_core_exact CC.pair_collision_core.
Proof.
exact: encoded_pair_collision_core_exact_from
  eval_pair_scaled_collision_projected.
Qed.

Theorem encoded_triple_collision_core_exact :
  IA.triple_collision_core_exact CC.triple_collision_core.
Proof.
exact: encoded_triple_collision_core_exact_from
  eval_triple_scaled_collision_projected.
Qed.

(* --------------------------------------------------------------------- *)
(* The direct homogeneous semantics close both rational-root contracts.  *)

Theorem encoded_pair_resolvent_root_core_exact :
  IA.pair_root_core_exact CC.pair_root_core.
Proof.
unfold CC.pair_root_core.
exact: RS.pair_resolvent_root_core_exact_from
  HS.eval_pair_scaled_homogeneous_from.
Qed.

Theorem encoded_triple_resolvent_root_core_exact :
  IA.triple_root_core_exact CC.triple_root_core.
Proof.
unfold CC.triple_root_core.
exact: RS.triple_resolvent_root_core_exact_from
  HS.eval_triple_scaled_homogeneous_from.
Qed.

(* Once the two collision value equalities are instantiated, this is the *)
(* complete parameter-free semantic package consumed by the final core.  *)
Definition verified_core_semantic_exactness_from
    (hpair : IA.pair_collision_core_exact CC.pair_collision_core)
    (htriple : IA.triple_collision_core_exact CC.triple_collision_core) :
    CC.core_semantic_exactness :=
  {| CC.pair_collision_exact := hpair;
     CC.pair_root_exact := encoded_pair_resolvent_root_core_exact;
     CC.triple_collision_exact := htriple;
     CC.triple_root_exact := encoded_triple_resolvent_root_core_exact |}.

Definition verified_core_semantic_exactness : CC.core_semantic_exactness :=
  verified_core_semantic_exactness_from
    encoded_pair_collision_core_exact
    encoded_triple_collision_core_exact.

End PolynomialFormulasSexticMuRecCoreExactness.
