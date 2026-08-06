(**
  Constructive arithmetic graphs for the typed [arith_code] language.

  The compiler is parameterized by an output term and a finite family of
  argument terms.  This makes substitution structural: clients can use the
  same graph under binders, with finite free variables, or as a semisentence
  without proving a separate substitution theorem for each presentation.

  Composition existentially binds all intermediate values.  Minimization
  states that the proposed result makes the underlying computation zero and
  that every smaller candidate terminates with a nonzero value.  No semantic
  correctness result is asserted in this file.
*)

From Stdlib Require Import Vectors.Fin.
From FoundationModal Require Import GenericLogicSymbol.
From Foundation.Vorspiel Require Import Arithmetic Matrix.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc Syntax Hierarchy.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Lift the retained bound variables to the right of a freshly introduced
    block of [fresh] variables. *)
Definition r0_code_graph_lift_term {X q} (fresh : nat)
    (t : semiterm oring_language X q) :
    semiterm oring_language X (fresh + q) :=
  rew_apply (rew_map (Fin.R fresh) (fun x => x)) t.

Definition r0_code_graph_shift_term {X q}
    (t : semiterm oring_language X q) :
    semiterm oring_language X (S q) :=
  rew_apply rew_bshift t.

Definition r0_code_graph_shift2_term {X q}
    (t : semiterm oring_language X q) :
    semiterm oring_language X (S (S q)) :=
  r0_code_graph_shift_term (r0_code_graph_shift_term t).

Definition r0_code_graph_neq {X q}
    (t u : semiterm oring_language X q) :
    semiformula oring_language X q :=
  @Semiformula_nrel oring_language X q 2 ORing_eq (fin_two t u).

Definition r0_code_graph_nlt {X q}
    (t u : semiterm oring_language X q) :
    semiformula oring_language X q :=
  @Semiformula_nrel oring_language X q 2 ORing_lt (fin_two t u).

(** The source compiler [codeAux], generalized from variables to arbitrary
    terms.  The output term is separate from the [n] input terms. *)
Fixpoint r0_arith_code_graph (n : nat) (c : arith_code n) :
    forall (X : Type) (q : nat),
      semiterm oring_language X q ->
      (Fin.t n -> semiterm oring_language X q) ->
      semiformula oring_language X q :=
  match c as c0 in arith_code n0 return
      forall (X : Type) (q : nat),
        semiterm oring_language X q ->
        (Fin.t n0 -> semiterm oring_language X q) ->
        semiformula oring_language X q with
  | arith_code_zero _ => fun X q out _ =>
      arithmetic_eq_formula out arithmetic_zero_term
  | arith_code_one _ => fun X q out _ =>
      arithmetic_eq_formula out arithmetic_one_term
  | @arith_code_add _ i j => fun X q out args =>
      arithmetic_eq_formula out
        (arithmetic_add_term (args i) (args j))
  | @arith_code_mul _ i j => fun X q out args =>
      arithmetic_eq_formula out
        (arithmetic_mul_term (args i) (args j))
  | @arith_code_proj _ i => fun X q out args =>
      arithmetic_eq_formula out (args i)
  | @arith_code_equal _ i j => fun X q out args =>
      Semiformula_or
        (Semiformula_and
          (arithmetic_eq_formula (args i) (args j))
          (arithmetic_eq_formula out arithmetic_one_term))
        (Semiformula_and
          (r0_code_graph_neq (args i) (args j))
          (arithmetic_eq_formula out arithmetic_zero_term))
  | @arith_code_lt _ i j => fun X q out args =>
      Semiformula_or
        (Semiformula_and
          (arithmetic_lt_formula (args i) (args j))
          (arithmetic_eq_formula out arithmetic_one_term))
        (Semiformula_and
          (r0_code_graph_nlt (args i) (args j))
          (arithmetic_eq_formula out arithmetic_zero_term))
  | @arith_code_comp m k outer inner => fun X q out args =>
      first_exists_iter
        (semiformula_existential_quantifier oring_language X) k q
        (Semiformula_and
          (@r0_arith_code_graph k outer X (k + q)
            (r0_code_graph_lift_term k out)
            (fun i => Semiterm_bvar (Fin.L q i)))
          (generic_matrix_conj
            (semiformula_connectives oring_language X (k + q)) k
            (fun i =>
              @r0_arith_code_graph m (inner i) X (k + q)
                (Semiterm_bvar (Fin.L q i))
                (fun j => r0_code_graph_lift_term k (args j)))))
  | @arith_code_find k body => fun X q out args =>
      Semiformula_and
        (@r0_arith_code_graph (S k) body X q arithmetic_zero_term
          (matrix_vec_cons out args))
        (semiformula_ball_lt arithmetic_lt_operator out
          (Semiformula_exists
            (Semiformula_and
              (r0_code_graph_neq
                (@Semiterm_bvar oring_language X (S (S q)) Fin.F1)
                arithmetic_zero_term)
              (@r0_arith_code_graph (S k) body X (S (S q))
                (@Semiterm_bvar oring_language X (S (S q)) Fin.F1)
                (matrix_vec_cons
                  (@Semiterm_bvar oring_language X (S (S q))
                    (Fin.FS Fin.F1))
                  (fun i => r0_code_graph_shift2_term (args i)))))))
  end.

Arguments r0_arith_code_graph {n} c {X q} out args.

(** A canonical graph with the variable order [output, arguments]. *)
Definition r0_arith_code_graph_open {n} (c : arith_code n) :
    semiformula oring_language (Fin.t (S n)) 0 :=
  r0_arith_code_graph c
    (@Semiterm_fvar oring_language (Fin.t (S n)) 0 Fin.F1)
    (fun i =>
      @Semiterm_fvar oring_language (Fin.t (S n)) 0 (Fin.FS i)).

(** The same canonical graph as a semisentence, again ordered
    [output, arguments]. *)
Definition r0_arith_code_graph_semisentence {n} (c : arith_code n) :
    arithmetic_semisentence (S n) :=
  r0_arith_code_graph c
    (@Semiterm_bvar oring_language Empty_set (S n) Fin.F1)
    (fun i =>
      @Semiterm_bvar oring_language Empty_set (S n) (Fin.FS i)).

(** Every generated graph is Sigma-one, uniformly in the chosen terms. *)
Theorem r0_arith_code_graph_sigma_one : forall n (c : arith_code n)
    X q (out : semiterm oring_language X q)
    (args : Fin.t n -> semiterm oring_language X q),
  arithmetic_hierarchy X arithmetic_sigma 1 q
    (r0_arith_code_graph c out args).
Proof.
  intros n c.
  induction c; intros X q out args; simpl.
  - apply arithmetic_hierarchy_eq.
  - apply arithmetic_hierarchy_eq.
  - apply arithmetic_hierarchy_eq.
  - apply arithmetic_hierarchy_eq.
  - apply arithmetic_hierarchy_eq.
  - apply AH_or; apply AH_and.
    + apply arithmetic_hierarchy_eq.
    + apply arithmetic_hierarchy_eq.
    + apply AH_nrel.
    + apply arithmetic_hierarchy_eq.
  - apply AH_or; apply AH_and.
    + apply arithmetic_hierarchy_lt.
    + apply arithmetic_hierarchy_eq.
    + apply AH_nrel.
    + apply arithmetic_hierarchy_eq.
  - apply (proj2 (@arithmetic_hierarchy_exists_iter_iff
      X 0 n q _)).
    apply AH_and.
    + apply IHc.
    + apply (proj2 (@arithmetic_hierarchy_matrix_conj_iff
        X arithmetic_sigma 1 (n + q) n _)).
      intro i. apply H.
  - apply AH_and.
    + apply IHc.
    + apply (proj2 (@arithmetic_hierarchy_ball_lt_iff
        X arithmetic_sigma 1 q out _)).
      apply AH_exists. apply AH_and.
      * apply AH_nrel.
      * apply IHc.
Qed.

Corollary r0_arith_code_graph_open_sigma_one : forall n
    (c : arith_code n),
  arithmetic_hierarchy (Fin.t (S n)) arithmetic_sigma 1 0
    (r0_arith_code_graph_open c).
Proof. intros. apply r0_arith_code_graph_sigma_one. Qed.

Corollary r0_arith_code_graph_semisentence_sigma_one : forall n
    (c : arith_code n),
  arithmetic_hierarchy Empty_set arithmetic_sigma 1 (S n)
    (r0_arith_code_graph_semisentence c).
Proof. intros. apply r0_arith_code_graph_sigma_one. Qed.

(** Proof-carrying Sigma-one views for clients using the sorted API. *)
Definition r0_arith_code_graph_open_sorted {n} (c : arith_code n) :
    arithmetic_sorted_formula (Fin.t (S n)) 0
      arithmetic_sigma_one_symbol :=
  ArithmeticSortedSigma 1 (r0_arith_code_graph_open c)
    (r0_arith_code_graph_open_sigma_one c).

Definition r0_arith_code_graph_semisentence_sorted {n}
    (c : arith_code n) :
    arithmetic_sorted_formula Empty_set (S n)
      arithmetic_sigma_one_symbol :=
  ArithmeticSortedSigma 1 (r0_arith_code_graph_semisentence c)
    (r0_arith_code_graph_semisentence_sigma_one c).
