(**
  Standard-model correctness of the arithmetic code graph compiler.

  The statement is uniform in the terms chosen for the output and inputs.
  This stronger form is what makes the induction go through beneath the
  existential blocks introduced by composition and minimization.
*)

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Lia
  Logic.FunctionalExtensionality
  Vectors.Fin.
From Foundation.Vorspiel Require Import Arithmetic Matrix Part.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Eq Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics OperatorSemantics RewriteClosure.
From Foundation.FirstOrder.Arithmetic.Basic Require Import
  Misc Syntax Model Hierarchy.
From Foundation.FirstOrder.Arithmetic.R0 Require Import CodeGraph.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Lemma r0_code_graph_lift_term_val : forall X q fresh
    (e : Fin.t fresh -> nat) (b : Fin.t q -> nat) (fv : X -> nat)
    (t : semiterm oring_language X q),
  semiterm_val nat_standard_structure (fin_env_append fresh q e b) fv
      (r0_code_graph_lift_term fresh t) =
  semiterm_val nat_standard_structure b fv t.
Proof.
  intros. unfold r0_code_graph_lift_term.
  rewrite semiterm_val_map, fin_env_append_right_eta. reflexivity.
Qed.

Lemma r0_code_graph_shift2_term_val : forall X q x z
    (b : Fin.t q -> nat) (fv : X -> nat)
    (t : semiterm oring_language X q),
  semiterm_val nat_standard_structure
      (fin_env_cons x (fin_env_cons z b)) fv
      (r0_code_graph_shift2_term t) =
  semiterm_val nat_standard_structure b fv t.
Proof.
  intros. unfold r0_code_graph_shift2_term, r0_code_graph_shift_term.
  rewrite !semiterm_val_bshift. reflexivity.
Qed.

Lemma r0_code_graph_matrix_vec_cons_val : forall X n q
    (b : Fin.t q -> nat) (fv : X -> nat)
    (head : semiterm oring_language X q)
    (tail : Fin.t n -> semiterm oring_language X q),
  (fun i => semiterm_val nat_standard_structure b fv
      (matrix_vec_cons head tail i)) =
  matrix_vec_cons (semiterm_val nat_standard_structure b fv head)
    (fun i => semiterm_val nat_standard_structure b fv (tail i)).
Proof.
  intros. change
    (matrix_vec_map (semiterm_val nat_standard_structure b fv)
      (matrix_vec_cons head tail) =
     matrix_vec_cons (semiterm_val nat_standard_structure b fv head)
       (matrix_vec_map (semiterm_val nat_standard_structure b fv) tail)).
  apply matrix_vec_map_cons.
Qed.

Lemma r0_code_graph_find_arguments_val : forall X n q x z
    (b : Fin.t q -> nat) (fv : X -> nat)
    (args : Fin.t n -> semiterm oring_language X q),
  (fun i => semiterm_val nat_standard_structure
      (fin_env_cons x (fin_env_cons z b)) fv
      (matrix_vec_cons
        (@Semiterm_bvar oring_language X (S (S q)) (Fin.FS Fin.F1))
        (fun j => r0_code_graph_shift2_term (args j)) i)) =
  matrix_vec_cons z
    (fun i => semiterm_val nat_standard_structure b fv (args i)).
Proof.
  intros. apply functional_extensionality. intro i.
  refine (@Fin.caseS' n i (fun j =>
    semiterm_val nat_standard_structure
      (fin_env_cons x (fin_env_cons z b)) fv
      (matrix_vec_cons
        (@Semiterm_bvar oring_language X (S (S q)) (Fin.FS Fin.F1))
        (fun u => r0_code_graph_shift2_term (args u)) j) =
    matrix_vec_cons z
      (fun u => semiterm_val nat_standard_structure b fv (args u)) j)
    eq_refl _).
  intro j. apply r0_code_graph_shift2_term_val.
Qed.

Lemma r0_code_graph_neq_eval : forall X q (b : Fin.t q -> nat)
    (fv : X -> nat) (t u : semiterm oring_language X q),
  semiformula_eval nat_standard_structure b fv
      (r0_code_graph_neq t u) <->
  semiterm_val nat_standard_structure b fv t <>
    semiterm_val nat_standard_structure b fv u.
Proof. intros. reflexivity. Qed.

Lemma r0_code_graph_nlt_eval : forall X q (b : Fin.t q -> nat)
    (fv : X -> nat) (t u : semiterm oring_language X q),
  semiformula_eval nat_standard_structure b fv
      (r0_code_graph_nlt t u) <->
  ~ semiterm_val nat_standard_structure b fv t <
    semiterm_val nat_standard_structure b fv u.
Proof. intros. reflexivity. Qed.

(** A code graph holds exactly at the unique value carried by the partial
    function denoted by its evaluation derivation. *)
Theorem r0_arith_code_graph_eval : forall n (c : arith_code n)
    (f : arith_partial_function n),
  arith_code_evaluates n c f ->
  forall X q (out : semiterm oring_language X q)
      (args : Fin.t n -> semiterm oring_language X q)
      (b : Fin.t q -> nat) (fv : X -> nat),
    semiformula_eval nat_standard_structure b fv
        (r0_arith_code_graph c out args) <->
    partial_member
      (f (fun i => semiterm_val nat_standard_structure b fv (args i)))
      (semiterm_val nat_standard_structure b fv out).
Proof.
  intros n c f Hcode.
  induction Hcode as
    [n
    |n
    |n i j
    |n i j
    |n i
    |n i j
    |n i j
    |m k outer inner f g Houter IHouter Hinner IHinner
    |n body f Hbody IHbody
    |n c f g Hf IHf Hext];
    intros X q out args b fv; simpl [r0_arith_code_graph].
  - rewrite (@arithmetic_eq_formula_eval nat X q
      nat_standard_structure b fv nat_oring_carrier out
      arithmetic_zero_term nat_standard_structure_interprets).
    rewrite (@arithmetic_zero_term_val nat X q
      nat_standard_structure b fv nat_oring_carrier
      nat_standard_structure_interprets).
    reflexivity.
  - rewrite (@arithmetic_eq_formula_eval nat X q
      nat_standard_structure b fv nat_oring_carrier out
      arithmetic_one_term nat_standard_structure_interprets).
    rewrite (@arithmetic_one_term_val nat X q
      nat_standard_structure b fv nat_oring_carrier
      nat_standard_structure_interprets).
    reflexivity.
  - rewrite (@arithmetic_eq_formula_eval nat X q
      nat_standard_structure b fv nat_oring_carrier out
      (arithmetic_add_term (args i) (args j))
      nat_standard_structure_interprets).
    rewrite (@arithmetic_add_term_val nat X q
      nat_standard_structure b fv nat_oring_carrier
      (args i) (args j) nat_standard_structure_interprets).
    reflexivity.
  - rewrite (@arithmetic_eq_formula_eval nat X q
      nat_standard_structure b fv nat_oring_carrier out
      (arithmetic_mul_term (args i) (args j))
      nat_standard_structure_interprets).
    rewrite (@arithmetic_mul_term_val nat X q
      nat_standard_structure b fv nat_oring_carrier
      (args i) (args j) nat_standard_structure_interprets).
    reflexivity.
  - reflexivity.
  - unfold nat_truth_eq. destruct (Nat.eq_dec
      (semiterm_val nat_standard_structure b fv (args i))
      (semiterm_val nat_standard_structure b fv (args j))); tauto.
  - unfold nat_truth_lt. destruct (lt_dec
      (semiterm_val nat_standard_structure b fv (args i))
      (semiterm_val nat_standard_structure b fv (args j))); tauto.
  - rewrite semiformula_eval_exists_iter. split.
    + intros [e [Hout Hins]].
      unfold arith_partial_comp, partial_bind. simpl.
      assert (Hargs :
        (fun j0 : Fin.t m =>
          semiterm_val nat_standard_structure
            (fin_env_append k q e b) fv
            (r0_code_graph_lift_term k (args j0))) =
        (fun j0 : Fin.t m =>
          semiterm_val nat_standard_structure b fv (args j0))).
      { apply functional_extensionality. intro j0.
        apply r0_code_graph_lift_term_val. }
      exists e. split.
      * intro i0.
        pose proof (proj1 (first_order_matrix_conj_eval
          nat_standard_structure (fin_env_append k q e b) fv
          (fun i1 => r0_arith_code_graph (inner i1)
            (Semiterm_bvar (Fin.L q i1))
            (fun j0 => r0_code_graph_lift_term k (args j0)))) Hins i0)
          as Hgraph.
        pose proof (proj1 (IHinner i0 X (k + q)
          (Semiterm_bvar (Fin.L q i0))
          (fun j0 => r0_code_graph_lift_term k (args j0))
          (fin_env_append k q e b) fv) Hgraph) as Hi.
        cbn beta in Hi.
        rewrite Hargs in Hi.
        simpl in Hi. rewrite fin_env_append_left in Hi. exact Hi.
      * apply (proj1 (IHouter X (k + q)
          (r0_code_graph_lift_term k out)
          (fun i0 => Semiterm_bvar (Fin.L q i0))
          (fin_env_append k q e b) fv)) in Hout.
        rewrite r0_code_graph_lift_term_val in Hout.
        assert (He :
          (fun i0 : Fin.t k =>
            semiterm_val nat_standard_structure
              (fin_env_append k q e b) fv
              (Semiterm_bvar (Fin.L q i0))) = e).
        { apply functional_extensionality. intro i0. simpl.
          apply fin_env_append_left. }
        now rewrite He in Hout.
    + intros [e [Hins Hout]].
      assert (Hargs :
        (fun j0 : Fin.t m =>
          semiterm_val nat_standard_structure
            (fin_env_append k q e b) fv
            (r0_code_graph_lift_term k (args j0))) =
        (fun j0 : Fin.t m =>
          semiterm_val nat_standard_structure b fv (args j0))).
      { apply functional_extensionality. intro j0.
        apply r0_code_graph_lift_term_val. }
      exists e. split.
      * apply (proj2 (IHouter X (k + q)
          (r0_code_graph_lift_term k out)
          (fun i0 => Semiterm_bvar (Fin.L q i0))
          (fin_env_append k q e b) fv)).
        rewrite r0_code_graph_lift_term_val.
        assert (He :
          (fun i0 : Fin.t k =>
            semiterm_val nat_standard_structure
              (fin_env_append k q e b) fv
              (Semiterm_bvar (Fin.L q i0))) = e).
        { apply functional_extensionality. intro i0. simpl.
          apply fin_env_append_left. }
        now rewrite He.
      * apply (proj2 (first_order_matrix_conj_eval
          nat_standard_structure (fin_env_append k q e b) fv
          (fun i0 => r0_arith_code_graph (inner i0)
            (Semiterm_bvar (Fin.L q i0))
            (fun j0 => r0_code_graph_lift_term k (args j0))))).
        intro i0.
        apply (proj2 (IHinner i0 X (k + q)
          (Semiterm_bvar (Fin.L q i0))
          (fun j0 => r0_code_graph_lift_term k (args j0))
          (fin_env_append k q e b) fv)).
        cbn beta. rewrite Hargs.
        simpl. rewrite fin_env_append_left. exact (Hins i0).
  - split.
    + intros [Hzero Hall]. split.
      * pose proof (proj1 (IHbody X q arithmetic_zero_term
          (matrix_vec_cons out args) b fv) Hzero) as Hz.
        cbn beta in Hz. rewrite r0_code_graph_matrix_vec_cons_val in Hz.
        simpl in Hz. now symmetry.
      * intros z Hzlt.
        specialize (Hall z).
        change
          (~ z < semiterm_val nat_standard_structure
              (fin_env_cons z b) fv (r0_code_graph_shift_term out) \/
           exists x, x <> 0 /\
             semiformula_eval nat_standard_structure
               (fin_env_cons x (fin_env_cons z b)) fv
               (r0_arith_code_graph body (Semiterm_bvar Fin.F1)
                 (matrix_vec_cons (Semiterm_bvar (Fin.FS Fin.F1))
                   (fun i => r0_code_graph_shift2_term (args i)))))
          in Hall.
        unfold r0_code_graph_shift_term in Hall.
        rewrite semiterm_val_bshift in Hall.
        destruct Hall as [Hnlt | [x [Hx Hgraph]]].
        -- contradiction.
        -- pose proof (proj1 (IHbody X (S (S q))
             (Semiterm_bvar Fin.F1)
             (matrix_vec_cons (Semiterm_bvar (Fin.FS Fin.F1))
               (fun i => r0_code_graph_shift2_term (args i)))
             (fin_env_cons x (fin_env_cons z b)) fv) Hgraph) as Hvalue.
           cbn beta in Hvalue.
           rewrite r0_code_graph_find_arguments_val in Hvalue.
           simpl in Hvalue. intro Hfz.
           apply Hx. now rewrite Hvalue, Hfz.
    + intros [Hzero Hall]. split.
      * apply (proj2 (IHbody X q arithmetic_zero_term
          (matrix_vec_cons out args) b fv)).
        cbn beta. rewrite r0_code_graph_matrix_vec_cons_val.
        simpl. now symmetry.
      * intro z.
        change
          (~ z < semiterm_val nat_standard_structure
              (fin_env_cons z b) fv (r0_code_graph_shift_term out) \/
           exists x, x <> 0 /\
             semiformula_eval nat_standard_structure
               (fin_env_cons x (fin_env_cons z b)) fv
               (r0_arith_code_graph body (Semiterm_bvar Fin.F1)
                 (matrix_vec_cons (Semiterm_bvar (Fin.FS Fin.F1))
                   (fun i => r0_code_graph_shift2_term (args i))))).
        unfold r0_code_graph_shift_term.
        rewrite semiterm_val_bshift.
        destruct (lt_dec z
          (semiterm_val nat_standard_structure b fv out)) as [Hzlt | Hnlt].
        -- right.
           set (value := f (matrix_vec_cons z
             (fun i => semiterm_val nat_standard_structure b fv (args i)))).
           exists value. split.
           ++ unfold value. apply Hall. exact Hzlt.
           ++ apply (proj2 (IHbody X (S (S q))
                (Semiterm_bvar Fin.F1)
                (matrix_vec_cons (Semiterm_bvar (Fin.FS Fin.F1))
                  (fun i => r0_code_graph_shift2_term (args i)))
                (fin_env_cons value (fin_env_cons z b)) fv)).
              cbn beta. rewrite r0_code_graph_find_arguments_val.
              simpl. reflexivity.
        -- now left.
  - etransitivity.
    + apply IHf.
    + apply Hext.
Qed.

(** Canonical finite-free-variable form, corresponding to the source
    correctness theorem for [codeAux]. *)
Corollary r0_arith_code_graph_open_eval : forall n (c : arith_code n)
    (f : arith_partial_function n),
  arith_code_evaluates n c f ->
  forall values : Fin.t (S n) -> nat,
    semiformula_eval nat_standard_structure (@fin_zero nat) values
        (r0_arith_code_graph_open c) <->
    partial_member (f (fun i => values (Fin.FS i))) (values Fin.F1).
Proof.
  intros n c f Hcode values.
  unfold r0_arith_code_graph_open.
  apply (r0_arith_code_graph_eval Hcode).
Qed.

(** Canonical bound-variable form, corresponding to the source theorem
    [models_code]. *)
Corollary r0_arith_code_graph_semisentence_eval : forall n
    (c : arith_code n) (f : arith_partial_function n),
  arith_code_evaluates n c f ->
  forall y (v : Fin.t n -> nat),
    semiformula_eval nat_standard_structure (matrix_vec_cons y v)
        (fun x : Empty_set => match x with end)
        (r0_arith_code_graph_semisentence c) <->
    partial_member (f v) y.
Proof.
  intros n c f Hcode y v.
  unfold r0_arith_code_graph_semisentence.
  apply (r0_arith_code_graph_eval Hcode).
Qed.
