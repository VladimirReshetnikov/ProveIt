From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** A small transparent sparse-polynomial implementation for the executable
    sextic resolvents.  Exponents have exactly six coordinates; a polynomial
    is an intentionally unnormalised list of integer coefficient/monomial
    pairs.  Equality is decided extensionally by collecting the finite union
    of the two supports and comparing summed coefficients there. *)
Module PolynomialFormulasSexticSparsePolynomials.

Definition sparse_exponent := 6.-tuple nat.
Definition sparse_term := (int * sparse_exponent)%type.
Definition sparse_polynomial := seq sparse_term.

Definition exponent_zero : sparse_exponent := [tuple 0 | _ < 6].

Definition exponent_single (j : 'I_6) : sparse_exponent :=
  [tuple if i == j then 1%N else 0%N | i < 6].

Definition exponent_add
    (a b : sparse_exponent) : sparse_exponent :=
  [tuple tnth a i + tnth b i | i < 6].

Lemma tnth_exponent_zeroE (i : 'I_6) : tnth exponent_zero i = 0%N.
Proof. by rewrite /exponent_zero tnth_mktuple. Qed.

Lemma tnth_exponent_singleE (i j : 'I_6) :
  tnth (exponent_single j) i = if i == j then 1%N else 0%N.
Proof. by rewrite /exponent_single tnth_mktuple. Qed.

Lemma tnth_exponent_addE (a b : sparse_exponent) (i : 'I_6) :
  tnth (exponent_add a b) i = tnth a i + tnth b i.
Proof. by rewrite /exponent_add tnth_mktuple. Qed.

Definition term_neg (t : sparse_term) : sparse_term := (- t.1, t.2).

Definition term_mul (a b : sparse_term) : sparse_term :=
  (a.1 * b.1, exponent_add a.2 b.2).

Definition sparse_zero : sparse_polynomial := [::].
Definition sparse_const (z : int) : sparse_polynomial := [:: (z, exponent_zero)].
Definition sparse_var (i : 'I_6) : sparse_polynomial :=
  [:: (1, exponent_single i)].
Definition sparse_add (p q : sparse_polynomial) : sparse_polynomial := p ++ q.
Definition sparse_neg (p : sparse_polynomial) : sparse_polynomial :=
  map term_neg p.
Definition sparse_sub (p q : sparse_polynomial) : sparse_polynomial :=
  sparse_add p (sparse_neg q).
Definition sparse_mul (p q : sparse_polynomial) : sparse_polynomial :=
  flatten [seq map (term_mul t) q | t <- p].

Fixpoint sparse_pow (p : sparse_polynomial) (n : nat) : sparse_polynomial :=
  if n is n'.+1 then sparse_mul p (sparse_pow p n') else sparse_const 1.

Definition sparse_support (p : sparse_polynomial) : seq sparse_exponent :=
  undup (map snd p).

Definition sparse_coefficient
    (p : sparse_polynomial) (d : sparse_exponent) : int :=
  
  \sum_(t <- p | t.2 == d) t.1.

Definition sparse_support_candidates
    (p q : sparse_polynomial) : seq sparse_exponent :=
  undup (sparse_support p ++ sparse_support q).

Definition sparse_equivalentb
    (p q : sparse_polynomial) : bool :=
  all (fun d => sparse_coefficient p d == sparse_coefficient q d)
    (sparse_support_candidates p q).

Lemma mem_sparse_support (p : sparse_polynomial) (d : sparse_exponent) :
  d \in sparse_support p <-> exists t, t \in p /\ t.2 = d.
Proof.
rewrite /sparse_support mem_undup.
split.
- move/mapP=> [t ht htd].
  by exists t; split.
- move=> [t [ht htd]].
  by apply/mapP; exists t.
Qed.

Lemma sparse_coefficient_eq0_of_not_mem
    (p : sparse_polynomial) (d : sparse_exponent) :
  d \notin sparse_support p -> sparse_coefficient p d = 0.
Proof.
move=> hd; rewrite /sparse_coefficient big_seq_cond.
apply: big1 => t /andP [ht /eqP htd].
have hmem : d \in sparse_support p.
  apply/(mem_sparse_support p d).
  by exists t; split=> //; exact: htd.
by move: hd; rewrite hmem.
Qed.

Lemma mem_sparse_support_candidates_left
    (p q : sparse_polynomial) (d : sparse_exponent) :
  d \in sparse_support p -> d \in sparse_support_candidates p q.
Proof.
rewrite /sparse_support_candidates
  (mem_undup (sparse_support p ++ sparse_support q)) mem_cat.
by move=> hp; rewrite hp.
Qed.

Lemma mem_sparse_support_candidates_right
    (p q : sparse_polynomial) (d : sparse_exponent) :
  d \in sparse_support q -> d \in sparse_support_candidates p q.
Proof.
rewrite /sparse_support_candidates
  (mem_undup (sparse_support p ++ sparse_support q)) mem_cat.
by move=> hq; rewrite hq orbT.
Qed.

Lemma sparse_equivalentbP (p q : sparse_polynomial) :
  reflect
    (forall d, sparse_coefficient p d = sparse_coefficient q d)
    (sparse_equivalentb p q).
Proof.
apply: (iffP allP).
- move=> h d.
  have [hd|hd] := boolP (d \in sparse_support_candidates p q).
  + exact/eqP/(h d hd).
  + have hdp : d \notin sparse_support p.
      apply/negP=> hmem.
      by move: hd; rewrite (mem_sparse_support_candidates_left q hmem).
    have hdq : d \notin sparse_support q.
      apply/negP=> hmem.
      by move: hd; rewrite (mem_sparse_support_candidates_right p hmem).
    by rewrite (sparse_coefficient_eq0_of_not_mem hdp)
      (sparse_coefficient_eq0_of_not_mem hdq).
- move=> h d hd.
  exact/eqP/h.
Qed.

(** Evaluation is defined directly from the unnormalised term list. *)
Definition exponent_value (values : 6.-tuple int)
    (d : sparse_exponent) : int :=
  \prod_(i : 'I_6) (tnth values i) ^+ (tnth d i).

Definition sparse_eval (values : 6.-tuple int)
    (p : sparse_polynomial) : int :=
  \sum_(t <- p) t.1 * exponent_value values t.2.

Lemma sparse_eval_support (values : 6.-tuple int) p :
  sparse_eval values p =
    \sum_(d <- sparse_support p)
      sparse_coefficient p d * exponent_value values d.
Proof.
rewrite /sparse_eval /sparse_support /sparse_coefficient.
symmetry.
under eq_bigr => d hd do rewrite big_distrl.
rewrite (exchange_big_dep predT) //=.
apply: eq_big_seq => t ht.
rewrite big_mkcond (bigD1_seq t.2).
- rewrite eqxx /=.
  rewrite big1 ?addr0 // => d hd.
  have htd : t.2 != d by rewrite eq_sym.
  by rewrite (negbTE htd).
- rewrite mem_undup.
  by apply/mapP; exists t.
- exact: undup_uniq.
Qed.

Lemma sparse_eval_ext (values : 6.-tuple int) p q :
  (forall d, sparse_coefficient p d = sparse_coefficient q d) ->
  sparse_eval values p = sparse_eval values q.
Proof.
move=> hpq; rewrite !sparse_eval_support.
under [RHS]eq_bigr => d hd do rewrite -hpq.
apply: perm_big_supp.
apply/uniq_perm.
- exact: filter_uniq (undup_uniq _).
- exact: filter_uniq (undup_uniq _).
- move=> d; rewrite !mem_filter.
  case hvalue: (sparse_coefficient p d * exponent_value values d != 0);
    last by [].
  have hcp : sparse_coefficient p d != 0.
    apply/negP=> /eqP hzero.
    by move: hvalue; rewrite hzero mul0r eqxx.
  have hmem_p : d \in sparse_support p.
    case hmem: (d \in sparse_support p) => //.
    have hnot : d \notin sparse_support p by rewrite hmem.
    by move: hcp; rewrite (sparse_coefficient_eq0_of_not_mem hnot) eqxx.
  have hcq : sparse_coefficient q d != 0 by rewrite -hpq.
  have hmem_q : d \in sparse_support q.
    case hmem: (d \in sparse_support q) => //.
    have hnot : d \notin sparse_support q by rewrite hmem.
    by move: hcq; rewrite (sparse_coefficient_eq0_of_not_mem hnot) eqxx.
  by rewrite hmem_p hmem_q.
Qed.

Lemma sparse_equivalentb_eval values p q :
  sparse_equivalentb p q -> sparse_eval values p = sparse_eval values q.
Proof. by move/(sparse_equivalentbP p q); apply: sparse_eval_ext. Qed.

Lemma exponent_value_zero (values : 6.-tuple int) :
  exponent_value values exponent_zero = 1.
Proof.
rewrite /exponent_value; apply: big1 => i _.
by rewrite tnth_exponent_zeroE expr0.
Qed.

Lemma exponent_value_single (values : 6.-tuple int) (j : 'I_6) :
  exponent_value values (exponent_single j) = tnth values j.
Proof.
rewrite /exponent_value.
rewrite (bigD1 j) //= tnth_exponent_singleE eqxx expr1.
suff hprod : \prod_(i < 6 | i != j)
    (tnth values i) ^+ (tnth (exponent_single j) i) = 1.
  by rewrite hprod mulr1.
apply: big1 => i hij.
by rewrite tnth_exponent_singleE (negbTE hij) expr0.
Qed.

Lemma exponent_value_add (values : 6.-tuple int)
    (a b : sparse_exponent) :
  exponent_value values (exponent_add a b) =
    exponent_value values a * exponent_value values b.
Proof.
rewrite /exponent_value.
under eq_bigr do rewrite tnth_exponent_addE exprD.
exact: big_split.
Qed.

Lemma sparse_eval_zero values : sparse_eval values sparse_zero = 0.
Proof. by rewrite /sparse_eval /sparse_zero big_nil. Qed.

Lemma sparse_eval_const values z :
  sparse_eval values (sparse_const z) = z.
Proof. by rewrite /sparse_eval /sparse_const big_seq1 exponent_value_zero mulr1. Qed.

Lemma sparse_eval_var values i :
  sparse_eval values (sparse_var i) = tnth values i.
Proof. by rewrite /sparse_eval /sparse_var big_seq1 exponent_value_single mul1r. Qed.

Lemma sparse_eval_add values p q :
  sparse_eval values (sparse_add p q) =
    sparse_eval values p + sparse_eval values q.
Proof. by rewrite /sparse_eval /sparse_add big_cat. Qed.

Lemma sparse_eval_neg values p :
  sparse_eval values (sparse_neg p) = - sparse_eval values p.
Proof.
rewrite /sparse_eval /sparse_neg big_map /=.
under eq_bigr do rewrite /term_neg /= mulNr.
exact: sumrN.
Qed.

Lemma sparse_eval_sub values p q :
  sparse_eval values (sparse_sub p q) =
    sparse_eval values p - sparse_eval values q.
Proof.
by rewrite /sparse_sub sparse_eval_add sparse_eval_neg.
Qed.

Lemma sparse_eval_mul values p q :
  sparse_eval values (sparse_mul p q) =
    sparse_eval values p * sparse_eval values q.
Proof.
rewrite /sparse_eval /sparse_mul big_flatten big_map /=.
under eq_bigr => t ht do
  rewrite big_map /=.
under eq_bigr => t ht do
  under eq_bigr => u hu do
    rewrite /term_mul /= exponent_value_add mulrACA.
rewrite big_distrl.
apply: eq_bigr => t ht.
by rewrite big_distrr.
Qed.

Lemma sparse_eval_pow values p n :
  sparse_eval values (sparse_pow p n) = sparse_eval values p ^+ n.
Proof.
elim: n => [|n ih] /=.
- exact (sparse_eval_const values 1).
- by rewrite sparse_eval_mul ih exprS.
Qed.

(** Transparent elementary-symmetric syntax and simultaneous substitution. *)
Fixpoint sparse_product (ps : seq sparse_polynomial) : sparse_polynomial :=
  if ps is p :: ps' then sparse_mul p (sparse_product ps')
  else sparse_const 1.

Fixpoint esymm_list (indices : seq 'I_6) (k : nat) : sparse_polynomial :=
  match k, indices with
  | 0%N, _ => sparse_const 1
  | _.+1, [::] => sparse_zero
  | k'.+1, i :: is' =>
      sparse_add
        (sparse_mul (sparse_var i) (esymm_list is' k'))
        (esymm_list is' k'.+1)
  end.

Definition six_indices : seq 'I_6 := enum 'I_6.

(** Coordinate [i] represents the elementary symmetric polynomial [e_(i+1)]. *)
Definition esymm_sparse (i : 'I_6) : sparse_polynomial :=
  esymm_list six_indices i.+1.

Definition substitute_term
    (values : 'I_6 -> sparse_polynomial) (t : sparse_term) :
    sparse_polynomial :=
  sparse_mul (sparse_const t.1)
    (sparse_product
      [seq sparse_pow (values i) (tnth t.2 i) | i <- six_indices]).

Definition sparse_substitute
    (values : 'I_6 -> sparse_polynomial) (p : sparse_polynomial) :
    sparse_polynomial :=
  flatten (map (substitute_term values) p).

Definition substitute_esymm (p : sparse_polynomial) : sparse_polynomial :=
  sparse_substitute esymm_sparse p.

Lemma sparse_eval_product values ps :
  sparse_eval values (sparse_product ps) =
    \prod_(p <- ps) sparse_eval values p.
Proof.
elim: ps => [|p ps ih] /=.
- by rewrite big_nil; exact (sparse_eval_const values 1).
- by rewrite sparse_eval_mul ih big_cons.
Qed.

Lemma sparse_eval_flatten values ps :
  sparse_eval values (flatten ps) =
    \sum_(p <- ps) sparse_eval values p.
Proof.
elim: ps => [|p ps ih] /=.
- by rewrite big_nil; exact (sparse_eval_zero values).
- by rewrite sparse_eval_add ih big_cons.
Qed.

Lemma sparse_eval_substitute_term
    (x : 6.-tuple int) (values : 'I_6 -> sparse_polynomial)
    (t : sparse_term) :
  sparse_eval x (substitute_term values t) =
    t.1 * exponent_value
      [tuple sparse_eval x (values i) | i < 6] t.2.
Proof.
rewrite /substitute_term sparse_eval_mul sparse_eval_const.
rewrite sparse_eval_product /exponent_value /six_indices.
apply f_equal.
rewrite big_map big_enum.
apply: eq_bigr => i _.
by rewrite sparse_eval_pow tnth_mktuple.
Qed.

Lemma sparse_eval_substitute
    (x : 6.-tuple int) (values : 'I_6 -> sparse_polynomial)
    (p : sparse_polynomial) :
  sparse_eval x (sparse_substitute values p) =
    sparse_eval [tuple sparse_eval x (values i) | i < 6] p.
Proof.
rewrite /sparse_substitute sparse_eval_flatten big_map /sparse_eval.
apply: eq_bigr => t ht.
exact: sparse_eval_substitute_term.
Qed.

Lemma sparse_eval_substitute_esymm (x : 6.-tuple int)
    (p : sparse_polynomial) :
  sparse_eval x (substitute_esymm p) =
    sparse_eval [tuple sparse_eval x (esymm_sparse i) | i < 6] p.
Proof. exact: sparse_eval_substitute. Qed.

End PolynomialFormulasSexticSparsePolynomials.
