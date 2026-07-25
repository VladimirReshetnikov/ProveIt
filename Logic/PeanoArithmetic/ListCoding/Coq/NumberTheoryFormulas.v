(** Explicit first-order PA formulae for [PAListNumberTheory]. *)

From Stdlib Require Import List Arith Lia Bool PeanoNat.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import
  ListCode Representability ListFormulas NumberTheory.

Import ListNotations.

Module PAListNumberTheoryFormulas.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAListFormulas.
Import PAListNumberTheory.

Definition oneTerm : term := tSucc tZero.
Definition twoTerm : term := tSucc oneTerm.

Definition pAnd7 (a b c d f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f (pAnd g h))))).

Definition pAnd8 (a b c d f g h i : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f (pAnd g (pAnd h i)))))).

(** * Divisibility and primality *)

(** Literally [exists q, value = divisor*q]. *)
Definition dividesTermAt (divisor value : term) : formula :=
  pEx (pEq
    (tMul (Term.rename S divisor) (tVar 0))
    (Term.rename S value)).

Lemma dividesTermAt_nat : forall e divisor value,
  Formula.Sat natModel e (dividesTermAt divisor value) <->
  Divides (Term.eval natModel e divisor) (Term.eval natModel e value).
Proof.
  intros e divisor value. unfold dividesTermAt, Divides.
  exact (Formula.dvdTermTermAt_nat e divisor value).
Qed.

(** A number greater than one whose only natural divisors are one and
    itself.  No primality atom is hidden in this syntax. *)
Definition primeTermAt (p : term) : formula :=
  pAnd
    (Formula.ltTermAt oneTerm p)
    (pAll
      (pImp
        (dividesTermAt (tVar 0) (liftTerm 1 p))
        (pOr
          (pEq (tVar 0) oneTerm)
          (pEq (tVar 0) (liftTerm 1 p))))).

Lemma primeTermAt_nat : forall e p,
  Formula.Sat natModel e (primeTermAt p) <->
  PrimeNat (Term.eval natModel e p).
Proof.
  intros e p. unfold primeTermAt, PrimeNat.
  cbn [Formula.Sat].
  setoid_rewrite Formula.ltTermAt_nat.
  setoid_rewrite dividesTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  reflexivity.
Qed.

(** * Strictly increasing coded lists *)

Definition strictlyIncreasingTermAt (v : term) : formula :=
  pEx
    (pAnd
      (hasLengthTermAt (liftTerm 1 v) (tVar 0))
      (pAll
        (pImp (Formula.ltTermAt (tSucc (tVar 0)) (tVar 1))
          (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 4 v) (tVar 2) (tVar 1))
              (pImp
                (nthElementTermAt (liftTerm 4 v)
                  (tSucc (tVar 2)) (tVar 0))
                (Formula.ltTermAt (tVar 1) (tVar 0))))))))).

Lemma strictlyIncreasingTermAt_nat : forall e v,
  Formula.Sat natModel e (strictlyIncreasingTermAt v) <->
  StrictlyIncreasingCode (Term.eval natModel e v).
Proof.
  intros e v. unfold strictlyIncreasingTermAt, StrictlyIncreasingCode.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [len [hlen h]]. exists len. split; [exact hlen |].
    intros i a b hi hia hib. exact (h i hi a b hia hib).
  - intros [len [hlen h]]. exists len. split; [exact hlen |].
    intros i hi a b hia hib. exact (h i a b hi hia hib).
Qed.

(** * The one-based nth prime *)

Definition nthPrimeTermAt (p n : term) : formula :=
  pEx (pEx
    (pAnd7
      (pEq (liftTerm 2 n) (tSucc (tVar 1)))
      (primeTermAt (liftTerm 2 p))
      (hasLengthTermAt (tVar 0) (tVar 1))
      (strictlyIncreasingTermAt (tVar 0))
      (pAll (pAll
        (pImp
          (nthElementTermAt (tVar 2) (tVar 1) (tVar 0))
          (pAnd
            (primeTermAt (tVar 0))
            (Formula.ltTermAt (tVar 0) (liftTerm 4 p))))))
      (pAll
        (pImp
          (pAnd
            (primeTermAt (tVar 0))
            (Formula.ltTermAt (tVar 0) (liftTerm 3 p)))
          (pEx (nthElementTermAt (tVar 2) (tVar 0) (tVar 1)))))
      (pEq tZero tZero))).

(** The last conjunct above is an explicit harmless truth, used only to keep
    the certificate layout visually parallel to the other relations. *)
Lemma nthPrimeTermAt_nat : forall e p n,
  Formula.Sat natModel e (nthPrimeTermAt p n) <->
  NthPrime (Term.eval natModel e p) (Term.eval natModel e n).
Proof.
  intros e p n. unfold nthPrimeTermAt, NthPrime, pAnd7.
  cbn [Formula.Sat].
  setoid_rewrite primeTermAt_nat.
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite strictlyIncreasingTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons3.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [k [below [hindex [hp [hlen [hstrict [hsound [hcomplete _]]]]]]]].
    split; [exact hp |]. exists k, below.
    split; [exact hindex |]. split; [exact hlen |].
    split; [exact hstrict |]. split.
    + intros i q hq. exact (hsound i q hq).
    + intros q hq. exact (hcomplete q hq).
  - intros [hp [k [below [hindex [hlen [hstrict [hsound hcomplete]]]]]]].
    exists k, below. split; [exact hindex |]. split; [exact hp |].
    split; [exact hlen |]. split; [exact hstrict |]. split.
    + intros i q hq. exact (hsound i q hq).
    + split.
      * intros q hq. exact (hcomplete q hq).
      * reflexivity.
Qed.

(** * Exponentiation *)

Definition powerTermAt (m n k : term) : formula :=
  pEx
    (pAnd4
      (hasLengthTermAt (tVar 0) (tSucc (liftTerm 1 k)))
      (nthElementTermAt (tVar 0) tZero oneTerm)
      (nthElementTermAt (tVar 0) (liftTerm 1 k) (liftTerm 1 m))
      (pAll
        (pImp
          (Formula.ltTermAt (tVar 0) (liftTerm 2 k))
          (pAll (pAll
            (pImp
              (nthElementTermAt (tVar 3) (tVar 2) (tVar 1))
              (pImp
                (nthElementTermAt (tVar 3) (tSucc (tVar 2)) (tVar 0))
                (pEq (tVar 0) (tMul (tVar 1) (liftTerm 4 n)))))))))).

Lemma powerTermAt_position : forall e m n k,
  Formula.Sat natModel e (powerTermAt m n k) <->
  PowerPosition (Term.eval natModel e m)
    (Term.eval natModel e n) (Term.eval natModel e k).
Proof.
  intros e m n k. unfold powerTermAt, PowerPosition, pAnd4.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons4.
  split.
  - intros [trace [hlen [hbase [hfinal hstep]]]].
    exists trace. repeat split; try assumption.
    intros i cur next hi hcur hnext. exact (hstep i hi cur next hcur hnext).
  - intros [trace [hlen [hbase [hfinal hstep]]]].
    exists trace. repeat split; try assumption.
    intros i hi cur next hcur hnext. exact (hstep i cur next hi hcur hnext).
Qed.

Lemma powerTermAt_nat : forall e m n k,
  Formula.Sat natModel e (powerTermAt m n k) <->
  PowerNat (Term.eval natModel e m)
    (Term.eval natModel e n) (Term.eval natModel e k).
Proof.
  intros. rewrite powerTermAt_position. apply PowerPosition_iff.
Qed.

(** Exact two-element list code [[p;e]]. *)
Definition factorPairTermAt (c p e : term) : formula :=
  pAnd3
    (hasLengthTermAt c twoTerm)
    (nthElementTermAt c tZero p)
    (nthElementTermAt c oneTerm e).

Lemma factorPairTermAt_nat : forall env c p e,
  Formula.Sat natModel env (factorPairTermAt c p e) <->
  FactorPair (Term.eval natModel env c)
    (Term.eval natModel env p) (Term.eval natModel env e).
Proof.
  intros env c p e. unfold factorPairTermAt, FactorPair, pAnd3.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  cbn. split.
  - intros [[xs [hx hlen]] [[ys [hy hp]] [zs [hz he]]]].
    rewrite hx in hy, hz. inversion hy; inversion hz; subst ys zs.
    destruct xs as [|x xs]; [discriminate |].
    destruct xs as [|y xs]; [discriminate |].
    destruct xs as [|z xs]; simpl in hlen; try lia.
    simpl in hp, he. inversion hp; inversion he; subst x y.
    exact hx.
  - intro h. repeat split.
    + exists [Term.eval natModel env p; Term.eval natModel env e].
      split; [exact h | reflexivity].
    + exists [Term.eval natModel env p; Term.eval natModel env e].
      split; [exact h | reflexivity].
    + exists [Term.eval natModel env p; Term.eval natModel env e].
      split; [exact h | reflexivity].
Qed.

(** Two additional lift-evaluation facts needed by the aligned
    factorization certificate. *)
Lemma eval_liftTerm_scons8 : forall a b c d f g h i env t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c (scons nat d
      (scons nat f (scons nat g (scons nat h (scons nat i env))))))))
    (liftTerm 8 t) = Term.eval natModel env t.
Proof. solve_eval_liftTerm. Qed.

Lemma eval_liftTerm_scons9 : forall a b c d f g h i j env t,
  Term.eval natModel
    (scons nat a (scons nat b (scons nat c (scons nat d
      (scons nat f (scons nat g (scons nat h
        (scons nat i (scons nat j env)))))))))
    (liftTerm 9 t) = Term.eval natModel env t.
Proof. solve_eval_liftTerm. Qed.

(** * Prime factorization

    The four outer witnesses are length, prime list, exponent list, and
    reconstructed-power list.  The public [v] remains the single canonical
    code whose entries are exact pair codes. *)
Definition primeFactorizationTermAt (v n : term) : formula :=
  pEx4
    (pAnd8
      (Formula.ltTermAt tZero (liftTerm 4 n))
      (hasLengthTermAt (liftTerm 4 v) (tVar 3))
      (hasLengthTermAt (tVar 2) (tVar 3))
      (hasLengthTermAt (tVar 1) (tVar 3))
      (hasLengthTermAt (tVar 0) (tVar 3))
      (strictlyIncreasingTermAt (tVar 2))
      (productElementsTermAt (liftTerm 4 n) (tVar 0))
      (pAll
        (pImp
          (Formula.ltTermAt (tVar 0) (tVar 4))
          (pAll (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 9 v) (tVar 4) (tVar 3))
              (pImp
                (nthElementTermAt (tVar 7) (tVar 4) (tVar 2))
                (pImp
                  (nthElementTermAt (tVar 6) (tVar 4) (tVar 1))
                  (pImp
                    (nthElementTermAt (tVar 5) (tVar 4) (tVar 0))
                    (pAnd4
                      (factorPairTermAt (tVar 3) (tVar 2) (tVar 1))
                      (primeTermAt (tVar 2))
                      (Formula.ltTermAt tZero (tVar 1))
                      (powerTermAt (tVar 0) (tVar 2) (tVar 1)))))))))))))).

Lemma primeFactorizationTermAt_nat : forall env v n,
  Formula.Sat natModel env (primeFactorizationTermAt v n) <->
  PrimeFactorizationCode
    (Term.eval natModel env v) (Term.eval natModel env n).
Proof.
  intros env v n.
  unfold primeFactorizationTermAt, PrimeFactorizationCode, pAnd8, pAnd4, pEx4.
  cbn [Formula.Sat].
  setoid_rewrite Formula.ltTermAt_nat.
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite strictlyIncreasingTermAt_nat.
  setoid_rewrite productElementsTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite factorPairTermAt_nat.
  setoid_rewrite primeTermAt_nat.
  setoid_rewrite powerTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons4.
  setoid_rewrite eval_liftTerm_scons9.
  split.
  - intros [len [primes [exponents [powers
      [hn [hv [hp [he [hw [hstrict [hprod halign]]]]]]]]]]].
    exists len, primes, exponents, powers.
    split; [exact hn |]. split; [exact hv |]. split; [exact hp |].
    split; [exact he |]. split; [exact hw |].
    split; [exact hstrict |]. split; [exact hprod |].
    intros i c p e w hi hvi hpi hei hwi.
    exact (halign i hi c p e w hvi hpi hei hwi).
  - intros [len [primes [exponents [powers
      [hn [hv [hp [he [hw [hstrict [hprod halign]]]]]]]]]]].
    exists len, primes, exponents, powers.
    split; [exact hn |]. split; [exact hv |]. split; [exact hp |].
    split; [exact he |]. split; [exact hw |].
    split; [exact hstrict |]. split; [exact hprod |].
    intros i hi c p e w hvi hpi hei hwi.
    exact (halign i c p e w hi hvi hpi hei hwi).
Qed.

(** * Most-significant-digit-first base expansions *)

Definition digitEvaluationTermAt (v n b : term) : formula :=
  pEx (pEx
    (pAnd5
      (hasLengthTermAt (liftTerm 2 v) (tVar 1))
      (hasLengthTermAt (tVar 0) (tSucc (tVar 1)))
      (nthElementTermAt (tVar 0) tZero tZero)
      (nthElementTermAt (tVar 0) (tVar 1) (liftTerm 2 n))
      (pAll
        (pImp (Formula.ltTermAt (tVar 0) (tVar 2))
          (pAll (pAll (pAll
            (pImp
              (nthElementTermAt (liftTerm 6 v) (tVar 3) (tVar 2))
              (pImp
                (nthElementTermAt (tVar 4) (tVar 3) (tVar 1))
                (pImp
                  (nthElementTermAt (tVar 4)
                    (tSucc (tVar 3)) (tVar 0))
                  (pEq (tVar 0)
                    (tAdd (tMul (tVar 1) (liftTerm 6 b))
                      (tVar 2))))))))))))).

Lemma digitEvaluationTermAt_nat : forall env v n b,
  Formula.Sat natModel env (digitEvaluationTermAt v n b) <->
  DigitEvaluationPosition
    (Term.eval natModel env v) (Term.eval natModel env n)
    (Term.eval natModel env b).
Proof.
  intros env v n b.
  unfold digitEvaluationTermAt, DigitEvaluationPosition,
    AggregatePosition, digitStep, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite hasLengthTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite Formula.ltTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons2.
  setoid_rewrite eval_liftTerm_scons6.
  split.
  - intros [len [trace [hv [ht [hbase [hfinal hstep]]]]]].
    exists len, trace. repeat split; try assumption.
    intros i d cur next hi hvi hti htn.
    exact (hstep i hi d cur next hvi hti htn).
  - intros [len [trace [hv [ht [hbase [hfinal hstep]]]]]].
    exists len, trace. repeat split; try assumption.
    intros i hi d cur next hvi hti htn.
    exact (hstep i d cur next hi hvi hti htn).
Qed.

Definition baseDigitsTermAt (v n b : term) : formula :=
  pAnd4
    (Formula.ltTermAt oneTerm b)
    (digitEvaluationTermAt v n b)
    (pAll (pAll
      (pImp
        (nthElementTermAt (liftTerm 2 v) (tVar 1) (tVar 0))
        (Formula.ltTermAt (tVar 0) (liftTerm 2 b)))))
    (pOr
      (pAnd (pEq n tZero) (singletonTermAt v tZero))
      (pAnd
        (Formula.ltTermAt tZero n)
        (pEx
          (pAnd
            (nthElementTermAt (liftTerm 1 v) tZero (tVar 0))
            (Formula.ltTermAt tZero (tVar 0)))))).

Lemma baseDigitsTermAt_nat : forall env v n b,
  Formula.Sat natModel env (baseDigitsTermAt v n b) <->
  BaseDigitsCode
    (Term.eval natModel env v) (Term.eval natModel env n)
    (Term.eval natModel env b).
Proof.
  intros env v n b. unfold baseDigitsTermAt, BaseDigitsCode, pAnd4.
  cbn [Formula.Sat].
  setoid_rewrite Formula.ltTermAt_nat.
  setoid_rewrite digitEvaluationTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite singletonTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons2.
  split.
  - intros [hb [heval [hbound hcanon]]].
    split; [lia |]. split; [exact heval |]. split.
    + intros i d hd. exact (hbound i d hd).
    + exact hcanon.
  - intros [hb [heval [hbound hcanon]]].
    split; [lia |]. split; [exact heval |]. split.
    + intros i d hd. exact (hbound i d hd).
    + exact hcanon.
Qed.

(** * Exact sorted divisor list *)

Definition divisorListTermAt (v n : term) : formula :=
  pAnd5
    (Formula.ltTermAt tZero n)
    (validCodeTermAt v)
    (strictlyIncreasingTermAt v)
    (pAll (pAll
      (pImp
        (nthElementTermAt (liftTerm 2 v) (tVar 1) (tVar 0))
        (pAnd
          (Formula.ltTermAt tZero (tVar 0))
          (dividesTermAt (tVar 0) (liftTerm 2 n))))))
    (pAll
      (pImp
        (Formula.ltTermAt tZero (tVar 0))
        (pImp
          (Formula.leTermAt (tVar 0) (liftTerm 1 n))
          (pImp
            (dividesTermAt (tVar 0) (liftTerm 1 n))
            (pEx
              (nthElementTermAt (liftTerm 2 v) (tVar 0) (tVar 1))))))).

Lemma divisorListTermAt_nat : forall env v n,
  Formula.Sat natModel env (divisorListTermAt v n) <->
  DivisorListCode
    (Term.eval natModel env v) (Term.eval natModel env n).
Proof.
  intros env v n. unfold divisorListTermAt, DivisorListCode, pAnd5.
  cbn [Formula.Sat].
  setoid_rewrite Formula.ltTermAt_nat.
  setoid_rewrite Formula.leTermAt_nat.
  setoid_rewrite validCodeTermAt_nat.
  setoid_rewrite strictlyIncreasingTermAt_nat.
  setoid_rewrite nthElementTermAt_nat.
  setoid_rewrite dividesTermAt_nat.
  cbn. setoid_rewrite eval_liftTerm_scons.
  setoid_rewrite eval_liftTerm_scons2.
  split.
  - intros [hn [hv [hstrict [hsound hcomplete]]]].
    split; [exact hn |]. split; [exact hv |].
    split; [exact hstrict |]. split; assumption.
  - intros [hn [hv [hstrict [hsound hcomplete]]]].
    split; [exact hn |]. split; [exact hv |].
    split; [exact hstrict |]. split; assumption.
Qed.

(** * Public formulae and their standard-model specifications

    Free-variable order is exactly the argument order advertised below. *)
Definition nthPrimeFormula : formula :=
  nthPrimeTermAt (tVar 0) (tVar 1).

Definition powerFormula : formula :=
  powerTermAt (tVar 0) (tVar 1) (tVar 2).

Definition primeFactorizationFormula : formula :=
  primeFactorizationTermAt (tVar 0) (tVar 1).

Definition baseDigitsFormula : formula :=
  baseDigitsTermAt (tVar 0) (tVar 1) (tVar 2).

Definition divisorListFormula : formula :=
  divisorListTermAt (tVar 0) (tVar 1).

Definition positiveDivisorsFormula : formula := divisorListFormula.

Theorem nthPrimeFormula_spec : forall env,
  Formula.Sat natModel env nthPrimeFormula <->
  NthPrime (env 0) (env 1).
Proof. intro env. unfold nthPrimeFormula. apply nthPrimeTermAt_nat. Qed.

Theorem powerFormula_spec : forall env,
  Formula.Sat natModel env powerFormula <->
  PowerNat (env 0) (env 1) (env 2).
Proof. intro env. unfold powerFormula. apply powerTermAt_nat. Qed.

Theorem primeFactorizationFormula_spec : forall env,
  Formula.Sat natModel env primeFactorizationFormula <->
  PrimeFactorizationCode (env 0) (env 1).
Proof.
  intro env. unfold primeFactorizationFormula.
  apply primeFactorizationTermAt_nat.
Qed.

Theorem baseDigitsFormula_spec : forall env,
  Formula.Sat natModel env baseDigitsFormula <->
  BaseDigitsCode (env 0) (env 1) (env 2).
Proof. intro env. unfold baseDigitsFormula. apply baseDigitsTermAt_nat. Qed.

Theorem divisorListFormula_spec : forall env,
  Formula.Sat natModel env divisorListFormula <->
  DivisorListCode (env 0) (env 1).
Proof. intro env. unfold divisorListFormula. apply divisorListTermAt_nat. Qed.

Theorem nthPrimeFormula_correct : forall env,
  Formula.Sat natModel env nthPrimeFormula <->
  NthPrime (env 0) (env 1).
Proof. exact nthPrimeFormula_spec. Qed.

Theorem powerFormula_correct : forall env,
  Formula.Sat natModel env powerFormula <->
  PowerNat (env 0) (env 1) (env 2).
Proof. exact powerFormula_spec. Qed.

Theorem primeFactorizationFormula_correct : forall env,
  Formula.Sat natModel env primeFactorizationFormula <->
  PrimeFactorizationCode (env 0) (env 1).
Proof. exact primeFactorizationFormula_spec. Qed.

Theorem baseDigitsFormula_correct : forall env,
  Formula.Sat natModel env baseDigitsFormula <->
  BaseDigitsCode (env 0) (env 1) (env 2).
Proof. exact baseDigitsFormula_spec. Qed.

Theorem divisorListFormula_correct : forall env,
  Formula.Sat natModel env divisorListFormula <->
  DivisorListCode (env 0) (env 1).
Proof. exact divisorListFormula_spec. Qed.

Theorem positiveDivisorsFormula_correct : forall env,
  Formula.Sat natModel env positiveDivisorsFormula <->
  PositiveDivisorsCode (env 0) (env 1).
Proof.
  intro env. unfold positiveDivisorsFormula, PositiveDivisorsCode.
  apply divisorListFormula_spec.
Qed.

End PAListNumberTheoryFormulas.
